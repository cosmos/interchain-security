package e2e

import (
	"time"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	icstestingutils "github.com/cosmos/interchain-security/testutil/ibc_testing"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	abci "github.com/tendermint/tendermint/abci/types"
)

func (s *CCVTestSuite) TestSlashPacketThrottling() {
	s.SetupAllCCVChannels()
	s.setupValidatorPowers()

	// try different params in test cases
	params := providertypes.DefaultParams()
	params.SlashMeterReplenishFraction = "0.2" // Will take two replenishes for second slash
	s.providerApp.GetProviderKeeper().SetParams(s.providerCtx(), params)

	valsBefore := s.getValidatorsWithPower()
	packet := constructSlashPacketFromConsumer(s, s.getFirstBundle(), 0, stakingtypes.Downtime, 1)

	// TODO: make this a helper or see if it exists
	err := s.path.EndpointA.SendPacket(packet)
	s.Require().NoError(err)
	err = s.path.EndpointB.RecvPacket(packet)
	s.Require().NoError(err)
	s.providerChain.NextBlock() // cause N+3

	valsAfter := s.getValidatorsWithPower()

	s.Require().Equal(len(valsBefore)-1, len(valsAfter))
	slashMeter := s.providerApp.GetProviderKeeper().GetSlashMeter(s.providerCtx())
	s.Require().True(slashMeter.IsNegative())

	packet = constructSlashPacketFromConsumer(s, s.getFirstBundle(), 2, stakingtypes.Downtime, 2)

	err = s.path.EndpointA.SendPacket(packet)
	s.Require().NoError(err)
	err = s.path.EndpointB.RecvPacket(packet)
	s.Require().NoError(err)
	s.providerChain.NextBlock() // cause N+3

	// Val isn't removed yet, slash meter is negative
	s.Require().Equal(len(valsAfter), len(s.getValidatorsWithPower()))
	s.Require().True(slashMeter.IsNegative())

	// TODO: do the below better, maybe replenish through block time.
	s.providerApp.GetProviderKeeper().ReplenishSlashMeter(s.providerCtx())
	slashMeter = s.providerApp.GetProviderKeeper().GetSlashMeter(s.providerCtx())
	s.Require().True(slashMeter.IsNegative())
	s.providerApp.GetProviderKeeper().ReplenishSlashMeter(s.providerCtx())
	slashMeter = s.providerApp.GetProviderKeeper().GetSlashMeter(s.providerCtx())
	s.Require().True(slashMeter.IsPositive())

	// TODO: assert more logic about meter level, etc.

	s.providerChain.NextBlock()
	s.providerChain.NextBlock()
	s.providerChain.NextBlock()

	// Val is removed
	s.Require().Equal(len(valsBefore)-2, len(s.getValidatorsWithPower()))

}

// TODO(Shawn): Add more e2e tests for edge cases

// TODO: write test around replenish fraction being too small and the allowance being 1 (min value)

// TODO: test vsc matured stuff too, or add to above test?

// TODO: multiple consumers

// TODO: Move to common.go and use in other slashing tests that you copied this from
func constructSlashPacketFromConsumer(s *CCVTestSuite, bundle icstestingutils.ConsumerBundle,
	valIdx int, infractionType stakingtypes.InfractionType, ibcSeqNum uint64) channeltypes.Packet {

	if valIdx >= len(bundle.Chain.Vals.Validators) {
		panic("valIdx out of range")
	}

	providerSlashingKeeper := s.providerApp.GetE2eSlashingKeeper()

	tmVal := bundle.Chain.Vals.Validators[valIdx]
	val, err := tmVal.ToProto()
	s.Require().NoError(err)
	pubkey, err := cryptocodec.FromTmProtoPublicKey(val.GetPubKey())
	s.Require().Nil(err)
	consAddr := sdk.GetConsAddress(pubkey)

	_, found := providerSlashingKeeper.GetValidatorSigningInfo(s.providerCtx(), consAddr)
	if !found {
		// create the validator's signing info record to allow jailing
		valInfo := slashingtypes.NewValidatorSigningInfo(consAddr, s.providerCtx().BlockHeight(),
			s.providerCtx().BlockHeight()-1, time.Time{}.UTC(), false, int64(0))
		providerSlashingKeeper.SetValidatorSigningInfo(s.providerCtx(), consAddr, valInfo)
	}

	valsetUpdateId := bundle.GetKeeper().GetHeightValsetUpdateID(
		bundle.GetCtx(), uint64(bundle.GetCtx().BlockHeight()))
	data := ccv.SlashPacketData{
		Validator: abci.Validator{
			Address: tmVal.Address,
			Power:   tmVal.VotingPower,
		},
		ValsetUpdateId: valsetUpdateId,
		Infraction:     infractionType,
	}
	return channeltypes.NewPacket(data.GetBytes(),
		ibcSeqNum,
		ccv.ConsumerPortID,              // Src port
		bundle.Path.EndpointA.ChannelID, // Src channel
		ccv.ProviderPortID,              // Dst port
		bundle.Path.EndpointB.ChannelID, // Dst channel
		clienttypes.Height{},
		uint64(bundle.GetCtx().BlockTime().Add(ccv.DefaultCCVTimeoutPeriod).UnixNano()),
	)
}
