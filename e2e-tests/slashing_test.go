package provider_test

import (
	"time"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"
	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
	abci "github.com/tendermint/tendermint/abci/types"
)

// TestSendDowntimePacket tests consumer initiated slashing
func (s *ProviderTestSuite) TestSendSlashPacketDowntime() {
	s.SetupCCVChannel()
	validatorsPerChain := len(s.consumerChain.Vals.Validators)

	providerStakingKeeper := s.providerChain.App.(*appProvider.App).StakingKeeper
	providerSlashingKeeper := s.providerChain.App.(*appProvider.App).SlashingKeeper

	consumerKeeper := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper

	// get a cross-chain validator address, pubkey and balance
	tmVals := s.consumerChain.Vals.Validators
	tmVal := tmVals[0]

	val, err := tmVal.ToProto()
	s.Require().NoError(err)
	pubkey, err := cryptocodec.FromTmProtoPublicKey(val.GetPubKey())
	s.Require().Nil(err)
	consAddr := sdk.GetConsAddress(pubkey)
	valData, found := providerStakingKeeper.GetValidatorByConsAddr(s.providerCtx(), consAddr)
	s.Require().True(found)
	valOldBalance := valData.Tokens

	// create the validator's signing info record to allow jailing
	valInfo := slashingtypes.NewValidatorSigningInfo(consAddr, s.providerCtx().BlockHeight(),
		s.providerCtx().BlockHeight()-1, time.Time{}.UTC(), false, int64(0))
	providerSlashingKeeper.SetValidatorSigningInfo(s.providerCtx(), consAddr, valInfo)

	// get valseUpdateId for current block height
	valsetUpdateId := consumerKeeper.GetHeightValsetUpdateID(s.consumerCtx(), uint64(s.consumerCtx().BlockHeight()))

	// construct the downtime packet with the validator address and power along
	// with the slashing and jailing parameters
	validator := abci.Validator{
		Address: tmVal.Address,
		Power:   tmVal.VotingPower,
	}

	oldBlockTime := s.consumerCtx().BlockTime()
	slashFraction := int64(100)
	packetData := ccvtypes.NewSlashPacketData(validator, valsetUpdateId, stakingtypes.Downtime)
	timeout := uint64(ccvtypes.GetTimeoutTimestamp(oldBlockTime).UnixNano())
	packet := channeltypes.NewPacket(packetData.GetBytes(), 1, consumertypes.PortID, s.path.EndpointA.ChannelID,
		providertypes.PortID, s.path.EndpointB.ChannelID, clienttypes.Height{}, timeout)

	// Send the downtime packet through CCV
	err = s.path.EndpointA.SendPacket(packet)
	s.Require().NoError(err)

	// Set outstanding slashing flag
	s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.SetOutstandingDowntime(s.consumerCtx(), consAddr)

	// save next VSC packet info
	oldBlockTime = s.providerCtx().BlockTime()
	timeout = uint64(ccvtypes.GetTimeoutTimestamp(oldBlockTime).UnixNano())
	valsetUpdateID := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetValidatorSetUpdateId(s.providerCtx())

	// receive the downtime packet on the provider chain;
	// RecvPacket() calls the provider endblocker thus sends a VSC packet to the consumer
	err = s.path.EndpointB.RecvPacket(packet)
	s.Require().NoError(err)

	// check that the validator was removed from the provider validator set
	s.Require().Len(s.providerChain.Vals.Validators, validatorsPerChain-1)
	// check that the VSC ID is updated on the consumer chain

	// update consumer client on the VSC packet sent from provider
	err = s.path.EndpointA.UpdateClient()
	s.Require().NoError(err)

	// reconstruct VSC packet
	valUpdates := []abci.ValidatorUpdate{
		{
			PubKey: val.GetPubKey(),
			Power:  int64(0),
		},
	}
	packetData2 := ccvtypes.NewValidatorSetChangePacketData(valUpdates, valsetUpdateID, []string{consAddr.String()})
	packet2 := channeltypes.NewPacket(packetData2.GetBytes(), 1, providertypes.PortID, s.path.EndpointB.ChannelID,
		consumertypes.PortID, s.path.EndpointA.ChannelID, clienttypes.Height{}, timeout)

	// receive VSC packet about jailing on the consumer chain
	err = s.path.EndpointA.RecvPacket(packet2)
	s.Require().NoError(err)

	// check that the consumer update its VSC ID for the subsequent block
	s.Require().Equal(consumerKeeper.GetHeightValsetUpdateID(s.consumerCtx(), uint64(s.consumerCtx().BlockHeight())+1), valsetUpdateID)

	// check that the validator was removed from the consumer validator set
	s.Require().Len(s.consumerChain.Vals.Validators, validatorsPerChain-1)

	err = s.path.EndpointB.UpdateClient()
	s.Require().NoError(err)

	// check that the validator is successfully jailed on provider

	validatorJailed, ok := s.providerChain.App.(*appProvider.App).StakingKeeper.GetValidatorByConsAddr(s.providerCtx(), consAddr)
	s.Require().True(ok)
	s.Require().True(validatorJailed.Jailed)
	s.Require().Equal(validatorJailed.Status, stakingtypes.Unbonding)

	// check that the validator's token was slashed
	slashedAmout := sdk.NewDec(1).QuoInt64(slashFraction).Mul(valOldBalance.ToDec())
	resultingTokens := valOldBalance.Sub(slashedAmout.TruncateInt())
	s.Require().Equal(resultingTokens, validatorJailed.GetTokens())

	// check that the validator's unjailing time is updated
	valSignInfo, found := providerSlashingKeeper.GetValidatorSigningInfo(s.providerCtx(), consAddr)
	s.Require().True(found)
	s.Require().True(valSignInfo.JailedUntil.After(s.providerCtx().BlockHeader().Time))

	// check that the outstanding slashing flag is reset on the consumer
	pFlag := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.OutstandingDowntime(s.consumerCtx(), consAddr)
	s.Require().False(pFlag)

	// check that slashing packet gets acknowledged
	ack := channeltypes.NewResultAcknowledgement([]byte{byte(1)})
	err = s.path.EndpointA.AcknowledgePacket(packet, ack.Acknowledgement())
	s.Require().NoError(err)
}

func (s *ProviderTestSuite) TestSendSlashPacketDoubleSign() {
	s.SetupCCVChannel()
	validatorsPerChain := len(s.consumerChain.Vals.Validators)

	providerStakingKeeper := s.providerChain.App.(*appProvider.App).StakingKeeper
	providerSlashingKeeper := s.providerChain.App.(*appProvider.App).SlashingKeeper
	consumerKeeper := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper

	// get a cross-chain validator address, pubkey and balance
	tmVals := s.consumerChain.Vals.Validators
	tmVal := tmVals[0]

	val, err := tmVal.ToProto()
	s.Require().NoError(err)
	pubkey, err := cryptocodec.FromTmProtoPublicKey(val.GetPubKey())
	s.Require().Nil(err)
	consAddr := sdk.GetConsAddress(pubkey)
	valData, found := providerStakingKeeper.GetValidatorByConsAddr(s.providerCtx(), consAddr)
	s.Require().True(found)
	valOldBalance := valData.Tokens

	// create the validator's signing info record to allow jailing
	valInfo := slashingtypes.NewValidatorSigningInfo(consAddr, s.providerCtx().BlockHeight(),
		s.providerCtx().BlockHeight()-1, time.Time{}.UTC(), false, int64(0))
	providerSlashingKeeper.SetValidatorSigningInfo(s.providerCtx(), consAddr, valInfo)

	// get valseUpdateId for current block height
	valsetUpdateId := consumerKeeper.GetHeightValsetUpdateID(s.consumerCtx(), uint64(s.consumerCtx().BlockHeight()))

	// construct the downtime packet with the validator address and power along
	// with the slashing and jailing parameters
	validator := abci.Validator{
		Address: tmVal.Address,
		Power:   tmVal.VotingPower,
	}

	oldBlockTime := s.consumerCtx().BlockTime()
	packetData := ccvtypes.NewSlashPacketData(validator, valsetUpdateId, stakingtypes.DoubleSign)

	timeout := uint64(ccvtypes.GetTimeoutTimestamp(oldBlockTime).UnixNano())
	packet := channeltypes.NewPacket(packetData.GetBytes(), 1, consumertypes.PortID, s.path.EndpointA.ChannelID,
		providertypes.PortID, s.path.EndpointB.ChannelID, clienttypes.Height{}, timeout)

	// Send the downtime packet through CCV
	err = s.path.EndpointA.SendPacket(packet)
	s.Require().NoError(err)

	// save next VSC packet info
	oldBlockTime = s.providerCtx().BlockTime()
	timeout = uint64(ccvtypes.GetTimeoutTimestamp(oldBlockTime).UnixNano())
	valsetUpdateID := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetValidatorSetUpdateId(s.providerCtx())

	// receive the downtime packet on the provider chain;
	// RecvPacket() calls the provider endblocker and thus sends a VSC packet to the consumer
	err = s.path.EndpointB.RecvPacket(packet)
	s.Require().NoError(err)

	// check that the validator was removed from the provider validator set
	s.Require().Len(s.providerChain.Vals.Validators, validatorsPerChain-1)
	// check that the VSC ID is updated on the consumer chain

	// update consumer client on the VSC packet sent from provider
	err = s.path.EndpointA.UpdateClient()
	s.Require().NoError(err)

	// reconstruct VSC packet
	valUpdates := []abci.ValidatorUpdate{
		{
			PubKey: val.GetPubKey(),
			Power:  int64(0),
		},
	}
	packetData2 := ccvtypes.NewValidatorSetChangePacketData(valUpdates, valsetUpdateID, []string{})
	packet2 := channeltypes.NewPacket(packetData2.GetBytes(), 1, providertypes.PortID, s.path.EndpointB.ChannelID,
		consumertypes.PortID, s.path.EndpointA.ChannelID, clienttypes.Height{}, timeout)

	// receive VSC packet about jailing on the consumer chain
	err = s.path.EndpointA.RecvPacket(packet2)
	s.Require().NoError(err)

	// check that the consumer update its VSC ID for the subsequent block
	s.Require().Equal(consumerKeeper.GetHeightValsetUpdateID(s.consumerCtx(), uint64(s.consumerCtx().BlockHeight())+1), valsetUpdateID)

	// check that the validator was removed from the consumer validator set
	s.Require().Len(s.consumerChain.Vals.Validators, validatorsPerChain-1)

	err = s.path.EndpointB.UpdateClient()
	s.Require().NoError(err)

	// check that the validator is successfully jailed on provider
	validatorJailed, ok := s.providerChain.App.(*appProvider.App).StakingKeeper.GetValidatorByConsAddr(s.providerCtx(), consAddr)
	s.Require().True(ok)
	s.Require().True(validatorJailed.Jailed)
	s.Require().Equal(validatorJailed.Status, stakingtypes.Unbonding)

	// check that the validator's token was slashed
	slashedAmount := providerSlashingKeeper.SlashFractionDoubleSign(s.providerCtx()).Mul(valOldBalance.ToDec())
	resultingTokens := valOldBalance.Sub(slashedAmount.TruncateInt())

	s.Require().Equal(resultingTokens, validatorJailed.GetTokens())

	// check that the validator's unjailing time is updated
	valSignInfo, found := providerSlashingKeeper.GetValidatorSigningInfo(s.providerCtx(), consAddr)
	s.Require().True(found)
	s.Require().True(valSignInfo.JailedUntil.After(s.providerCtx().BlockHeader().Time))

	// check that validator was tombstoned
	s.Require().True(valSignInfo.Tombstoned)
	s.Require().True(valSignInfo.JailedUntil.Equal(evidencetypes.DoubleSignJailEndTime))
}

func (s *ProviderTestSuite) TestSlashPacketAcknowledgement() {
	providerKeeper := s.providerChain.App.(*appProvider.App).ProviderKeeper
	consumerKeeper := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper

	packet := channeltypes.NewPacket([]byte{}, 1, consumertypes.PortID, s.path.EndpointA.ChannelID,
		providertypes.PortID, "wrongchannel", clienttypes.Height{}, 0)

	ack := providerKeeper.OnRecvSlashPacket(s.providerCtx(), packet, ccvtypes.SlashPacketData{})
	s.Require().NotNil(ack)

	err := consumerKeeper.OnAcknowledgementPacket(s.consumerCtx(), packet, channeltypes.NewResultAcknowledgement(ack.Acknowledgement()))
	s.Require().NoError(err)

	err = consumerKeeper.OnAcknowledgementPacket(s.consumerCtx(), packet, channeltypes.NewErrorAcknowledgement("another error"))
	s.Require().Error(err)
}
