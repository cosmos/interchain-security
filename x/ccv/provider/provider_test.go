package provider_test

import (
	"bytes"
	"testing"
	"time"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	distrtypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"
	slashingtypes "github.com/cosmos/cosmos-sdk/x/slashing/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/cosmos/interchain-security/x/ccv/utils"

	transfertypes "github.com/cosmos/ibc-go/v3/modules/apps/transfer/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"

	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	"github.com/cosmos/interchain-security/testutil/simapp"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/cosmos/interchain-security/x/ccv/types"

	abci "github.com/tendermint/tendermint/abci/types"
	tmtypes "github.com/tendermint/tendermint/types"

	"github.com/stretchr/testify/suite"
)

type ProviderTestSuite struct {
	suite.Suite

	coordinator *ibctesting.Coordinator

	// testing chains
	providerChain *ibctesting.TestChain
	consumerChain *ibctesting.TestChain

	path         *ibctesting.Path
	transferPath *ibctesting.Path

	providerDistrIndex int
}

func (suite *ProviderTestSuite) SetupTest() {
	suite.coordinator, suite.providerChain, suite.consumerChain = simapp.NewProviderConsumerCoordinator(suite.T())

	// valsets must match
	providerValUpdates := tmtypes.TM2PB.ValidatorUpdates(suite.providerChain.Vals)
	consumerValUpdates := tmtypes.TM2PB.ValidatorUpdates(suite.consumerChain.Vals)
	suite.Require().True(len(providerValUpdates) == len(consumerValUpdates), "initial valset not matching")
	for i := 0; i < len(providerValUpdates); i++ {
		addr1 := utils.GetChangePubKeyAddress(providerValUpdates[i])
		addr2 := utils.GetChangePubKeyAddress(consumerValUpdates[i])
		suite.Require().True(bytes.Compare(addr1, addr2) == 0, "validator mismatch")
	}

	// suite.DisableConsumerDistribution()

	// move both chains to the next block
	suite.providerChain.NextBlock()
	suite.consumerChain.NextBlock()

	// create consumer client on provider chain and set as consumer client for consumer chainID in provider keeper.
	suite.providerChain.App.(*appProvider.App).ProviderKeeper.CreateConsumerClient(
		suite.providerCtx(),
		suite.consumerChain.ChainID,
		suite.consumerChain.LastHeader.GetHeight().(clienttypes.Height),
	)
	// move provider to next block to commit the state
	suite.providerChain.NextBlock()

	// initialize the consumer chain with the genesis state stored on the provider
	consumerGenesis, found := suite.providerChain.App.(*appProvider.App).ProviderKeeper.GetConsumerGenesis(
		suite.providerCtx(),
		suite.consumerChain.ChainID,
	)
	suite.Require().True(found, "consumer genesis not found")
	suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.InitGenesis(suite.consumerChain.GetContext(), &consumerGenesis)

	// create path for the CCV channel
	suite.path = ibctesting.NewPath(suite.consumerChain, suite.providerChain)

	// update CCV path with correct info
	// - set provider endpoint's clientID
	consumerClient, found := suite.providerChain.App.(*appProvider.App).ProviderKeeper.GetConsumerClientId(
		suite.providerCtx(),
		suite.consumerChain.ChainID,
	)
	suite.Require().True(found, "consumer client not found")
	suite.path.EndpointB.ClientID = consumerClient
	// - set consumer endpoint's clientID
	providerClient, found := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetProviderClient(suite.consumerChain.GetContext())
	suite.Require().True(found, "provider client not found")
	suite.path.EndpointA.ClientID = providerClient
	// - client config
	providerUnbondingPeriod := suite.providerChain.App.(*appProvider.App).GetStakingKeeper().UnbondingTime(suite.providerCtx())
	suite.path.EndpointB.ClientConfig.(*ibctesting.TendermintConfig).UnbondingPeriod = providerUnbondingPeriod
	suite.path.EndpointB.ClientConfig.(*ibctesting.TendermintConfig).TrustingPeriod = providerUnbondingPeriod / utils.TrustingPeriodFraction
	consumerUnbondingPeriod := utils.ComputeConsumerUnbondingPeriod(providerUnbondingPeriod)
	suite.path.EndpointA.ClientConfig.(*ibctesting.TendermintConfig).UnbondingPeriod = consumerUnbondingPeriod
	suite.path.EndpointA.ClientConfig.(*ibctesting.TendermintConfig).TrustingPeriod = consumerUnbondingPeriod / utils.TrustingPeriodFraction
	// - channel config
	suite.path.EndpointA.ChannelConfig.PortID = consumertypes.PortID
	suite.path.EndpointB.ChannelConfig.PortID = providertypes.PortID
	suite.path.EndpointA.ChannelConfig.Version = types.Version
	suite.path.EndpointB.ChannelConfig.Version = types.Version
	suite.path.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
	suite.path.EndpointB.ChannelConfig.Order = channeltypes.ORDERED

	// set chains sender account number
	// TODO: to be fixed in #151
	suite.path.EndpointB.Chain.SenderAccount.SetAccountNumber(6)
	suite.path.EndpointA.Chain.SenderAccount.SetAccountNumber(1)

	// create path for the transfer channel
	suite.transferPath = ibctesting.NewPath(suite.consumerChain, suite.providerChain)
	suite.transferPath.EndpointA.ChannelConfig.PortID = transfertypes.PortID
	suite.transferPath.EndpointB.ChannelConfig.PortID = transfertypes.PortID
	suite.transferPath.EndpointA.ChannelConfig.Version = transfertypes.Version
	suite.transferPath.EndpointB.ChannelConfig.Version = transfertypes.Version
}

func (suite *ProviderTestSuite) SetupCCVChannel() {
	suite.coordinator.CreateConnections(suite.path)

	// CCV channel handshake will automatically initiate transfer channel handshake on ACK
	// so transfer channel will be on stage INIT when CreateChannels for ccv path returns.
	suite.coordinator.CreateChannels(suite.path)

	// transfer path will use the same connection as ccv path

	suite.transferPath.EndpointA.ClientID = suite.path.EndpointA.ClientID
	suite.transferPath.EndpointA.ConnectionID = suite.path.EndpointA.ConnectionID
	suite.transferPath.EndpointB.ClientID = suite.path.EndpointB.ClientID
	suite.transferPath.EndpointB.ConnectionID = suite.path.EndpointB.ConnectionID

	// INIT step for transfer path has already been called during CCV channel setup
	suite.transferPath.EndpointA.ChannelID = suite.consumerChain.App.(*appConsumer.App).
		ConsumerKeeper.GetDistributionTransmissionChannel(suite.consumerChain.GetContext())

	// Complete TRY, ACK, CONFIRM for transfer path
	err := suite.transferPath.EndpointB.ChanOpenTry()
	suite.Require().NoError(err)

	err = suite.transferPath.EndpointA.ChanOpenAck()
	suite.Require().NoError(err)

	err = suite.transferPath.EndpointB.ChanOpenConfirm()
	suite.Require().NoError(err)

	// ensure counterparty is up to date
	suite.transferPath.EndpointA.UpdateClient()
}

func TestProviderTestSuite(t *testing.T) {
	suite.Run(t, new(ProviderTestSuite))
}

func (s *ProviderTestSuite) TestPacketRoundtrip() {
	s.SetupCCVChannel()
	providerCtx := s.providerChain.GetContext()
	providerStakingKeeper := s.providerChain.App.(*appProvider.App).StakingKeeper

	origTime := s.providerCtx().BlockTime()
	bondAmt := sdk.NewInt(1000000)

	delAddr := s.providerChain.SenderAccount.GetAddress()

	// Choose a validator, and get its address and data structure into the correct types
	tmValidator := s.providerChain.Vals.Validators[0]
	valAddr, err := sdk.ValAddressFromHex(tmValidator.Address.String())
	s.Require().NoError(err)
	validator, found := providerStakingKeeper.GetValidator(s.providerCtx(), valAddr)
	s.Require().True(found)

	// Bond some tokens on provider to change validator powers
	_, err = providerStakingKeeper.Delegate(s.providerCtx(), delAddr, bondAmt, stakingtypes.Unbonded, stakingtypes.Validator(validator), true)
	s.Require().NoError(err)

	// Save valset update ID to reconstruct packet
	valUpdateID := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetValidatorSetUpdateId(s.providerCtx())

	// Send CCV packet to consumer
	s.providerChain.App.EndBlock(abci.RequestEndBlock{})

	// Get validator update created in Endblock to use in reconstructing packet
	valUpdates := providerStakingKeeper.GetValidatorUpdates(s.providerCtx())

	// commit block on provider chain and update consumer chain's client
	oldBlockTime := s.providerCtx().BlockTime()
	s.coordinator.CommitBlock(s.providerChain)
	s.path.EndpointA.UpdateClient()

	// Reconstruct packet
	packetData := types.NewValidatorSetChangePacketData(valUpdates, valUpdateID, nil)
	timeout := uint64(ccv.GetTimeoutTimestamp(oldBlockTime).UnixNano())
	packet := channeltypes.NewPacket(packetData.GetBytes(), 1, providertypes.PortID, s.path.EndpointB.ChannelID,
		consumertypes.PortID, s.path.EndpointA.ChannelID, clienttypes.Height{}, timeout)

	// Receive CCV packet on consumer chain
	err = s.path.EndpointA.RecvPacket(packet)
	s.Require().NoError(err)

	// - End provider unbonding period
	providerCtx = providerCtx.WithBlockTime(origTime.Add(providerStakingKeeper.UnbondingTime(s.providerCtx())).Add(3 * time.Hour))
	s.providerChain.App.EndBlock(abci.RequestEndBlock{})

	// - End consumer unbonding period
	unbondingPeriod, found := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetUnbondingTime(s.consumerCtx())
	s.Require().True(found)
	consumerCtx := s.consumerCtx().WithBlockTime(origTime.Add(unbondingPeriod).Add(3 * time.Hour))
	// TODO: why doesn't this work: s.consumerChain.App.EndBlock(abci.RequestEndBlock{})
	err = s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.UnbondMaturePackets(consumerCtx)
	s.Require().NoError(err)

	// commit consumer chain and update provider chain client
	s.coordinator.CommitBlock(s.consumerChain)

	err = s.path.EndpointB.UpdateClient()
	s.Require().NoError(err)

	ack := channeltypes.NewResultAcknowledgement([]byte{byte(1)})

	err = s.path.EndpointB.AcknowledgePacket(packet, ack.Acknowledgement())
	s.Require().NoError(err)
}

func (s *ProviderTestSuite) providerCtx() sdk.Context {
	return s.providerChain.GetContext()
}

func (s *ProviderTestSuite) consumerCtx() sdk.Context {
	return s.consumerChain.GetContext()
}

func (s *ProviderTestSuite) providerBondDenom() string {
	return s.providerChain.App.(*appProvider.App).StakingKeeper.BondDenom(s.providerCtx())
}

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
	packetData := types.NewSlashPacketData(validator, valsetUpdateId, stakingtypes.Downtime)
	timeout := uint64(types.GetTimeoutTimestamp(oldBlockTime).UnixNano())
	packet := channeltypes.NewPacket(packetData.GetBytes(), 1, consumertypes.PortID, s.path.EndpointA.ChannelID,
		providertypes.PortID, s.path.EndpointB.ChannelID, clienttypes.Height{}, timeout)

	// Send the downtime packet through CCV
	err = s.path.EndpointA.SendPacket(packet)
	s.Require().NoError(err)

	// Set outstanding slashing flag
	s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.SetOutstandingDowntime(s.consumerCtx(), consAddr)

	// save next VSC packet info
	oldBlockTime = s.providerCtx().BlockTime()
	timeout = uint64(types.GetTimeoutTimestamp(oldBlockTime).UnixNano())
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
	packetData2 := ccv.NewValidatorSetChangePacketData(valUpdates, valsetUpdateID, []string{consAddr.String()})
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
	packetData := types.NewSlashPacketData(validator, valsetUpdateId, stakingtypes.DoubleSign)

	timeout := uint64(types.GetTimeoutTimestamp(oldBlockTime).UnixNano())
	packet := channeltypes.NewPacket(packetData.GetBytes(), 1, consumertypes.PortID, s.path.EndpointA.ChannelID,
		providertypes.PortID, s.path.EndpointB.ChannelID, clienttypes.Height{}, timeout)

	// Send the downtime packet through CCV
	err = s.path.EndpointA.SendPacket(packet)
	s.Require().NoError(err)

	// save next VSC packet info
	oldBlockTime = s.providerCtx().BlockTime()
	timeout = uint64(types.GetTimeoutTimestamp(oldBlockTime).UnixNano())
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
	packetData2 := ccv.NewValidatorSetChangePacketData(valUpdates, valsetUpdateID, []string{})
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
	slashedAmout := providerSlashingKeeper.SlashFractionDoubleSign(s.providerCtx()).Mul(valOldBalance.ToDec())
	resultingTokens := valOldBalance.Sub(slashedAmout.TruncateInt())
	s.Require().Equal(resultingTokens, validatorJailed.GetTokens())

	// check that the validator's unjailing time is updated
	valSignInfo, found := providerSlashingKeeper.GetValidatorSigningInfo(s.providerCtx(), consAddr)
	s.Require().True(found)
	s.Require().True(valSignInfo.JailedUntil.After(s.providerCtx().BlockHeader().Time))

	// check that validator was tombstoned
	s.Require().True(valSignInfo.Tombstoned)
	s.Require().True(valSignInfo.JailedUntil.Equal(evidencetypes.DoubleSignJailEndTime))
}

func (s *ProviderTestSuite) getVal(index int) (validator stakingtypes.Validator, valAddr sdk.ValAddress) {
	// Choose a validator, and get its address and data structure into the correct types
	tmValidator := s.providerChain.Vals.Validators[index]
	valAddr, err := sdk.ValAddressFromHex(tmValidator.Address.String())
	s.Require().NoError(err)
	validator, found := s.providerChain.App.(*appProvider.App).StakingKeeper.GetValidator(s.providerCtx(), valAddr)
	s.Require().True(found)

	return validator, valAddr
}

func (s *ProviderTestSuite) TestSlashPacketAcknowldgement() {
	providerKeeper := s.providerChain.App.(*appProvider.App).ProviderKeeper
	consumerKeeper := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper

	packet := channeltypes.NewPacket([]byte{}, 1, consumertypes.PortID, s.path.EndpointA.ChannelID,
		providertypes.PortID, "wrongchannel", clienttypes.Height{}, 0)

	ack := providerKeeper.OnRecvPacket(s.providerCtx(), packet, ccv.SlashPacketData{})
	s.Require().NotNil(ack)

	err := consumerKeeper.OnAcknowledgementPacket(s.consumerCtx(), packet, ccv.SlashPacketData{}, channeltypes.NewResultAcknowledgement(ack.Acknowledgement()))
	s.Require().NoError(err)

	err = consumerKeeper.OnAcknowledgementPacket(s.consumerCtx(), packet, ccv.SlashPacketData{}, channeltypes.NewErrorAcknowledgement("another error"))
	s.Require().Error(err)
}

func (s *ProviderTestSuite) DisableConsumerDistribution() {
	cChain := s.consumerChain
	cApp := cChain.App.(*appConsumer.App)
	for i, moduleName := range cApp.MM.OrderBeginBlockers {
		if moduleName == distrtypes.ModuleName {
			cApp.MM.OrderBeginBlockers = append(cApp.MM.OrderBeginBlockers[:i], cApp.MM.OrderBeginBlockers[i+1:]...)
			return
		}
	}
}

func (s *ProviderTestSuite) DisableProviderDistribution() {
	pChain := s.providerChain
	pApp := pChain.App.(*appProvider.App)
	for i, moduleName := range pApp.MM.OrderBeginBlockers {
		if moduleName == distrtypes.ModuleName {
			s.providerDistrIndex = i
			pApp.MM.OrderBeginBlockers = append(pApp.MM.OrderBeginBlockers[:i], pApp.MM.OrderBeginBlockers[i+1:]...)
			return
		}
	}
}

func (s *ProviderTestSuite) ReenableProviderDistribution() {
	pChain := s.providerChain
	pApp := pChain.App.(*appProvider.App)
	i := s.providerDistrIndex
	pApp.MM.OrderBeginBlockers = append(
		pApp.MM.OrderBeginBlockers[:i+1], pApp.MM.OrderBeginBlockers[i:]...) // make space
	pApp.MM.OrderBeginBlockers[i] = distrtypes.ModuleName // set value
}

// TestDistribution tests that tokens are distributed to the
// provider chain from the consumer chain appropriately
// func (s *ProviderTestSuite) TestDistribution() {
// 	s.SetupCCVChannel() // also sets up transfer channels
// 	// NOTE s.transferPath.EndpointA == Consumer Chain
// 	//      s.transferPath.EndpointB == Provider Chain

// 	pChain, cChain := s.providerChain, s.consumerChain
// 	pApp, cApp := pChain.App.(*appProvider.App), cChain.App.(*appConsumer.App)
// 	cKeep := cApp.ConsumerKeeper

// 	// Get the receiving fee pool on the provider chain
// 	fcAddr := pApp.ProviderKeeper.GetFeeCollectorAddressStr(pChain.GetContext())

// 	// Ensure that the provider fee pool address stored on the consumer chain
// 	// is the correct address
// 	fcAddr2 := cApp.ConsumerKeeper.GetProviderFeePoolAddrStr(cChain.GetContext())
// 	s.Require().Equal(fcAddr, fcAddr2)

// 	// make sure we're starting at consumer height 21 (some blocks commited during setup)
// 	s.Require().Equal(int64(21), cChain.GetContext().BlockHeight())

// 	// get last consumer transmission
// 	ltbh, err := cKeep.GetLastTransmissionBlockHeight(cChain.GetContext())
// 	s.Require().NoError(err)
// 	s.Require().Equal(int64(0), ltbh.Height)

// 	bpdt := cKeep.GetBlocksPerDistributionTransmission(cChain.GetContext())
// 	s.Require().Equal(int64(1000), bpdt)

// 	// check the consumer chain fee pool
// 	consumerFeePoolAddr := cApp.AccountKeeper.GetModuleAccount(
// 		cChain.GetContext(), authtypes.FeeCollectorName).GetAddress()
// 	providerFeePoolAddr := pApp.AccountKeeper.GetModuleAccount(
// 		pChain.GetContext(), authtypes.FeeCollectorName).GetAddress()
// 	balance := cApp.BankKeeper.GetBalance(cChain.GetContext(), consumerFeePoolAddr, "stake")
// 	s.Assert().Equal(balance.Amount.Int64(), int64(140062235461521))

// 	// Commit some new blocks (commit blocks less than the distribution event blocks)
// 	s.coordinator.CommitNBlocks(cChain, (1000-1)-21)
// 	err = s.path.EndpointB.UpdateClient()
// 	s.Require().Equal(int64(1000), cChain.GetContext().BlockHeight())

// 	// check the consumer chain fee pool (should have increased
// 	balance = cApp.BankKeeper.GetBalance(cChain.GetContext(), consumerFeePoolAddr, "stake")
// 	expFeePoolAtDistr := int64(4175822659438993)
// 	s.Assert().Equal(balance.Amount.Int64(), expFeePoolAtDistr)

// 	// Verify that the destinationChannel exists
// 	// if this doesn't exist then the transfer logic will fail when
// 	// a the distribution transfer is invoked in the next block.
// 	ctx := cChain.GetContext()
// 	sourcePort := transfertypes.PortID
// 	sourceChannel := cKeep.GetDistributionTransmissionChannel(ctx)
// 	sourceChannelEnd, found := cApp.IBCKeeper.ChannelKeeper.GetChannel(ctx, sourcePort, sourceChannel)
// 	s.Require().True(found)
// 	destinationChannel := sourceChannelEnd.GetCounterparty().GetChannelID()
// 	s.Require().True(len(destinationChannel) > 0)

// 	// commit 1 more block (which should invoke a distribution event)
// 	rspEB, _, _ := s.coordinator.CommitBlockGetResponses(cChain)

// 	// get the packet from the endblock events
// 	var packet channeltypes.Packet
// 	var ftpd transfertypes.FungibleTokenPacketData
// 	found = false
// 	for _, evnt := range rspEB.Events {
// 		if evnt.Type == channeltypes.EventTypeSendPacket {
// 			found = true
// 			packet, err = channelkeeper.ReconstructPacketFromEvent(evnt)
// 			s.Require().NoError(err)
// 			cApp.AppCodec().MustUnmarshalJSON(packet.GetData(), &ftpd)
// 		}
// 	}
// 	s.Require().True(found)

// 	// ensure the correct amount is being transmitted within the packet
// 	expConsRedistrAmt := expFeePoolAtDistr * 3 / 4 // because of default 75% redistribute fraction (will truc decimal)
// 	expProviderAmt := expFeePoolAtDistr - expConsRedistrAmt
// 	s.Assert().Equal(ftpd.Amount, fmt.Sprintf("%v", expProviderAmt))

// 	// halt provider distribution (for testing purposes to be able to review the
// 	// provider fee pool)
// 	s.DisableProviderDistribution()

// 	// relay the packet
// 	err = s.transferPath.RelayPacket(packet)
// 	s.Require().NoError(err)

// 	// check the consumer chain fee pool which should be now emptied (besides
// 	// new minted tokens since the transfer)
// 	balance = cApp.BankKeeper.GetBalance(cChain.GetContext(), consumerFeePoolAddr, "stake")
// 	s.Assert().Equal(balance.Amount.Int64(), int64(26786189989304)) // this is "small"

// 	// check the provider chain fee pool which should now have
// 	// the consumer chain tokens
// 	balance = pApp.BankKeeper.GetBalance(pChain.GetContext(), providerFeePoolAddr,
// 		"ibc/3C3D7B3BE4ECC85A0E5B52A3AEC3B7DFC2AA9CA47C37821E57020D6807043BE9")
// 	s.Assert().Equal(balance.Amount.Int64(), expProviderAmt)

// 	// check the consumer redistribution amount arrives in the module account
// 	consumerRedistrAddr := cApp.AccountKeeper.GetModuleAccount(ctx,
// 		consumertypes.ConsumerRedistributeName).GetAddress()
// 	balance = cApp.BankKeeper.GetBalance(cChain.GetContext(), consumerRedistrAddr, "stake")
// 	s.Assert().Equal(balance.Amount.Int64(), expConsRedistrAmt)

// 	// Ensure provider pool emptied and that allocation was called normally
// 	// allocation would result in validator rewards, but due to limitations in
// 	// the testing framework (where validators do not actually sign votes and
// 	// therefor do not produce abci.VoteInfo) the expected behaviour of
// 	// allocation is to send all rewards to the community pool
// 	s.ReenableProviderDistribution()
// 	s.coordinator.CommitNBlocks(pChain, 1)
// 	balance = pApp.BankKeeper.GetBalance(pChain.GetContext(), providerFeePoolAddr,
// 		"ibc/3C3D7B3BE4ECC85A0E5B52A3AEC3B7DFC2AA9CA47C37821E57020D6807043BE9")
// 	s.Assert().Equal(balance.Amount.Int64(), int64(0))
// 	communityPool := pApp.DistrKeeper.GetFeePool(pChain.GetContext()).CommunityPool
// 	balanceI64 := communityPool.AmountOf(
// 		"ibc/3C3D7B3BE4ECC85A0E5B52A3AEC3B7DFC2AA9CA47C37821E57020D6807043BE9").RoundInt64()
// 	s.Assert().Equal(balanceI64, expProviderAmt)
// }
