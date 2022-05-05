package provider_test

import (
	"testing"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	distrtypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	transfertypes "github.com/cosmos/ibc-go/v3/modules/apps/transfer/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	commitmenttypes "github.com/cosmos/ibc-go/v3/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"

	appConsumer "github.com/cosmos/interchain-security/app_consumer"
	appProvider "github.com/cosmos/interchain-security/app_provider"
	"github.com/cosmos/interchain-security/testutil/simapp"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/cosmos/interchain-security/x/ccv/types"

	abci "github.com/tendermint/tendermint/abci/types"
	tmtypes "github.com/tendermint/tendermint/types"

	"github.com/stretchr/testify/suite"
)

type PBTTestSuite struct {
	suite.Suite

	coordinator *ibctesting.Coordinator

	// testing chains
	providerChain *ibctesting.TestChain
	consumerChain *ibctesting.TestChain

	providerClient    *ibctmtypes.ClientState
	providerConsState *ibctmtypes.ConsensusState

	path         *ibctesting.Path
	transferPath *ibctesting.Path

	providerDistrIndex int

	ctx sdk.Context
}

// UpdateConsumerHistInfo updates consumer chains historical info manually since
// the staking keeper is disabled. Provider chains need this to update their client trusted validators
// in IBC-GO testing (see ConstructUpdateTMClientHeaderWithTrustedHeight in chain.go)
func (s *PBTTestSuite) UpdateConsumerHistInfo(changes []abci.ValidatorUpdate) {
	// map changes per pubkey
	changesPower := make(map[string]int64)
	for _, c := range changes {
		pk, err := cryptocodec.FromTmProtoPublicKey(c.PubKey)
		s.Require().NoError(err)
		changesPower[pk.String()] = c.Power
	}

	// update validators power
	var validators stakingtypes.Validators
	for _, v := range s.consumerChain.Vals.Validators {
		pk, err := cryptocodec.FromTmPubKeyInterface(v.PubKey)
		s.Require().NoError(err)
		val, err := stakingtypes.NewValidator(nil, pk, stakingtypes.Description{})
		s.Require().NoError(err)

		if p, ok := changesPower[pk.String()]; ok {
			val.Tokens = sdk.TokensFromConsensusPower(p, sdk.DefaultPowerReduction)
		} else {
			val.Tokens = sdk.TokensFromConsensusPower(v.VotingPower, sdk.DefaultPowerReduction)
		}

		if val.Tokens.IsZero() {
			val.Status = stakingtypes.Unbonding
			val.Jailed = true
		} else {
			val.Status = stakingtypes.Bonded
		}
		validators = append(validators, val)
	}

	// update chain historical info
	hi := stakingtypes.NewHistoricalInfo(s.ctx.BlockHeader(), validators, sdk.DefaultPowerReduction)
	s.consumerChain.App.GetStakingKeeper().SetHistoricalInfo(s.consumerCtx(), s.consumerCtx().BlockHeight(), &hi)
}

func (s *PBTTestSuite) DisableConsumerDistribution() {
	cChain := s.consumerChain
	cApp := cChain.App.(*appConsumer.App)
	for i, moduleName := range cApp.MM.OrderBeginBlockers {
		if moduleName == distrtypes.ModuleName {
			cApp.MM.OrderBeginBlockers = append(cApp.MM.OrderBeginBlockers[:i], cApp.MM.OrderBeginBlockers[i+1:]...)
			return
		}
	}
}

func (s *PBTTestSuite) DisableProviderDistribution() {
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

func (s *PBTTestSuite) ReenableProviderDistribution() {
	pChain := s.providerChain
	pApp := pChain.App.(*appProvider.App)
	i := s.providerDistrIndex
	pApp.MM.OrderBeginBlockers = append(
		pApp.MM.OrderBeginBlockers[:i+1], pApp.MM.OrderBeginBlockers[i:]...) // make space
	pApp.MM.OrderBeginBlockers[i] = distrtypes.ModuleName // set value
}

func (suite *PBTTestSuite) SetupCCVChannel() {
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

func (s *PBTTestSuite) providerCtx() sdk.Context {
	return s.providerChain.GetContext()
}

func (s *PBTTestSuite) consumerCtx() sdk.Context {
	return s.consumerChain.GetContext()
}

func (s *PBTTestSuite) providerBondDenom() string {
	return s.providerChain.App.(*appProvider.App).StakingKeeper.BondDenom(s.providerCtx())
}

func (s *PBTTestSuite) getVal(index int) (validator stakingtypes.Validator, valAddr sdk.ValAddress) {
	// Choose a validator, and get its address and data structure into the correct types
	tmValidator := s.providerChain.Vals.Validators[index]
	valAddr, err := sdk.ValAddressFromHex(tmValidator.Address.String())
	s.Require().NoError(err)
	validator, found := s.providerChain.App.GetStakingKeeper().GetValidator(s.providerCtx(), valAddr)
	s.Require().True(found)

	return validator, valAddr
}

func (suite *PBTTestSuite) SetupTest() {

	suite.coordinator, suite.providerChain, suite.consumerChain = simapp.NewProviderConsumerCoordinator(suite.T())

	suite.DisableConsumerDistribution()

	tmConfig := ibctesting.NewTendermintConfig()

	// commit a block on provider chain before creating client
	suite.coordinator.CommitBlock(suite.providerChain)

	// create client and consensus state of provider chain to initialize consumer chain genesis.
	height := suite.providerChain.LastHeader.GetHeight().(clienttypes.Height)
	UpgradePath := []string{"upgrade", "upgradedIBCState"}

	suite.providerClient = ibctmtypes.NewClientState(
		suite.providerChain.ChainID, tmConfig.TrustLevel, tmConfig.TrustingPeriod, tmConfig.UnbondingPeriod, tmConfig.MaxClockDrift,
		height, commitmenttypes.GetSDKSpecs(), UpgradePath, tmConfig.AllowUpdateAfterExpiry, tmConfig.AllowUpdateAfterMisbehaviour,
	)
	suite.providerConsState = suite.providerChain.LastHeader.ConsensusState()

	valUpdates := tmtypes.TM2PB.ValidatorUpdates(suite.providerChain.Vals)

	params := consumertypes.NewParams(
		true,
		1000, // about 2 hr at 7.6 seconds per blocks
		"",
		"",
		"0.5", // 50%
	)
	consumerGenesis := consumertypes.NewInitialGenesisState(suite.providerClient, suite.providerConsState, valUpdates, params)
	suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.InitGenesis(suite.consumerChain.GetContext(), consumerGenesis)

	suite.ctx = suite.providerChain.GetContext()

	suite.path = ibctesting.NewPath(suite.consumerChain, suite.providerChain)
	suite.path.EndpointA.ChannelConfig.PortID = consumertypes.PortID
	suite.path.EndpointB.ChannelConfig.PortID = providertypes.PortID
	suite.path.EndpointA.ChannelConfig.Version = types.Version
	suite.path.EndpointB.ChannelConfig.Version = types.Version
	suite.path.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
	suite.path.EndpointB.ChannelConfig.Order = channeltypes.ORDERED
	providerClient, ok := suite.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetProviderClient(suite.consumerChain.GetContext())
	if !ok {
		panic("must already have provider client on consumer chain")
	}
	// set consumer endpoint's clientID
	suite.path.EndpointA.ClientID = providerClient

	// TODO: No idea why or how this works, but it seems that it needs to be done.
	suite.path.EndpointB.Chain.SenderAccount.SetAccountNumber(6)
	suite.path.EndpointA.Chain.SenderAccount.SetAccountNumber(6)

	// create consumer client on provider chain and set as consumer client for consumer chainID in provider keeper.
	suite.path.EndpointB.CreateClient()
	suite.providerChain.App.(*appProvider.App).ProviderKeeper.SetConsumerClient(suite.providerChain.GetContext(), suite.consumerChain.ChainID, suite.path.EndpointB.ClientID)

	suite.transferPath = ibctesting.NewPath(suite.consumerChain, suite.providerChain)
	suite.transferPath.EndpointA.ChannelConfig.PortID = transfertypes.PortID
	suite.transferPath.EndpointB.ChannelConfig.PortID = transfertypes.PortID
	suite.transferPath.EndpointA.ChannelConfig.Version = transfertypes.Version
	suite.transferPath.EndpointB.ChannelConfig.Version = transfertypes.Version
}

func TestPBTTestSuite(t *testing.T) {
	suite.Run(t, new(PBTTestSuite))
}
