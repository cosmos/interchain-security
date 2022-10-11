package e2e_test

import (
	"bytes"
	"testing"

	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"

	ccv "github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/cosmos/interchain-security/x/ccv/utils"

	transfertypes "github.com/cosmos/ibc-go/v3/modules/apps/transfer/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"

	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	"github.com/cosmos/interchain-security/testutil/simapp"

	tmtypes "github.com/tendermint/tendermint/types"

	"github.com/stretchr/testify/suite"
)

type CCVTestSuite struct {
	suite.Suite
	coordinator       *ibctesting.Coordinator
	providerChain     *ibctesting.TestChain
	consumerChain     *ibctesting.TestChain
	providerClient    *ibctmtypes.ClientState
	providerConsState *ibctmtypes.ConsensusState
	path              *ibctesting.Path
	transferPath      *ibctesting.Path
}

func TestCCVTestSuite(t *testing.T) {
	suite.Run(t, new(CCVTestSuite))
}

// SetupTest sets up in-mem state for the standard group of tests validating chains which implement the ccv modules
// TODO: Make this method more generalizable to be called by any provider/consumer implementation
func (ccvSuite *CCVTestSuite) SetupTest() {
	ccvSuite.coordinator, ccvSuite.providerChain,
		ccvSuite.consumerChain = simapp.NewProviderConsumerCoordinator(ccvSuite.T())

	ccvSuite.providerClient, ccvSuite.providerConsState,
		ccvSuite.path, ccvSuite.transferPath = CommonSetup(

		ccvSuite.Suite,
		// Pointers to provider/consumer keeper implementations are passed as interfaces here
		&ccvSuite.providerChain.App.(*appProvider.App).ProviderKeeper,
		&ccvSuite.consumerChain.App.(*appConsumer.App).ConsumerKeeper,
		ccvSuite.providerChain,
		ccvSuite.consumerChain,
	)
}

// CommonSetup sets up various state for the test suite. It is used by both the standard
// group of ccv tests, and the group of tests relevant to a democracy consumer.
func CommonSetup(
	suite suite.Suite,
	providerKeeper providerKeeper,
	consumerKeeper consumerKeeper,
	providerChain *ibctesting.TestChain,
	consumerChain *ibctesting.TestChain,
) (
	providerClientState *ibctmtypes.ClientState,
	providerConsState *ibctmtypes.ConsensusState,
	path *ibctesting.Path,
	transferPath *ibctesting.Path,
) {

	// valsets must match
	providerValUpdates := tmtypes.TM2PB.ValidatorUpdates(providerChain.Vals)
	consumerValUpdates := tmtypes.TM2PB.ValidatorUpdates(consumerChain.Vals)
	suite.Require().True(len(providerValUpdates) == len(consumerValUpdates), "initial valset not matching")
	for i := 0; i < len(providerValUpdates); i++ {
		addr1 := utils.GetChangePubKeyAddress(providerValUpdates[i])
		addr2 := utils.GetChangePubKeyAddress(consumerValUpdates[i])
		suite.Require().True(bytes.Equal(addr1, addr2), "validator mismatch")
	}

	// move both chains to the next block
	providerChain.NextBlock()
	consumerChain.NextBlock()

	// create consumer client on provider chain and set as consumer client for consumer chainID in provider keeper.
	err := providerKeeper.CreateConsumerClient(
		providerChain.GetContext(),
		consumerChain.ChainID,
		consumerChain.LastHeader.GetHeight().(clienttypes.Height),
		false,
	)
	suite.Require().NoError(err)
	// move provider to next block to commit the state
	providerChain.NextBlock()

	// initialize the consumer chain with the genesis state stored on the provider
	consumerGenesis, found := providerKeeper.GetConsumerGenesis(
		providerChain.GetContext(),
		consumerChain.ChainID,
	)
	suite.Require().True(found, "consumer genesis not found")
	consumerKeeper.InitGenesis(consumerChain.GetContext(), &consumerGenesis)
	providerClientState = consumerGenesis.ProviderClientState
	providerConsState = consumerGenesis.ProviderConsensusState

	// create path for the CCV channel
	path = ibctesting.NewPath(consumerChain, providerChain)

	// update CCV path with correct info
	// - set provider endpoint's clientID
	consumerClient, found := providerChain.App.(*appProvider.App).ProviderKeeper.GetConsumerClientId(
		providerChain.GetContext(),
		consumerChain.ChainID,
	)

	suite.Require().True(found, "consumer client not found")
	path.EndpointB.ClientID = consumerClient
	// - set consumer endpoint's clientID
	providerClientID, found := consumerKeeper.GetProviderClientID(consumerChain.GetContext())
	suite.Require().True(found, "provider client not found")
	path.EndpointA.ClientID = providerClientID
	// - client config
	providerUnbondingPeriod := providerChain.App.GetStakingKeeper().UnbondingTime(providerChain.GetContext())
	path.EndpointB.ClientConfig.(*ibctesting.TendermintConfig).UnbondingPeriod = providerUnbondingPeriod
	path.EndpointB.ClientConfig.(*ibctesting.TendermintConfig).TrustingPeriod = providerUnbondingPeriod / utils.TrustingPeriodFraction
	consumerUnbondingPeriod := utils.ComputeConsumerUnbondingPeriod(providerUnbondingPeriod)
	path.EndpointA.ClientConfig.(*ibctesting.TendermintConfig).UnbondingPeriod = consumerUnbondingPeriod
	path.EndpointA.ClientConfig.(*ibctesting.TendermintConfig).TrustingPeriod = consumerUnbondingPeriod / utils.TrustingPeriodFraction
	// - channel config
	path.EndpointA.ChannelConfig.PortID = ccv.ConsumerPortID
	path.EndpointB.ChannelConfig.PortID = ccv.ProviderPortID
	path.EndpointA.ChannelConfig.Version = ccv.Version
	path.EndpointB.ChannelConfig.Version = ccv.Version
	path.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
	path.EndpointB.ChannelConfig.Order = channeltypes.ORDERED

	// set chains sender account number
	// TODO: to be fixed in #151
	err = path.EndpointB.Chain.SenderAccount.SetAccountNumber(6)
	suite.Require().NoError(err)
	err = path.EndpointA.Chain.SenderAccount.SetAccountNumber(1)
	suite.Require().NoError(err)

	// create path for the transfer channel
	transferPath = ibctesting.NewPath(consumerChain, providerChain)
	transferPath.EndpointA.ChannelConfig.PortID = transfertypes.PortID
	transferPath.EndpointB.ChannelConfig.PortID = transfertypes.PortID
	transferPath.EndpointA.ChannelConfig.Version = transfertypes.Version
	transferPath.EndpointB.ChannelConfig.Version = transfertypes.Version

	return providerClientState, providerConsState, path, transferPath
}

func (suite *CCVTestSuite) SetupCCVChannel() {
	suite.StartSetupCCVChannel()
	suite.CompleteSetupCCVChannel()
}

func (suite *CCVTestSuite) StartSetupCCVChannel() {
	suite.coordinator.CreateConnections(suite.path)

	err := suite.path.EndpointA.ChanOpenInit()
	suite.Require().NoError(err)

	err = suite.path.EndpointB.ChanOpenTry()
	suite.Require().NoError(err)
}

func (suite *CCVTestSuite) CompleteSetupCCVChannel() {
	err := suite.path.EndpointA.ChanOpenAck()
	suite.Require().NoError(err)

	err = suite.path.EndpointB.ChanOpenConfirm()
	suite.Require().NoError(err)

	// ensure counterparty is up to date
	err = suite.path.EndpointA.UpdateClient()
	suite.Require().NoError(err)
}

func (suite *CCVTestSuite) SetupTransferChannel() {
	// transfer path will use the same connection as ccv path

	suite.transferPath.EndpointA.ClientID = suite.path.EndpointA.ClientID
	suite.transferPath.EndpointA.ConnectionID = suite.path.EndpointA.ConnectionID
	suite.transferPath.EndpointB.ClientID = suite.path.EndpointB.ClientID
	suite.transferPath.EndpointB.ConnectionID = suite.path.EndpointB.ConnectionID

	// CCV channel handshake will automatically initiate transfer channel handshake on ACK
	// so transfer channel will be on stage INIT when CompleteSetupCCVChannel returns.
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
	err = suite.transferPath.EndpointA.UpdateClient()
	suite.Require().NoError(err)
}
