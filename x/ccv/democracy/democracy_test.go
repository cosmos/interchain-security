package democracy_test

// TODO Ethernal: move to e2e folder, remove commented code
import (
	"bytes"
	"fmt"
	"regexp"
	"testing"

	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	transfertypes "github.com/cosmos/ibc-go/v3/modules/apps/transfer/types"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/v3/modules/core/04-channel/types"
	ibctesting "github.com/cosmos/ibc-go/v3/testing"

	appConsumer "github.com/cosmos/interchain-security/app/consumer-democracy"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	"github.com/cosmos/interchain-security/testutil/simapp"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	"github.com/cosmos/interchain-security/x/ccv/types"
	"github.com/cosmos/interchain-security/x/ccv/utils"

	tmtypes "github.com/tendermint/tendermint/types"

	"github.com/stretchr/testify/suite"
)

type ConsumerDemocracyTestSuite struct {
	suite.Suite

	coordinator *ibctesting.Coordinator

	// testing chains
	providerChain *ibctesting.TestChain
	consumerChain *ibctesting.TestChain

	path         *ibctesting.Path
	transferPath *ibctesting.Path

	// providerDistrIndex int
}

func (s *ConsumerDemocracyTestSuite) SetupTest() {
	s.coordinator, s.providerChain, s.consumerChain = simapp.NewProviderConsumerDemocracyCoordinator(s.T())

	// valsets must match
	providerValUpdates := tmtypes.TM2PB.ValidatorUpdates(s.providerChain.Vals)
	consumerValUpdates := tmtypes.TM2PB.ValidatorUpdates(s.consumerChain.Vals)
	s.Require().True(len(providerValUpdates) == len(consumerValUpdates), "initial valset not matching")
	for i := 0; i < len(providerValUpdates); i++ {
		addr1 := utils.GetChangePubKeyAddress(providerValUpdates[i])
		addr2 := utils.GetChangePubKeyAddress(consumerValUpdates[i])
		s.Require().True(bytes.Equal(addr1, addr2), "validator mismatch")
	}

	// move both chains to the next block
	s.providerChain.NextBlock()
	s.consumerChain.NextBlock()

	// create consumer client on provider chain and set as consumer client for consumer chainID in provider keeper.
	err := s.providerChain.App.(*appProvider.App).ProviderKeeper.CreateConsumerClient(
		s.providerCtx(),
		s.consumerChain.ChainID,
		s.consumerChain.LastHeader.GetHeight().(clienttypes.Height),
		false,
	)
	s.Require().NoError(err)

	// move provider to next block to commit the state
	s.providerChain.NextBlock()

	// initialize the consumer chain with the genesis state stored on the provider
	consumerGenesis, found := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetConsumerGenesis(
		s.providerCtx(),
		s.consumerChain.ChainID,
	)
	s.Require().True(found, "consumer genesis not found")
	s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.InitGenesis(s.consumerChain.GetContext(), &consumerGenesis)

	// create path for the CCV channel
	s.path = ibctesting.NewPath(s.consumerChain, s.providerChain)

	// update CCV path with correct info
	// - set provider endpoint's clientID
	consumerClient, found := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetConsumerClientId(
		s.providerCtx(),
		s.consumerChain.ChainID,
	)
	s.Require().True(found, "consumer client not found")
	s.path.EndpointB.ClientID = consumerClient
	// - set consumer endpoint's clientID
	providerClient, found := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetProviderClientID(s.consumerChain.GetContext())
	s.Require().True(found, "provider client not found")
	s.path.EndpointA.ClientID = providerClient
	// - client config
	providerUnbondingPeriod := s.providerChain.App.(*appProvider.App).GetStakingKeeper().UnbondingTime(s.providerCtx())
	s.path.EndpointB.ClientConfig.(*ibctesting.TendermintConfig).UnbondingPeriod = providerUnbondingPeriod
	s.path.EndpointB.ClientConfig.(*ibctesting.TendermintConfig).TrustingPeriod = providerUnbondingPeriod / utils.TrustingPeriodFraction
	consumerUnbondingPeriod := utils.ComputeConsumerUnbondingPeriod(providerUnbondingPeriod)
	s.path.EndpointA.ClientConfig.(*ibctesting.TendermintConfig).UnbondingPeriod = consumerUnbondingPeriod
	s.path.EndpointA.ClientConfig.(*ibctesting.TendermintConfig).TrustingPeriod = consumerUnbondingPeriod / utils.TrustingPeriodFraction
	// - channel config
	s.path.EndpointA.ChannelConfig.PortID = types.ConsumerPortID
	s.path.EndpointB.ChannelConfig.PortID = types.ProviderPortID
	s.path.EndpointA.ChannelConfig.Version = types.Version
	s.path.EndpointB.ChannelConfig.Version = types.Version
	s.path.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
	s.path.EndpointB.ChannelConfig.Order = channeltypes.ORDERED

	// set chains sender account number
	// TODO: to be fixed in #151
	err = s.path.EndpointB.Chain.SenderAccount.SetAccountNumber(6)
	s.Require().NoError(err)
	err = s.path.EndpointA.Chain.SenderAccount.SetAccountNumber(0)
	s.Require().NoError(err)

	// create path for the transfer channel
	s.transferPath = ibctesting.NewPath(s.consumerChain, s.providerChain)
	s.transferPath.EndpointA.ChannelConfig.PortID = transfertypes.PortID
	s.transferPath.EndpointB.ChannelConfig.PortID = transfertypes.PortID
	s.transferPath.EndpointA.ChannelConfig.Version = transfertypes.Version
	s.transferPath.EndpointB.ChannelConfig.Version = transfertypes.Version
}

func (s *ConsumerDemocracyTestSuite) SetupCCVChannel() {
	s.StartSetupCCVChannel()
	s.CompleteSetupCCVChannel()
	s.SetupTransferChannel()
}

func (s *ConsumerDemocracyTestSuite) StartSetupCCVChannel() {
	s.coordinator.CreateConnections(s.path)

	err := s.path.EndpointA.ChanOpenInit()
	s.Require().NoError(err)

	err = s.path.EndpointB.ChanOpenTry()
	s.Require().NoError(err)
}

func (s *ConsumerDemocracyTestSuite) CompleteSetupCCVChannel() {
	err := s.path.EndpointA.ChanOpenAck()
	s.Require().NoError(err)

	err = s.path.EndpointB.ChanOpenConfirm()
	s.Require().NoError(err)

	// ensure counterparty is up to date
	err = s.path.EndpointA.UpdateClient()
	s.Require().NoError(err)
}

func (s *ConsumerDemocracyTestSuite) SetupTransferChannel() {
	// transfer path will use the same connection as ccv path

	s.transferPath.EndpointA.ClientID = s.path.EndpointA.ClientID
	s.transferPath.EndpointA.ConnectionID = s.path.EndpointA.ConnectionID
	s.transferPath.EndpointB.ClientID = s.path.EndpointB.ClientID
	s.transferPath.EndpointB.ConnectionID = s.path.EndpointB.ConnectionID

	// CCV channel handshake will automatically initiate transfer channel handshake on ACK
	// so transfer channel will be on stage INIT when CompleteSetupCCVChannel returns.
	s.transferPath.EndpointA.ChannelID = s.consumerChain.App.(*appConsumer.App).
		ConsumerKeeper.GetDistributionTransmissionChannel(s.consumerChain.GetContext())

	// Complete TRY, ACK, CONFIRM for transfer path
	err := s.transferPath.EndpointB.ChanOpenTry()
	s.Require().NoError(err)

	err = s.transferPath.EndpointA.ChanOpenAck()
	s.Require().NoError(err)

	err = s.transferPath.EndpointB.ChanOpenConfirm()
	s.Require().NoError(err)

	// ensure counterparty is up to date
	err = s.transferPath.EndpointA.UpdateClient()
	s.Require().NoError(err)
}

func TestConsumerDemocracyTestSuite(t *testing.T) {
	suite.Run(t, new(ConsumerDemocracyTestSuite))
}

func (s *ConsumerDemocracyTestSuite) checkBalancesOverNextBlock() {

	stakingKeeper := s.consumerChain.App.(*appConsumer.App).StakingKeeper
	authKeeper := s.consumerChain.App.(*appConsumer.App).AccountKeeper
	distrKeeper := s.consumerChain.App.(*appConsumer.App).DistrKeeper
	bankKeeper := s.consumerChain.App.(*appConsumer.App).BankKeeper

	distrAccount := distrKeeper.GetDistributionAccount(s.consumerCtx())

	fmt.Printf("feeAccountName is %s\n", authtypes.FeeCollectorName)
	fmt.Printf("consumerRedistributeAccount is %s\n", consumertypes.ConsumerRedistributeName)
	fmt.Printf("providerRedistributeAccount is %s\n", consumertypes.ConsumerToSendToProviderName)
	feeCollectorAccount := authKeeper.GetModuleAccount(s.consumerCtx(), authtypes.FeeCollectorName)
	consumerRedistributeAccount := authKeeper.GetModuleAccount(s.consumerCtx(), consumertypes.ConsumerRedistributeName)
	providerRedistributeAccount := authKeeper.GetModuleAccount(s.consumerCtx(), consumertypes.ConsumerToSendToProviderName)

	bondDenom := stakingKeeper.BondDenom(s.consumerCtx())

	distrAccountBalance0 := bankKeeper.GetBalance(s.consumerCtx(), distrAccount.GetAddress(), bondDenom).Amount.QuoRaw(1000000)
	feeAccountBalance0 := bankKeeper.GetBalance(s.consumerCtx(), feeCollectorAccount.GetAddress(), bondDenom).Amount.QuoRaw(1000000)
	cosumerFeeAccountBalance0 := bankKeeper.GetBalance(s.consumerCtx(), consumerRedistributeAccount.GetAddress(), bondDenom).Amount.QuoRaw(1000000)
	providerFeeAccountBalance0 := bankKeeper.GetBalance(s.consumerCtx(), providerRedistributeAccount.GetAddress(), bondDenom).Amount.QuoRaw(1000000)

	fmt.Println("distrAccountBalance0", formatCommas(distrAccountBalance0))
	fmt.Println("feeAccountBalance0", formatCommas(feeAccountBalance0))
	fmt.Println("cosumerFeeAccountBalance0", formatCommas(cosumerFeeAccountBalance0))
	fmt.Println("providerFeeAccountBalance0", formatCommas(providerFeeAccountBalance0))

	s.consumerChain.NextBlock()

	distrAccountBalance1 := bankKeeper.GetBalance(s.consumerCtx(), distrAccount.GetAddress(), bondDenom).Amount.QuoRaw(1000000)
	feeAccountBalance1 := bankKeeper.GetBalance(s.consumerCtx(), feeCollectorAccount.GetAddress(), bondDenom).Amount.QuoRaw(1000000)
	cosumerFeeAccountBalance1 := bankKeeper.GetBalance(s.consumerCtx(), consumerRedistributeAccount.GetAddress(), bondDenom).Amount.QuoRaw(1000000)
	providerFeeAccountBalance1 := bankKeeper.GetBalance(s.consumerCtx(), providerRedistributeAccount.GetAddress(), bondDenom).Amount.QuoRaw(1000000)

	fmt.Println("distrAccountBalance1", formatCommas(distrAccountBalance1))
	fmt.Println("feeAccountBalance1", formatCommas(feeAccountBalance1))
	fmt.Println("cosumerFeeAccountBalance1", formatCommas(cosumerFeeAccountBalance1))
	fmt.Println("providerFeeAccountBalance1", formatCommas(providerFeeAccountBalance1))

	distrDifference := distrAccountBalance1.Sub(distrAccountBalance0)
	fmt.Println("distrDifference", formatCommas(distrDifference))

	providerDifference := providerFeeAccountBalance1.Sub(providerFeeAccountBalance0)
	fmt.Println("providerDifference", formatCommas(providerDifference))

	ratio := providerFeeAccountBalance1.ToDec().QuoInt(distrAccountBalance1)
	fmt.Println("ratio between distr and provider pool", ratio)
}

func (s *ConsumerDemocracyTestSuite) TestPacketRoundtrip() {
	s.SetupCCVChannel()

	s.checkBalancesOverNextBlock()
	s.checkBalancesOverNextBlock()
	s.checkBalancesOverNextBlock()
	s.checkBalancesOverNextBlock()

	// s.consumerChain.NextBlock()

	// feeAccountBalance2 := bankKeeper.GetBalance(s.consumerCtx(), distrAccount.GetAddress(), bondDenom)
	// cosumerFeeAccountBalance2 := bankKeeper.GetBalance(s.consumerCtx(), consumerRedistributeAccount.GetAddress(), bondDenom)

	// fmt.Println("feeAccountBalance2", feeAccountBalance2)
	// fmt.Println("cosumerFeeAccountBalance2", cosumerFeeAccountBalance2)

	// feeAccountBalanceDifference = feeAccountBalance2.Sub(feeAccountBalance1)
	// fmt.Println("feeAccountBalanceDifference", feeAccountBalanceDifference)

	// // providerCtx := s.providerChain.GetContext()
	// providerStakingKeeper := s.providerChain.App.(*appProvider.App).StakingKeeper

	// origTime := s.providerCtx().BlockTime()
	// bondAmt := sdk.NewInt(1000000)

	// delAddr := s.providerChain.SenderAccount.GetAddress()

	// // Choose a validator, and get its address and data structure into the correct types
	// tmValidator := s.providerChain.Vals.Validators[0]
	// valAddr, err := sdk.ValAddressFromHex(tmValidator.Address.String())
	// s.Require().NoError(err)
	// validator, found := providerStakingKeeper.GetValidator(s.providerCtx(), valAddr)
	// s.Require().True(found)

	// // Bond some tokens on provider to change validator powers
	// _, err = providerStakingKeeper.Delegate(s.providerCtx(), delAddr, bondAmt, stakingtypes.Unbonded, stakingtypes.Validator(validator), true)
	// s.Require().NoError(err)

	// // Save valset update ID to reconstruct packet
	// valUpdateID := s.providerChain.App.(*appProvider.App).ProviderKeeper.GetValidatorSetUpdateId(s.providerCtx())

	// // Send CCV packet to consumer
	// s.providerChain.App.EndBlock(abci.RequestEndBlock{})

	// // Get validator update created in Endblock to use in reconstructing packet
	// valUpdates := providerStakingKeeper.GetValidatorUpdates(s.providerCtx())

	// // commit block on provider chain and update consumer chain's client
	// oldBlockTime := s.providerCtx().BlockTime()
	// s.coordinator.CommitBlock(s.providerChain)
	// err = s.path.EndpointA.UpdateClient()
	// s.Require().NoError(err)

	// // Reconstruct packet
	// packetData := types.NewValidatorSetChangePacketData(valUpdates, valUpdateID, nil)
	// timeout := uint64(ccv.GetTimeoutTimestamp(oldBlockTime).UnixNano())
	// packet := channeltypes.NewPacket(packetData.GetBytes(), 1, providertypes.PortID, s.path.EndpointB.ChannelID,
	// 	consumertypes.PortID, s.path.EndpointA.ChannelID, clienttypes.Height{}, timeout)

	// // Receive CCV packet on consumer chain
	// err = s.path.EndpointA.RecvPacket(packet)
	// s.Require().NoError(err)

	// // - End provider unbonding period
	// // providerCtx = providerCtx.WithBlockTime(origTime.Add(providerStakingKeeper.UnbondingTime(s.providerCtx())).Add(3 * time.Hour))
	// s.providerChain.App.EndBlock(abci.RequestEndBlock{})

	// // - End consumer unbonding period
	// unbondingPeriod, found := s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.GetUnbondingTime(s.consumerCtx())
	// s.Require().True(found)
	// consumerCtx := s.consumerCtx().WithBlockTime(origTime.Add(unbondingPeriod).Add(3 * time.Hour))
	// // TODO: why doesn't this work: s.consumerChain.App.EndBlock(abci.RequestEndBlock{})
	// err = s.consumerChain.App.(*appConsumer.App).ConsumerKeeper.UnbondMaturePackets(consumerCtx)
	// s.Require().NoError(err)

	// // commit consumer chain and update provider chain client
	// s.coordinator.CommitBlock(s.consumerChain)

	// err = s.path.EndpointB.UpdateClient()
	// s.Require().NoError(err)

	// ack := channeltypes.NewResultAcknowledgement([]byte{byte(1)})

	// err = s.path.EndpointB.AcknowledgePacket(packet, ack.Acknowledgement())
	// s.Require().NoError(err)
}

func (s *ConsumerDemocracyTestSuite) providerCtx() sdk.Context {
	return s.providerChain.GetContext()
}

func (s *ConsumerDemocracyTestSuite) consumerCtx() sdk.Context {
	return s.consumerChain.GetContext()
}

// func (s *ConsumerDemocracyTestSuite) providerBondDenom() string {
// 	return s.providerChain.App.(*appProvider.App).StakingKeeper.BondDenom(s.providerCtx())
// }

func formatCommas(numm sdk.Int) string {
	num := numm.Int64()
	str := fmt.Sprintf("%d", num)
	re := regexp.MustCompile(`(\\d+)(\\d{3})`)
	for n := ""; n != str; {
		n = str
		str = re.ReplaceAllString(str, "$1,$2")
	}
	return str
}
