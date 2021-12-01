package parent_test

import (
	"testing"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"

	stakingkeeper "github.com/cosmos/cosmos-sdk/x/staking/keeper"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	clienttypes "github.com/cosmos/ibc-go/modules/core/02-client/types"
	channeltypes "github.com/cosmos/ibc-go/modules/core/04-channel/types"
	commitmenttypes "github.com/cosmos/ibc-go/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/modules/light-clients/07-tendermint/types"
	ibctesting "github.com/cosmos/ibc-go/testing"

	"github.com/cosmos/interchain-security/app"
	"github.com/cosmos/interchain-security/testutil/simapp"
	childtypes "github.com/cosmos/interchain-security/x/ccv/child/types"
	parenttypes "github.com/cosmos/interchain-security/x/ccv/parent/types"
	"github.com/cosmos/interchain-security/x/ccv/types"

	"github.com/stretchr/testify/suite"
)

func init() {
	ibctesting.DefaultTestingAppInit = simapp.SetupTestingApp
}

type ParentTestSuite struct {
	suite.Suite

	coordinator *ibctesting.Coordinator

	// testing chains
	parentChain *ibctesting.TestChain
	childChain  *ibctesting.TestChain

	parentClient    *ibctmtypes.ClientState
	parentConsState *ibctmtypes.ConsensusState

	path *ibctesting.Path

	ctx sdk.Context
}

func (suite *ParentTestSuite) SetupTest() {
	suite.coordinator = ibctesting.NewCoordinator(suite.T(), 2)
	suite.parentChain = suite.coordinator.GetChain(ibctesting.GetChainID(0))
	suite.childChain = suite.coordinator.GetChain(ibctesting.GetChainID(1))

	tmConfig := ibctesting.NewTendermintConfig()

	// commit a block on parent chain before creating client
	suite.coordinator.CommitBlock(suite.parentChain)

	// create client and consensus state of parent chain to initialize child chain genesis.
	height := suite.parentChain.LastHeader.GetHeight().(clienttypes.Height)
	UpgradePath := []string{"upgrade", "upgradedIBCState"}

	suite.parentClient = ibctmtypes.NewClientState(
		suite.parentChain.ChainID, tmConfig.TrustLevel, tmConfig.TrustingPeriod, tmConfig.UnbondingPeriod, tmConfig.MaxClockDrift,
		height, commitmenttypes.GetSDKSpecs(), UpgradePath, tmConfig.AllowUpdateAfterExpiry, tmConfig.AllowUpdateAfterMisbehaviour,
	)
	suite.parentConsState = suite.parentChain.LastHeader.ConsensusState()

	childGenesis := childtypes.NewInitialGenesisState(suite.parentClient, suite.parentConsState)
	suite.childChain.App.(*app.App).ChildKeeper.InitGenesis(suite.childChain.GetContext(), childGenesis)

	suite.ctx = suite.parentChain.GetContext()

	suite.path = ibctesting.NewPath(suite.childChain, suite.parentChain)
	suite.path.EndpointA.ChannelConfig.PortID = childtypes.PortID
	suite.path.EndpointB.ChannelConfig.PortID = parenttypes.PortID
	suite.path.EndpointA.ChannelConfig.Version = types.Version
	suite.path.EndpointB.ChannelConfig.Version = types.Version
	suite.path.EndpointA.ChannelConfig.Order = channeltypes.ORDERED
	suite.path.EndpointB.ChannelConfig.Order = channeltypes.ORDERED
	parentClient, ok := suite.childChain.App.(*app.App).ChildKeeper.GetParentClient(suite.childChain.GetContext())
	if !ok {
		panic("must already have parent client on child chain")
	}
	// set child endpoint's clientID
	suite.path.EndpointA.ClientID = parentClient

	// create child client on parent chain and set as child client for child chainID in parent keeper.
	suite.path.EndpointB.CreateClient()
	suite.parentChain.App.(*app.App).ParentKeeper.SetChildClient(suite.parentChain.GetContext(), suite.childChain.ChainID, suite.path.EndpointB.ClientID)
}

func TestParentTestSuite(t *testing.T) {
	suite.Run(t, new(ParentTestSuite))

}

func (suite *ParentTestSuite) TestStakingHooks() {
	parentCtx := suite.parentChain.GetContext()
	childCtx := suite.childChain.GetContext()
	parentStakingKeeper := suite.parentChain.App.GetStakingKeeper()
	suite.coordinator.Setup(suite.path)

	origTime := suite.ctx.BlockTime()
	var valsetUpdateId uint64
	valsetUpdateId = 1
	bondAmt := sdk.NewInt(1000000)

	delAddr := suite.parentChain.SenderAccount.GetAddress()
	validator := suite.parentChain.Vals.Validators[0]
	valAddr := validator.Address

	// - Bond and unbond some tokens on provider
	shares, err := parentStakingKeeper.Delegate(parentCtx, delAddr, bondAmt, stakingtypes.Unbonded, stakingtypes.Validator(validator), true)
	_, err = parentStakingKeeper.Undelegate(parentCtx, delAddr, valAddr, shares)

	// - Check if CCV UBDE is created
	ccvUbdes, found := suite.parentChain.App.(*app.App).ParentKeeper.GetUBDEsFromIndex(parentCtx, suite.parentChain.ChainID, valsetUpdateId)

	ccvUbde := ccvUbdes[0]

	// - Send CCV packet to consumer
	suite.parentChain.App.(*app.App).ParentKeeper.EndBlockCallback(parentCtx, suite.childChain.ChainID, valsetUpdateId)

	// - End provider unbonding period
	parentCtx = parentCtx.WithBlockTime(origTime.Add(childtypes.UnbondingTime).Add(3 * time.Hour))

	// - Check if hook was called and that unbonding did not succeed
	stakingUbde, found := GetStakingUbde(parentCtx, parentStakingKeeper, ccvUbde.UnbondingDelegationEntryId)

	stakingUbde.OnHold  // Should equal true
	stakingUbde.Balance // Should probably check some other properties too

	// - End consumer unbonding period
	childCtx = childCtx.WithBlockTime(origTime.Add(childtypes.UnbondingTime).Add(3 * time.Hour))

	// - Check if unbonding succeeded
	stakingUbde, found := parentStakingKeeper.GetUnbondingDelegationByEntry(parentCtx, ubdeId)

	// - Bond and unbond some tokens on provider
	// - Send CCV packet to consumer
	// - Get consumer to send ack back (consumer unbonding period expires)
	// - Check if CompleteStoppedUnbonding was attempted
	// - End provider unbonding period
	// - Check if tokens are unbonded
}

func GetStakingUbde(ctx sdk.Context, k stakingkeeper.Keeper, id uint64) (stakingUbde stakingtypes.UnbondingDelegationEntry, found bool) {
	stakingUbd, found := k.GetUnbondingDelegationByEntry(ctx, id)

	for _, entry := range stakingUbd.Entries {
		if entry.Id == id {
			stakingUbde = entry
			found = true
			break
		}
	}

	return stakingUbde, found
}
