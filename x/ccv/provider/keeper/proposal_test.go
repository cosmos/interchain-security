package keeper_test

import (
	"encoding/json"
	"testing"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/stretchr/testify/require"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	appProvider "github.com/cosmos/interchain-security/app/provider"
	testkeeper "github.com/cosmos/interchain-security/testutil/keeper"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	abci "github.com/tendermint/tendermint/abci/types"
	crypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
)

func (suite *KeeperTestSuite) TestMakeConsumerGenesis() {
	suite.SetupTest()

	actualGenesis, err := suite.providerChain.App.(*appProvider.App).ProviderKeeper.MakeConsumerGenesis(suite.providerChain.GetContext())
	suite.Require().NoError(err)

	jsonString := `{"params":{"enabled":true, "blocks_per_distribution_transmission":1000, "lock_unbonding_on_timeout": false},"new_chain":true,"provider_client_state":{"chain_id":"testchain1","trust_level":{"numerator":1,"denominator":3},"trusting_period":907200000000000,"unbonding_period":1814400000000000,"max_clock_drift":10000000000,"frozen_height":{},"latest_height":{"revision_height":5},"proof_specs":[{"leaf_spec":{"hash":1,"prehash_value":1,"length":1,"prefix":"AA=="},"inner_spec":{"child_order":[0,1],"child_size":33,"min_prefix_length":4,"max_prefix_length":12,"hash":1}},{"leaf_spec":{"hash":1,"prehash_value":1,"length":1,"prefix":"AA=="},"inner_spec":{"child_order":[0,1],"child_size":32,"min_prefix_length":1,"max_prefix_length":1,"hash":1}}],"upgrade_path":["upgrade","upgradedIBCState"],"allow_update_after_expiry":true,"allow_update_after_misbehaviour":true},"provider_consensus_state":{"timestamp":"2020-01-02T00:00:10Z","root":{"hash":"LpGpeyQVLUo9HpdsgJr12NP2eCICspcULiWa5u9udOA="},"next_validators_hash":"E30CE736441FB9101FADDAF7E578ABBE6DFDB67207112350A9A904D554E1F5BE"},"unbonding_sequences":null,"initial_val_set":[{"pub_key":{"type":"tendermint/PubKeyEd25519","value":"dcASx5/LIKZqagJWN0frOlFtcvz91frYmj/zmoZRWro="},"power":1}]}`

	var expectedGenesis consumertypes.GenesisState
	err = json.Unmarshal([]byte(jsonString), &expectedGenesis)
	suite.Require().NoError(err)

	// Zero out differing fields- TODO: figure out how to get the test suite to
	// keep these deterministic
	actualGenesis.ProviderConsensusState.NextValidatorsHash = []byte{}
	expectedGenesis.ProviderConsensusState.NextValidatorsHash = []byte{}

	// set valset to one empty validator because SetupTest() creates 4 validators per chain
	actualGenesis.InitialValSet = []abci.ValidatorUpdate{{PubKey: crypto.PublicKey{}, Power: actualGenesis.InitialValSet[0].Power}}
	expectedGenesis.InitialValSet[0].PubKey = crypto.PublicKey{}

	actualGenesis.ProviderConsensusState.Root.Hash = []byte{}
	expectedGenesis.ProviderConsensusState.Root.Hash = []byte{}

	suite.Require().Equal(actualGenesis, expectedGenesis, "consumer chain genesis created incorrectly")
}

func (suite *KeeperTestSuite) TestCreateConsumerChainProposal() {
	var (
		ctx      sdk.Context
		proposal *types.CreateConsumerChainProposal
		ok       bool
	)

	chainID := "chainID"
	initialHeight := clienttypes.NewHeight(2, 3)
	lockUbdOnTimeout := false

	testCases := []struct {
		name         string
		malleate     func(*KeeperTestSuite)
		expPass      bool
		spawnReached bool
	}{
		{
			"valid create consumer chain proposal: spawn time reached", func(suite *KeeperTestSuite) {
				// ctx blocktime is after proposal's spawn time
				ctx = suite.providerChain.GetContext().WithBlockTime(time.Now().Add(time.Hour))
				content, err := types.NewCreateConsumerChainProposal("title", "description", chainID, initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Now())
				suite.Require().NoError(err)
				proposal, ok = content.(*types.CreateConsumerChainProposal)
				suite.Require().True(ok)
				proposal.LockUnbondingOnTimeout = lockUbdOnTimeout
			}, true, true,
		},
		{
			"valid proposal: spawn time has not yet been reached", func(suite *KeeperTestSuite) {
				// ctx blocktime is before proposal's spawn time
				ctx = suite.providerChain.GetContext().WithBlockTime(time.Now())
				content, err := types.NewCreateConsumerChainProposal("title", "description", chainID, initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Now().Add(time.Hour))
				suite.Require().NoError(err)
				proposal, ok = content.(*types.CreateConsumerChainProposal)
				suite.Require().True(ok)
				proposal.LockUnbondingOnTimeout = lockUbdOnTimeout
			}, true, false,
		},
	}

	for _, tc := range testCases {
		tc := tc

		suite.Run(tc.name, func() {
			suite.SetupTest()

			tc.malleate(suite)

			err := suite.providerChain.App.(*appProvider.App).ProviderKeeper.CreateConsumerChainProposal(ctx, proposal)
			if tc.expPass {
				suite.Require().NoError(err, "error returned on valid case")
				if tc.spawnReached {
					clientId, found := suite.providerChain.App.(*appProvider.App).ProviderKeeper.GetConsumerClientId(ctx, chainID)
					suite.Require().True(found, "consumer client not found")
					consumerGenesis, ok := suite.providerChain.App.(*appProvider.App).ProviderKeeper.GetConsumerGenesis(ctx, chainID)
					suite.Require().True(ok)

					expectedGenesis, err := suite.providerChain.App.(*appProvider.App).ProviderKeeper.MakeConsumerGenesis(ctx)
					suite.Require().NoError(err)

					suite.Require().Equal(expectedGenesis, consumerGenesis)
					suite.Require().NotEqual("", clientId, "consumer client was not created after spawn time reached")
				} else {
					gotProposal := suite.providerChain.App.(*appProvider.App).ProviderKeeper.GetPendingCreateProposal(ctx, proposal.SpawnTime, chainID)
					suite.Require().Equal(initialHeight, gotProposal.InitialHeight, "unexpected pending proposal (InitialHeight)")
					suite.Require().Equal(lockUbdOnTimeout, gotProposal.LockUnbondingOnTimeout, "unexpected pending proposal (LockUnbondingOnTimeout)")
				}
			} else {
				suite.Require().Error(err, "did not return error on invalid case")
			}
		})
	}
}

func TestPendingStopProposalDeletion(t *testing.T) {

	testCases := []struct {
		types.StopConsumerChainProposal
		ExpDeleted bool
	}{
		{
			StopConsumerChainProposal: types.StopConsumerChainProposal{ChainId: "8", StopTime: time.Now().UTC()},
			ExpDeleted:                true,
		},
		{
			StopConsumerChainProposal: types.StopConsumerChainProposal{ChainId: "9", StopTime: time.Now().UTC().Add(time.Hour)},
			ExpDeleted:                false,
		},
	}
	providerKeeper, ctx := testkeeper.GetProviderKeeperAndCtx(t)

	for _, tc := range testCases {
		providerKeeper.SetPendingStopProposal(ctx, tc.ChainId, tc.StopTime)
	}

	ctx = ctx.WithBlockTime(time.Now().UTC())

	propsToExecute := providerKeeper.StopProposalsToExecute(ctx)
	// Delete stop proposals, same as what would be done by IteratePendingStopProposal
	providerKeeper.DeletePendingStopProposals(ctx, propsToExecute...)
	numDeleted := 0
	for _, tc := range testCases {
		res := providerKeeper.GetPendingStopProposal(ctx, tc.ChainId, tc.StopTime)
		if !tc.ExpDeleted {
			require.NotEmpty(t, res, "stop proposal was deleted: %s %s", tc.ChainId, tc.StopTime.String())
			continue
		}
		require.Empty(t, res, "stop proposal was not deleted %s %s", tc.ChainId, tc.StopTime.String())
		require.Equal(t, propsToExecute[numDeleted].ChainId, tc.ChainId)
		numDeleted += 1
	}
}

// Tests that pending stop proposals are accessed in order by timestamp via the iterator
func TestPendingStopProposalsOrder(t *testing.T) {

	now := time.Now().UTC()

	// props with unique chain ids and spawn times
	sampleProp1 := types.StopConsumerChainProposal{ChainId: "1", StopTime: now}
	sampleProp2 := types.StopConsumerChainProposal{ChainId: "2", StopTime: now.Add(1 * time.Hour)}
	sampleProp3 := types.StopConsumerChainProposal{ChainId: "3", StopTime: now.Add(2 * time.Hour)}
	sampleProp4 := types.StopConsumerChainProposal{ChainId: "4", StopTime: now.Add(3 * time.Hour)}
	sampleProp5 := types.StopConsumerChainProposal{ChainId: "5", StopTime: now.Add(4 * time.Hour)}

	testCases := []struct {
		propSubmitOrder      []types.StopConsumerChainProposal
		accessTime           time.Time
		expectedOrderedProps []types.StopConsumerChainProposal
	}{
		{
			propSubmitOrder: []types.StopConsumerChainProposal{
				sampleProp1, sampleProp2, sampleProp3, sampleProp4, sampleProp5,
			},
			accessTime: now.Add(30 * time.Minute),
			expectedOrderedProps: []types.StopConsumerChainProposal{
				sampleProp1,
			},
		},
		{
			propSubmitOrder: []types.StopConsumerChainProposal{
				sampleProp3, sampleProp2, sampleProp1, sampleProp5, sampleProp4,
			},
			accessTime: now.Add(3 * time.Hour).Add(30 * time.Minute),
			expectedOrderedProps: []types.StopConsumerChainProposal{
				sampleProp1, sampleProp2, sampleProp3, sampleProp4,
			},
		},
		{
			propSubmitOrder: []types.StopConsumerChainProposal{
				sampleProp5, sampleProp4, sampleProp3, sampleProp2, sampleProp1,
			},
			accessTime: now.Add(5 * time.Hour),
			expectedOrderedProps: []types.StopConsumerChainProposal{
				sampleProp1, sampleProp2, sampleProp3, sampleProp4, sampleProp5,
			},
		},
	}

	for _, tc := range testCases {
		providerKeeper, ctx := testkeeper.GetProviderKeeperAndCtx(t)
		ctx = ctx.WithBlockTime(tc.accessTime)

		for _, prop := range tc.propSubmitOrder {
			providerKeeper.SetPendingStopProposal(ctx, prop.ChainId, prop.StopTime)
		}
		propsToExecute := providerKeeper.StopProposalsToExecute(ctx)
		require.Equal(t, tc.expectedOrderedProps, propsToExecute)
	}
}

func TestPendingCreateProposalsDeletion(t *testing.T) {

	testCases := []struct {
		types.CreateConsumerChainProposal
		ExpDeleted bool
	}{
		{
			CreateConsumerChainProposal: types.CreateConsumerChainProposal{ChainId: "0", SpawnTime: time.Now().UTC()},
			ExpDeleted:                  true,
		},
		{
			CreateConsumerChainProposal: types.CreateConsumerChainProposal{ChainId: "1", SpawnTime: time.Now().UTC().Add(time.Hour)},
			ExpDeleted:                  false,
		},
	}
	providerKeeper, ctx := testkeeper.GetProviderKeeperAndCtx(t)

	for _, tc := range testCases {
		err := providerKeeper.SetPendingCreateProposal(ctx, &tc.CreateConsumerChainProposal)
		require.NoError(t, err)
	}

	ctx = ctx.WithBlockTime(time.Now().UTC())

	propsToExecute := providerKeeper.CreateProposalsToExecute(ctx)
	// Delete create proposals, same as what would be done by IteratePendingCreateProposal
	providerKeeper.DeletePendingCreateProposal(ctx, propsToExecute...)
	numDeleted := 0
	for _, tc := range testCases {
		res := providerKeeper.GetPendingCreateProposal(ctx, tc.SpawnTime, tc.ChainId)
		if !tc.ExpDeleted {
			require.NotEmpty(t, res, "create proposal was deleted: %s %s", tc.ChainId, tc.SpawnTime.String())
			continue
		}
		require.Empty(t, res, "create proposal was not deleted %s %s", tc.ChainId, tc.SpawnTime.String())
		require.Equal(t, propsToExecute[numDeleted].ChainId, tc.ChainId)
		numDeleted += 1
	}
}

// Tests that pending create proposals are accessed in order by timestamp via the iterator
func TestPendingCreateProposalsOrder(t *testing.T) {

	now := time.Now().UTC()

	// props with unique chain ids and spawn times
	sampleProp1 := types.CreateConsumerChainProposal{ChainId: "1", SpawnTime: now}
	sampleProp2 := types.CreateConsumerChainProposal{ChainId: "2", SpawnTime: now.Add(1 * time.Hour)}
	sampleProp3 := types.CreateConsumerChainProposal{ChainId: "3", SpawnTime: now.Add(2 * time.Hour)}
	sampleProp4 := types.CreateConsumerChainProposal{ChainId: "4", SpawnTime: now.Add(3 * time.Hour)}
	sampleProp5 := types.CreateConsumerChainProposal{ChainId: "5", SpawnTime: now.Add(4 * time.Hour)}

	testCases := []struct {
		propSubmitOrder      []types.CreateConsumerChainProposal
		accessTime           time.Time
		expectedOrderedProps []types.CreateConsumerChainProposal
	}{
		{
			propSubmitOrder: []types.CreateConsumerChainProposal{
				sampleProp1, sampleProp2, sampleProp3, sampleProp4, sampleProp5,
			},
			accessTime: now.Add(30 * time.Minute),
			expectedOrderedProps: []types.CreateConsumerChainProposal{
				sampleProp1,
			},
		},
		{
			propSubmitOrder: []types.CreateConsumerChainProposal{
				sampleProp3, sampleProp2, sampleProp1, sampleProp5, sampleProp4,
			},
			accessTime: now.Add(3 * time.Hour).Add(30 * time.Minute),
			expectedOrderedProps: []types.CreateConsumerChainProposal{
				sampleProp1, sampleProp2, sampleProp3, sampleProp4,
			},
		},
		{
			propSubmitOrder: []types.CreateConsumerChainProposal{
				sampleProp5, sampleProp4, sampleProp3, sampleProp2, sampleProp1,
			},
			accessTime: now.Add(5 * time.Hour),
			expectedOrderedProps: []types.CreateConsumerChainProposal{
				sampleProp1, sampleProp2, sampleProp3, sampleProp4, sampleProp5,
			},
		},
	}

	for _, tc := range testCases {
		providerKeeper, ctx := testkeeper.GetProviderKeeperAndCtx(t)
		ctx = ctx.WithBlockTime(tc.accessTime)

		for _, prop := range tc.propSubmitOrder {
			err := providerKeeper.SetPendingCreateProposal(ctx, &prop)
			require.NoError(t, err)
		}
		propsToExecute := providerKeeper.CreateProposalsToExecute(ctx)
		require.Equal(t, tc.expectedOrderedProps, propsToExecute)
	}
}
