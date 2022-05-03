package keeper_test

import (
	"encoding/json"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	"github.com/cosmos/interchain-security/app"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	abci "github.com/tendermint/tendermint/abci/types"
	crypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
)

func (suite *KeeperTestSuite) TestMakeConsumerGenesis() {
	var ctx sdk.Context
	suite.SetupTest()
	ctx = suite.providerChain.GetContext().WithBlockTime(time.Now())

	actualGenesis, err := suite.providerChain.App.(*app.App).ProviderKeeper.MakeConsumerGenesis(ctx)
	suite.Require().NoError(err)

	jsonString := `{"params":{"Enabled":true},"new_chain":true,"provider_client_state":{"chain_id":"testchain1","trust_level":{"numerator":1,"denominator":3},"trusting_period":907200000000000,"unbonding_period":1814400000000000,"max_clock_drift":10000000000,"frozen_height":{},"latest_height":{"revision_height":5},"proof_specs":[{"leaf_spec":{"hash":1,"prehash_value":1,"length":1,"prefix":"AA=="},"inner_spec":{"child_order":[0,1],"child_size":33,"min_prefix_length":4,"max_prefix_length":12,"hash":1}},{"leaf_spec":{"hash":1,"prehash_value":1,"length":1,"prefix":"AA=="},"inner_spec":{"child_order":[0,1],"child_size":32,"min_prefix_length":1,"max_prefix_length":1,"hash":1}}],"upgrade_path":["upgrade","upgradedIBCState"],"allow_update_after_expiry":true,"allow_update_after_misbehaviour":true},"provider_consensus_state":{"timestamp":"2020-01-02T00:00:25Z","root":{"hash":"LpGpeyQVLUo9HpdsgJr12NP2eCICspcULiWa5u9udOA="},"next_validators_hash":"E30CE736441FB9101FADDAF7E578ABBE6DFDB67207112350A9A904D554E1F5BE"},"unbonding_sequences":null,"initial_val_set":[{"pub_key":{"Sum":{"ed25519":"dcASx5/LIKZqagJWN0frOlFtcvz91frYmj/zmoZRWro="}},"power":1}]}`

	var expectedGenesis consumertypes.GenesisState
	json.Unmarshal([]byte(jsonString), &expectedGenesis)

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
			}, true, false,
		},
	}

	for _, tc := range testCases {
		tc := tc

		suite.Run(tc.name, func() {
			suite.SetupTest()

			tc.malleate(suite)

			err := suite.providerChain.App.(*app.App).ProviderKeeper.CreateConsumerChainProposal(ctx, proposal)
			if tc.expPass {
				suite.Require().NoError(err, "error returned on valid case")
				if tc.spawnReached {
					clientId := suite.providerChain.App.(*app.App).ProviderKeeper.GetConsumerClient(ctx, chainID)
					consumerGenesis, ok := suite.providerChain.App.(*app.App).ProviderKeeper.GetConsumerGenesis(ctx, chainID)
					suite.Require().True(ok)

					expectedGenesis, err := suite.providerChain.App.(*app.App).ProviderKeeper.MakeConsumerGenesis(ctx)
					suite.Require().NoError(err)

					suite.Require().Equal(expectedGenesis, consumerGenesis)
					suite.Require().NotEqual("", clientId, "consumer client was not created after spawn time reached")
				} else {
					gotHeight := suite.providerChain.App.(*app.App).ProviderKeeper.GetPendingClientInfo(ctx, proposal.SpawnTime, chainID)
					suite.Require().Equal(initialHeight, gotHeight, "pending client not equal to clientstate in proposal")
				}
			} else {
				suite.Require().Error(err, "did not return error on invalid case")
			}
		})
	}
}
