package keeper_test

import (
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	appConsumer "github.com/cosmos/interchain-security/app/consumer"
	"github.com/cosmos/interchain-security/x/ccv/consumer/types"
	abci "github.com/tendermint/tendermint/abci/types"
	tmrand "github.com/tendermint/tendermint/libs/rand"
	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

func (k KeeperTestSuite) TestApplyCCValidatorChanges() {
	consumerKeeper := k.consumerChain.App.(*appConsumer.App).ConsumerKeeper
	ctx := k.ctx

	// utility functions
	getCCVals := func() (vals []types.CrossChainValidator) {
		vals = consumerKeeper.GetAllCCValidator(ctx)
		return
	}

	setCCVals := func(vals []*tmtypes.Validator) {
		for _, v := range vals {
			pubkey, err := cryptocodec.FromTmPubKeyInterface(v.PubKey)
			k.Require().NoError(err)

			ccv, err := types.NewCCValidator(v.Address, v.VotingPower, pubkey)
			k.Require().NoError(err)
			consumerKeeper.SetCCValidator(ctx, ccv)
		}
	}

	clearCCVals := func() {
		ccVals := consumerKeeper.GetAllCCValidator(ctx)
		for _, v := range ccVals {
			consumerKeeper.DeleteCCValidator(ctx, v.Address)
		}
	}

	sumCCValsPow := func(vals []types.CrossChainValidator) (power int64) {
		for _, v := range vals {
			power += v.Power
		}
		return
	}

	// prepare the testing setup by clearing
	// the current cross-chain validators in states
	clearCCVals()

	// reuse the testsuite consumer chain validators
	// to construct changes
	tcVals := k.consumerChain.Vals.Validators
	changes := []abci.ValidatorUpdate{}
	changesPower := int64(0)

	for _, v := range tcVals {
		changes = append(changes, tmtypes.TM2PB.ValidatorUpdate(v))
		changesPower += v.VotingPower
	}

	// finish setup by importing 3 out 4 testing validators
	// into cross-chain validator states
	setCCVals(tcVals[:len(tcVals)-1])

	// verify setup
	ccVals := getCCVals()
	k.Require().Len(ccVals, len(tcVals)-1)

	// test behaviors
	testCases := []struct {
		changes       []abci.ValidatorUpdate
		expTotalPower int64
		expValsNum    int
	}{{ // add new bonded validator
		changes:       changes[len(changes)-1:],
		expTotalPower: changesPower,
		expValsNum:    len(ccVals) + 1,
	}, { // update a validator voting power
		changes:       []abci.ValidatorUpdate{{PubKey: changes[0].PubKey, Power: changes[0].Power + 3}},
		expTotalPower: changesPower + 3,
		expValsNum:    len(ccVals) + 1,
	}, { // unbond a validator
		changes:       []abci.ValidatorUpdate{{PubKey: changes[0].PubKey, Power: 0}},
		expTotalPower: changesPower - changes[0].Power,
		expValsNum:    len(ccVals),
	},
		{ // update all validators voting power
			changes: []abci.ValidatorUpdate{
				{PubKey: changes[0].PubKey, Power: changes[0].Power + 1},
				{PubKey: changes[1].PubKey, Power: changes[1].Power + 2},
				{PubKey: changes[2].PubKey, Power: changes[1].Power + 3},
				{PubKey: changes[3].PubKey, Power: changes[1].Power + 4},
			},
			expTotalPower: changesPower + 10,
			expValsNum:    len(ccVals) + 1,
		},
	}

	for _, t := range testCases {

		consumerKeeper.ApplyCCValidatorChanges(ctx, t.changes)
		gotVals := getCCVals()

		k.Require().Len(gotVals, t.expValsNum)
		k.Require().Equal(t.expTotalPower, sumCCValsPow(gotVals))
	}
}

func (k KeeperTestSuite) TestHistoricalInfo() {
	consumerKeeper := k.consumerChain.App.(*appConsumer.App).ConsumerKeeper
	cCtx := k.consumerChain.GetContext

	// get consumer validators
	cVals := consumerKeeper.GetAllCCValidator(cCtx())

	// iterates over validators and convert them to staking type
	sVals := []stakingtypes.Validator{}
	for _, v := range cVals {
		pk, err := v.ConsPubKey()
		k.Require().NoError(err)

		val, err := stakingtypes.NewValidator(nil, pk, stakingtypes.Description{})
		k.Require().NoError(err)

		// set voting power to random value
		val.Tokens = sdk.TokensFromConsensusPower(tmrand.NewRand().Int64(), sdk.DefaultPowerReduction)
		sVals = append(sVals, val)
	}

	currHeight := cCtx().BlockHeight()

	// create and store historical info
	hi := stakingtypes.NewHistoricalInfo(cCtx().BlockHeader(), sVals, sdk.DefaultPowerReduction)
	consumerKeeper.SetHistoricalInfo(cCtx(), currHeight, &hi)

	// expect to get historical info
	recv, found := consumerKeeper.GetHistoricalInfo(cCtx(), currHeight)
	k.Require().True(found, "HistoricalInfo not found after set")
	k.Require().Equal(hi, recv, "HistoricalInfo not equal")

	// verify that historical info valset has validators sorted in order
	k.Require().True(IsValSetSorted(recv.Valset, sdk.DefaultPowerReduction), "HistoricalInfo validators is not sorted")
}

func (k KeeperTestSuite) TestTrackHistoricalInfo() {
	consumerKeeper := k.consumerChain.App.(*appConsumer.App).ConsumerKeeper
	cCtx := k.consumerChain.GetContext

	// save init consumer valset length
	initValsetLen := len(consumerKeeper.GetAllCCValidator(cCtx()))
	// save current block height
	initHeight := cCtx().BlockHeight()

	// define an utility function that creates a new cross-chain validator
	// and then call track historical info in the next block
	createVal := func(k KeeperTestSuite) {
		// add new validator to consumer states
		pk := ed25519.GenPrivKey().PubKey()
		cVal, err := types.NewCCValidator(pk.Address(), int64(1), pk)
		k.Require().NoError(err)

		consumerKeeper.SetCCValidator(k.consumerChain.GetContext(), cVal)

		// commit block in order to call TrackHistoricalInfo
		k.consumerChain.NextBlock()
	}

	// testsetup create 2 validators and then call track historical info with header block height
	// increased by HistoricalEntries in order to prune the historical info less or equal to the current block height
	// Note that historical info containing the created validators are stored during the next block BeginBlocker
	// and thus are indexed with the respective block heights InitHeight+1 and InitHeight+2
	testSetup := []func(KeeperTestSuite){
		createVal,
		createVal,
		func(k KeeperTestSuite) {
			newHeight := k.consumerChain.GetContext().BlockHeight() + int64(types.HistoricalEntries)
			header := tmproto.Header{
				ChainID: "HelloChain",
				Height:  newHeight,
			}
			ctx := k.consumerChain.GetContext().WithBlockHeader(header)
			k.consumerChain.App.(*appConsumer.App).ConsumerKeeper.TrackHistoricalInfo(ctx)
		},
	}

	for _, ts := range testSetup {
		ts(k)
	}

	// test cases verify that historical info entries are pruned when their height
	// is below CurrentHeight - HistoricalEntries, and check that their valset gets updated
	testCases := []struct {
		height int64
		found  bool
		expLen int
	}{
		{
			height: initHeight + 1,
			found:  false,
			expLen: 0,
		},
		{
			height: initHeight + 2,
			found:  false,
			expLen: 0,
		},
		{
			height: initHeight + int64(types.HistoricalEntries) + 2,
			found:  true,
			expLen: initValsetLen + 2,
		},
	}

	for _, tc := range testCases {
		cCtx().WithBlockHeight(tc.height)
		hi, found := consumerKeeper.GetHistoricalInfo(cCtx().WithBlockHeight(tc.height), tc.height)
		k.Require().Equal(tc.found, found)
		k.Require().Len(hi.Valset, tc.expLen)
	}
}

// IsValSetSorted reports whether valset is sorted.
func IsValSetSorted(data []stakingtypes.Validator, powerReduction sdk.Int) bool {
	n := len(data)
	for i := n - 1; i > 0; i-- {
		if stakingtypes.ValidatorsByVotingPower(data).Less(i, i-1, powerReduction) {
			return false
		}
	}
	return true
}
