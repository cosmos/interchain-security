package keeper_test

import (
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
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
		expPanic      bool
	}{{ // add new bonded validator
		changes:       changes[len(changes)-1:],
		expTotalPower: changesPower,
		expValsNum:    len(ccVals) + 1,
	}, { // update a validator voting power
		changes:       []abci.ValidatorUpdate{{PubKey: changes[0].PubKey, Power: changes[0].Power + 3}},
		expTotalPower: changesPower + 3,
		expValsNum:    len(ccVals) + 1,
	}, { // unbound a validator
		changes:       []abci.ValidatorUpdate{{PubKey: changes[0].PubKey, Power: 0}},
		expTotalPower: changesPower - changes[0].Power,
		expValsNum:    len(ccVals),
	}, { // unbound an unexisting validator
		changes:  []abci.ValidatorUpdate{{PubKey: changes[0].PubKey, Power: 0}},
		expPanic: true,
	}, { // update all validators voting power
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
		if t.expPanic {
			k.Require().Panics(func() {
				consumerKeeper.ApplyCCValidatorChanges(ctx, t.changes)
			})
			continue
		}

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
		// update validators power
		val.Tokens = sdk.TokensFromConsensusPower(tmrand.NewRand().Int64(), sdk.DefaultPowerReduction)
		sVals = append(sVals, val)
	}

	// create and store historical info
	hi := stakingtypes.NewHistoricalInfo(cCtx().BlockHeader(), sVals, sdk.DefaultPowerReduction)
	consumerKeeper.SetHistoricalInfo(cCtx(), 2, &hi)

	// expect to get historical info
	recv, found := consumerKeeper.GetHistoricalInfo(cCtx(), 2)
	k.Require().True(found, "HistoricalInfo not found after set")
	k.Require().Equal(hi, recv, "HistoricalInfo not equal")
	// verify
	k.Require().True(IsValSetSorted(recv.Valset, sdk.DefaultPowerReduction), "HistoricalInfo validators is not sorted")
}

// TODO: use table testing
func (k KeeperTestSuite) TestTrackHistoricalInfo() {
	consumerKeeper := k.consumerChain.App.(*appConsumer.App).ConsumerKeeper
	cCtx := k.consumerChain.GetContext

	// get consumer validators
	cVals := consumerKeeper.GetAllCCValidator(cCtx())

	// iterates over validators and convert them to staking type
	sVals := []stakingtypes.Validator{}
	for _, v := range cVals[:len(cVals)-1] {
		pk, err := v.ConsPubKey()
		k.Require().NoError(err)

		val, err := stakingtypes.NewValidator(nil, pk, stakingtypes.Description{})
		k.Require().NoError(err)
		// update validators power
		val.Tokens = sdk.TokensFromConsensusPower(tmrand.NewRand().Int64(), sdk.DefaultPowerReduction)
		sVals = append(sVals, val)
	}

	// save current height
	oldHeight := cCtx().BlockHeight()

	// store historical info with one validator for previous block's height
	hi := stakingtypes.NewHistoricalInfo(cCtx().BlockHeader(), []stakingtypes.Validator{sVals[0]}, sdk.DefaultPowerReduction)
	consumerKeeper.SetHistoricalInfo(cCtx(), oldHeight-1, &hi)

	// store historical info with one validator for the current block's height
	hi = stakingtypes.NewHistoricalInfo(cCtx().BlockHeader(), []stakingtypes.Validator{sVals[1]}, sdk.DefaultPowerReduction)
	consumerKeeper.SetHistoricalInfo(cCtx(), oldHeight, &hi)

	// create new consumer validators
	pk := ed25519.GenPrivKey().PubKey()

	cVal, err := types.NewCCValidator(pk.Address(), int64(100), pk)
	k.Require().NoError(err)
	consumerKeeper.SetCCValidator(cCtx(), cVal)

	// Set Header for BeginBlock context with block height increased over the historical entires limit
	newHeight := int64(types.HistoricalEntries) + cCtx().BlockHeight()
	header := tmproto.Header{
		ChainID: "HelloChain",
		Height:  newHeight,
	}
	ctx := cCtx().WithBlockHeader(header)

	consumerKeeper.TrackHistoricalInfo(ctx)

	_, found := consumerKeeper.GetHistoricalInfo(ctx, newHeight)
	k.Require().True(found, "GetHistoricalInfo failed after BeginBlock")

	// TODO: compare the returned historical info header valset

	_, found = consumerKeeper.GetHistoricalInfo(cCtx(), newHeight)
	k.Require().True(found, "HistoricalInfo not found after set")

	_, found = consumerKeeper.GetHistoricalInfo(cCtx(), oldHeight-1)
	k.Require().False(found, "HistoricalInfo not found after set")

	_, found = consumerKeeper.GetHistoricalInfo(cCtx(), oldHeight)
	k.Require().False(found, "HistoricalInfo not found after set")

	// k.Require().Equal(expected, recv, "GetHistoricalInfo returned unexpected result")
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
