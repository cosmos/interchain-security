package keeper_test

import (
	appConsumer "github.com/cosmos/interchain-security/app_consumer"
	"github.com/cosmos/interchain-security/x/ccv/child/types"
	abci "github.com/tendermint/tendermint/abci/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

func (k KeeperTestSuite) TestApplyCCValidatorChanges() {
	childKeeper := k.childChain.App.(*appConsumer.App).ChildKeeper
	ctx := k.ctx

	// utility functions
	getCCVals := func() (vals []types.CrossChainValidator) {
		vals = childKeeper.GetAllCCValidator(ctx)
		return
	}

	setCCVals := func(vals []*tmtypes.Validator) {
		for _, v := range vals {
			childKeeper.SetCCValidator(ctx, types.NewCCValidator(v.Address, v.VotingPower))
		}
	}

	clearCCVals := func() {
		ccVals := childKeeper.GetAllCCValidator(ctx)
		for _, v := range ccVals {
			childKeeper.DeleteCCValidator(ctx, v.Address)
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

	// reuse the testsuite child chain validators
	// to construct changes
	tcVals := k.childChain.Vals.Validators
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
				childKeeper.ApplyCCValidatorChanges(ctx, t.changes)
			})
			continue
		}

		childKeeper.ApplyCCValidatorChanges(ctx, t.changes)
		gotVals := getCCVals()

		k.Require().Len(gotVals, t.expValsNum)
		k.Require().Equal(t.expTotalPower, sumCCValsPow(gotVals))
	}
}
