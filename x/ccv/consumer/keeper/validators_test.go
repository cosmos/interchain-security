package keeper_test

import (
	"github.com/cosmos/interchain-security/app"
	"github.com/cosmos/interchain-security/x/ccv/consumer/types"
	abci "github.com/tendermint/tendermint/abci/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

func (k KeeperTestSuite) TestApplyCCValidatorChanges() {
	consumerKeeper := k.consumerChain.App.(*app.App).ConsumerKeeper
	ctx := k.ctx

	// utility functions
	getCCVals := func() (vals []types.CrossChainValidator) {
		vals = consumerKeeper.GetAllCCValidator(ctx)
		return
	}

	setCCVals := func(vals []*tmtypes.Validator) {
		for _, v := range vals {
			consumerKeeper.SetCCValidator(ctx, types.NewCCValidator(v.Address, v.VotingPower))
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
