package keeper_test

import (
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	"github.com/cosmos/interchain-security/app"
	abci "github.com/tendermint/tendermint/abci/types"
)

func (k KeeperTestSuite) TestApplyCCValidatorChanges() {
	childKeeper := k.childChain.App.(*app.App).ChildKeeper
	ctx := k.ctx

	pk, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	k.Require().NoError(err)

	// expect an error when trying to unbound a validator not found in the child states
	err = childKeeper.ApplyCCValidatorChanges(ctx,
		[]abci.ValidatorUpdate{{PubKey: pk, Power: 0}})
	k.Require().Error(err)

	// get validators created from genesis
	vals := childKeeper.GetAllCCValidator(ctx)
	k.Require().Len(vals, 4)

	// create 6 changes including a new bonded validator
	changes := []abci.ValidatorUpdate{
		{
			PubKey: pk,
			Power:  int64(1),
		},
	}
	// sum total voting power
	expVotingPower := int64(1)

	for i, val := range vals {
		// update power
		newPow := int64((i + 1) * 100)
		val.ValidatorUpdate.Power = newPow
		changes = append(changes, val.ValidatorUpdate)
		// sum total voting power
		expVotingPower += newPow
	}

	// apply changes to child states
	err = childKeeper.ApplyCCValidatorChanges(ctx, changes)
	k.Require().NoError(err)

	// check total voting power
	ccVals := childKeeper.GetAllCCValidator(ctx)
	k.Require().NoError(err)
	k.Require().Len(ccVals, 5)

	vp := int64(0)
	for _, v := range ccVals {
		vp += v.ValidatorUpdate.Power
	}
	k.Require().Equal(expVotingPower, vp)

	// create changes unbounding two validators
	for i := 0; i < 2; i++ {
		expVotingPower -= changes[i].Power
		changes[i].Power = 0
	}

	// apply and verify changes from the child states
	err = childKeeper.ApplyCCValidatorChanges(ctx, changes[0:2])
	k.Require().NoError(err)

	ccVals = childKeeper.GetAllCCValidator(ctx)
	k.Require().NoError(err)
	k.Require().Len(ccVals, 3)

	// compute total voting power obtained
	vp = int64(0)
	for _, v := range ccVals {
		vp += v.ValidatorUpdate.Power
	}

	k.Require().Equal(expVotingPower, vp)
}
