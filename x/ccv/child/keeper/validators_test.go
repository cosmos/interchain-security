package keeper_test

import (
	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	"github.com/cosmos/cosmos-sdk/crypto/keys/ed25519"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/app"
	"github.com/cosmos/interchain-security/x/ccv/child/types"
	abci "github.com/tendermint/tendermint/abci/types"
)

func (k KeeperTestSuite) TestApplyCCValidatorChain() {
	childKeeper := k.childChain.App.(*app.App).ChildKeeper
	ctx := k.ctx

	pk, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	k.Require().NoError(err)

	// expect an error when trying to unbound a validator not found in the child states
	_, err = childKeeper.ApplyCCValidatorChanges(ctx,
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
	newVals, err := childKeeper.ApplyCCValidatorChanges(ctx, changes)
	k.Require().NoError(err)
	// check that the new bonded validator is returned
	k.Require().Len(newVals, 1)

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
	newVals, err = childKeeper.ApplyCCValidatorChanges(ctx, changes[0:2])
	k.Require().NoError(err)
	k.Require().Len(newVals, 0)

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

func (s KeeperTestSuite) TestHandleValidatorsBonded() {
	childKeeper := s.childChain.App.(*app.App).ChildKeeper
	ctx := s.ctx

	// create new validator
	pk, err := cryptocodec.ToTmProtoPublicKey(ed25519.GenPrivKey().PubKey())
	s.Require().NoError(err)
	val := types.NewCCValidator(abci.ValidatorUpdate{PubKey: pk, Power: int64(1)})

	// expect an error when the validator isn't bonded, e.g. not found in child states
	err = childKeeper.HandleCCValidatorsBonded(ctx, []types.CrossChainValidator{*val})
	s.Require().Error(err)

	// set validator
	childKeeper.SetCCValidator(s.ctx, *val)

	// expect no error
	err = childKeeper.HandleCCValidatorsBonded(ctx, []types.CrossChainValidator{*val})
	s.Require().NoError(err)

	// check that all validators have their signing info
	// and pubkey created in slashing module states
	vals := childKeeper.GetAllCCValidator(ctx)

	for _, v := range vals {
		consAddr := sdk.ConsAddress(v.Address)
		_, found := s.childChain.App.(*app.App).SlashingKeeper.GetValidatorSigningInfo(ctx, consAddr)
		s.Require().True(found)
	}
}
