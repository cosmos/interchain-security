package keeper

import (
	"fmt"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/child/types"
	abci "github.com/tendermint/tendermint/abci/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

// validator index
func (k Keeper) SetValidatorByConsAddr(ctx sdk.Context, v types.Validator) {
	store := ctx.KVStore(k.storeKey)
	bz := k.cdc.MustMarshal(&v)

	store.Set(types.GetValidatorByConsAddrKey(types.MustParseConsAdrr(v.ConsensusAddress)), bz)
}

// get a single validator by consensus address
func (k Keeper) GetValidatorByConsAddr(ctx sdk.Context, addr sdk.ConsAddress) (validator types.Validator, found bool) {
	store := ctx.KVStore(k.storeKey)
	v := store.Get(types.GetValidatorByConsAddrKey(addr))
	if v == nil {
		return validator, false
	}
	k.cdc.MustUnmarshal(v, &validator)

	return validator, true
}

func (k Keeper) DeleteValidatorByConsAddr(ctx sdk.Context, addr sdk.ConsAddress) {
	store := ctx.KVStore(k.storeKey)
	store.Delete(types.GetValidatorByConsAddrKey(addr))
}

// get the set of all validators
func (k Keeper) GetAllValidators(ctx sdk.Context) (validators []types.Validator) {
	store := ctx.KVStore(k.storeKey)

	iterator := sdk.KVStorePrefixIterator(store, []byte(types.ValidatorByConsAddrPrefix))
	defer iterator.Close()

	for ; iterator.Valid(); iterator.Next() {
		val := types.Validator{}
		k.cdc.MustUnmarshal(iterator.Value(), &val)
		validators = append(validators, val)
	}

	return validators
}

// GetValsetFromValidators returns the validators valset
func (k Keeper) GetValsetFromValidators(ctx sdk.Context) (valset tmtypes.ValidatorSet, err error) {
	vals := k.GetAllValidators(ctx)
	return types.Validators(vals).GetValset()
}

// ProcessNewChanges computes and proccess the changes which validator are not part
// of the given valset
func (k Keeper) ApplyValidatorChanges(ctx sdk.Context, changes []abci.ValidatorUpdate) ([]sdk.ConsAddress, error) {
	// newChanges, err := utils.GetNewChanges(changes, valset)
	newValAddrs := []sdk.ConsAddress{}
	for _, change := range changes {
		pk, err := cryptocodec.FromTmProtoPublicKey(change.GetPubKey())
		if err != nil {
			return nil, err
		}
		consAddr := sdk.ConsAddress(pk.Address())
		val, found := k.GetValidatorByConsAddr(ctx, consAddr)

		if change.Power < 1 {
			if found {
				k.DeleteValidatorByConsAddr(ctx, consAddr)
				continue
			}
			return nil, fmt.Errorf("failed to find validator %X to remove", consAddr)
		}

		if !found {
			val, err = types.NewValidator(pk, change.Power)
			if err != nil {
				return nil, err
			}
			newValAddrs = append(newValAddrs, consAddr)
		} else {
			val.VotingPower = change.Power
		}

		k.SetValidatorByConsAddr(ctx, val)
	}

	if len(newValAddrs) > 0 {
		k.HandleNewBondings(ctx, newValAddrs)
	}

	return newValAddrs, nil
}

func (k Keeper) HandleNewBondings(ctx sdk.Context, valAddresses []sdk.ConsAddress) {
	for _, addr := range valAddresses {
		k.slashingKeeper.AfterValidatorBonded(ctx, addr, nil)
		k.ClearPenaltySentToProvider(ctx, addr)
	}
}
