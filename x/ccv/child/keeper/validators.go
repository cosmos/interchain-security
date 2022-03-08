package keeper

import (
	"fmt"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/child/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

// GetValsetFromValidators returns the validators valset
func (k Keeper) GetValsetFromValidators(ctx sdk.Context) (valset tmtypes.ValidatorSet, err error) {
	validators := k.GetAllValidators(ctx)
	if len(validators) == 0 {
		return valset, fmt.Errorf("expecting to have at least one validator")
	}

	for _, val := range validators {
		valTm, err := val.ToTmValidator()
		if err != nil {
			return valset, err
		}
		valset.Validators = append(valset.Validators, &valTm)
	}

	return valset, err
}

func (k Keeper) SetValidatorsFromValset(ctx sdk.Context, valset tmtypes.ValidatorSet) error {
	for _, tmVal := range valset.Validators {
		val, err := types.FromTmValidator(*tmVal)
		if err != nil {
			return err
		}
		k.SetValidatorByConsAddr(ctx, val)
	}
	return nil
}

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

// get the set of all validators with no limits, used during genesis dump
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
