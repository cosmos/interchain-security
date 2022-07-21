package keeper

import (
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	abci "github.com/tendermint/tendermint/abci/types"

	"github.com/cosmos/cosmos-sdk/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	sdkerrors "github.com/cosmos/cosmos-sdk/types/errors"
	"github.com/cosmos/cosmos-sdk/x/staking/types"
)

// creates a querier for staking REST endpoints
func NewQuerier(k Keeper, legacyQuerierCdc *codec.LegacyAmino) sdk.Querier {

	return func(ctx sdk.Context, path []string, req abci.RequestQuery) ([]byte, error) {
		switch path[0] {
		case types.QueryValidators:
			return queryValidators(ctx, req, k, legacyQuerierCdc)

		case types.QueryValidator:
			return queryValidator(ctx, req, k, legacyQuerierCdc)

		case types.QueryHistoricalInfo:
			return queryHistoricalInfo(ctx, req, k, legacyQuerierCdc)

		case types.QueryParameters:
			return queryParameters(ctx, k, legacyQuerierCdc)

		default:
			return nil, sdkerrors.Wrapf(sdkerrors.ErrUnknownRequest, "unknown %s query endpoint: %s", types.ModuleName, path[0])
		}
	}
}

func queryValidators(ctx sdk.Context, req abci.RequestQuery, k Keeper, legacyQuerierCdc *codec.LegacyAmino) ([]byte, error) {

	ctx.Logger().Info("consumer ccv module recv rest query staking/validators/")

	var params types.QueryValidatorsParams

	err := legacyQuerierCdc.UnmarshalJSON(req.Data, &params)
	if err != nil {
		return nil, sdkerrors.Wrap(sdkerrors.ErrJSONUnmarshal, err.Error())
	}

	validators := k.GetAllCCValidator(ctx)
	// validators := k.GetAllValidators(ctx)
	filteredVals := make(types.Validators, 0, len(validators))

	for _, val := range validators {
		v := stakingtypes.Validator{}
		v.OperatorAddress = sdk.ValAddress(val.Address).String()
		v.ConsensusPubkey = val.Pubkey
		v.Tokens = sdk.TokensFromConsensusPower(val.Power, sdk.DefaultPowerReduction)
		filteredVals = append(filteredVals, v)
	}

	res, err := codec.MarshalJSONIndent(legacyQuerierCdc, filteredVals)
	if err != nil {
		return nil, sdkerrors.Wrap(sdkerrors.ErrJSONMarshal, err.Error())
	}

	return res, nil
}

func queryValidator(ctx sdk.Context, req abci.RequestQuery, k Keeper, legacyQuerierCdc *codec.LegacyAmino) ([]byte, error) {

	ctx.Logger().Info("recv rest query staking/validator/")

	var params types.QueryValidatorParams

	err := legacyQuerierCdc.UnmarshalJSON(req.Data, &params)
	if err != nil {
		return nil, sdkerrors.Wrap(sdkerrors.ErrJSONUnmarshal, err.Error())
	}

	validators := k.GetAllCCValidator(ctx)
	found := false
	validator := stakingtypes.Validator{}
	for _, val := range validators {
		if sdk.ValAddress(val.Address).Equals(params.ValidatorAddr) {
			validator.OperatorAddress = sdk.ValAddress(val.Address).String()
			validator.ConsensusPubkey = val.Pubkey
			validator.Tokens = sdk.TokensFromConsensusPower(val.Power, sdk.DefaultPowerReduction)
			found = true
		}
	}

	if !found {
		return nil, types.ErrNoValidatorFound
	}

	res, err := codec.MarshalJSONIndent(legacyQuerierCdc, validator)
	if err != nil {
		return nil, sdkerrors.Wrap(sdkerrors.ErrJSONMarshal, err.Error())
	}

	return res, nil
}

func queryHistoricalInfo(ctx sdk.Context, req abci.RequestQuery, k Keeper, legacyQuerierCdc *codec.LegacyAmino) ([]byte, error) {
	var params types.QueryHistoricalInfoRequest

	err := legacyQuerierCdc.UnmarshalJSON(req.Data, &params)
	if err != nil {
		return nil, sdkerrors.Wrap(sdkerrors.ErrJSONUnmarshal, err.Error())
	}

	hi, found := k.GetHistoricalInfo(ctx, params.Height)
	if !found {
		return nil, types.ErrNoHistoricalInfo
	}

	res, err := codec.MarshalJSONIndent(legacyQuerierCdc, hi)
	if err != nil {
		return nil, sdkerrors.Wrap(sdkerrors.ErrJSONMarshal, err.Error())
	}

	return res, nil
}

func queryParameters(ctx sdk.Context, k Keeper, legacyQuerierCdc *codec.LegacyAmino) ([]byte, error) {
	params := k.GetParams(ctx)

	res, err := codec.MarshalJSONIndent(legacyQuerierCdc, params)
	if err != nil {
		return nil, sdkerrors.Wrap(sdkerrors.ErrJSONMarshal, err.Error())
	}

	return res, nil
}
