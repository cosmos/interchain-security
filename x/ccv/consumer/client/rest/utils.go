package rest

import (
	"net/http"

	"github.com/gorilla/mux"

	"github.com/cosmos/cosmos-sdk/client"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/types/rest"
	"github.com/cosmos/cosmos-sdk/x/staking/types"
)

func queryValidator(clientCtx client.Context, endpoint string) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		vars := mux.Vars(r)
		bech32validatorAddr := vars["validatorAddr"]

		_, page, limit, err := rest.ParseHTTPArgsWithLimit(r, 0)
		if rest.CheckBadRequestError(w, err) {
			return
		}

		validatorAddr, err := sdk.ValAddressFromBech32(bech32validatorAddr)
		if rest.CheckBadRequestError(w, err) {
			return
		}

		clientCtx, ok := rest.ParseQueryHeightOrReturnBadRequest(w, clientCtx, r)
		if !ok {
			return
		}

		params := types.NewQueryValidatorParams(validatorAddr, page, limit)

		bz, err := clientCtx.LegacyAmino.MarshalJSON(params)
		if rest.CheckBadRequestError(w, err) {
			return
		}

		res, height, err := clientCtx.QueryWithData(endpoint, bz)
		if rest.CheckInternalServerError(w, err) {
			return
		}

		clientCtx = clientCtx.WithHeight(height)
		rest.PostProcessResponse(w, clientCtx, res)
	}
}
