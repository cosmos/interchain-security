package rest

import (
	"fmt"
	"net/http"
	"strconv"
	"strings"

	"github.com/gorilla/mux"

	"github.com/cosmos/cosmos-sdk/client"
	clientrest "github.com/cosmos/cosmos-sdk/client/rest"
	"github.com/cosmos/cosmos-sdk/types/rest"
	"github.com/cosmos/cosmos-sdk/x/staking/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
)

func registerQueryRoutes(clientCtx client.Context, r *mux.Router) {
	// Get all validators
	r.HandleFunc(
		"/staking/validators",
		validatorsHandlerFn(clientCtx),
	).Methods("GET")

	// Get a single validator info
	r.HandleFunc(
		"/staking/validators/{validatorAddr}",
		validatorHandlerFn(clientCtx),
	).Methods("GET")

	// Get HistoricalInfo at a given height
	r.HandleFunc(
		"/staking/historical_info/{height}",
		historicalInfoHandlerFn(clientCtx),
	).Methods("GET")

	// Get the current staking parameter values
	r.HandleFunc(
		"/staking/parameters",
		paramsHandlerFn(clientCtx),
	).Methods("GET")
}

// HTTP request handler to query list of validators
func validatorsHandlerFn(clientCtx client.Context) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		_, page, limit, err := rest.ParseHTTPArgsWithLimit(r, 0)
		if rest.CheckBadRequestError(w, err) {
			return
		}

		clientCtx, ok := rest.ParseQueryHeightOrReturnBadRequest(w, clientCtx, r)
		if !ok {
			return
		}

		status := r.FormValue("status")
		// These are query params that were available in =<0.39. We show a nice
		// error message for this breaking change.
		if status == "bonded" || status == "unbonding" || status == "unbonded" {
			err := fmt.Errorf("cosmos sdk v0.40 introduces a breaking change on this endpoint:"+
				" instead of querying using `?status=%s`, please use `status=BOND_STATUS_%s`. For more"+
				" info, please see our REST endpoint migration guide at %s", status, strings.ToUpper(status), clientrest.DeprecationURL)

			if rest.CheckBadRequestError(w, err) {
				return
			}

		}

		if status == "" {
			status = types.BondStatusBonded
		}

		params := types.NewQueryValidatorsParams(page, limit, status)

		bz, err := clientCtx.LegacyAmino.MarshalJSON(params)
		if rest.CheckBadRequestError(w, err) {
			return
		}

		route := fmt.Sprintf("custom/%s/%s", ccvtypes.QuerierRoute, types.QueryValidators)

		res, height, err := clientCtx.QueryWithData(route, bz)
		if rest.CheckInternalServerError(w, err) {
			return
		}

		clientCtx = clientCtx.WithHeight(height)
		rest.PostProcessResponse(w, clientCtx, res)
	}
}

// HTTP request handler to query the validator information from a given validator address
func validatorHandlerFn(cliCtx client.Context) http.HandlerFunc {
	return queryValidator(cliCtx, fmt.Sprintf("custom/%s/%s", ccvtypes.QuerierRoute, types.QueryValidator))
}

// HTTP request handler to query historical info at a given height
func historicalInfoHandlerFn(clientCtx client.Context) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		vars := mux.Vars(r)
		heightStr := vars["height"]

		height, err := strconv.ParseInt(heightStr, 10, 64)
		if err != nil || height < 0 {
			rest.WriteErrorResponse(w, http.StatusBadRequest, fmt.Sprintf("Must provide non-negative integer for height: %v", err))
			return
		}

		params := types.QueryHistoricalInfoRequest{Height: height}

		bz, err := clientCtx.LegacyAmino.MarshalJSON(params)
		if rest.CheckInternalServerError(w, err) {
			return
		}

		res, height, err := clientCtx.QueryWithData(fmt.Sprintf("custom/%s/%s", ccvtypes.QuerierRoute, types.QueryHistoricalInfo), bz)
		if rest.CheckBadRequestError(w, err) {
			return
		}

		clientCtx = clientCtx.WithHeight(height)
		rest.PostProcessResponse(w, clientCtx, res)
	}
}

// HTTP request handler to query the staking params values
func paramsHandlerFn(clientCtx client.Context) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		clientCtx, ok := rest.ParseQueryHeightOrReturnBadRequest(w, clientCtx, r)
		if !ok {
			return
		}

		res, height, err := clientCtx.QueryWithData(fmt.Sprintf("custom/%s/%s", ccvtypes.QuerierRoute, types.QueryParameters), nil)
		if rest.CheckInternalServerError(w, err) {
			return
		}

		clientCtx = clientCtx.WithHeight(height)
		rest.PostProcessResponse(w, clientCtx, res)
	}
}
