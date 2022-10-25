package rest

import (
	"fmt"
	"net/http"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/types/rest"
	"github.com/cosmos/interchain-security/x/ccv/adminmodule/types"
	"github.com/gorilla/mux"
)

func registerQueryRoutes(clientCtx client.Context, r *mux.Router) {
	// curl -X GET "http://localhost:1317/adminmodule/admins"
	r.HandleFunc("/adminmodule/admins", queryAdminsHandlerFn(clientCtx)).Methods("GET")
	// curl -X GET "http://localhost:1317/adminmodule/archivedproposals"
	r.HandleFunc("/adminmodule/archivedproposals", queryArchivedProposalsHandlerFn(clientCtx)).Methods("GET")
}

func queryAdminsHandlerFn(clientCtx client.Context) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		clientCtx, ok := rest.ParseQueryHeightOrReturnBadRequest(w, clientCtx, r)
		if !ok {
			return
		}

		res, height, err := clientCtx.Query(fmt.Sprintf("custom/adminmodule/%s", types.QueryAdmins))
		if rest.CheckNotFoundError(w, err) {
			return
		}

		clientCtx = clientCtx.WithHeight(height)
		rest.PostProcessResponse(w, clientCtx, res)
	}
}

func queryArchivedProposalsHandlerFn(clientCtx client.Context) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		clientCtx, ok := rest.ParseQueryHeightOrReturnBadRequest(w, clientCtx, r)
		if !ok {
			return
		}

		res, height, err := clientCtx.Query(fmt.Sprintf("custom/adminmodule/%s", types.QueryArchivedProposals))
		if rest.CheckNotFoundError(w, err) {
			return
		}

		clientCtx = clientCtx.WithHeight(height)
		rest.PostProcessResponse(w, clientCtx, res)
	}
}
