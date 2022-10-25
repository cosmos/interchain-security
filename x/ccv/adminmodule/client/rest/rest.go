package rest

import (
	"github.com/gorilla/mux"

	"github.com/cosmos/cosmos-sdk/client"
	clientrest "github.com/cosmos/cosmos-sdk/client/rest"
	sdkrest "github.com/cosmos/cosmos-sdk/types/rest"
	govrest "github.com/cosmos/cosmos-sdk/x/gov/client/rest"
)

func RegisterHandlers(clientCtx client.Context, rtr *mux.Router, phs []govrest.ProposalRESTHandler) {
	r := clientrest.WithHTTPDeprecationHeaders(rtr)
	registerQueryRoutes(clientCtx, r)
	registerTxHandlers(clientCtx, r, phs)
}

// AddAdminReq ...
type AddAdminReq struct {
	BaseReq sdkrest.BaseReq `json:"base_req" yaml:"base_req"`
	Admin   string          `json:"admin" yaml:"admin"`
}

// DeleteAdminReq ...
type DeleteAdminReq struct {
	BaseReq sdkrest.BaseReq `json:"base_req" yaml:"base_req"`
	Admin   string          `json:"admin" yaml:"admin"`
}
