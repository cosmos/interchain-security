package client

import (
	"encoding/json"
	"io/ioutil"
	"net/http"
	"time"

	"path/filepath"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/client/tx"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/types/rest"
	govclient "github.com/cosmos/cosmos-sdk/x/gov/client"
	govrest "github.com/cosmos/cosmos-sdk/x/gov/client/rest"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/spf13/cobra"
)

// ProposalHandler is the param change proposal handler.
var ProposalHandler = govclient.NewProposalHandler(SubmitConsumerAdditionPropTxCmd, ProposalRESTHandler)

// SubmitConsumerAdditionPropTxCmd returns a CLI command handler for submitting
// a consumer addition proposal via a transaction.
func SubmitConsumerAdditionPropTxCmd() *cobra.Command {
	return &cobra.Command{
		Use:   "consumer-addition [proposal-file]",
		Args:  cobra.ExactArgs(1),
		Short: "Submit a consumer addition proposal",
		Long: `
Submit a consumer addition proposal along with an initial deposit.
The proposal details must be supplied via a JSON file.

Example:
$ %s tx gov submit-proposal consumer-addition <path/to/proposal.json> --from=<key_or_address>

Where proposal.json contains:

{
    "title": "Create the FooChain",
    "description": "Gonna be a great chain",
    "chain_id": "foochain",
    "initial_height": {
        "revision_number": 2,
        "revision_height": 3
    },
    "genesis_hash": "Z2VuZXNpcyBoYXNo",
    "binary_hash": "YmluYXJ5IGhhc2g=",
    "spawn_time": "2022-01-27T15:59:50.121607-08:00",
    "deposit": "10000stake"
	"consumer_unbonding_period": 1728000000000000,
}
		`,
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientTxContext(cmd)
			if err != nil {
				return err
			}

			proposal, err := ParseConsumerAdditionProposalJSON(args[0])
			if err != nil {
				return err
			}

			content := types.NewConsumerAdditionProposal(
				proposal.Title, proposal.Description, proposal.ChainId, proposal.InitialHeight,
				proposal.GenesisHash, proposal.BinaryHash, proposal.SpawnTime, proposal.ConsumerUnbondingPeriod)

			from := clientCtx.GetFromAddress()

			deposit, err := sdk.ParseCoinsNormalized(proposal.Deposit)
			if err != nil {
				return err
			}

			msg, err := govtypes.NewMsgSubmitProposal(content, deposit, from)
			if err != nil {
				return err
			}

			return tx.GenerateOrBroadcastTxCLI(clientCtx, cmd.Flags(), msg)
		},
	}
}

type ConsumerAdditionProposalJSON struct {
	Title                   string             `json:"title"`
	Description             string             `json:"description"`
	ChainId                 string             `json:"chain_id"`
	InitialHeight           clienttypes.Height `json:"initial_height"`
	GenesisHash             []byte             `json:"genesis_hash"`
	BinaryHash              []byte             `json:"binary_hash"`
	SpawnTime               time.Time          `json:"spawn_time"`
	Deposit                 string             `json:"deposit"`
	ConsumerUnbondingPeriod time.Duration      `json:"consumer_unbonding_period"`
}

type ConsumerAdditionProposalReq struct {
	BaseReq  rest.BaseReq   `json:"base_req"`
	Proposer sdk.AccAddress `json:"proposer"`

	Title                   string             `json:"title"`
	Description             string             `json:"description"`
	ChainId                 string             `json:"chainId"`
	InitialHeight           clienttypes.Height `json:"initialHeight"`
	GenesisHash             []byte             `json:"genesisHash"`
	BinaryHash              []byte             `json:"binaryHash"`
	SpawnTime               time.Time          `json:"spawnTime"`
	Deposit                 sdk.Coins          `json:"deposit"`
	ConsumerUnbondingPeriod time.Duration      `json:"consumer_unbonding_period"`
}

func ParseConsumerAdditionProposalJSON(proposalFile string) (ConsumerAdditionProposalJSON, error) {
	proposal := ConsumerAdditionProposalJSON{}

	contents, err := ioutil.ReadFile(filepath.Clean(proposalFile))
	if err != nil {
		return proposal, err
	}

	if err := json.Unmarshal(contents, &proposal); err != nil {
		return proposal, err
	}

	return proposal, nil
}

// ProposalRESTHandler returns a ProposalRESTHandler that exposes the param
// change REST handler with a given sub-route.
func ProposalRESTHandler(clientCtx client.Context) govrest.ProposalRESTHandler {
	return govrest.ProposalRESTHandler{
		SubRoute: "propose_consumer_addition",
		Handler:  postProposalHandlerFn(clientCtx),
	}
}

func postProposalHandlerFn(clientCtx client.Context) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		var req ConsumerAdditionProposalReq
		if !rest.ReadRESTReq(w, r, clientCtx.LegacyAmino, &req) {
			return
		}

		req.BaseReq = req.BaseReq.Sanitize()
		if !req.BaseReq.ValidateBasic(w) {
			return
		}

		content := types.NewConsumerAdditionProposal(
			req.Title, req.Description, req.ChainId, req.InitialHeight,
			req.GenesisHash, req.BinaryHash, req.SpawnTime, req.ConsumerUnbondingPeriod)

		msg, err := govtypes.NewMsgSubmitProposal(content, req.Deposit, req.Proposer)
		if rest.CheckBadRequestError(w, err) {
			return
		}

		if rest.CheckBadRequestError(w, msg.ValidateBasic()) {
			return
		}

		tx.WriteGeneratedTxResponse(clientCtx, w, req.BaseReq, msg)
	}
}
