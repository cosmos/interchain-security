package client

import (
	"encoding/json"
	"io/ioutil"
	"net/http"
	"os"
	"time"

	"path/filepath"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/client/tx"
	sdkcodec "github.com/cosmos/cosmos-sdk/codec"
	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/types/rest"
	govclient "github.com/cosmos/cosmos-sdk/x/gov/client"
	govrest "github.com/cosmos/cosmos-sdk/x/gov/client/rest"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/golang/protobuf/proto"
	"github.com/spf13/cobra"
)

// ProposalHandler is the param change proposal handler.
var ProposalHandler = govclient.NewProposalHandler(SubmitConsumerAdditionPropTxCmd, ProposalRESTHandler)
var ConsumerGovernanceHandler = govclient.NewProposalHandler(SubmitConsumerGovernancePropTxCmd, ConsumerGovernanceProposalRESTHandler)

const (
	FlagUpgradeHeight = "upgrade-height"
	FlagUpgradeInfo   = "upgrade-info"
)

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
				proposal.GenesisHash, proposal.BinaryHash, proposal.SpawnTime)

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

// ConsumerGovernanceProposalJSON defines the new Msg-based proposal.
type ConsumerGovernanceProposalJSON struct {
	Content      json.RawMessage `json:"content"`
	ConnectionId string          `json:"connection_id"`
	Deposit      string          `json:"deposit"`
}

type ConsumerGovernanceProposalReq struct {
	BaseReq  rest.BaseReq   `json:"base_req"`
	Proposer sdk.AccAddress `json:"proposer"`

	Content      json.RawMessage `json:"content"`
	ConnectionId string          `json:"connection_id"`
	Deposit      sdk.Coins       `json:"deposit"`
}

type ConsumerAdditionProposalJSON struct {
	Title         string             `json:"title"`
	Description   string             `json:"description"`
	ChainId       string             `json:"chain_id"`
	InitialHeight clienttypes.Height `json:"initial_height"`
	GenesisHash   []byte             `json:"genesis_hash"`
	BinaryHash    []byte             `json:"binary_hash"`
	SpawnTime     time.Time          `json:"spawn_time"`
	Deposit       string             `json:"deposit"`
}

type ConsumerAdditionProposalReq struct {
	BaseReq  rest.BaseReq   `json:"base_req"`
	Proposer sdk.AccAddress `json:"proposer"`

	Title         string             `json:"title"`
	Description   string             `json:"description"`
	ChainId       string             `json:"chainId"`
	InitialHeight clienttypes.Height `json:"initialHeight"`
	GenesisHash   []byte             `json:"genesisHash"`
	BinaryHash    []byte             `json:"binaryHash"`
	SpawnTime     time.Time          `json:"spawnTime"`
	Deposit       sdk.Coins          `json:"deposit"`
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
			req.GenesisHash, req.BinaryHash, req.SpawnTime)

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

// SubmitConsumerGovernancePropTxCmd returns a CLI command handler for submitting
// a consumer governance proposal via a transaction.
func SubmitConsumerGovernancePropTxCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "consumer-governance path/to/proposal.json",
		Args:  cobra.ExactArgs(1),
		Short: "Submit a consumer chain governance proposal",
		Long: `
Submit a consumer chain governance proposal along with an initial deposit.

Example:
$ interchain-security-pd tx gov submit-proposal consumer-governance path/to/proposal.json --from=<key_or_address>`,
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientTxContext(cmd)
			if err != nil {
				return err
			}

			proposalPath := args[0]
			connectionId, content, deposit, err := parseSubmitProposal(clientCtx.Codec, proposalPath)
			if err != nil {
				return err
			}

			any, err := codectypes.NewAnyWithValue(content.(proto.Message))
			if err != nil {
				return err
			}

			consumerProposal := types.ConsumerGovernanceProposal{
				ConnectionId: connectionId,
				Content:      any,
			}

			msg, err := govtypes.NewMsgSubmitProposal(&consumerProposal, deposit, clientCtx.GetFromAddress())
			if err != nil {
				return err
			}

			return tx.GenerateOrBroadcastTxCLI(clientCtx, cmd.Flags(), msg)
		},
	}

	return cmd
}

func ConsumerGovernanceProposalRESTHandler(clientCtx client.Context) govrest.ProposalRESTHandler {
	return govrest.ProposalRESTHandler{
		SubRoute: "propose_consumer_governance",
		Handler:  postProposalGovernanceHandlerFn(clientCtx),
	}
}

func postProposalGovernanceHandlerFn(clientCtx client.Context) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		var req ConsumerGovernanceProposalReq
		if !rest.ReadRESTReq(w, r, clientCtx.LegacyAmino, &req) {
			return
		}

		req.BaseReq = req.BaseReq.Sanitize()
		if !req.BaseReq.ValidateBasic(w) {
			return
		}

		var content govtypes.Content
		err := clientCtx.Codec.UnmarshalInterfaceJSON(req.Content, &content)
		if err != nil {
			return
		}
		any, err := codectypes.NewAnyWithValue(content.(proto.Message))
		if err != nil {
			return
		}
		consumerProposal := types.ConsumerGovernanceProposal{
			ConnectionId: req.ConnectionId,
			Content:      any,
		}

		msg, err := govtypes.NewMsgSubmitProposal(&consumerProposal, req.Deposit, req.Proposer)
		if rest.CheckBadRequestError(w, err) {
			return
		}

		if rest.CheckBadRequestError(w, msg.ValidateBasic()) {
			return
		}

		tx.WriteGeneratedTxResponse(clientCtx, w, req.BaseReq, msg)
	}
}

func parseSubmitProposal(cdc sdkcodec.Codec, path string) (string, govtypes.Content, sdk.Coins, error) {
	var proposal ConsumerGovernanceProposalJSON

	proposalJson, err := os.ReadFile(path)
	if err != nil {
		return "", nil, nil, err
	}

	err = json.Unmarshal(proposalJson, &proposal)
	if err != nil {
		return "", nil, nil, err
	}

	var content govtypes.Content
	err = cdc.UnmarshalInterfaceJSON(proposal.Content, &content)
	if err != nil {
		return "", nil, nil, err
	}

	deposit, err := sdk.ParseCoinsNormalized(proposal.Deposit)
	if err != nil {
		return "", nil, nil, err
	}

	return proposal.ConnectionId, content, deposit, nil
}
