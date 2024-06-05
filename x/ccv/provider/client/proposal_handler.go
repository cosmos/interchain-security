package client

import (
	"context"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	"github.com/spf13/cobra"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/client/tx"
	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	govclient "github.com/cosmos/cosmos-sdk/x/gov/client"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	govv1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"

	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
)

var (
	ConsumerAdditionProposalHandler   = govclient.NewProposalHandler(SubmitConsumerAdditionPropTxCmd)
	ConsumerRemovalProposalHandler    = govclient.NewProposalHandler(SubmitConsumerRemovalProposalTxCmd)
	ChangeRewardDenomsProposalHandler = govclient.NewProposalHandler(SubmitChangeRewardDenomsProposalTxCmd)
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
Unbonding period, transfer timeout period and ccv timeout period should be provided as nanosecond time periods.

Example:
$ <appd> tx gov submit-legacy-proposal consumer-addition <path/to/proposal.json> --from=<key_or_address>

Where proposal.json contains:

{
    "title": "Create the FooChain",
    "summary": "Gonna be a great chain",
    "chain_id": "foochain",
    "initial_height": {
        "revision_number": 2,
        "revision_height": 3
    },
    "genesis_hash": "Z2VuZXNpcyBoYXNo",
    "binary_hash": "YmluYXJ5IGhhc2g=",
    "spawn_time": "2022-01-27T15:59:50.121607-08:00",
    "blocks_per_distribution_transmission": 1000,
    "consumer_redistribution_fraction": "0.75",
	"distribution_transmission_channel": "",
    "historical_entries": 10000,
    "transfer_timeout_period": 3600000000000,
    "ccv_timeout_period": 2419200000000000,
    "unbonding_period": 1728000000000000,
    "deposit": "10000stake",
    "top_n": 0,
    "validators_power_cap": 32,
    "validator_set_cap": 50,
    "allowlist": [],
    "denylist": ["validatorAConsensusAddress", "validatorBConsensusAddress"]
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

			// do not fail for errors regarding the unbonding period, but just log a warning
			CheckPropUnbondingPeriod(clientCtx, proposal.UnbondingPeriod)

			content := types.NewConsumerAdditionProposal(
				proposal.Title, proposal.Summary, proposal.ChainId, proposal.InitialHeight,
				proposal.GenesisHash, proposal.BinaryHash, proposal.SpawnTime,
				proposal.ConsumerRedistributionFraction, proposal.BlocksPerDistributionTransmission,
				proposal.DistributionTransmissionChannel, proposal.HistoricalEntries,
				proposal.CcvTimeoutPeriod, proposal.TransferTimeoutPeriod, proposal.UnbondingPeriod, proposal.TopN,
				proposal.ValidatorsPowerCap, proposal.ValidatorSetCap, proposal.Allowlist, proposal.Denylist)

			from := clientCtx.GetFromAddress()

			deposit, err := sdk.ParseCoinsNormalized(proposal.Deposit)
			if err != nil {
				return err
			}

			msgContent, err := govv1.NewLegacyContent(content, authtypes.NewModuleAddress(govtypes.ModuleName).String())
			if err != nil {
				return err
			}

			msg, err := govv1.NewMsgSubmitProposal([]sdk.Msg{msgContent}, deposit, from.String(), "", content.GetTitle(), proposal.Summary)
			if err != nil {
				return err
			}

			return tx.GenerateOrBroadcastTxCLI(clientCtx, cmd.Flags(), msg)
		},
	}
}

// SubmitConsumerRemovalPropTxCmd returns a CLI command handler for submitting
// a consumer addition proposal via a transaction.
func SubmitConsumerRemovalProposalTxCmd() *cobra.Command {
	return &cobra.Command{
		Use:   "consumer-removal [proposal-file]",
		Args:  cobra.ExactArgs(1),
		Short: "Submit a consumer chain removal proposal",
		Long: `
Submit a consumer chain removal proposal along with an initial deposit.
The proposal details must be supplied via a JSON file.

Example:
$ <appd> tx gov submit-legacy-proposal consumer-removal <path/to/proposal.json> --from=<key_or_address>

Where proposal.json contains:
{
	 "title": "Stop the FooChain",
	 "summary": "It was a great chain",
	 "chain_id": "foochain",
	 "stop_time": "2022-01-27T15:59:50.121607-08:00",
	 "deposit": "10000stake"
}
			`, RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientTxContext(cmd)
			if err != nil {
				return err
			}

			proposal, err := ParseConsumerRemovalProposalJSON(args[0])
			if err != nil {
				return err
			}

			content := types.NewConsumerRemovalProposal(proposal.Title, proposal.Summary, proposal.ChainId, proposal.StopTime)
			from := clientCtx.GetFromAddress()

			msgContent, err := govv1.NewLegacyContent(content, authtypes.NewModuleAddress(govtypes.ModuleName).String())
			if err != nil {
				return err
			}

			deposit, err := sdk.ParseCoinsNormalized(proposal.Deposit)
			if err != nil {
				return err
			}

			msg, err := govv1.NewMsgSubmitProposal([]sdk.Msg{msgContent}, deposit, from.String(), "", content.GetTitle(), proposal.Summary)
			if err != nil {
				return err
			}

			return tx.GenerateOrBroadcastTxCLI(clientCtx, cmd.Flags(), msg)
		},
	}
}

// SubmitChangeRewardDenomsProposalTxCmd returns a CLI command handler for submitting
// a change reward denoms proposal via a transaction.
func SubmitChangeRewardDenomsProposalTxCmd() *cobra.Command {
	return &cobra.Command{
		Use:   "change-reward-denoms [proposal-file]",
		Args:  cobra.ExactArgs(1),
		Short: "Submit a change reward denoms proposal",
		Long: `Submit an change reward denoms proposal with an initial deposit.
		The proposal details must be supplied via a JSON file.

		Example:
		$ <appd> tx gov submit-legacy-proposal change-reward-denoms <path/to/proposal.json> --from=<key_or_address>

		Where proposal.json contains:
		{
			"title": "Change reward denoms",
			"summary": "Change reward denoms",
			"denoms_to_add": ["untrn"],
			"denoms_to_remove": ["stake"],
			"deposit": "10000stake"
		}
		`,
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientTxContext(cmd)
			if err != nil {
				return err
			}

			proposal, err := ParseChangeRewardDenomsProposalJSON(args[0])
			if err != nil {
				return err
			}

			content := types.NewChangeRewardDenomsProposal(proposal.Title, proposal.Summary, proposal.DenomsToAdd, proposal.DenomsToRemove)

			from := clientCtx.GetFromAddress()

			msgContent, err := govv1.NewLegacyContent(content, authtypes.NewModuleAddress(govtypes.ModuleName).String())
			if err != nil {
				return err
			}

			deposit, err := sdk.ParseCoinsNormalized(proposal.Deposit)
			if err != nil {
				return err
			}

			msg, err := govv1.NewMsgSubmitProposal([]sdk.Msg{msgContent}, deposit, from.String(), "", content.GetTitle(), proposal.Summary)
			if err != nil {
				return err
			}

			return tx.GenerateOrBroadcastTxCLI(clientCtx, cmd.Flags(), msg)
		},
	}
}

type ConsumerAdditionProposalJSON struct {
	Title         string             `json:"title"`
	Summary       string             `json:"summary"`
	ChainId       string             `json:"chain_id"`
	InitialHeight clienttypes.Height `json:"initial_height"`
	GenesisHash   []byte             `json:"genesis_hash"`
	BinaryHash    []byte             `json:"binary_hash"`
	SpawnTime     time.Time          `json:"spawn_time"`

	ConsumerRedistributionFraction    string        `json:"consumer_redistribution_fraction"`
	BlocksPerDistributionTransmission int64         `json:"blocks_per_distribution_transmission"`
	DistributionTransmissionChannel   string        `json:"distribution_transmission_channel"`
	HistoricalEntries                 int64         `json:"historical_entries"`
	CcvTimeoutPeriod                  time.Duration `json:"ccv_timeout_period"`
	TransferTimeoutPeriod             time.Duration `json:"transfer_timeout_period"`
	UnbondingPeriod                   time.Duration `json:"unbonding_period"`

	Deposit string `json:"deposit"`

	TopN               uint32   `json:"top_N"`
	ValidatorsPowerCap uint32   `json:"validators_power_cap"`
	ValidatorSetCap    uint32   `json:"validator_set_cap"`
	Allowlist          []string `json:"allowlist"`
	Denylist           []string `json:"denylist"`
}

type ConsumerAdditionProposalReq struct {
	Proposer sdk.AccAddress `json:"proposer"`

	Title         string             `json:"title"`
	Description   string             `json:"description"`
	ChainId       string             `json:"chainId"`
	InitialHeight clienttypes.Height `json:"initialHeight"`
	GenesisHash   []byte             `json:"genesisHash"`
	BinaryHash    []byte             `json:"binaryHash"`
	SpawnTime     time.Time          `json:"spawnTime"`

	ConsumerRedistributionFraction    string        `json:"consumer_redistribution_fraction"`
	BlocksPerDistributionTransmission int64         `json:"blocks_per_distribution_transmission"`
	DistributionTransmissionChannel   string        `json:"distribution_transmission_channel"`
	HistoricalEntries                 int64         `json:"historical_entries"`
	CcvTimeoutPeriod                  time.Duration `json:"ccv_timeout_period"`
	TransferTimeoutPeriod             time.Duration `json:"transfer_timeout_period"`
	UnbondingPeriod                   time.Duration `json:"unbonding_period"`

	Deposit sdk.Coins `json:"deposit"`
}

func ParseConsumerAdditionProposalJSON(proposalFile string) (ConsumerAdditionProposalJSON, error) {
	proposal := ConsumerAdditionProposalJSON{}

	contents, err := os.ReadFile(filepath.Clean(proposalFile))
	if err != nil {
		return proposal, err
	}

	if err := json.Unmarshal(contents, &proposal); err != nil {
		return proposal, err
	}

	return proposal, nil
}

type ConsumerRemovalProposalJSON struct {
	Title    string    `json:"title"`
	Summary  string    `json:"summary"`
	ChainId  string    `json:"chain_id"`
	StopTime time.Time `json:"stop_time"`
	Deposit  string    `json:"deposit"`
}

type ConsumerRemovalProposalReq struct {
	Proposer sdk.AccAddress `json:"proposer"`

	Title       string `json:"title"`
	Description string `json:"description"`
	ChainId     string `json:"chainId"`

	StopTime time.Time `json:"stopTime"`
	Deposit  sdk.Coins `json:"deposit"`
}

func ParseConsumerRemovalProposalJSON(proposalFile string) (ConsumerRemovalProposalJSON, error) {
	proposal := ConsumerRemovalProposalJSON{}

	contents, err := os.ReadFile(filepath.Clean(proposalFile))
	if err != nil {
		return proposal, err
	}

	if err := json.Unmarshal(contents, &proposal); err != nil {
		return proposal, err
	}

	return proposal, nil
}

type ChangeRewardDenomsProposalJSON struct {
	Summary string `json:"summary"`
	types.ChangeRewardDenomsProposal
	Deposit string `json:"deposit"`
}

type ChangeRewardDenomsProposalReq struct {
	Proposer sdk.AccAddress `json:"proposer"`
	types.ChangeRewardDenomsProposal
	Deposit sdk.Coins `json:"deposit"`
}

func ParseChangeRewardDenomsProposalJSON(proposalFile string) (ChangeRewardDenomsProposalJSON, error) {
	proposal := ChangeRewardDenomsProposalJSON{}

	contents, err := os.ReadFile(filepath.Clean(proposalFile))
	if err != nil {
		return proposal, err
	}
	if err := json.Unmarshal(contents, &proposal); err != nil {
		return proposal, err
	}
	return proposal, nil
}

func CheckPropUnbondingPeriod(clientCtx client.Context, propUnbondingPeriod time.Duration) {
	queryClient := stakingtypes.NewQueryClient(clientCtx)

	res, err := queryClient.Params(context.Background(), &stakingtypes.QueryParamsRequest{})
	if err != nil {
		fmt.Println(err.Error())
		return
	}

	providerUnbondingTime := res.Params.UnbondingTime

	if providerUnbondingTime < propUnbondingPeriod {
		fmt.Fprintf(
			os.Stderr,
			`consumer unbonding period is advised to be smaller than provider unbonding period, but is longer.
This is not a security risk, but will effectively lengthen the unbonding period on the provider.
consumer unbonding: %s
provider unbonding: %s`,
			propUnbondingPeriod,
			providerUnbondingTime)
	}
}

/* Proposal REST handlers: NOT NEEDED POST 47, BUT PLEASE CHECK THAT ALL FUNCTIONALITY EXISTS IN THE 47 VERSION.

// ConsumerAdditionProposalRESTHandler returns a ProposalRESTHandler that exposes the consumer addition rest handler.
func ConsumerAdditionProposalRESTHandler(clientCtx client.Context) govrest.ProposalRESTHandler {
	return govrest.ProposalRESTHandler{
		SubRoute: "consumer_addition",
		Handler:  postConsumerAdditionProposalHandlerFn(clientCtx),
	}
}

// ConsumerRemovalProposalRESTHandler returns a ProposalRESTHandler that exposes the consumer removal rest handler.
func ConsumerRemovalProposalRESTHandler(clientCtx client.Context) govrest.ProposalRESTHandler {
	return govrest.ProposalRESTHandler{
		SubRoute: "consumer_removal",
		Handler:  postConsumerRemovalProposalHandlerFn(clientCtx),
	}
}

func postConsumerAdditionProposalHandlerFn(clientCtx client.Context) http.HandlerFunc {
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
			req.GenesisHash, req.BinaryHash, req.SpawnTime,
			req.ConsumerRedistributionFraction, req.BlocksPerDistributionTransmission,
			req.DistributionTransmissionChannel, req.HistoricalEntries,
			req.CcvTimeoutPeriod, req.TransferTimeoutPeriod, req.UnbondingPeriod)

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

func postConsumerRemovalProposalHandlerFn(clientCtx client.Context) http.HandlerFunc {
	return func(w http.ResponseWriter, r *http.Request) {
		var req ConsumerRemovalProposalReq
		if !rest.ReadRESTReq(w, r, clientCtx.LegacyAmino, &req) {
			return
		}

		req.BaseReq = req.BaseReq.Sanitize()
		if !req.BaseReq.ValidateBasic(w) {
			return
		}

		content := types.NewConsumerRemovalProposal(
			req.Title, req.Description, req.ChainId, req.StopTime,
		)

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
*/
