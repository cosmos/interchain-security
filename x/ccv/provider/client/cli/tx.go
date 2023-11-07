package cli

import (
	"fmt"
	"os"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/client/flags"
	"github.com/cosmos/cosmos-sdk/client/tx"
	"github.com/cosmos/cosmos-sdk/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/types/address"
	govcli "github.com/cosmos/cosmos-sdk/x/gov/client/cli"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	"github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
	"github.com/spf13/cobra"
)

const FlagAuthority = "authority"

// Get authority address from command line arguments or
// governance address as default if not provided on cli
func getAuthority(cmd *cobra.Command) (string, error) {
	authority, _ := cmd.Flags().GetString(FlagAuthority)
	if authority != "" {
		if _, err := sdk.AccAddressFromBech32(authority); err != nil {
			return "", fmt.Errorf("invalid authority address: %w", err)
		}
	} else {
		authority = sdk.AccAddress(address.Module(govtypes.ModuleName)).String()
	}
	return authority, nil
}

// Unmarshall json content of a file to given message type
func createMessageFromFile(ctx client.Context, cmd *cobra.Command, msg sdk.Msg, filePath string) error {
	content, err := os.ReadFile(filePath)
	if err != nil {
		return fmt.Errorf("error reading file: %w", err)
	}

	cdc := codec.NewProtoCodec(ctx.InterfaceRegistry)

	err = cdc.UnmarshalJSON(content, msg)
	if err != nil {
		return fmt.Errorf("invalid json content: %w", err)
	}
	return nil
}

// GetTxCmd returns the transaction commands for this module
func GetTxCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:                        types.ModuleName,
		Short:                      fmt.Sprintf("%s transactions subcommands", types.ModuleName),
		DisableFlagParsing:         true,
		SuggestionsMinimumDistance: 2,
		RunE:                       client.ValidateCmd,
	}

	cmd.AddCommand(
		NewAssignConsumerKeyCmd(),
		NewConsumerAdditionProposalCmd(),
		NewConsumerRemovalProposalCmd(),
		NewChangeRewardDenomsCmd())

	return cmd
}

func NewAssignConsumerKeyCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "assign-consensus-key [consumer-chain-id] [consumer-pubkey]",
		Short: "assign a consensus public key to use for a consumer chain",
		Args:  cobra.ExactArgs(2),
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientTxContext(cmd)
			if err != nil {
				return err
			}

			signer := clientCtx.GetFromAddress().String()
			txf, err := tx.NewFactoryCLI(clientCtx, cmd.Flags())
			if err != nil {
				return err
			}
			txf = txf.WithTxConfig(clientCtx.TxConfig).WithAccountRetriever(clientCtx.AccountRetriever)

			providerValAddr := clientCtx.GetFromAddress()

			msg, err := types.NewMsgAssignConsumerKey(args[0], sdk.ValAddress(providerValAddr), args[1], signer)
			if err != nil {
				return err
			}
			if err := msg.ValidateBasic(); err != nil {
				return err
			}

			return tx.GenerateOrBroadcastTxWithFactory(clientCtx, txf, msg)
		},
	}

	flags.AddTxFlagsToCmd(cmd)

	_ = cmd.MarkFlagRequired(flags.FlagFrom)

	return cmd
}

// NewConsumerAdditionProposalCmd creates a CLI command to submit a ConsumerAdditon proposal.
func NewConsumerAdditionProposalCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "consumer-addition [proposal-file] [flags]",
		Args:  cobra.ExactArgs(1),
		Short: "submit a consumer addition proposal",
		Long: `
		Submit a consumer addition proposal along with an initial deposit.
		The proposal details must be supplied via a JSON file.

		Example:
		$ <appd> tx provider consumer-addition <path/to/proposal.json> --from=<key_or_address> --title=<title> --summary=<summary>

		Where proposal.json contains:

		{
			"chain_id": "consumer",
			"initial_height": {
			 "revision_number": "1",
			 "revision_height": "1"
			},
			"genesis_hash": "Z2VuX2hhc2g=",
			"binary_hash": "YmluX2hhc2g=",
			"spawn_time": "2022-06-25T09:02:14.718477-08:00",
			"unbonding_period": "86400s",
			"ccv_timeout_period": "259200s",
			"transfer_timeout_period": "1800s",
			"consumer_redistribution_fraction": "0.75",
			"blocks_per_distribution_transmission": "1000",
			"historical_entries": "10000",
			"distribution_transmission_channel": ""
		 }`,
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientTxContext(cmd)
			if err != nil {
				return err
			}

			submitProposal, err := govcli.ReadGovPropFlags(clientCtx, cmd.Flags())
			if err != nil {
				return err
			}

			authority, err := getAuthority(cmd)
			if err != nil {
				return err
			}

			msgFileName := args[0]
			var msg types.MsgConsumerAddition
			err = createMessageFromFile(clientCtx, cmd, &msg, msgFileName)
			if err != nil {
				return err
			}

			msg.Signer = authority

			if err = msg.ValidateBasic(); err != nil {
				return fmt.Errorf("error validating %T: %w", types.MsgConsumerAddition{}, err)
			}

			if err := submitProposal.SetMsgs([]sdk.Msg{&msg}); err != nil {
				return fmt.Errorf("failed to create consumer addition proposal message: %w", err)
			}

			return tx.GenerateOrBroadcastTxCLI(clientCtx, cmd.Flags(), submitProposal)
		},
	}

	cmd.Flags().String(FlagAuthority, "", "The address of the client module authority (defaults to gov)")

	flags.AddTxFlagsToCmd(cmd)
	govcli.AddGovPropFlagsToCmd(cmd)
	err := cmd.MarkFlagRequired(govcli.FlagTitle)
	if err != nil {
		panic(err)
	}

	return cmd
}

// NewConsumerRemovalProposalCmd creates a CLI command to submit a ConsumerRemoval proposal.
func NewConsumerRemovalProposalCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "consumer-removal [proposal-file] [flags]",
		Args:  cobra.ExactArgs(1),
		Short: "submit a consumer removal proposal",
		Long: `
		Submit a consumer removal proposal along with an initial deposit.
		The proposal details must be supplied via a JSON file.

		Example:
		$ <appd> tx gov submit-legacy-proposal consumer-removal <path/to/proposal.json> --from=<key_or_address> --title=<title> --summary=<summary>

		Where proposal.json contains:

		{
			"chain_id": "foochain",
			"stop_time": "2022-01-27T15:59:50.121607-08:00",
		 }`,
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientTxContext(cmd)
			if err != nil {
				return err
			}

			submitProposal, err := govcli.ReadGovPropFlags(clientCtx, cmd.Flags())
			if err != nil {
				return err
			}

			msgFileName := args[0]
			var msg types.MsgConsumerRemoval
			err = createMessageFromFile(clientCtx, cmd, &msg, msgFileName)
			if err != nil {
				return err
			}

			authority, err := getAuthority(cmd)
			if err != nil {
				return err
			}
			msg.Signer = authority

			if err = msg.ValidateBasic(); err != nil {
				return fmt.Errorf("error validating %T: %w", types.MsgConsumerRemoval{}, err)
			}

			if err := submitProposal.SetMsgs([]sdk.Msg{&msg}); err != nil {
				return fmt.Errorf("failed to create consumer addition proposal message: %w", err)
			}

			return tx.GenerateOrBroadcastTxCLI(clientCtx, cmd.Flags(), submitProposal)
		},
	}

	cmd.Flags().String(FlagAuthority, "", "The address of the client module authority (defaults to gov)")

	flags.AddTxFlagsToCmd(cmd)
	govcli.AddGovPropFlagsToCmd(cmd)
	err := cmd.MarkFlagRequired(govcli.FlagTitle)
	if err != nil {
		panic(err)
	}

	return cmd
}

// NewChangeRewardDenomsCmd creates a CLI command to submit a ChangeRewardDenoms proposal.
func NewChangeRewardDenomsCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "change-reward-denoms [proposal-file] [flags]",
		Args:  cobra.ExactArgs(1),
		Short: "Submit a change reward denoms proposal",
		Long: `Submit an change reward denoms proposal with an initial deposit.
		The proposal details must be supplied via a JSON file.

		Example:
		$ <appd> tx gov submit-legacy-proposal change-reward-denoms <path/to/proposal.json> --from=<key_or_address>

		Where proposal.json contains:
		{
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

			submitProposal, err := govcli.ReadGovPropFlags(clientCtx, cmd.Flags())
			if err != nil {
				return err
			}

			msgFileName := args[0]
			var msg types.MsgChangeRewardDenoms
			err = createMessageFromFile(clientCtx, cmd, &msg, msgFileName)
			if err != nil {
				return err
			}

			authority, err := getAuthority(cmd)
			if err != nil {
				return err
			}
			msg.Signer = authority

			if err = msg.ValidateBasic(); err != nil {
				return fmt.Errorf("error validating %T: %w", types.MsgConsumerRemoval{}, err)
			}

			if err := submitProposal.SetMsgs([]sdk.Msg{&msg}); err != nil {
				return fmt.Errorf("failed to create consumer addition proposal message: %w", err)
			}

			return tx.GenerateOrBroadcastTxCLI(clientCtx, cmd.Flags(), submitProposal)
		},
	}

	cmd.Flags().String(FlagAuthority, "", "The address of the client module authority (defaults to gov)")

	flags.AddTxFlagsToCmd(cmd)
	govcli.AddGovPropFlagsToCmd(cmd)
	err := cmd.MarkFlagRequired(govcli.FlagTitle)
	if err != nil {
		panic(err)
	}

	return cmd
}
