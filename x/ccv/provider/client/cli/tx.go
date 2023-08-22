package cli

import (
	"fmt"
	"strings"

	"github.com/spf13/cobra"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/client/flags"
	"github.com/cosmos/cosmos-sdk/client/tx"
	"github.com/cosmos/cosmos-sdk/version"
	ibctmtypes "github.com/cosmos/ibc-go/v4/modules/light-clients/07-tendermint/types"
	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/v2/x/ccv/provider/types"
)

// GetTxCmd returns the transaction commands for this module
func GetTxCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:                        types.ModuleName,
		Short:                      fmt.Sprintf("%s transactions subcommands", types.ModuleName),
		DisableFlagParsing:         true,
		SuggestionsMinimumDistance: 2,
		RunE:                       client.ValidateCmd,
	}

	cmd.AddCommand(NewAssignConsumerKeyCmd())
	cmd.AddCommand(NewRegisterConsumerRewardDenomCmd())
	cmd.AddCommand(NewSubmitConsumerMisbehaviourCmd())
	cmd.AddCommand(NewSubmitConsumerDoubleVotingCmd())

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

			txf := tx.NewFactoryCLI(clientCtx, cmd.Flags()).
				WithTxConfig(clientCtx.TxConfig).WithAccountRetriever(clientCtx.AccountRetriever)

			providerValAddr := clientCtx.GetFromAddress()

			msg, err := types.NewMsgAssignConsumerKey(args[0], sdk.ValAddress(providerValAddr), args[1])
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

func NewRegisterConsumerRewardDenomCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "register-consumer-reward-denom [denom]",
		Args:  cobra.ExactArgs(1),
		Short: "Registers a denom that can be sent from consumer chains to all validators and delegators as a reward",
		Long: strings.TrimSpace(
			fmt.Sprintf(`Registers a denom that can be sent from consumer chains to all validators and delegators as a reward.

Costs a fee, which is specified in genesis.json under the "consumer_reward_denom_fee" key. Will fail if the sending account has an insufficient balance.

Example:
$ %s tx provider register-consumer-reward-denom untrn --from mykey
`,
				version.AppName,
			),
		),
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientTxContext(cmd)
			if err != nil {
				return err
			}
			depositorAddr := clientCtx.GetFromAddress()

			msg := types.NewMsgRegisterConsumerRewardDenom(args[0], depositorAddr)

			return tx.GenerateOrBroadcastTxCLI(clientCtx, cmd.Flags(), msg)
		},
	}

	flags.AddTxFlagsToCmd(cmd)

	return cmd
}

func NewSubmitConsumerMisbehaviourCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "submit-consumer-misbehaviour [misbehaviour]",
		Short: "submit an IBC misbehaviour for a consumer chain",
		Long: strings.TrimSpace(
			fmt.Sprintf(`Submit an IBC misbehaviour detected on a consumer chain.
An IBC misbehaviour contains two conflicting IBC client headers, which are used to form a light client attack evidence.
The misbehaviour type definition can be found in the IBC client messages, see ibc-go/proto/ibc/core/client/v1/tx.proto.

Examples:
%s tx provider submit-consumer-misbehaviour [path/to/misbehaviour.json] --from node0 --home ../node0 --chain-id $CID
			`, version.AppName)),
		Args: cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientTxContext(cmd)
			if err != nil {
				return err
			}

			txf := tx.NewFactoryCLI(clientCtx, cmd.Flags()).
				WithTxConfig(clientCtx.TxConfig).WithAccountRetriever(clientCtx.AccountRetriever)

			submitter := clientCtx.GetFromAddress()
			var misbehaviour ibctmtypes.Misbehaviour
			if err := clientCtx.Codec.UnmarshalInterfaceJSON([]byte(args[1]), &misbehaviour); err != nil {
				return err
			}

			msg, err := types.NewMsgSubmitConsumerMisbehaviour(submitter, &misbehaviour)
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

func NewSubmitConsumerDoubleVotingCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "submit-consumer-double-voting [evidence]",
		Short: "submit a double-vote evidence for a consumer chain",
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientTxContext(cmd)
			if err != nil {
				return err
			}

			txf := tx.NewFactoryCLI(clientCtx, cmd.Flags()).
				WithTxConfig(clientCtx.TxConfig).WithAccountRetriever(clientCtx.AccountRetriever)

			submitter := clientCtx.GetFromAddress()
			var ev *tmproto.DuplicateVoteEvidence
			if err := clientCtx.Codec.UnmarshalInterfaceJSON([]byte(args[1]), &ev); err != nil {
				return err
			}

			// TODO: uncomment this when the infraction header is used
			// var header ibctmtypes.Header
			// if err := clientCtx.Codec.UnmarshalInterfaceJSON([]byte(args[2]), &header); err != nil {
			// 	return err
			// }

			msg, err := types.NewMsgSubmitConsumerDoubleVoting(submitter, ev, nil)
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
