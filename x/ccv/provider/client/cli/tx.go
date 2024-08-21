package cli

import (
	"encoding/json"
	"fmt"
	"os"
	"strings"
	"time"

	"cosmossdk.io/math"

	ibctmtypes "github.com/cosmos/ibc-go/v8/modules/light-clients/07-tendermint"
	"github.com/spf13/cobra"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/client/flags"
	"github.com/cosmos/cosmos-sdk/client/tx"
	"github.com/cosmos/cosmos-sdk/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/version"

	tmproto "github.com/cometbft/cometbft/proto/tendermint/types"

	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
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
	cmd.AddCommand(NewSubmitConsumerMisbehaviourCmd())
	cmd.AddCommand(NewSubmitConsumerDoubleVotingCmd())
	cmd.AddCommand(NewCreateConsumerCmd())
	cmd.AddCommand(NewUpdateConsumerCmd())
	cmd.AddCommand(NewRemoveConsumerCmd())
	cmd.AddCommand(NewOptInCmd())
	cmd.AddCommand(NewOptOutCmd())
	cmd.AddCommand(NewSetConsumerCommissionRateCmd())

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

func NewSubmitConsumerMisbehaviourCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "submit-consumer-misbehaviour [misbehaviour]",
		Short: "submit an IBC misbehaviour for a consumer chain",
		Long: strings.TrimSpace(
			fmt.Sprintf(`Submit an IBC misbehaviour detected on a consumer chain.
An IBC misbehaviour contains two conflicting IBC client headers, which are used to form a light client attack evidence.
The misbehaviour type definition can be found in the IBC client messages, see ibc-go/proto/ibc/core/client/v1/tx.proto.

Example:
%s tx provider submit-consumer-misbehaviour [path/to/misbehaviour.json] --from node0 --home ../node0 --chain-id $CID
			`, version.AppName)),
		Args: cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientTxContext(cmd)
			if err != nil {
				return err
			}

			txf, err := tx.NewFactoryCLI(clientCtx, cmd.Flags())
			if err != nil {
				return err
			}
			txf = txf.WithTxConfig(clientCtx.TxConfig).WithAccountRetriever(clientCtx.AccountRetriever)

			submitter := clientCtx.GetFromAddress()
			misbJson, err := os.ReadFile(args[0])
			if err != nil {
				return err
			}

			cdc := codec.NewProtoCodec(clientCtx.InterfaceRegistry)

			misbehaviour := ibctmtypes.Misbehaviour{}
			if err := cdc.UnmarshalJSON(misbJson, &misbehaviour); err != nil {
				return fmt.Errorf("misbehaviour unmarshalling failed: %s", err)
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
		Use:   "submit-consumer-double-voting [evidence] [infraction_header]",
		Short: "submit a double voting evidence for a consumer chain",
		Long: strings.TrimSpace(
			fmt.Sprintf(`Submit a Tendermint duplicate vote evidence detected on a consumer chain with
 the IBC light client header for the infraction height.
 The DuplicateVoteEvidence type definition can be found in the Tendermint messages,
 see cometbft/proto/tendermint/types/evidence.proto and the IBC header
 definition can be found in the IBC messages, see ibc-go/proto/ibc/lightclients/tendermint/v1/tendermint.proto.

Example:
%s tx provider submit-consumer-double-voting [path/to/evidence.json] [path/to/infraction_header.json] --from node0 --home ../node0 --chain-id $CID
`, version.AppName)),
		Args: cobra.ExactArgs(2),
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientTxContext(cmd)
			if err != nil {
				return err
			}

			txf, err := tx.NewFactoryCLI(clientCtx, cmd.Flags())
			if err != nil {
				return err
			}
			txf = txf.WithTxConfig(clientCtx.TxConfig).WithAccountRetriever(clientCtx.AccountRetriever)

			submitter := clientCtx.GetFromAddress()

			ev := tmproto.DuplicateVoteEvidence{}
			evidenceJson, err := os.ReadFile(args[0])
			if err != nil {
				return err
			}

			if err := json.Unmarshal(evidenceJson, &ev); err != nil {
				return fmt.Errorf("duplicate vote evidence unmarshalling failed: %s", err)
			}

			headerJson, err := os.ReadFile(args[1])
			if err != nil {
				return err
			}

			cdc := codec.NewProtoCodec(clientCtx.InterfaceRegistry)

			header := ibctmtypes.Header{}
			if err := cdc.UnmarshalJSON(headerJson, &header); err != nil {
				return fmt.Errorf("infraction IBC header unmarshalling failed: %s", err)
			}

			msg, err := types.NewMsgSubmitConsumerDoubleVoting(submitter, &ev, &header)
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

func NewCreateConsumerCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "create-consumer [chain-id] [path/to/metadata.json] [path/to/initialization-parameters.json] [path/to/power-shaping-parameters.json]",
		Short: "create a consumer chain",
		Long: strings.TrimSpace(
			fmt.Sprintf(`Create a consumer chain and get the assigned consumer id of this chain.
Note that the one that signs this message is the owner of this consumer chain. The owner can be later
changed by updating the consumer chain.

Example:
%s tx provider create-consumer [chain-id] [path/to/metadata.json] [path/to/initialization-parameters.json] [path/to/power-shaping-parameters.json] --from node0 --home ../node0 --chain-id $CID
`, version.AppName)),
		Args: cobra.ExactArgs(4),
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientTxContext(cmd)
			if err != nil {
				return err
			}

			txf, err := tx.NewFactoryCLI(clientCtx, cmd.Flags())
			if err != nil {
				return err
			}
			txf = txf.WithTxConfig(clientCtx.TxConfig).WithAccountRetriever(clientCtx.AccountRetriever)

			signer := clientCtx.GetFromAddress().String()

			chainId := args[0]

			metadata := types.ConsumerMetadata{}
			metadataJson, err := os.ReadFile(args[1])
			if err != nil {
				return err
			}
			if err = json.Unmarshal(metadataJson, &metadata); err != nil {
				return fmt.Errorf("metadata unmarshalling failed: %w", err)
			}

			initializationParameters := types.ConsumerInitializationParameters{}
			initializationParametersJson, err := os.ReadFile(args[2])
			if err != nil {
				return err
			}
			if err = json.Unmarshal(initializationParametersJson, &initializationParameters); err != nil {
				return fmt.Errorf("initialization parameters unmarshalling failed: %w", err)
			}

			powerShapingParameters := types.PowerShapingParameters{}

			powerShapingParametersJson, err := os.ReadFile(args[3])
			if err != nil {
				return err
			}
			if err = json.Unmarshal(powerShapingParametersJson, &powerShapingParameters); err != nil {
				return fmt.Errorf("power-shaping parameters unmarshalling failed: %w", err)
			}

			msg, err := types.NewMsgCreateConsumer(signer, chainId, metadata, initializationParameters, powerShapingParameters)
			if err != nil {
				return err
			}
			if err = msg.ValidateBasic(); err != nil {
				return err
			}

			return tx.GenerateOrBroadcastTxWithFactory(clientCtx, txf, msg)
		},
	}

	flags.AddTxFlagsToCmd(cmd)

	_ = cmd.MarkFlagRequired(flags.FlagFrom)

	return cmd
}

func NewUpdateConsumerCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "update-consumer [consumer-id] [owner-address] [path/to/metadata.json] [path/to/initialization-parameters.json] [path/to/power-shaping-parameters.json]",
		Short: "update a consumer chain",
		Long: strings.TrimSpace(
			fmt.Sprintf(`Update a consumer chain to change its parameters (e.g., spawn time, allow list, etc.).
Note that only the owner of the chain can initialize it.

Example:
%s tx provider update-consumer [consumer-id] [owner-address] [path/to/metadata.json] [path/to/initialization-parameters.json] [path/to/power-shaping-parameters.json] --from node0 --home ../node0 --chain-id $CID
`, version.AppName)),
		Args: cobra.ExactArgs(5),
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientTxContext(cmd)
			if err != nil {
				return err
			}

			txf, err := tx.NewFactoryCLI(clientCtx, cmd.Flags())
			if err != nil {
				return err
			}
			txf = txf.WithTxConfig(clientCtx.TxConfig).WithAccountRetriever(clientCtx.AccountRetriever)

			signer := clientCtx.GetFromAddress().String()
			consumerId := args[0]
			ownerAddress := args[1]

			metadata := types.ConsumerMetadata{}
			metadataJson, err := os.ReadFile(args[2])
			if err != nil {
				return err
			}
			if err = json.Unmarshal(metadataJson, &metadata); err != nil {
				return fmt.Errorf("metadata unmarshalling failed: %w", err)
			}

			initializationParameters := types.ConsumerInitializationParameters{}
			initializationParametersJson, err := os.ReadFile(args[3])
			if err != nil {
				return err
			}
			if err = json.Unmarshal(initializationParametersJson, &initializationParameters); err != nil {
				return fmt.Errorf("initialization parameters unmarshalling failed: %w", err)
			}

			powerShapingParameters := types.PowerShapingParameters{}
			powerShapingParametersJson, err := os.ReadFile(args[4])
			if err != nil {
				return err
			}
			if err = json.Unmarshal(powerShapingParametersJson, &powerShapingParameters); err != nil {
				return fmt.Errorf("power-shaping parameters unmarshalling failed: %w", err)
			}

			msg, err := types.NewMsgUpdateConsumer(signer, consumerId, ownerAddress, metadata, initializationParameters, powerShapingParameters)
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

func NewRemoveConsumerCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "remove-consumer [consumer-id] [stop-time-layout] [stop-time-value]",
		Short: "remove a consumer chain",
		Long: strings.TrimSpace(
			fmt.Sprintf(`Removes (and stops) a consumer chain. Note that only the owner of the chain can remove it.
Stop time is parsed by using the layout and the value (see https://pkg.go.dev/time#Parse).

Example:
%s tx provider remove-consumer [consumer-id] [stop-time-layout] [stop-time-value] --from node0 --home ../node0 --chain-id $CID
`, version.AppName)),
		Args: cobra.ExactArgs(3),
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientTxContext(cmd)
			if err != nil {
				return err
			}

			txf, err := tx.NewFactoryCLI(clientCtx, cmd.Flags())
			if err != nil {
				return err
			}
			txf = txf.WithTxConfig(clientCtx.TxConfig).WithAccountRetriever(clientCtx.AccountRetriever)

			signer := clientCtx.GetFromAddress().String()
			consumerId := args[0]
			stopTimeLayout := args[1]
			stopTimeValue := args[2]

			stopTime, err := time.Parse(stopTimeLayout, stopTimeValue)
			if err != nil {
				return err
			}

			msg, err := types.NewMsgRemoveConsumer(signer, consumerId, stopTime)
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

func NewOptInCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use: "opt-in [consumer-chain-id] [consumer-pubkey]",
		Short: "opts in validator to the consumer chain, and if given uses the " +
			"provided consensus public key for this consumer chain",
		Args: cobra.RangeArgs(1, 2),
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientTxContext(cmd)
			if err != nil {
				return err
			}

			txf, err := tx.NewFactoryCLI(clientCtx, cmd.Flags())
			if err != nil {
				return err
			}
			txf = txf.WithTxConfig(clientCtx.TxConfig).WithAccountRetriever(clientCtx.AccountRetriever)

			providerValAddr := clientCtx.GetFromAddress()

			var consumerPubKey string
			if len(args) == 2 {
				// consumer public key was provided
				consumerPubKey = args[1]
			} else {
				consumerPubKey = ""
			}

			signer := clientCtx.GetFromAddress().String()
			msg, err := types.NewMsgOptIn(args[0], sdk.ValAddress(providerValAddr), consumerPubKey, signer)
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

func NewOptOutCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "opt-out [consumer-chain-id]",
		Short: "opts out validator from this consumer chain",
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientTxContext(cmd)
			if err != nil {
				return err
			}

			txf, err := tx.NewFactoryCLI(clientCtx, cmd.Flags())
			if err != nil {
				return err
			}
			txf = txf.WithTxConfig(clientCtx.TxConfig).WithAccountRetriever(clientCtx.AccountRetriever)

			providerValAddr := clientCtx.GetFromAddress()

			signer := clientCtx.GetFromAddress().String()
			msg, err := types.NewMsgOptOut(args[0], sdk.ValAddress(providerValAddr), signer)
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

func NewSetConsumerCommissionRateCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "set-consumer-commission-rate [consumer-chain-id] [commission-rate]",
		Short: "set a per-consumer chain commission",
		Long: strings.TrimSpace(
			fmt.Sprintf(`Note that the "commission-rate" argument is a fraction and should be in the range [0,1].
			Example:
			%s set-consumer-commission-rate consumer-1 0.5 --from node0 --home ../node0`,
				version.AppName),
		),
		Args: cobra.ExactArgs(2),
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientTxContext(cmd)
			if err != nil {
				return err
			}

			txf, err := tx.NewFactoryCLI(clientCtx, cmd.Flags())
			if err != nil {
				return err
			}
			txf = txf.WithTxConfig(clientCtx.TxConfig).WithAccountRetriever(clientCtx.AccountRetriever)

			providerValAddr := clientCtx.GetFromAddress()

			commission, err := math.LegacyNewDecFromStr(args[1])
			if err != nil {
				return err
			}
			signer := clientCtx.GetFromAddress().String()
			msg := types.NewMsgSetConsumerCommissionRate(args[0], commission, sdk.ValAddress(providerValAddr), signer)
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
