package cli

import (
	"fmt"

	"github.com/spf13/cobra"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/client/flags"
	"github.com/cosmos/cosmos-sdk/client/tx"
<<<<<<< HEAD
	"github.com/cosmos/cosmos-sdk/version"
=======
	sdk "github.com/cosmos/cosmos-sdk/types"
>>>>>>> 48a2186 (feat!: provider proposal for changing reward denoms (#1280))

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
