package cli

import (
	"strconv"

	"github.com/spf13/cobra"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/client/flags"
	"github.com/cosmos/cosmos-sdk/client/tx"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/adminmodule/types"
)

var _ = strconv.Itoa(0)

func CmdAddAdmin() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "add-admin [admin]",
		Short: "Broadcast message AddAdmin",
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {

			clientCtx, err := client.GetClientTxContext(cmd)
			if err != nil {
				return err
			}

			newAdmin, err := sdk.AccAddressFromBech32(args[0])
			if err != nil {
				return err
			}

			msg := types.NewMsgAddAdmin(clientCtx.GetFromAddress(), newAdmin)
			if err := msg.ValidateBasic(); err != nil {
				return err
			}
			return tx.GenerateOrBroadcastTxCLI(clientCtx, cmd.Flags(), msg)
		},
	}

	flags.AddTxFlagsToCmd(cmd)

	return cmd
}
