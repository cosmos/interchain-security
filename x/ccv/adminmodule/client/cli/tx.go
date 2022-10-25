package cli

import (
	"fmt"

	"github.com/spf13/cobra"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/client/flags"
	"github.com/cosmos/interchain-security/x/ccv/adminmodule/types"
)

// GetTxCmd returns the transaction commands for this module
func GetTxCmd(propCmds []*cobra.Command) *cobra.Command {
	cmd := &cobra.Command{
		Use:                        types.ModuleName,
		Short:                      fmt.Sprintf("%s transactions subcommands", types.ModuleName),
		DisableFlagParsing:         true,
		SuggestionsMinimumDistance: 2,
		RunE:                       client.ValidateCmd,
	}

	cmd.AddCommand(CmdDeleteAdmin())

	cmd.AddCommand(CmdAddAdmin())

	cmdSubmitProp := CmdSubmitProposal()
	for _, propCmd := range propCmds {
		flags.AddTxFlagsToCmd(propCmd)
		cmdSubmitProp.AddCommand(propCmd)
	}

	cmd.AddCommand(cmdSubmitProp)
	// this line is used by starport scaffolding # 1

	return cmd
}
