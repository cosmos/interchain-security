package cli

import (
	"github.com/spf13/cobra"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/client/flags"
	"github.com/cosmos/interchain-security/x/ccv/parent/types"
)

// NewQueryCmd returns a root CLI command handler for all x/ccv/parent query commands.
func NewQueryCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:                        types.ModuleName,
		Short:                      "Querying commands for the ccv parent module",
		DisableFlagParsing:         true,
		SuggestionsMinimumDistance: 2,
		RunE:                       client.ValidateCmd,
	}

	cmd.AddCommand(NewQueryChildGenesisCmd())

	return cmd
}

// NewQuerySubspaceParamsCmd returns a CLI command handler for querying subspace
// parameters managed by the x/params module.
func NewQueryChildGenesisCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "child-genesis [chainid]",
		Short: "Query for child chain genesis state by chain id",
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientQueryContext(cmd)
			if err != nil {
				return err
			}
			queryClient := types.NewQueryClient(clientCtx)

			req := types.QueryChildGenesisRequest{ChainId: args[0]}
			res, err := queryClient.ChildGenesis(cmd.Context(), &req)
			if err != nil {
				return err
			}

			return clientCtx.PrintProto(&res.GenesisState)
		},
	}

	flags.AddQueryFlagsToCmd(cmd)

	return cmd
}
