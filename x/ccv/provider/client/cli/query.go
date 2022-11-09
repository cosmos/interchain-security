package cli

import (
	"github.com/spf13/cobra"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/client/flags"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
)

// NewQueryCmd returns a root CLI command handler for all x/ccv/provider query commands.
func NewQueryCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:                        types.ModuleName,
		Short:                      "Querying commands for the ccv provider module",
		DisableFlagParsing:         true,
		SuggestionsMinimumDistance: 2,
		RunE:                       client.ValidateCmd,
	}

	cmd.AddCommand(NewQueryConsumerGenesisCmd())

	return cmd
}

// NewQuerySubspaceParamsCmd returns a CLI command handler for querying subspace
// parameters managed by the x/params module.
func NewQueryConsumerGenesisCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "consumer-genesis [chainid]",
		Short: "Query for consumer chain genesis state by chain id",
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientQueryContext(cmd)
			if err != nil {
				return err
			}
			queryClient := types.NewQueryClient(clientCtx)

			req := types.QueryConsumerGenesisRequest{ChainId: args[0]}
			res, err := queryClient.ConsumerGenesis(cmd.Context(), &req)
			if err != nil {
				return err
			}

			return clientCtx.PrintProto(&res.GenesisState)
		},
	}

	flags.AddQueryFlagsToCmd(cmd)

	return cmd
}
