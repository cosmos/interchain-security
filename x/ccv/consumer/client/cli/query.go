package cli

import (
	"github.com/spf13/cobra"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/client/flags"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/x/ccv/types"
)

// NewQueryCmd returns a root CLI command handler for all x/ccv/provider query commands.
func NewQueryCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:                        consumertypes.ModuleName,
		Short:                      "Querying commands for the ccv consumer module",
		DisableFlagParsing:         true,
		SuggestionsMinimumDistance: 2,
		RunE:                       client.ValidateCmd,
	}

	cmd.AddCommand(CmdNextFeeDistribution())

	return cmd
}

func CmdNextFeeDistribution() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "next-fee-distribution",
		Short: "Query next fee distribution data",
		Args:  cobra.ExactArgs(0),
		RunE: func(cmd *cobra.Command, args []string) (err error) {
			clientCtx, err := client.GetClientQueryContext(cmd)
			if err != nil {
				return err
			}
			queryClient := ccvtypes.NewConsumerQueryClient(clientCtx)

			req := &ccvtypes.QueryNextFeeDistributionEstimateRequest{}
			res, err := queryClient.QueryNextFeeDistribution(cmd.Context(), req)
			if err != nil {
				return err
			}

			return clientCtx.PrintProto(res)
		},
	}

	flags.AddQueryFlagsToCmd(cmd)

	return cmd
}
