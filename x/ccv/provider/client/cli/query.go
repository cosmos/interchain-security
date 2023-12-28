package cli

import (
	"fmt"
	"strings"

	"github.com/spf13/cobra"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/client/flags"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/version"

	"github.com/cosmos/interchain-security/v3/x/ccv/provider/types"
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

	cmd.AddCommand(CmdConsumerGenesis())
	cmd.AddCommand(CmdConsumerChains())
	cmd.AddCommand(CmdConsumerStartProposals())
	cmd.AddCommand(CmdConsumerStopProposals())
	cmd.AddCommand(CmdConsumerValidatorKeyAssignment())
	cmd.AddCommand(CmdConsumerAllValidatorKeysAssignment())
	cmd.AddCommand(CmdProviderValidatorKey())
	cmd.AddCommand(CmdThrottleState())
	cmd.AddCommand(CmdRegisteredConsumerRewardDenoms())
	cmd.AddCommand(CmdProposedConsumerChains())

	return cmd
}

// NewQuerySubspaceParamsCmd returns a CLI command handler for querying subspace
// parameters managed by the x/params module.
func CmdConsumerGenesis() *cobra.Command {
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
			res, err := queryClient.QueryConsumerGenesis(cmd.Context(), &req)
			if err != nil {
				return err
			}

			return clientCtx.PrintProto(&res.GenesisState)
		},
	}

	flags.AddQueryFlagsToCmd(cmd)

	return cmd
}

func CmdConsumerChains() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "list-consumer-chains",
		Short: "Query active consumer chains for provider chain.",
		Args:  cobra.ExactArgs(0),
		RunE: func(cmd *cobra.Command, args []string) (err error) {
			clientCtx, err := client.GetClientQueryContext(cmd)
			if err != nil {
				return err
			}
			queryClient := types.NewQueryClient(clientCtx)

			req := &types.QueryConsumerChainsRequest{}
			res, err := queryClient.QueryConsumerChains(cmd.Context(), req)
			if err != nil {
				return err
			}

			return clientCtx.PrintProto(res)
		},
	}

	flags.AddQueryFlagsToCmd(cmd)

	return cmd
}

func CmdProposedConsumerChains() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "list-proposed-consumer-chains",
		Short: "Query chainIDs in consumer addition proposal before voting finishes",
		Args:  cobra.ExactArgs(0),
		RunE: func(cmd *cobra.Command, args []string) (err error) {
			clientCtx, err := client.GetClientQueryContext(cmd)
			if err != nil {
				return err
			}
			queryClient := types.NewQueryClient(clientCtx)

			req := &types.QueryProposedChainIDsRequest{}
			res, err := queryClient.QueryProposedConsumerChainIDs(cmd.Context(), req)
			if err != nil {
				return err
			}

			return clientCtx.PrintProto(res)
		},
	}

	flags.AddQueryFlagsToCmd(cmd)

	return cmd
}

func CmdConsumerStartProposals() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "list-start-proposals",
		Short: "Query consumer chains start proposals on provider chain.",
		Long: `Query mature and pending consumer chains start proposals on provider chain.
		Matured proposals will be executed on the next block - their spawn_time has passed
		Pending proposals are waiting for their spawn_time to pass.
		`,
		Args: cobra.ExactArgs(0),
		RunE: func(cmd *cobra.Command, args []string) (err error) {
			clientCtx, err := client.GetClientQueryContext(cmd)
			if err != nil {
				return err
			}
			queryClient := types.NewQueryClient(clientCtx)

			req := &types.QueryConsumerChainStartProposalsRequest{}
			res, err := queryClient.QueryConsumerChainStarts(cmd.Context(), req)
			if err != nil {
				return err
			}

			return clientCtx.PrintProto(res)
		},
	}

	flags.AddQueryFlagsToCmd(cmd)

	return cmd
}

func CmdConsumerStopProposals() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "list-stop-proposals",
		Short: "Query consumer chains stop proposals on provider chain.",
		Long: `Query mature and pending consumer chains stop proposals on provider chain.
		Matured proposals will be executed on the next block - their stop_time has passed
		Pending proposals are waiting for their stop_time to pass.
		`,
		Args: cobra.ExactArgs(0),
		RunE: func(cmd *cobra.Command, args []string) (err error) {
			clientCtx, err := client.GetClientQueryContext(cmd)
			if err != nil {
				return err
			}
			queryClient := types.NewQueryClient(clientCtx)

			req := &types.QueryConsumerChainStopProposalsRequest{}
			res, err := queryClient.QueryConsumerChainStops(cmd.Context(), req)
			if err != nil {
				return err
			}

			return clientCtx.PrintProto(res)
		},
	}

	flags.AddQueryFlagsToCmd(cmd)

	return cmd
}

// TODO: fix naming
func CmdConsumerValidatorKeyAssignment() *cobra.Command {
	bech32PrefixConsAddr := sdk.GetConfig().GetBech32ConsensusAddrPrefix()
	cmd := &cobra.Command{
		Use:   "validator-consumer-key [chainid] [provider-validator-address]",
		Short: "Query assigned validator consensus public key for a consumer chain",
		Long: strings.TrimSpace(
			fmt.Sprintf(`Returns the currently assigned validator consensus public key for a
consumer chain, if one has been assigned.
Example:
$ %s query provider validator-consumer-key foochain %s1gghjut3ccd8ay0zduzj64hwre2fxs9ldmqhffj
`,
				version.AppName, bech32PrefixConsAddr,
			),
		),
		Args: cobra.ExactArgs(2),
		RunE: func(cmd *cobra.Command, args []string) (err error) {
			clientCtx, err := client.GetClientQueryContext(cmd)
			if err != nil {
				return err
			}
			queryClient := types.NewQueryClient(clientCtx)

			consumerChainID := args[0]

			addr, err := sdk.ConsAddressFromBech32(args[1])
			if err != nil {
				return err
			}

			req := &types.QueryValidatorConsumerAddrRequest{
				ChainId:         consumerChainID,
				ProviderAddress: addr.String(),
			}
			res, err := queryClient.QueryValidatorConsumerAddr(cmd.Context(), req)
			if err != nil {
				return err
			}

			return clientCtx.PrintProto(res)
		},
	}

	flags.AddQueryFlagsToCmd(cmd)

	return cmd
}

// TODO: fix naming
func CmdConsumerAllValidatorKeysAssignment() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "validators-consumer-keys [chainid]",
		Short: "Query all assigned validators consensus public keys",
		Long: strings.TrimSpace(
			fmt.Sprintf(`Returns the currently assigned validators consensus public keys for a
specified consumer chain (or all chains), if one has been assigned.
Example:
$ %s query provider validators-consumer-keys foochain
`,
				version.AppName,
			),
		),
		Args: cobra.MaximumNArgs(1),
		RunE: func(cmd *cobra.Command, args []string) (err error) {
			clientCtx, err := client.GetClientQueryContext(cmd)
			if err != nil {
				return err
			}
			queryClient := types.NewQueryClient(clientCtx)

			consumerChainID := ""
			if len(args) > 0 {
				consumerChainID = args[0]
			}

			req := &types.QueryAllValidatorsConsumerAddrRequest{
				ChainId: consumerChainID,
			}
			res, err := queryClient.QueryAllValidatorsConsumerAddr(cmd.Context(), req)
			if err != nil {
				return err
			}

			return clientCtx.PrintProto(res)
		},
	}

	flags.AddQueryFlagsToCmd(cmd)

	return cmd
}

// TODO: fix naming
func CmdProviderValidatorKey() *cobra.Command {
	bech32PrefixConsAddr := sdk.GetConfig().GetBech32ConsensusAddrPrefix()
	cmd := &cobra.Command{
		Use:   "validator-provider-key [chainid] [consumer-validator-address]",
		Short: "Query validator consensus public key for the provider chain",
		Long: strings.TrimSpace(
			fmt.Sprintf(`Returns the currently assigned validator consensus public key for the provider chain.
Example:
$ %s query provider validator-provider-key foochain %s1gghjut3ccd8ay0zduzj64hwre2fxs9ldmqhffj
`,
				version.AppName, bech32PrefixConsAddr,
			),
		),
		Args: cobra.ExactArgs(2),
		RunE: func(cmd *cobra.Command, args []string) (err error) {
			clientCtx, err := client.GetClientQueryContext(cmd)
			if err != nil {
				return err
			}
			queryClient := types.NewQueryClient(clientCtx)

			consumerChainID := args[0]

			addr, err := sdk.ConsAddressFromBech32(args[1])
			if err != nil {
				return err
			}

			req := &types.QueryValidatorProviderAddrRequest{
				ChainId:         consumerChainID,
				ConsumerAddress: addr.String(),
			}
			res, err := queryClient.QueryValidatorProviderAddr(cmd.Context(), req)
			if err != nil {
				return err
			}

			return clientCtx.PrintProto(res)
		},
	}

	flags.AddQueryFlagsToCmd(cmd)

	return cmd
}

func CmdThrottleState() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "throttle-state",
		Short: "Query on-chain state relevant to slash packet throttling",
		Long: strings.TrimSpace(
			fmt.Sprintf(`Returns state relevant to throttled slash packet queue on the provider chain.
			Queue is ordered by time of arrival.
Example:
$ %s query provider throttle-state
`,
				version.AppName,
			),
		),
		Args: cobra.ExactArgs(0),
		RunE: func(cmd *cobra.Command, args []string) (err error) {
			clientCtx, err := client.GetClientQueryContext(cmd)
			if err != nil {
				return err
			}
			queryClient := types.NewQueryClient(clientCtx)

			req := &types.QueryThrottleStateRequest{}
			res, err := queryClient.QueryThrottleState(cmd.Context(), req)
			if err != nil {
				return err
			}

			return clientCtx.PrintProto(res)
		},
	}

	flags.AddQueryFlagsToCmd(cmd)

	return cmd
}

func CmdRegisteredConsumerRewardDenoms() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "registered-consumer-reward-denoms",
		Short: "Query registered consumer reward denoms",
		Long: strings.TrimSpace(
			fmt.Sprintf(`Returns the registered consumer reward denoms.
Example:
$ %s query provider registered-consumer-reward-denoms
`,
				version.AppName,
			),
		),
		Args: cobra.ExactArgs(0),
		RunE: func(cmd *cobra.Command, args []string) (err error) {
			clientCtx, err := client.GetClientQueryContext(cmd)
			if err != nil {
				return err
			}
			queryClient := types.NewQueryClient(clientCtx)

			req := &types.QueryRegisteredConsumerRewardDenomsRequest{}
			res, err := queryClient.QueryRegisteredConsumerRewardDenoms(cmd.Context(), req)
			if err != nil {
				return err
			}

			return clientCtx.PrintProto(res)
		},
	}

	flags.AddQueryFlagsToCmd(cmd)

	return cmd
}
