package cli

import (
	"fmt"
	"strconv"
	"strings"

	"github.com/spf13/cobra"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/client/flags"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/version"

	"github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
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
	cmd.AddCommand(CmdConsumerValidatorKeyAssignment())
	cmd.AddCommand(CmdProviderValidatorKey())
	cmd.AddCommand(CmdThrottleState())
	cmd.AddCommand(CmdRegisteredConsumerRewardDenoms())
	cmd.AddCommand(CmdAllPairsValConsAddrByConsumer())
	cmd.AddCommand(CmdProviderParameters())
	cmd.AddCommand(CmdConsumerChainOptedInValidators())
	cmd.AddCommand(CmdConsumerValidators())
	cmd.AddCommand(CmdConsumerChainsValidatorHasToValidate())
	cmd.AddCommand(CmdValidatorConsumerCommissionRate())
	cmd.AddCommand(CmdBlocksUntilNextEpoch())
	cmd.AddCommand(CmdConsumerIdFromClientId())
	cmd.AddCommand(CmdConsumerChain())
	return cmd
}

// NewQuerySubspaceParamsCmd returns a CLI command handler for querying subspace
// parameters managed by the x/params module.
func CmdConsumerGenesis() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "consumer-genesis [consumer-id]",
		Short: "Query for consumer chain genesis state by consumer id",
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientQueryContext(cmd)
			if err != nil {
				return err
			}
			queryClient := types.NewQueryClient(clientCtx)

			req := types.QueryConsumerGenesisRequest{ConsumerId: args[0]}
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
		Use:   "list-consumer-chains [phase] [limit]",
		Short: "Query consumer chains for provider chain.",
		Long: `Query consumer chains for provider chain. An optional
		integer parameter can be passed for phase filtering of consumer chains,
		(Registered=1|Initialized=2|Launched=3|Stopped=4|Deleted=5).`,
		Args: cobra.MaximumNArgs(2),
		RunE: func(cmd *cobra.Command, args []string) (err error) {
			clientCtx, err := client.GetClientQueryContext(cmd)
			if err != nil {
				return err
			}
			queryClient := types.NewQueryClient(clientCtx)

			req := &types.QueryConsumerChainsRequest{}

			if len(args) >= 1 && args[0] != "" {
				phase, err := strconv.ParseInt(args[0], 10, 32)
				if err != nil {
					return err
				}
				req.Phase = types.ConsumerPhase(phase)
			}

			if len(args) == 2 && args[1] != "" {
				limit, err := strconv.ParseInt(args[1], 10, 32)
				if err != nil {
					return err
				}
				req.Limit = int32(limit)
			}

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

// TODO: fix naming
func CmdConsumerValidatorKeyAssignment() *cobra.Command {
	bech32PrefixConsAddr := sdk.GetConfig().GetBech32ConsensusAddrPrefix()
	cmd := &cobra.Command{
		Use:   "validator-consumer-key [consumerId] [provider-validator-address]",
		Short: "Query assigned validator consensus public key for a consumer chain",
		Long: strings.TrimSpace(
			fmt.Sprintf(`Returns the currently assigned validator consensus public key for a
consumer chain, if one has been assigned.
Example:
$ %s query provider validator-consumer-key 3 %s1gghjut3ccd8ay0zduzj64hwre2fxs9ldmqhffj
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

			consumerId := args[0]

			addr, err := sdk.ConsAddressFromBech32(args[1])
			if err != nil {
				return err
			}

			req := &types.QueryValidatorConsumerAddrRequest{
				ConsumerId:      consumerId,
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
func CmdProviderValidatorKey() *cobra.Command {
	bech32PrefixConsAddr := sdk.GetConfig().GetBech32ConsensusAddrPrefix()
	cmd := &cobra.Command{
		Use:   "validator-provider-key [consumer-id] [consumer-validator-address]",
		Short: "Query validator consensus public key for the provider chain",
		Long: strings.TrimSpace(
			fmt.Sprintf(`Returns the currently assigned validator consensus public key for the provider chain.
Example:
$ %s query provider validator-provider-key 333 %s1gghjut3ccd8ay0zduzj64hwre2fxs9ldmqhffj
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

			consumerID := args[0]

			addr, err := sdk.ConsAddressFromBech32(args[1])
			if err != nil {
				return err
			}

			req := &types.QueryValidatorProviderAddrRequest{
				ConsumerId:      consumerID,
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

func CmdAllPairsValConsAddrByConsumer() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "all-pairs-valconsensus-address [consumer-id]",
		Short: "Query all pairs of valconsensus address by consumer ID.",
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientQueryContext(cmd)
			if err != nil {
				return err
			}
			queryClient := types.NewQueryClient(clientCtx)

			req := types.QueryAllPairsValConsAddrByConsumerRequest{ConsumerId: args[0]}
			res, err := queryClient.QueryAllPairsValConsAddrByConsumer(cmd.Context(), &req)
			if err != nil {
				return err
			}

			return clientCtx.PrintProto(res)
		},
	}

	flags.AddQueryFlagsToCmd(cmd)

	return cmd
}

// Command to query provider parameters
func CmdProviderParameters() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "params",
		Short: "Query provider parameters information",
		Long: strings.TrimSpace(
			fmt.Sprintf(`Query parameter values of provider.
Example:
$ %s query provider params
		`, version.AppName),
		),
		Args: cobra.NoArgs,
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientQueryContext(cmd)
			if err != nil {
				return err
			}
			queryClient := types.NewQueryClient(clientCtx)

			res, err := queryClient.QueryParams(cmd.Context(),
				&types.QueryParamsRequest{})
			if err != nil {
				return err
			}

			return clientCtx.PrintProto(&res.Params)
		},
	}

	flags.AddQueryFlagsToCmd(cmd)

	return cmd
}

// Command to query opted-in validators by consumer ID
func CmdConsumerChainOptedInValidators() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "consumer-opted-in-validators [consumer-id]",
		Short: "Query opted-in validators for a given consumer chain",
		Long: strings.TrimSpace(
			fmt.Sprintf(`Query opted-in validators for a given consumer chain.
Example:
$ %s consumer-opted-in-validators 3
		`, version.AppName),
		),
		Args: cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientQueryContext(cmd)
			if err != nil {
				return err
			}
			queryClient := types.NewQueryClient(clientCtx)

			res, err := queryClient.QueryConsumerChainOptedInValidators(cmd.Context(),
				&types.QueryConsumerChainOptedInValidatorsRequest{ConsumerId: args[0]})
			if err != nil {
				return err
			}

			return clientCtx.PrintProto(res)
		},
	}

	flags.AddQueryFlagsToCmd(cmd)

	return cmd
}

// Command to query the consumer validators by consumer ID
func CmdConsumerValidators() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "consumer-validators [consumer-id]",
		Short: "Query the last set consumer-validator set for a given consumer chain",
		Long: strings.TrimSpace(
			fmt.Sprintf(`Query the last set consumer-validator set for a given consumer chain.
Note that this does not necessarily mean that the consumer chain is currently using this validator set because a VSCPacket could be delayed, etc.
Example:
$ %s consumer-validators 3
		`, version.AppName),
		),
		Args: cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientQueryContext(cmd)
			if err != nil {
				return err
			}
			queryClient := types.NewQueryClient(clientCtx)

			res, err := queryClient.QueryConsumerValidators(cmd.Context(),
				&types.QueryConsumerValidatorsRequest{ConsumerId: args[0]})
			if err != nil {
				return err
			}

			return clientCtx.PrintProto(res)
		},
	}

	flags.AddQueryFlagsToCmd(cmd)

	return cmd
}

// Command to query the consumer chains list a given validator has to validate
func CmdConsumerChainsValidatorHasToValidate() *cobra.Command {
	bech32PrefixConsAddr := sdk.GetConfig().GetBech32ConsensusAddrPrefix()
	cmd := &cobra.Command{
		Use:   "has-to-validate [provider-validator-address]",
		Short: "Query the consumer chains list a given validator has to validate",
		Long: strings.TrimSpace(
			fmt.Sprintf(`the list of consumer chains that as a validator, you need to be running right now, is always a subset of this, so it seems like a very nice "safe bet".
Example:
$ %s has-to-validate %s1gghjut3ccd8ay0zduzj64hwre2fxs9ldmqhffj
		`, version.AppName, bech32PrefixConsAddr),
		),
		Args: cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientQueryContext(cmd)
			if err != nil {
				return err
			}
			queryClient := types.NewQueryClient(clientCtx)

			addr, err := sdk.ConsAddressFromBech32(args[0])
			if err != nil {
				return err
			}

			res, err := queryClient.QueryConsumerChainsValidatorHasToValidate(cmd.Context(),
				&types.QueryConsumerChainsValidatorHasToValidateRequest{
					ProviderAddress: addr.String(),
				})
			if err != nil {
				return err
			}

			return clientCtx.PrintProto(res)
		},
	}

	flags.AddQueryFlagsToCmd(cmd)

	return cmd
}

// Command to query the consumer commission rate a validator charges
// on a consumer chain
func CmdValidatorConsumerCommissionRate() *cobra.Command {
	bech32PrefixConsAddr := sdk.GetConfig().GetBech32ConsensusAddrPrefix()
	cmd := &cobra.Command{
		Use:   "validator-consumer-commission-rate [consumer-id] [provider-validator-address]",
		Short: "Query the consumer commission rate a validator charges on a consumer chain",
		Long: strings.TrimSpace(
			fmt.Sprintf(`Query the consumer commission rate a validator charges on a consumer chain.
Example:
$ %s validator-consumer-commission-rate 3 %s1gghjut3ccd8ay0zduzj64hwre2fxs9ldmqhffj
		`, version.AppName, bech32PrefixConsAddr),
		),
		Args: cobra.ExactArgs(2),
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientQueryContext(cmd)
			if err != nil {
				return err
			}
			queryClient := types.NewQueryClient(clientCtx)

			addr, err := sdk.ConsAddressFromBech32(args[1])
			if err != nil {
				return err
			}

			res, err := queryClient.QueryValidatorConsumerCommissionRate(cmd.Context(),
				&types.QueryValidatorConsumerCommissionRateRequest{
					ConsumerId:      args[0],
					ProviderAddress: addr.String(),
				})
			if err != nil {
				return err
			}

			return clientCtx.PrintProto(res)
		},
	}

	flags.AddQueryFlagsToCmd(cmd)

	return cmd
}

func CmdBlocksUntilNextEpoch() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "blocks-until-next-epoch",
		Short: "Query the number of blocks until the next epoch begins and validator updates are sent to consumer chains",
		Args:  cobra.ExactArgs(0),
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientQueryContext(cmd)
			if err != nil {
				return err
			}
			queryClient := types.NewQueryClient(clientCtx)

			req := &types.QueryBlocksUntilNextEpochRequest{}
			res, err := queryClient.QueryBlocksUntilNextEpoch(cmd.Context(), req)
			if err != nil {
				return err
			}

			return clientCtx.PrintProto(res)
		},
	}

	flags.AddQueryFlagsToCmd(cmd)

	return cmd
}

func CmdConsumerIdFromClientId() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "consumer-id-from-client-id [client-id]",
		Short: "Query the consumer id of the chain associated with the provided client id",
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientQueryContext(cmd)
			if err != nil {
				return err
			}
			queryClient := types.NewQueryClient(clientCtx)

			req := &types.QueryConsumerIdFromClientIdRequest{ClientId: args[0]}
			res, err := queryClient.QueryConsumerIdFromClientId(cmd.Context(), req)
			if err != nil {
				return err
			}

			return clientCtx.PrintProto(res)
		},
	}

	flags.AddQueryFlagsToCmd(cmd)

	return cmd
}

func CmdConsumerChain() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "consumer-chain [consumer-id]",
		Short: "Query the consumer chain associated with the consumer id",
		Args:  cobra.ExactArgs(1),
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientQueryContext(cmd)
			if err != nil {
				return err
			}
			queryClient := types.NewQueryClient(clientCtx)

			req := &types.QueryConsumerChainRequest{ConsumerId: args[0]}
			res, err := queryClient.QueryConsumerChain(cmd.Context(), req)
			if err != nil {
				return err
			}

			return clientCtx.PrintProto(res)
		},
	}

	flags.AddQueryFlagsToCmd(cmd)

	return cmd
}
