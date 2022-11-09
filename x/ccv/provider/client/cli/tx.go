package cli

import (
	"github.com/spf13/cobra"

	"fmt"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/client/flags"
	"github.com/cosmos/cosmos-sdk/client/tx"
	cryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	flag "github.com/spf13/pflag"
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

	cmd.AddCommand(NewAssignConsensusPublicKeyToConsumerChainCmd())

	return cmd
}

func NewAssignConsensusPublicKeyToConsumerChainCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "assign-consensus-key [consumer-chain-id] [consumer-pubkey]",
		Short: "assign a consensus public key to use for a consumer chain",
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientTxContext(cmd)
			if err != nil {
				return err
			}

			txf := tx.NewFactoryCLI(clientCtx, cmd.Flags()).
				WithTxConfig(clientCtx.TxConfig).WithAccountRetriever(clientCtx.AccountRetriever)
			txf, msg, err := newAssignConsensusPublicKeyToConsumerChainMsg(clientCtx, txf, cmd.Flags())
			if err != nil {
				return err
			}

			return tx.GenerateOrBroadcastTxWithFactory(clientCtx, txf, msg)
		},
	}

	cmd.Flags().AddFlagSet(FlagSetConsumerChainId())
	cmd.Flags().AddFlagSet(FlagSetPublicKey())

	cmd.Flags().String(FlagIP, "", fmt.Sprintf("The node's public IP. It takes effect only when used in combination with --%s", flags.FlagGenerateOnly))
	cmd.Flags().String(FlagNodeID, "", "The node's ID")
	flags.AddTxFlagsToCmd(cmd)

	_ = cmd.MarkFlagRequired(flags.FlagFrom)
	_ = cmd.MarkFlagRequired(FlagConsumerChainId)
	_ = cmd.MarkFlagRequired(FlagConsumerPubKey)

	return cmd
}

func newAssignConsensusPublicKeyToConsumerChainMsg(clientCtx client.Context, txf tx.Factory, fs *flag.FlagSet) (tx.Factory, *types.MsgAssignConsensusPublicKeyToConsumerChain, error) {

	providerValAddr := clientCtx.GetFromAddress()
	consumerPubKeyStr, err := fs.GetString(FlagConsumerPubKey)
	if err != nil {
		return txf, nil, err
	}

	var consumerPubKey cryptotypes.PubKey
	if err := clientCtx.Codec.UnmarshalInterfaceJSON([]byte(consumerPubKeyStr), &consumerPubKey); err != nil {
		return txf, nil, err
	}

	chainId, _ := fs.GetString(FlagConsumerChainId)

	msg, err := types.NewMsgAssignConsensusPublicKeyToConsumerChain(chainId, sdk.ValAddress(providerValAddr), consumerPubKey)
	if err != nil {
		return txf, nil, err
	}
	if err := msg.ValidateBasic(); err != nil {
		return txf, nil, err
	}

	genOnly, _ := fs.GetBool(flags.FlagGenerateOnly)
	if genOnly {
		ip, _ := fs.GetString(FlagIP)
		nodeID, _ := fs.GetString(FlagNodeID)

		if nodeID != "" && ip != "" {
			txf = txf.WithMemo(fmt.Sprintf("%s@%s:26656", nodeID, ip))
		}
	}

	return txf, msg, nil
}
