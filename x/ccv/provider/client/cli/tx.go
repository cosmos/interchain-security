package cli

import (
	"github.com/spf13/cobra"

	"fmt"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/client/flags"
	"github.com/cosmos/cosmos-sdk/client/tx"
	cryptotypes "github.com/cosmos/cosmos-sdk/crypto/types"

	cryptocodec "github.com/cosmos/cosmos-sdk/crypto/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	flag "github.com/spf13/pflag"
	crypto "github.com/tendermint/tendermint/proto/tendermint/crypto"
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

	cmd.AddCommand(NewDesignateConsensusKeyForConsumerChainCmd())

	return cmd
}

func NewDesignateConsensusKeyForConsumerChainCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   ":TODO:",
		Short: ":TODO:",
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientTxContext(cmd)
			if err != nil {
				return err
			}

			txf := tx.NewFactoryCLI(clientCtx, cmd.Flags()).
				WithTxConfig(clientCtx.TxConfig).WithAccountRetriever(clientCtx.AccountRetriever)
			txf, msg, err := newBuildDesignateConsensusKeyForConsumerChainMsg(clientCtx, txf, cmd.Flags())
			if err != nil {
				return err
			}

			return tx.GenerateOrBroadcastTxWithFactory(clientCtx, txf, msg)
		},
	}

	cmd.Flags().AddFlagSet(FlagSetPublicKey())

	cmd.Flags().String(FlagIP, "", fmt.Sprintf("The node's public IP. It takes effect only when used in combination with --%s", flags.FlagGenerateOnly))
	cmd.Flags().String(FlagNodeID, "", "The node's ID")
	flags.AddTxFlagsToCmd(cmd)

	_ = cmd.MarkFlagRequired(flags.FlagFrom)
	_ = cmd.MarkFlagRequired(FlagPubKey)

	return cmd
}

func newBuildDesignateConsensusKeyForConsumerChainMsg(clientCtx client.Context, txf tx.Factory, fs *flag.FlagSet) (tx.Factory, *types.MsgDesignateConsensusKeyForConsumerChain, error) {

	pkStr, err := fs.GetString(FlagPubKey)
	if err != nil {
		return txf, nil, err
	}

	var pk cryptotypes.PubKey
	if err := clientCtx.Codec.UnmarshalInterfaceJSON([]byte(pkStr), &pk); err != nil {
		return txf, nil, err
	}

	// TODO: replace with real data
	chainId := "chainid"
	providerValidatorAddress := sdk.ValAddress{}
	consumerValidatorPubKey, _ := cryptocodec.FromTmProtoPublicKey(crypto.PublicKey{})

	msg, err := types.NewMsgDesignateConsensusKeyForConsumerChain(chainId, providerValidatorAddress, consumerValidatorPubKey)
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
