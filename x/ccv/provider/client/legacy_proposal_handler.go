package client

import (
	"github.com/spf13/cobra"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/client/tx"
	sdk "github.com/cosmos/cosmos-sdk/types"
	authtypes "github.com/cosmos/cosmos-sdk/x/auth/types"
	govclient "github.com/cosmos/cosmos-sdk/x/gov/client"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	govv1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"

	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
)

var (
	ChangeRewardDenomsProposalHandler = govclient.NewProposalHandler(SubmitChangeRewardDenomsProposalTxCmd)
)

// SubmitChangeRewardDenomsProposalTxCmd returns a CLI command handler for submitting
// a change reward denoms proposal via a transaction.
func SubmitChangeRewardDenomsProposalTxCmd() *cobra.Command {
	return &cobra.Command{
		Use:   "change-reward-denoms [proposal-file]",
		Args:  cobra.ExactArgs(1),
		Short: "Submit a change reward denoms proposal",
		Long: `Submit an change reward denoms proposal with an initial deposit.
		The proposal details must be supplied via a JSON file.

		Example:
		$ <appd> tx gov submit-legacy-proposal change-reward-denoms <path/to/proposal.json> --from=<key_or_address>

		Where proposal.json contains:
		{
			"title": "Change reward denoms",
			"summary": "Change reward denoms",
			"denoms_to_add": ["untrn"],
			"denoms_to_remove": ["stake"],
			"deposit": "10000stake"
		}
		`,
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientTxContext(cmd)
			if err != nil {
				return err
			}

			proposal, err := ParseChangeRewardDenomsProposalJSON(args[0])
			if err != nil {
				return err
			}

			content := types.NewChangeRewardDenomsProposal(proposal.Title, proposal.Summary, proposal.DenomsToAdd, proposal.DenomsToRemove)

			from := clientCtx.GetFromAddress()

			msgContent, err := govv1.NewLegacyContent(content, authtypes.NewModuleAddress(govtypes.ModuleName).String())
			if err != nil {
				return err
			}

			deposit, err := sdk.ParseCoinsNormalized(proposal.Deposit)
			if err != nil {
				return err
			}

			msg, err := govv1.NewMsgSubmitProposal([]sdk.Msg{msgContent}, deposit, from.String(), "", content.GetTitle(), proposal.Summary, false)
			if err != nil {
				return err
			}

			return tx.GenerateOrBroadcastTxCLI(clientCtx, cmd.Flags(), msg)
		},
	}
}
