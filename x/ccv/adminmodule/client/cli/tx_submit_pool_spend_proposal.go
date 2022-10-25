package cli

import (
	"fmt"
	"os"
	"strings"

	"path/filepath"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/client/tx"
	"github.com/cosmos/cosmos-sdk/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/version"
	distrtypes "github.com/cosmos/cosmos-sdk/x/distribution/types"
	"github.com/cosmos/interchain-security/x/ccv/adminmodule/types"
	"github.com/spf13/cobra"
)

// NewSubmitPoolSpendProposalTxCmd implements the command to submit a community-pool-spend proposal
func NewSubmitPoolSpendProposalTxCmd() *cobra.Command {
	bech32PrefixAccAddr := sdk.GetConfig().GetBech32AccountAddrPrefix()

	cmd := &cobra.Command{
		Use:   "community-pool-spend [proposal-file]",
		Args:  cobra.ExactArgs(1),
		Short: "Submit a community pool spend proposal",
		Long: strings.TrimSpace(
			fmt.Sprintf(`Submit a community pool spend proposal.
The proposal details must be supplied via a JSON file.

Example:
$ %s tx adminmodule submit-proposal community-pool-spend <path/to/proposal.json> --from=<key_or_address>

Where proposal.json contains:

{
  "title": "Community Pool Spend",
  "description": "Pay me some Atoms!",
  "recipient": "%s1s5afhd6gxevu37mkqcvvsj8qeylhn0rz46zdlq",
  "amount": "1000stake"
}
`,
				version.AppName, bech32PrefixAccAddr,
			),
		),
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientTxContext(cmd)
			if err != nil {
				return err
			}
			proposal, err := ParseCommunityPoolSpendProposalWithDeposit(clientCtx.JSONCodec, args[0])
			if err != nil {
				return err
			}

			amount, err := sdk.ParseCoinsNormalized(proposal.Amount)
			if err != nil {
				return err
			}

			from := clientCtx.GetFromAddress()
			recpAddr, err := sdk.AccAddressFromBech32(proposal.Recipient)
			if err != nil {
				return err
			}
			content := distrtypes.NewCommunityPoolSpendProposal(proposal.Title, proposal.Description, recpAddr, amount)

			msg, err := types.NewMsgSubmitProposal(content, from)
			if err != nil {
				return err
			}

			if err := msg.ValidateBasic(); err != nil {
				return err
			}

			return tx.GenerateOrBroadcastTxCLI(clientCtx, cmd.Flags(), msg)
		},
	}

	return cmd
}

// ParseCommunityPoolSpendProposalWithDeposit reads and parses a CommunityPoolSpendProposalWithDeposit from a file.
func ParseCommunityPoolSpendProposalWithDeposit(cdc codec.JSONCodec, proposalFile string) (distrtypes.CommunityPoolSpendProposalWithDeposit, error) {
	proposal := distrtypes.CommunityPoolSpendProposalWithDeposit{}

	contents, err := os.ReadFile(filepath.Clean(proposalFile))
	if err != nil {
		return proposal, err
	}

	if err = cdc.UnmarshalJSON(contents, &proposal); err != nil {
		return proposal, err
	}

	return proposal, nil
}
