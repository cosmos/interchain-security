package cli

import (
	"fmt"
	"strconv"
	"strings"

	"github.com/spf13/cobra"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/client/flags"
	"github.com/cosmos/cosmos-sdk/client/tx"
	"github.com/cosmos/cosmos-sdk/version"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	"github.com/cosmos/interchain-security/x/ccv/adminmodule/types"
)

var _ = strconv.Itoa(0)

// Proposal flags
const (
	FlagTitle        = "title"
	FlagDescription  = "description"
	FlagProposalType = "type"
	FlagProposal     = "proposal"
)

type proposal struct {
	Title       string
	Description string
	Type        string
}

// ProposalFlags defines the core required fields of a proposal. It is used to
// verify that these values are not provided in conjunction with a JSON proposal
// file.
var ProposalFlags = []string{
	FlagTitle,
	FlagDescription,
	FlagProposalType,
}

func CmdSubmitProposal() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "submit-proposal",
		Short: "Submit a proposal",
		Long: strings.TrimSpace(
			fmt.Sprintf(`Submit a proposal.
Proposal title, description, type and can be given directly or through a proposal JSON file.

Example:
$ %s adminmodule submit-proposal --proposal="path/to/proposal.json" --from mykey

Where proposal.json contains:

{
  "title": "Test Proposal",
  "description": "My awesome proposal",
  "type": "Text"
}

Which is equivalent to:

$ %s tx adminmodule submit-proposal --title="Test Proposal" --description="My awesome proposal" --type="Text" --from mykey
`,
				version.AppName, version.AppName,
			),
		),
		RunE: func(cmd *cobra.Command, args []string) error {
			clientCtx, err := client.GetClientTxContext(cmd)
			if err != nil {
				return err
			}

			proposal, err := parseSubmitProposalFlags(cmd.Flags())
			if err != nil {
				return fmt.Errorf("failed to parse proposal: %w", err)
			}

			content := govtypes.ContentFromProposalType(proposal.Title, proposal.Description, proposal.Type)

			msg, err := types.NewMsgSubmitProposal(content, clientCtx.GetFromAddress())
			if err != nil {
				return fmt.Errorf("invalid message: %w", err)
			}

			if err = msg.ValidateBasic(); err != nil {
				return fmt.Errorf("message validation failed: %w", err)
			}

			return tx.GenerateOrBroadcastTxCLI(clientCtx, cmd.Flags(), msg)
		},
	}

	cmd.Flags().String(FlagTitle, "", "The proposal title")
	cmd.Flags().String(FlagDescription, "", "The proposal description")
	cmd.Flags().String(FlagProposalType, "", "The proposal Type")
	cmd.Flags().String(FlagProposal, "", "Proposal file path (if this path is given, other proposal flags are ignored)")
	flags.AddTxFlagsToCmd(cmd)

	return cmd
}
