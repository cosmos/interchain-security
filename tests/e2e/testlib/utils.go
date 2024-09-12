package e2e

import (
	"bufio"
	"encoding/json"
	"fmt"
	"log"
	"os/exec"

	"github.com/cosmos/cosmos-sdk/codec"
	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	sdk "github.com/cosmos/cosmos-sdk/types"
)

// GovernanceProposal is used to generate content to be used for `gov submit-proposal` command
type GovernanceProposal struct {
	// Msgs defines an array of sdk.Msgs proto-JSON-encoded as Anys.
	Messages  []json.RawMessage `json:"messages,omitempty"`
	Metadata  string            `json:"metadata"`
	Deposit   string            `json:"deposit"`
	Title     string            `json:"title"`
	Summary   string            `json:"summary"`
	Expedited bool              `json:"expedited"`
}

type TxResponse struct {
	TxHash string      `json:"txhash"`
	Code   int         `json:"code"`
	RawLog string      `json:"raw_log"`
	Events []sdk.Event `json:"events"`
}

// GenerateGovProposalContent creates proposal content ready to be used by `gov submit-proposal` command
func GenerateGovProposalContent(title, summary, metadata, deposit, description string, expedited bool, msgs ...sdk.Msg) string {
	// Register the messages. Needed for correct type annotation in the resulting json
	modcodec := codec.NewProtoCodec(codectypes.NewInterfaceRegistry())
	modcodec.InterfaceRegistry().RegisterImplementations(
		(*sdk.Msg)(nil),
		msgs...,
	)

	proposal := GovernanceProposal{
		Metadata:  metadata,
		Deposit:   deposit,
		Title:     title,
		Summary:   summary,
		Expedited: expedited,
	}

	for _, msg := range msgs {
		msgJson, err := modcodec.MarshalInterfaceJSON(msg)
		if err != nil {
			panic(fmt.Errorf("failed marshalling message '%v' for gov proposal: err=%s", msg, err))
		}
		proposal.Messages = append(proposal.Messages, msgJson)
	}
	raw, err := json.MarshalIndent(proposal, "", " ")
	if err != nil {
		panic(fmt.Errorf("failed to marshal proposal: %w", err))
	}

	return string(raw)
}

func GetTxResponse(rawResponse []byte) TxResponse {
	txResponse := &TxResponse{}
	err := json.Unmarshal(rawResponse, txResponse)
	if err != nil {
		log.Fatalf("failed unmarshalling tx response: %s, json: %s",
			err.Error(), string(rawResponse))
	}
	return *txResponse
}

func ExecuteCommand(cmd *exec.Cmd, cmdName string, verbose bool) {
	if verbose {
		fmt.Println(cmdName+" cmd:", cmd.String())
	}

	cmdReader, err := cmd.StdoutPipe()
	if err != nil {
		log.Fatal(err)
	}
	cmd.Stderr = cmd.Stdout

	if err := cmd.Start(); err != nil {
		log.Fatal(err)
	}

	scanner := bufio.NewScanner(cmdReader)

	for scanner.Scan() {
		out := scanner.Text()
		if verbose {
			fmt.Println(cmdName + ": " + out)
		}
	}
	if err := scanner.Err(); err != nil {
		log.Fatal(err)
	}
}
