package v4

import (
	"fmt"

	e2e "github.com/cosmos/interchain-security/v6/tests/e2e/testlib"
)

func (tr Commands) AssignConsumerPubKey(action e2e.AssignConsumerPubKeyAction, gas, home, node string, verbose bool) ([]byte, error) {

	assignKey := fmt.Sprintf(
		`%s tx provider assign-consensus-key %s '%s' --from validator%s --chain-id %s --home %s --node %s --gas %s --keyring-backend test -y -o json`,
		tr.ChainConfigs[ChainID("provi")].BinaryName,
		string(tr.ChainConfigs[action.Chain].ChainId),
		action.ConsumerPubkey,
		action.Validator,
		tr.ChainConfigs[ChainID("provi")].ChainId,
		home,
		node,
		gas,
	)

	cmd := tr.ExecCommand(
		"/bin/bash", "-c",
		assignKey,
	)

	if verbose {
		fmt.Println("assignConsumerPubKey cmd:", cmd.String())
	}

	return cmd.CombinedOutput()
}
