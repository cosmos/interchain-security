package main

import (
	"bufio"
	"encoding/json"
	"fmt"
	"log"
	"os/exec"
)

type StartSovereignChainAction struct {
	chain      chainID
	validators []StartChainValidator
	// Genesis changes specific to this action, appended to genesis changes defined in chain config
	genesisChanges string
}

// calls a simplified startup script (start-sovereign.sh) and runs a validator node
// upgrades are simpler with a single validator node since only one node needs to be upgraded
func (tr TestRun) startSovereignChain(
	action StartSovereignChainAction,
	verbose bool,
) {
	chainConfig := tr.chainConfigs["sover"]
	type jsonValAttrs struct {
		Mnemonic         string `json:"mnemonic"`
		Allocation       string `json:"allocation"`
		Stake            string `json:"stake"`
		ValId            string `json:"val_id"`
		PrivValidatorKey string `json:"priv_validator_key"`
		NodeKey          string `json:"node_key"`
		IpSuffix         string `json:"ip_suffix"`

		ConsumerMnemonic         string `json:"consumer_mnemonic"`
		ConsumerPrivValidatorKey string `json:"consumer_priv_validator_key"`
		StartWithConsumerKey     bool   `json:"start_with_consumer_key"`
	}

	var validators []jsonValAttrs
	for _, val := range action.validators {
		validators = append(validators, jsonValAttrs{
			Mnemonic:         tr.validatorConfigs[val.id].mnemonic,
			NodeKey:          tr.validatorConfigs[val.id].nodeKey,
			ValId:            fmt.Sprint(val.id),
			PrivValidatorKey: tr.validatorConfigs[val.id].privValidatorKey,
			Allocation:       fmt.Sprint(val.allocation) + "stake",
			Stake:            fmt.Sprint(val.stake) + "stake",
			IpSuffix:         tr.validatorConfigs[val.id].ipSuffix,

			ConsumerMnemonic:         tr.validatorConfigs[val.id].consumerMnemonic,
			ConsumerPrivValidatorKey: tr.validatorConfigs[val.id].consumerPrivValidatorKey,
			// if true node will be started with consumer key for each consumer chain
			StartWithConsumerKey: tr.validatorConfigs[val.id].useConsumerKey,
		})
	}

	vals, err := json.Marshal(validators)
	if err != nil {
		log.Fatal(err)
	}

	// Concat genesis changes defined in chain config, with any custom genesis changes for this chain instantiation
	var genesisChanges string
	if action.genesisChanges != "" {
		genesisChanges = chainConfig.genesisChanges + " | " + action.genesisChanges
	} else {
		genesisChanges = chainConfig.genesisChanges
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, "/bin/bash",
		"/testnet-scripts/start-sovereign.sh", chainConfig.binaryName, string(vals),
		string(chainConfig.chainId), chainConfig.ipPrefix, genesisChanges,
		tr.tendermintConfigOverride,
	)
	fmt.Println("CMD:", cmd.String())

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
			fmt.Println("startSovereignChain: " + out)
		}
		if out == done {
			break
		}
	}
	if err := scanner.Err(); err != nil {
		log.Fatal(err)
	}
}

type UpgradeProposalAction struct {
	chainID       chainID
	upgradeTitle  string
	proposer      validatorID
	upgradeHeight uint64
}

func (tr *TestRun) submitUpgradeProposal(action UpgradeProposalAction, verbose bool) {
	submit := fmt.Sprintf(
		`%s tx gov submit-proposal software-upgrade %s \
		--title  %s \
		--deposit 10000000stake \
		--upgrade-height %s \
		--upgrade-info "perform changeover" \
		--description "perform changeover" \
		--gas 900000 \
		--from validator%s \
		--keyring-backend test \
		--chain-id %s \
		--home %s \
		--node %s \
		-b block \
		-y`,
		tr.chainConfigs[chainID("sover")].binaryName,
		action.upgradeTitle,
		action.upgradeTitle,
		fmt.Sprint(action.upgradeHeight),
		action.proposer,
		tr.chainConfigs[chainID("sover")].chainId,
		tr.getValidatorHome(chainID("sover"), action.proposer),
		tr.getValidatorNode(chainID("sover"), action.proposer),
	)
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec",
		tr.containerConfig.instanceName,
		"/bin/bash", "-c",
		submit,
	)

	if verbose {
		fmt.Println("submitUpgradeProposal cmd:", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}
