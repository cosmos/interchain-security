package main

import (
	"bufio"
	"encoding/json"
	"fmt"
	"log"
	"time"
)

type StartSovereignChainAction struct {
	Chain      ChainID
	Validators []StartChainValidator
	// Genesis changes specific to this action, appended to genesis changes defined in chain config
	GenesisChanges string
}

// calls a simplified startup script (start-sovereign.sh) and runs a validator node
// upgrades are simpler with a single validator node since only one node needs to be upgraded
func (tr Chain) startSovereignChain(
	action StartSovereignChainAction,
	verbose bool,
) {
	chainConfig := tr.testConfig.chainConfigs["sover"]
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
	for _, val := range action.Validators {
		validators = append(validators, jsonValAttrs{
			Mnemonic:         tr.testConfig.validatorConfigs[val.Id].Mnemonic,
			NodeKey:          tr.testConfig.validatorConfigs[val.Id].NodeKey,
			ValId:            fmt.Sprint(val.Id),
			PrivValidatorKey: tr.testConfig.validatorConfigs[val.Id].PrivValidatorKey,
			Allocation:       fmt.Sprint(val.Allocation) + "stake",
			Stake:            fmt.Sprint(val.Stake) + "stake",
			IpSuffix:         tr.testConfig.validatorConfigs[val.Id].IpSuffix,

			ConsumerMnemonic:         tr.testConfig.validatorConfigs[val.Id].ConsumerMnemonic,
			ConsumerPrivValidatorKey: tr.testConfig.validatorConfigs[val.Id].ConsumerPrivValidatorKey,
			// if true node will be started with consumer key for each consumer chain
			StartWithConsumerKey: tr.testConfig.validatorConfigs[val.Id].UseConsumerKey,
		})
	}

	vals, err := json.Marshal(validators)
	if err != nil {
		log.Fatal(err)
	}

	// Concat genesis changes defined in chain config, with any custom genesis changes for this chain instantiation
	var genesisChanges string
	if action.GenesisChanges != "" {
		genesisChanges = chainConfig.GenesisChanges + " | " + action.GenesisChanges
	} else {
		genesisChanges = chainConfig.GenesisChanges
	}

	isConsumer := chainConfig.BinaryName != "interchain-security-pd"
	testScriptPath := tr.target.GetTestScriptPath(isConsumer, "start-sovereign.sh")
	cmd := tr.target.ExecCommand("/bin/bash", testScriptPath, chainConfig.BinaryName, string(vals),
		string(chainConfig.ChainId), chainConfig.IpPrefix, genesisChanges,
		tr.testConfig.tendermintConfigOverride)

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
	tr.addChainToRelayer(AddChainToRelayerAction{
		Chain:     action.Chain,
		Validator: action.Validators[0].Id,
	}, verbose)
}

type UpgradeProposalAction struct {
	ChainID       ChainID
	UpgradeTitle  string
	Proposer      ValidatorID
	UpgradeHeight uint64
	Expedited     bool
}

func (tr *Chain) submitUpgradeProposal(action UpgradeProposalAction, verbose bool) {

	// Get authority address
	binary := tr.testConfig.chainConfigs[ChainID("sover")].BinaryName
	cmd := tr.target.ExecCommand(binary,
		"query", "upgrade", "authority",
		"--node", tr.getValidatorNode(ChainID("sover"), action.Proposer),
		"-o", "json")
	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatalf("failed running command '%s': %v", cmd, err)
	}

	var authority struct {
		Address string `json:"address"`
	}
	err = json.Unmarshal(bz, &authority)
	if err != nil {
		log.Fatalf("Failed getting authority: err=%v, data=%s", err, string(bz))
	}

	// Upgrade Proposal Content
	metadata := "ipfs://CID"
	deposit := "10000000stake"
	summary := "my summary"
	proposalJson := fmt.Sprintf(`
{
	"messages": [
		{
			"@type": "/cosmos.upgrade.v1beta1.MsgSoftwareUpgrade",
			"authority": "%s",
			"plan": {
				"name": "sovereign-changeover",
				"height": "%d",
				"info": "my upgrade info",
				"upgraded_client_state": null
			}
		}
  	],
	"metadata": "%s",
	"title": "%s",
	"summary": "%s",
	"deposit": "%s",
	"expedited": %t
}`, authority.Address, action.UpgradeHeight, metadata, action.UpgradeTitle, summary, deposit, action.Expedited)

	//#nosec G204 -- bypass unsafe quoting warning (no production code)
	proposalPath := "/temp-proposal.json"
	bz, err = tr.target.ExecCommand(
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, proposalJson, proposalPath),
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// Submit Proposal
	cmd = tr.target.ExecCommand(binary,
		"tx", "gov", "submit-proposal", proposalPath,
		"--gas", "900000",
		"--from", "validator"+string(action.Proposer),
		"--keyring-backend", "test",
		"--chain-id", string(tr.testConfig.chainConfigs[ChainID("sover")].ChainId),
		"--home", tr.getValidatorHome(ChainID("sover"), action.Proposer),
		"--node", tr.getValidatorNode(ChainID("sover"), action.Proposer),
		"-y")

	if verbose {
		fmt.Println("Submit proposal:", cmd.String())
	}

	bz, err = cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
	if verbose {
		log.Println("Response to submit-proposal: ", string(bz))
	}

	tr.waitBlocks(action.ChainID, 1, 15*time.Second)
}

type WaitUntilBlockAction struct {
	Block uint
	Chain ChainID
}

func (tr *Chain) waitUntilBlockOnChain(action WaitUntilBlockAction) {
	fmt.Println("waitUntilBlockOnChain is waiting for block:", action.Block)
	tr.waitUntilBlock(action.Chain, action.Block, 120*time.Second)
	fmt.Println("waitUntilBlockOnChain done waiting for block:", action.Block)
}
