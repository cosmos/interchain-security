package main

import (
	"bufio"
	"encoding/json"
	"fmt"
	"log"
	"strconv"
	"time"
)

// ForkConsumerChainAction forks the consumer chain by cloning of a validator node
// Note that the chain fork is running in an different network
type ForkConsumerChainAction struct {
	ConsumerChain ChainID
	ProviderChain ChainID
	Validator     ValidatorID
	RelayerConfig string
}

func (tc Chain) forkConsumerChain(action ForkConsumerChainAction, verbose bool) {
	valCfg := tc.testConfig.ValidatorConfigs[action.Validator]
	configureNodeCmd := tc.target.ExecCommand("/bin/bash",
		"/testnet-scripts/fork-consumer.sh", tc.testConfig.ChainConfigs[action.ConsumerChain].BinaryName,
		string(action.Validator), string(action.ConsumerChain),
		tc.testConfig.ChainConfigs[action.ConsumerChain].IpPrefix,
		tc.testConfig.ChainConfigs[action.ProviderChain].IpPrefix,
		valCfg.Mnemonic,
		action.RelayerConfig,
	)

	if verbose {
		log.Println("forkConsumerChain - reconfigure node cmd:", configureNodeCmd.String())
	}

	cmdReader, err := configureNodeCmd.StdoutPipe()
	if err != nil {
		log.Fatal(err)
	}
	configureNodeCmd.Stderr = configureNodeCmd.Stdout

	if err := configureNodeCmd.Start(); err != nil {
		log.Fatal(err)
	}

	scanner := bufio.NewScanner(cmdReader)

	for scanner.Scan() {
		out := scanner.Text()
		if verbose {
			log.Println("fork consumer validator : " + out)
		}
		if out == done {
			break
		}
	}
	if err := scanner.Err(); err != nil {
		log.Fatal(err)
	}

	time.Sleep(5 * time.Second)
}

type UpdateLightClientAction struct {
	Chain         ChainID
	HostChain     ChainID
	RelayerConfig string
	ClientID      string
}

func (tc Chain) updateLightClient(
	action UpdateLightClientAction,
	verbose bool,
) {
	// retrieve a trusted height of the consumer light client
	revHeight, _ := tc.target.GetTrustedHeight(action.HostChain, action.ClientID, 2)

	cmd := tc.target.ExecCommand("hermes",
		"--config", action.RelayerConfig,
		"update",
		"client",
		"--client", action.ClientID,
		"--host-chain", string(action.HostChain),
		"--trusted-height", strconv.Itoa(int(revHeight)),
	)
	if verbose {
		log.Println("UpdateLightClientAction cmd:", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	tc.waitBlocks(action.HostChain, 8, 30*time.Second)
}

type SubmitConsumerMisbehaviourAction struct {
	FromChain ChainID
	ToChain   ChainID
	Submitter ValidatorID
	ClientID  string
}

func (tr Chain) submitConsumerMisbehaviour(action SubmitConsumerMisbehaviourAction, verbose bool) {
	consumerBinaryName := tr.testConfig.ChainConfigs[action.FromChain].BinaryName

	// retrieve a trusted height of the consumer client from the provider
	trustedHeight, _ := tr.target.GetTrustedHeight(action.ToChain, action.ClientID, 2)

	// get current block height
	currHeight := tr.target.GetBlockHeight(action.FromChain)

	tr.waitBlocks(action.FromChain, 3, 10*time.Second)

	// retrieve both IBC headers from main consumer and forked consumer,
	// which are conflicting at the current block height
	cmd := tr.target.ExecCommand(
		consumerBinaryName,
		"query", "ibc", "client", "header", "--height", strconv.Itoa(int(currHeight)),
		`--node`, tr.target.GetQueryNode(action.FromChain),
		`-o`, `json`,
	)

	if verbose {
		fmt.Println("query IBC header cmd:", cmd.String())
	}

	header, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(header))
	}

	cmd = tr.target.ExecCommand(
		consumerBinaryName,
		"query", "ibc", "client", "header", "--height", strconv.Itoa(int(currHeight)),
		`--node`, fmt.Sprintf("tcp://%s.252:26658", tr.testConfig.ChainConfigs[action.FromChain].IpPrefix),
		`-o`, `json`,
	)

	conflictingHeader, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(conflictingHeader))
	}

	// get IBC header at TrustedHeight+1 since the trusted validators hash
	// corresponds to the consensus state "NextValidatorHash" of the consumer client
	cmd = tr.target.ExecCommand(
		consumerBinaryName,
		"query", "ibc", "client", "header", "--height", strconv.Itoa(int(trustedHeight+1)),
		`--node`, fmt.Sprintf("tcp://%s.252:26658", tr.testConfig.ChainConfigs[action.FromChain].IpPrefix),
		`-o`, `json`,
	)

	if verbose {
		fmt.Println("query IBC header cmd:", cmd.String())
	}

	trustedHeader, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(trustedHeader))
	}

	// persist consumer misbehaviour in json format
	misbPath := "/misbehaviour.json"
	bz, err := tr.target.ExecCommand(
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, prepareMisb(header, conflictingHeader, trustedHeader, trustedHeight, action.ClientID), misbPath),
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	if verbose {
		fmt.Println("query IBC header cmd:", cmd.String())
	}

	// submit consumer misbehaviour
	gas := "auto"
	submitMisb := fmt.Sprintf(
		`%s tx provider submit-consumer-misbehaviour %s %s --from validator%s --chain-id %s --home %s --node %s --gas %s --keyring-backend test -y`,
		tr.testConfig.ChainConfigs[ChainID("provi")].BinaryName,
		string(tr.testConfig.ChainConfigs[action.FromChain].ConsumerId),
		misbPath,
		action.Submitter,
		tr.testConfig.ChainConfigs[ChainID("provi")].ChainId,
		tr.getValidatorHome(ChainID("provi"), action.Submitter),
		tr.getValidatorNode(ChainID("provi"), action.Submitter),
		gas,
	)

	cmd = tr.target.ExecCommand(
		"/bin/bash", "-c",
		submitMisb,
	)

	if verbose {
		fmt.Println("submit consumer misbehaviour cmd:", cmd.String())
	}

	bz, err = cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	fmt.Println(string(bz))
}

type Header struct {
	SignedHeader      json.RawMessage `json:"signed_header"`
	ValidatorSet      json.RawMessage `json:"validator_set"`
	TrustedHeight     json.RawMessage `json:"trusted_height"`
	TrustedValidators json.RawMessage `json:"trusted_validators"`
}

func prepareMisb(header1, header2, trustedHeader []byte, trustedHeight uint64, clientID string) []byte {
	misb := struct {
		ClientID string `json:"client_id"`
		Header1  Header `json:"header_1"`
		Header2  Header `json:"header_2"`
	}{
		ClientID: clientID,
		Header1:  prepareHeader(header1, trustedHeader, trustedHeight),
		Header2:  prepareHeader(header2, trustedHeader, trustedHeight),
	}

	bz, err := json.Marshal(misb)
	if err != nil {
		log.Fatal(err)
	}
	return bz
}

func prepareHeader(headerJson, trustedHeaderJson []byte, trustedHeight uint64) Header {
	header := Header{}
	err := json.Unmarshal(headerJson, &header)
	if err != nil {
		log.Fatal(err)
	}

	trustedHeader := Header{}
	err = json.Unmarshal(trustedHeaderJson, &trustedHeader)
	if err != nil {
		log.Fatal(err)
	}

	header.TrustedValidators = trustedHeader.ValidatorSet
	header.TrustedHeight = []byte(fmt.Sprintf(`{"revision_number": "0","revision_height": "%d"}`, trustedHeight))

	return header
}
