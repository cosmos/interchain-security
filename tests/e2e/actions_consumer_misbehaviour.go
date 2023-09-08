package main

import (
	"bufio"
	"fmt"
	"log"
	"os/exec"
	"strconv"
	"time"
)

type forkConsumerChainAction struct {
	consumerChain chainID
	providerChain chainID
	validator     validatorID
	relayerConfig string
}

func (tr TestRun) forkConsumerChain(action forkConsumerChainAction, verbose bool) {
	valCfg := tr.validatorConfigs[action.validator]

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	configureNodeCmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, "/bin/bash",
		"/testnet-scripts/fork-consumer.sh", tr.chainConfigs[action.consumerChain].binaryName,
		string(action.validator), string(action.consumerChain),
		tr.chainConfigs[action.consumerChain].ipPrefix,
		tr.chainConfigs[action.providerChain].ipPrefix,
		valCfg.mnemonic,
		action.relayerConfig,
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

type updateLightClientAction struct {
	chain         chainID
	hostChain     chainID
	relayerConfig string
	clientID      string
}

func (tr TestRun) updateLightClient(
	action updateLightClientAction,
	verbose bool,
) {
	// retrieve a trusted height of the consumer light client
	trustedHeight := tr.getTrustedHeight(action.hostChain, action.clientID, 2)

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, "hermes",
		"--config", action.relayerConfig,
		"update",
		"client",
		"--client", action.clientID,
		"--host-chain", string(action.hostChain),
		"--trusted-height", strconv.Itoa(int(trustedHeight.RevisionHeight)),
	)
	if verbose {
		log.Println("updateLightClientAction cmd:", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	tr.waitBlocks(action.hostChain, 5, 30*time.Second)
}

type assertChainIsHaltedAction struct {
	chain chainID
}

// assertChainIsHalted verifies that the chain isn't producing blocks
// by checking that the block height is still the same after 20 seconds
func (tr TestRun) assertChainIsHalted(
	action assertChainIsHaltedAction,
	verbose bool,
) {
	blockHeight := tr.getBlockHeight(action.chain)
	time.Sleep(20 * time.Second)
	if blockHeight != tr.getBlockHeight(action.chain) {
		panic(fmt.Sprintf("chain %v isn't expected to produce blocks", action.chain))
	}
	if verbose {
		log.Printf("assertChainIsHalted - chain %v was successfully halted\n", action.chain)
	}
}
