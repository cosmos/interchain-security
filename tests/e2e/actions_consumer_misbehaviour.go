package main

import (
	"bufio"
	"fmt"
	"log"
	"os/exec"
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
	hostChain     chainID
	relayerConfig string
	clientID      string
}

func (tr TestRun) updateLightClient(
	action updateLightClientAction,
	verbose bool,
) {
	// hermes clear packets ibc0 transfer channel-13
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, "hermes",
		"--config", action.relayerConfig,
		"update",
		"client",
		"--client", action.clientID,
		"--host-chain", string(action.hostChain),
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

func (tr TestRun) assertChainIsHalted(
	action assertChainIsHaltedAction,
	verbose bool,
) {
	// Recover the panic if the chain doesn't produce blocks as expected
	defer func() {
		if r := recover(); r != nil {
			if verbose {
				log.Printf("assertChainIsHalted - chain %v was successfully halted\n", action.chain)
			}
		}
	}()

	// Panic if the chain still produces blocks
	tr.waitBlocks(action.chain, 1, 20*time.Second)
	panic(fmt.Sprintf("chain %v isn't expected to produce blocks", action.chain))
}
