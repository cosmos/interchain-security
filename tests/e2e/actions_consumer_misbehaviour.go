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
}

func (tr TestRun) forkConsumerChain(action forkConsumerChainAction, verbose bool) {
	valCfg := tr.validatorConfigs[action.validator]

	fmt.Println(valCfg.mnemonic)

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	configureNodeCmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, "/bin/bash",
		"/testnet-scripts/fork-consumer.sh", tr.chainConfigs[action.consumerChain].binaryName,
		string(action.validator), string(action.consumerChain),
		tr.chainConfigs[action.consumerChain].ipPrefix,
		tr.chainConfigs[action.providerChain].ipPrefix,
		valCfg.mnemonic,
	)

	if verbose {
		fmt.Println("forkConsumerChain - reconfigure node cmd:", configureNodeCmd.String())
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
			fmt.Println("fork consumer validator : " + out)
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
	hostChain    chainID
	hermesConfig string
	clientID     string
}

func (tr TestRun) updateLightClient(
	action updateLightClientAction,
	verbose bool,
) {
	// hermes clear packets ibc0 transfer channel-13
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, "hermes",
		"--config", action.hermesConfig,
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

	tr.waitBlocks(action.hostChain, 1, 30*time.Second)
}
