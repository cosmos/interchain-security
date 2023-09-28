package main

import (
	"bufio"
	"fmt"
	"log"
	"os/exec"
	"strconv"
	"time"
)

// forkConsumerChainAction forks the consumer chain by cloning of a validator node
// Note that the chain fork is running in an different network
type forkConsumerChainAction struct {
	ConsumerChain ChainID
	ProviderChain ChainID
	Validator     ValidatorID
	RelayerConfig string
}

func (tr TestRun) forkConsumerChain(action forkConsumerChainAction, verbose bool) {
	valCfg := tr.validatorConfigs[action.Validator]

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	configureNodeCmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, "/bin/bash",
		"/testnet-scripts/fork-consumer.sh", tr.chainConfigs[action.ConsumerChain].BinaryName,
		string(action.Validator), string(action.ConsumerChain),
		tr.chainConfigs[action.ConsumerChain].IpPrefix,
		tr.chainConfigs[action.ProviderChain].IpPrefix,
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

type updateLightClientAction struct {
	Chain         ChainID
	HostChain     ChainID
	RelayerConfig string
	ClientID      string
}

func (tr TestRun) updateLightClient(
	action updateLightClientAction,
	verbose bool,
) {
	// retrieve a trusted height of the consumer light client
	trustedHeight := tr.getTrustedHeight(action.HostChain, action.ClientID, 2)

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, "hermes",
		"--config", action.RelayerConfig,
		"update",
		"client",
		"--client", action.ClientID,
		"--host-chain", string(action.HostChain),
		"--trusted-height", strconv.Itoa(int(trustedHeight.RevisionHeight)),
	)
	if verbose {
		log.Println("updateLightClientAction cmd:", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	tr.waitBlocks(action.HostChain, 5, 30*time.Second)
}

type assertChainIsHaltedAction struct {
	chain ChainID
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
