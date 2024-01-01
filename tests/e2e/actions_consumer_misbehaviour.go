package main

import (
	"bufio"
	"log"
	"os/exec"
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

func (tc TestConfig) forkConsumerChain(action ForkConsumerChainAction, verbose bool) {
	valCfg := tc.validatorConfigs[action.Validator]

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	configureNodeCmd := exec.Command("docker", "exec", tc.containerConfig.InstanceName, "/bin/bash",
		"/testnet-scripts/fork-consumer.sh", tc.chainConfigs[action.ConsumerChain].BinaryName,
		string(action.Validator), string(action.ConsumerChain),
		tc.chainConfigs[action.ConsumerChain].IpPrefix,
		tc.chainConfigs[action.ProviderChain].IpPrefix,
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

func (tc TestConfig) updateLightClient(
	action UpdateLightClientAction,
	verbose bool,
) {
	// retrieve a trusted height of the consumer light client
	trustedHeight := tc.getTrustedHeight(action.HostChain, action.ClientID, 2)

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tc.containerConfig.InstanceName, "hermes",
		"--config", action.RelayerConfig,
		"update",
		"client",
		"--client", action.ClientID,
		"--host-chain", string(action.HostChain),
		"--trusted-height", strconv.Itoa(int(trustedHeight.RevisionHeight)),
	)
	if verbose {
		log.Println("UpdateLightClientAction cmd:", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	tc.waitBlocks(action.HostChain, 5, 30*time.Second)
}
