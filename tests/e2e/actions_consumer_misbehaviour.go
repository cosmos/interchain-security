package main

import (
	"bufio"
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
	valCfg := tc.testConfig.validatorConfigs[action.Validator]
	configureNodeCmd := tc.target.ExecCommand("/bin/bash",
		"/testnet-scripts/fork-consumer.sh", tc.testConfig.chainConfigs[action.ConsumerChain].BinaryName,
		string(action.Validator), string(action.ConsumerChain),
		tc.testConfig.chainConfigs[action.ConsumerChain].IpPrefix,
		tc.testConfig.chainConfigs[action.ProviderChain].IpPrefix,
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
