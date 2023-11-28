package main

import (
	"bufio"
	"encoding/json"
	"fmt"
	"log"
	"os"
	"os/exec"
	"strconv"
	"strings"
	"sync"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v4/modules/core/02-client/types"
	consumertypes "github.com/cosmos/interchain-security/v2/x/ccv/consumer/types"

	"github.com/cosmos/interchain-security/v2/x/ccv/provider/client"
	"github.com/cosmos/interchain-security/v2/x/ccv/provider/types"
	"github.com/tidwall/gjson"
)

type SendTokensAction struct {
	chain  chainID
	from   validatorID
	to     validatorID
	amount uint
}

const done = "done!!!!!!!!"

func (tr TestRun) sendTokens(
	action SendTokensAction,
	verbose bool,
) {
	binaryName := tr.chainConfigs[action.chain].binaryName
	broadcastMode := "block"
	// TODO: Hack to make compatiblity test work. Don't commit this !!!!
	if binaryName == "interchain-security-cd" && tr.consumerVersion != "" {
		broadcastMode = "sync"
	}
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, binaryName,

		"tx", "bank", "send",
		tr.validatorConfigs[action.from].delAddress,
		tr.validatorConfigs[action.to].delAddress,
		fmt.Sprint(action.amount)+`stake`,

		`--chain-id`, string(tr.chainConfigs[action.chain].chainId),
		`--home`, tr.getValidatorHome(action.chain, action.from),
		`--node`, tr.getValidatorNode(action.chain, action.from),
		`--keyring-backend`, `test`,
		`-b`, broadcastMode,
		`-y`,
	)
	if verbose {
		fmt.Println("sendTokens cmd:", cmd.String())
	}
	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
	if broadcastMode == "sync" {
		time.Sleep(8 * time.Second)
	}
}

type StartChainAction struct {
	chain      chainID
	validators []StartChainValidator
	// Genesis changes specific to this action, appended to genesis changes defined in chain config
	genesisChanges string
	isConsumer     bool
}

type StartChainValidator struct {
	id         validatorID
	allocation uint
	stake      uint
}

func (tr TestRun) startChain(
	action StartChainAction,
	verbose bool,
) {
	chainConfig := tr.chainConfigs[action.chain]
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

	var cometmockArg string
	if tr.useCometmock {
		cometmockArg = "true"
	} else {
		cometmockArg = "false"
	}

	startChainScript := "/testnet-scripts/start-chain.sh"
	if tr.providerVersion != "" && chainConfig.binaryName == "interchain-security-pd" {
		log.Printf("Using start-chain script for provider version '%s'", tr.providerVersion)
		startChainScript = fmt.Sprintf("/provider-%s/testnet-scripts/start-chain.sh", tr.providerVersion)
	}
	if tr.consumerVersion != "" && chainConfig.binaryName != "interchain-security-pd" {
		log.Printf("Using start-chain script for consumer version '%s'", tr.consumerVersion)
		startChainScript = fmt.Sprintf("/consumer-%s/testnet-scripts/start-chain.sh", tr.consumerVersion)
	}
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, "/bin/bash",
		startChainScript, chainConfig.binaryName, string(vals),
		string(chainConfig.chainId), chainConfig.ipPrefix, genesisChanges,
		fmt.Sprint(action.isConsumer),
		// override config/config.toml for each node on chain
		// usually timeout_commit and peer_gossip_sleep_duration are changed to vary the test run duration
		// lower timeout_commit means the blocks are produced faster making the test run shorter
		// with short timeout_commit (eg. timeout_commit = 1s) some nodes may miss blocks causing the test run to fail
		tr.tendermintConfigOverride,
		cometmockArg,
	)

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
			fmt.Println("startChain: " + out)
		}
		if out == done {
			break
		}
	}
	if err := scanner.Err(); err != nil {
		log.Fatal(err)
	}

	tr.addChainToRelayer(addChainToRelayerAction{
		chain:     action.chain,
		validator: action.validators[0].id,
		consumer:  action.isConsumer,
	}, verbose)
}

type submitTextProposalAction struct {
	chain       chainID
	from        validatorID
	deposit     uint
	propType    string
	title       string
	description string
}

func (tr TestRun) submitTextProposal(
	action submitTextProposalAction,
	verbose bool,
) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[action.chain].binaryName,

		"tx", "gov", "submit-proposal",
		`--title`, action.title,
		`--description`, action.description,
		`--type`, action.propType,
		`--deposit`, fmt.Sprint(action.deposit)+`stake`,

		`--from`, `validator`+fmt.Sprint(action.from),
		`--chain-id`, string(tr.chainConfigs[action.chain].chainId),
		`--home`, tr.getValidatorHome(action.chain, action.from),
		`--node`, tr.getValidatorNode(action.chain, action.from),
		`--keyring-backend`, `test`,
		`-b`, `block`,
		`-y`,
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

type submitConsumerAdditionProposalAction struct {
	preCCV              bool
	chain               chainID
	from                validatorID
	deposit             uint
	consumerChain       chainID
	spawnTime           uint
	initialHeight       clienttypes.Height
	distributionChannel string
}

func (tr TestRun) submitConsumerAdditionProposal(
	action submitConsumerAdditionProposalAction,
	verbose bool,
) {
	spawnTime := tr.containerConfig.now.Add(time.Duration(action.spawnTime) * time.Millisecond)
	params := consumertypes.DefaultParams()
	prop := client.ConsumerAdditionProposalJSON{
		Title:                             "Propose the addition of a new chain",
		Description:                       "Gonna be a great chain",
		ChainId:                           string(tr.chainConfigs[action.consumerChain].chainId),
		InitialHeight:                     action.initialHeight,
		GenesisHash:                       []byte("gen_hash"),
		BinaryHash:                        []byte("bin_hash"),
		SpawnTime:                         spawnTime,
		ConsumerRedistributionFraction:    params.ConsumerRedistributionFraction,
		BlocksPerDistributionTransmission: params.BlocksPerDistributionTransmission,
		HistoricalEntries:                 params.HistoricalEntries,
		CcvTimeoutPeriod:                  params.CcvTimeoutPeriod,
		TransferTimeoutPeriod:             params.TransferTimeoutPeriod,
		UnbondingPeriod:                   params.UnbondingPeriod,
		Deposit:                           fmt.Sprint(action.deposit) + `stake`,
		DistributionTransmissionChannel:   action.distributionChannel,
	}

	bz, err := json.Marshal(prop)
	if err != nil {
		log.Fatal(err)
	}

	jsonStr := string(bz)
	if strings.Contains(jsonStr, "'") {
		log.Fatal("prop json contains single quote")
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err = exec.Command("docker", "exec", tr.containerConfig.instanceName,
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, jsonStr, "/temp-proposal.json")).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err = exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[action.chain].binaryName,

		"tx", "gov", "submit-proposal", "consumer-addition",
		"/temp-proposal.json",

		`--from`, `validator`+fmt.Sprint(action.from),
		`--chain-id`, string(tr.chainConfigs[action.chain].chainId),
		`--home`, tr.getValidatorHome(action.chain, action.from),
		`--gas`, `900000`,
		`--node`, tr.getValidatorNode(action.chain, action.from),
		`--keyring-backend`, `test`,
		`-b`, `block`,
		`-y`,
	).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	tr.waitBlocks(action.chain, 1, 5*time.Second)
}

type submitConsumerRemovalProposalAction struct {
	chain          chainID
	from           validatorID
	deposit        uint
	consumerChain  chainID
	stopTimeOffset time.Duration // offset from time.Now()
}

func (tr TestRun) submitConsumerRemovalProposal(
	action submitConsumerRemovalProposalAction,
	verbose bool,
) {
	stopTime := tr.containerConfig.now.Add(action.stopTimeOffset)
	prop := client.ConsumerRemovalProposalJSON{
		Title:       fmt.Sprintf("Stop the %v chain", action.consumerChain),
		Description: "It was a great chain",
		ChainId:     string(tr.chainConfigs[action.consumerChain].chainId),
		StopTime:    stopTime,
		Deposit:     fmt.Sprint(action.deposit) + `stake`,
	}

	bz, err := json.Marshal(prop)
	if err != nil {
		log.Fatal(err)
	}

	jsonStr := string(bz)
	if strings.Contains(jsonStr, "'") {
		log.Fatal("prop json contains single quote")
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err = exec.Command("docker", "exec", tr.containerConfig.instanceName,
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, jsonStr, "/temp-proposal.json")).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err = exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[action.chain].binaryName,

		"tx", "gov", "submit-proposal", "consumer-removal",
		"/temp-proposal.json",

		`--from`, `validator`+fmt.Sprint(action.from),
		`--chain-id`, string(tr.chainConfigs[action.chain].chainId),
		`--home`, tr.getValidatorHome(action.chain, action.from),
		`--node`, tr.getValidatorNode(action.chain, action.from),
		`--gas`, `auto`,
		`-b`, `block`,
		`--keyring-backend`, `test`,
		`-y`,
	).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

type submitParamChangeProposalAction struct {
	chain    chainID
	from     validatorID
	deposit  uint
	subspace string
	key      string
	value    interface{}
}

type paramChangeProposalJSON struct {
	Title       string            `json:"title"`
	Description string            `json:"description"`
	Changes     []paramChangeJSON `json:"changes"`
	Deposit     string            `json:"deposit"`
}

type paramChangeJSON struct {
	Subspace string      `json:"subspace"`
	Key      string      `json:"key"`
	Value    interface{} `json:"value"`
}

func (tr TestRun) submitParamChangeProposal(
	action submitParamChangeProposalAction,
	verbose bool,
) {
	prop := paramChangeProposalJSON{
		Title:       "Param change",
		Description: "Changing module params",
		Changes:     []paramChangeJSON{{Subspace: action.subspace, Key: action.key, Value: action.value}},
		Deposit:     fmt.Sprint(action.deposit) + `stake`,
	}

	bz, err := json.Marshal(prop)
	if err != nil {
		log.Fatal(err)
	}

	jsonStr := string(bz)
	if strings.Contains(jsonStr, "'") {
		log.Fatal("prop json contains single quote")
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err = exec.Command("docker", "exec", tr.containerConfig.instanceName,
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, jsonStr, "/params-proposal.json")).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err = exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[action.chain].binaryName,

		"tx", "gov", "submit-proposal", "param-change",
		"/params-proposal.json",

		`--from`, `validator`+fmt.Sprint(action.from),
		`--chain-id`, string(tr.chainConfigs[action.chain].chainId),
		`--home`, tr.getValidatorHome(action.chain, action.from),
		`--node`, tr.getValidatorNode(action.chain, action.from),
		`--gas`, "900000",
		`--keyring-backend`, `test`,
		`-b`, `block`,
		`-y`,
	).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

type voteGovProposalAction struct {
	chain      chainID
	from       []validatorID
	vote       []string
	propNumber uint
}

func (tr TestRun) voteGovProposal(
	action voteGovProposalAction,
	verbose bool,
) {
	var wg sync.WaitGroup
	for i, val := range action.from {
		wg.Add(1)
		vote := action.vote[i]
		go func(val validatorID, vote string) {
			defer wg.Done()
			//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
			bz, err := exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[action.chain].binaryName,

				"tx", "gov", "vote",
				fmt.Sprint(action.propNumber), vote,

				`--from`, `validator`+fmt.Sprint(val),
				`--chain-id`, string(tr.chainConfigs[action.chain].chainId),
				`--home`, tr.getValidatorHome(action.chain, val),
				`--node`, tr.getValidatorNode(action.chain, val),
				`--keyring-backend`, `test`,
				`--gas`, "900000",
				`-b`, `block`,
				`-y`,
			).CombinedOutput()
			if err != nil {
				log.Fatal(err, "\n", string(bz))
			}
		}(val, vote)
	}

	wg.Wait()
	time.Sleep(time.Duration(tr.chainConfigs[action.chain].votingWaitTime) * time.Second)
	tr.waitBlocks(action.chain, 1, 5*time.Second)
}

type startConsumerChainAction struct {
	consumerChain  chainID
	providerChain  chainID
	validators     []StartChainValidator
	genesisChanges string
}

func (tr TestRun) startConsumerChain(
	action startConsumerChainAction,
	verbose bool,
) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[action.providerChain].binaryName,

		"query", "provider", "consumer-genesis",
		string(tr.chainConfigs[action.consumerChain].chainId),

		`--node`, tr.getQueryNode(action.providerChain),
		`-o`, `json`,
	)

	if verbose {
		log.Println("startConsumerChain cmd: ", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	if tr.consumerVersion != "" {
		log.Printf("Transforming consumer genesis for a newer version: %s\n", tr.consumerVersion)
		log.Printf("Original ccv genesis: %s\n", string(bz))

		file, err := os.Create("consumer_genesis.json")
		if err != nil {
			panic(fmt.Sprintf("failed writing ccv consumer file : %v", err))
		}
		os.WriteFile(file.Name(), bz, 0644)
		cmd := exec.Command("docker", "cp", file.Name(), fmt.Sprintf("%s:/tmp/%s", tr.containerConfig.instanceName, file.Name()))
		bz, err = cmd.CombinedOutput()
		if err != nil {
			log.Fatal(err, "\n", string(bz))
		}
		cmd = exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[action.consumerChain].binaryName,
			"genesis", "transform", fmt.Sprintf("/tmp/%s", file.Name()))
		bz, err = cmd.CombinedOutput()
		if err != nil {
			log.Fatal(err, "CCV consumer genesis transformation failed: %s", string(bz))
		}
		/* 		new := strings.Replace(string(bz), "\"retry_delay_period\":\"0s\"", "\"retry_delay_period\": \"1000s\"", -1)
		   		bz = []byte(new)
		*/
		log.Printf("Transformed genesis is: %s", string(bz))
	}

	consumerGenesis := ".app_state.ccvconsumer = " + string(bz)
	consumerGenesisChanges := tr.chainConfigs[action.consumerChain].genesisChanges
	if consumerGenesisChanges != "" {
		consumerGenesis = consumerGenesis + " | " + consumerGenesisChanges + " | " + action.genesisChanges
	}

	tr.startChain(StartChainAction{
		chain:          action.consumerChain,
		validators:     action.validators,
		genesisChanges: consumerGenesis,
		isConsumer:     true,
	}, verbose)
}

type ChangeoverChainAction struct {
	sovereignChain chainID
	providerChain  chainID
	validators     []StartChainValidator
	genesisChanges string
}

func (tr TestRun) changeoverChain(
	action ChangeoverChainAction,
	verbose bool,
) {
	// sleep until the consumer chain genesis is ready on consumer
	time.Sleep(5 * time.Second)
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[action.providerChain].binaryName,

		"query", "provider", "consumer-genesis",
		string(tr.chainConfigs[action.sovereignChain].chainId),

		`--node`, tr.getQueryNode(action.providerChain),
		`-o`, `json`,
	)

	if verbose {
		log.Println("changeoverChain cmd: ", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	consumerGenesis := ".app_state.ccvconsumer = " + string(bz)
	consumerGenesisChanges := tr.chainConfigs[action.sovereignChain].genesisChanges
	if consumerGenesisChanges != "" {
		consumerGenesis = consumerGenesis + " | " + consumerGenesisChanges + " | " + action.genesisChanges
	}

	tr.startChangeover(ChangeoverChainAction{
		validators:     action.validators,
		genesisChanges: consumerGenesis,
	}, verbose)
}

func (tr TestRun) startChangeover(
	action ChangeoverChainAction,
	verbose bool,
) {
	chainConfig := tr.chainConfigs[chainID("sover")]
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
		"/testnet-scripts/start-changeover.sh", chainConfig.upgradeBinary, string(vals),
		"sover", chainConfig.ipPrefix, genesisChanges,
		tr.tendermintConfigOverride,
	)

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
			fmt.Println("startChangeover: " + out)
		}
		if out == done {
			break
		}
	}
	if err := scanner.Err(); err != nil {
		log.Fatal("startChangeover died", err)
	}
}

type addChainToRelayerAction struct {
	chain     chainID
	validator validatorID
	consumer  bool
}

const hermesChainConfigTemplate = `

[[chains]]
account_prefix = "cosmos"
clock_drift = "5s"
gas_multiplier = 1.1
grpc_addr = "%s"
id = "%s"
key_name = "%s"
max_gas = 20000000
rpc_addr = "%s"
rpc_timeout = "10s"
store_prefix = "ibc"
trusting_period = "14days"
event_source = { mode = "push", url = "%s", batch_delay = "50ms" }
ccv_consumer_chain = %v

[chains.gas_price]
	denom = "stake"
	price = 0.000

[chains.trust_threshold]
	denominator = "3"
	numerator = "1"
`

// Set up the config for a new chain for gorelayer.
// This config is added to the container as a file.
// We then add the chain to the relayer, using this config as the chain config with `rly chains add --file`
// This is functionally similar to the config used by Hermes for chains, e.g. gas is free.
const gorelayerChainConfigTemplate = `
{
	"type": "cosmos",
	"value": {
		"key": "default",
		"chain-id": "%s",
		"rpc-addr": "%s",
		"account-prefix": "cosmos",
		"keyring-backend": "test",
		"gas-adjustment": 1.2,
		"gas-prices": "0.00stake",
		"debug": true,
		"timeout": "20s",
		"output-format": "json",
		"sign-mode": "direct"
	}
}`

func (tr TestRun) addChainToRelayer(
	action addChainToRelayerAction,
	verbose bool,
) {
	if !tr.useGorelayer {
		tr.addChainToHermes(action, verbose)
	} else {
		tr.addChainToGorelayer(action, verbose)
	}
}

func (tr TestRun) addChainToGorelayer(
	action addChainToRelayerAction,
	verbose bool,
) {
	queryNodeIP := tr.getQueryNodeIP(action.chain)
	chainId := tr.chainConfigs[action.chain].chainId
	rpcAddr := "http://" + queryNodeIP + ":26658"

	chainConfig := fmt.Sprintf(gorelayerChainConfigTemplate,
		chainId,
		rpcAddr,
	)

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", tr.containerConfig.instanceName, "rly", "config", "init").CombinedOutput()
	if err != nil && !strings.Contains(string(bz), "config already exists") {
		log.Fatal(err, "\n", string(bz))
	}

	chainConfigFileName := fmt.Sprintf("/root/%s_config.json", chainId)

	bashCommand := fmt.Sprintf(`echo '%s' >> %s`, chainConfig, chainConfigFileName)
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err = exec.Command("docker", "exec", tr.containerConfig.instanceName, "bash", "-c",
		bashCommand).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	addChainCommand := exec.Command("docker", "exec", tr.containerConfig.instanceName, "rly", "chains", "add", "--file", chainConfigFileName, string(chainId))
	executeCommand(addChainCommand, "add chain")

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	keyRestoreCommand := exec.Command("docker", "exec", tr.containerConfig.instanceName, "rly", "keys", "restore", string(chainId), "default", tr.validatorConfigs[action.validator].mnemonic)
	executeCommand(keyRestoreCommand, "restore keys")
}

func (tr TestRun) addChainToHermes(
	action addChainToRelayerAction,
	verbose bool,
) {
	queryNodeIP := tr.getQueryNodeIP(action.chain)
	chainId := tr.chainConfigs[action.chain].chainId
	keyName := "query"
	rpcAddr := "http://" + queryNodeIP + ":26658"
	grpcAddr := "tcp://" + queryNodeIP + ":9091"
	wsAddr := "ws://" + queryNodeIP + ":26658/websocket"

	chainConfig := fmt.Sprintf(hermesChainConfigTemplate,
		grpcAddr,
		chainId,
		keyName,
		rpcAddr,
		wsAddr,
		action.consumer,
	)

	bashCommand := fmt.Sprintf(`echo '%s' >> %s`, chainConfig, "/root/.hermes/config.toml")

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", tr.containerConfig.instanceName, "bash", "-c",
		bashCommand,
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// Save mnemonic to file within container
	var mnemonic string
	if tr.validatorConfigs[action.validator].useConsumerKey && action.consumer {
		mnemonic = tr.validatorConfigs[action.validator].consumerMnemonic
	} else {
		mnemonic = tr.validatorConfigs[action.validator].mnemonic
	}

	saveMnemonicCommand := fmt.Sprintf(`echo '%s' > %s`, mnemonic, "/root/.hermes/mnemonic.txt")
	fmt.Println("Add to hermes", action.validator)
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err = exec.Command("docker", "exec", tr.containerConfig.instanceName, "bash", "-c",
		saveMnemonicCommand,
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err = exec.Command("docker", "exec", tr.containerConfig.instanceName, "hermes",
		"keys", "add",
		"--chain", string(tr.chainConfigs[action.chain].chainId),
		"--mnemonic-file", "/root/.hermes/mnemonic.txt",
	).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

// This config file is used by gorelayer to create a path between chains.
// Since the tests assume we use a certain client-id for certain paths,
// in the config we specify the client id, e.g. 07-tendermint-5.
// The src-channel-filter is empty because we want to relay all channels.
const gorelayerPathConfigTemplate = `{
    "src": {
        "chain-id": "%s",
        "client-id": "07-tendermint-%v"
    },
    "dst": {
        "chain-id": "%s",
        "client-id": "07-tendermint-%v"
    },
    "src-channel-filter": {
        "rule": "",
        "channel-list": []
    }
}
`

type addIbcConnectionAction struct {
	chainA  chainID
	chainB  chainID
	clientA uint
	clientB uint
}

func (tr TestRun) addIbcConnection(
	action addIbcConnectionAction,
	verbose bool,
) {
	if !tr.useGorelayer {
		tr.addIbcConnectionHermes(action, verbose)
	} else {
		tr.addIbcConnectionGorelayer(action, verbose)
	}
}

func (tr TestRun) addIbcConnectionGorelayer(
	action addIbcConnectionAction,
	verbose bool,
) {
	pathName := tr.GetPathNameForGorelayer(action.chainA, action.chainB)

	pathConfig := fmt.Sprintf(gorelayerPathConfigTemplate, action.chainA, action.clientA, action.chainB, action.clientB)

	pathConfigFileName := fmt.Sprintf("/root/%s_config.json", pathName)

	bashCommand := fmt.Sprintf(`echo '%s' >> %s`, pathConfig, pathConfigFileName)
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	pathConfigCommand := exec.Command("docker", "exec", tr.containerConfig.instanceName, "bash", "-c",
		bashCommand)
	executeCommand(pathConfigCommand, "add path config")

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	newPathCommand := exec.Command("docker", "exec", tr.containerConfig.instanceName, "rly",
		"paths", "add",
		string(tr.chainConfigs[action.chainA].chainId),
		string(tr.chainConfigs[action.chainB].chainId),
		pathName,
		"--file", pathConfigFileName,
	)

	executeCommand(newPathCommand, "new path")

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	newClientsCommand := exec.Command("docker", "exec", tr.containerConfig.instanceName, "rly",
		"transact", "clients",
		pathName,
	)

	executeCommand(newClientsCommand, "new clients")

	tr.waitBlocks(action.chainA, 1, 10*time.Second)
	tr.waitBlocks(action.chainB, 1, 10*time.Second)

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	newConnectionCommand := exec.Command("docker", "exec", tr.containerConfig.instanceName, "rly",
		"transact", "connection",
		pathName,
	)

	executeCommand(newConnectionCommand, "new connection")

	tr.waitBlocks(action.chainA, 1, 10*time.Second)
	tr.waitBlocks(action.chainB, 1, 10*time.Second)
}

type createIbcClientsAction struct {
	chainA chainID
	chainB chainID
}

// if clients are not provided hermes will first
// create new clients and then a new connection
// otherwise, it would use client provided as CLI argument (-a-client)
func (tr TestRun) createIbcClientsHermes(
	action createIbcClientsAction,
	verbose bool,
) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, "hermes",
		"create", "connection",
		"--a-chain", string(tr.chainConfigs[action.chainA].chainId),
		"--b-chain", string(tr.chainConfigs[action.chainB].chainId),
	)

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
			fmt.Println("createIbcClientsHermes: " + out)
		}
		if out == done {
			break
		}
	}
	if err := scanner.Err(); err != nil {
		log.Fatal(err)
	}
}

func (tr TestRun) addIbcConnectionHermes(
	action addIbcConnectionAction,
	verbose bool,
) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, "hermes",
		"create", "connection",
		"--a-chain", string(tr.chainConfigs[action.chainA].chainId),
		"--a-client", "07-tendermint-"+fmt.Sprint(action.clientA),
		"--b-client", "07-tendermint-"+fmt.Sprint(action.clientB),
	)

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
			fmt.Println("addIbcConnection: " + out)
		}
		if out == done {
			break
		}
	}
	if err := scanner.Err(); err != nil {
		log.Fatal(err)
	}
}

type addIbcChannelAction struct {
	chainA      chainID
	chainB      chainID
	connectionA uint
	portA       string
	portB       string
	order       string
	version     string
}

type startRelayerAction struct{}

func (tr TestRun) startRelayer(
	action startRelayerAction,
	verbose bool,
) {
	if tr.useGorelayer {
		tr.startGorelayer(action, verbose)
	} else {
		tr.startHermes(action, verbose)
	}
}

func (tr TestRun) startGorelayer(
	action startRelayerAction,
	verbose bool,
) {
	// gorelayer start is running in detached mode
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", "-d", tr.containerConfig.instanceName, "rly",
		"start",
	)

	if err := cmd.Start(); err != nil {
		log.Fatal(err)
	}

	if verbose {
		fmt.Println("started gorelayer")
	}
}

func (tr TestRun) startHermes(
	action startRelayerAction,
	verbose bool,
) {
	// hermes start is running in detached mode
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", "-d", tr.containerConfig.instanceName, "hermes",
		"start",
	)

	if err := cmd.Start(); err != nil {
		log.Fatal(err)
	}

	if verbose {
		fmt.Println("started Hermes")
	}
}

func (tr TestRun) addIbcChannel(
	action addIbcChannelAction,
	verbose bool,
) {
	if tr.useGorelayer {
		tr.addIbcChannelGorelayer(action, verbose)
	} else {
		tr.addIbcChannelHermes(action, verbose)
	}
}

func (tr TestRun) addIbcChannelGorelayer(
	action addIbcChannelAction,
	verbose bool,
) {
	pathName := tr.GetPathNameForGorelayer(action.chainA, action.chainB)
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, "rly",
		"transact", "channel",
		pathName,
		"--src-port", action.portA,
		"--dst-port", action.portB,
		"--version", tr.containerConfig.ccvVersion,
		"--order", action.order,
		"--debug",
	)
	executeCommand(cmd, "addChannel")
}

func (tr TestRun) addIbcChannelHermes(
	action addIbcChannelAction,
	verbose bool,
) {
	// if version is not specified, use the default version when creating ccv connections
	// otherwise, use the provided version schema (usually it is ICS20-1 for IBC transfer)
	chanVersion := action.version
	if chanVersion == "" {
		chanVersion = tr.containerConfig.ccvVersion
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, "hermes",
		"create", "channel",
		"--a-chain", string(tr.chainConfigs[action.chainA].chainId),
		"--a-connection", "connection-"+fmt.Sprint(action.connectionA),
		"--a-port", action.portA,
		"--b-port", action.portB,
		"--channel-version", chanVersion,
		"--order", action.order,
	)

	if verbose {
		fmt.Println("addIbcChannel cmd:", cmd.String())
	}

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
			fmt.Println("addIBCChannel: " + out)
		}
		if out == done {
			break
		}
	}
	if err := scanner.Err(); err != nil {
		log.Fatal(err)
	}
}

type transferChannelCompleteAction struct {
	chainA      chainID
	chainB      chainID
	connectionA uint
	portA       string
	portB       string
	order       string
	channelA    uint
	channelB    uint
}

func (tr TestRun) transferChannelComplete(
	action transferChannelCompleteAction,
	verbose bool,
) {
	if tr.useGorelayer {
		log.Fatal("transferChannelComplete is not implemented for rly")
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with chanOpenTryCmd arguments.
	chanOpenTryCmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, "hermes",
		"tx", "chan-open-try",
		"--dst-chain", string(tr.chainConfigs[action.chainB].chainId),
		"--src-chain", string(tr.chainConfigs[action.chainA].chainId),
		"--dst-connection", "connection-"+fmt.Sprint(action.connectionA),
		"--dst-port", action.portB,
		"--src-port", action.portA,
		"--src-channel", "channel-"+fmt.Sprint(action.channelA),
	)
	executeCommand(chanOpenTryCmd, "transferChanOpenTry")

	//#nosec G204 -- Bypass linter warning for spawning subprocess with chanOpenAckCmd arguments.
	chanOpenAckCmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, "hermes",
		"tx", "chan-open-ack",
		"--dst-chain", string(tr.chainConfigs[action.chainA].chainId),
		"--src-chain", string(tr.chainConfigs[action.chainB].chainId),
		"--dst-connection", "connection-"+fmt.Sprint(action.connectionA),
		"--dst-port", action.portA,
		"--src-port", action.portB,
		"--dst-channel", "channel-"+fmt.Sprint(action.channelA),
		"--src-channel", "channel-"+fmt.Sprint(action.channelB),
	)
	executeCommand(chanOpenAckCmd, "transferChanOpenAck")

	//#nosec G204 -- Bypass linter warning for spawning subprocess with chanOpenConfirmCmd arguments.
	chanOpenConfirmCmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, "hermes",
		"tx", "chan-open-confirm",
		"--dst-chain", string(tr.chainConfigs[action.chainB].chainId),
		"--src-chain", string(tr.chainConfigs[action.chainA].chainId),
		"--dst-connection", "connection-"+fmt.Sprint(action.connectionA),
		"--dst-port", action.portB,
		"--src-port", action.portA,
		"--dst-channel", "channel-"+fmt.Sprint(action.channelB),
		"--src-channel", "channel-"+fmt.Sprint(action.channelA),
	)
	executeCommand(chanOpenConfirmCmd, "transferChanOpenConfirm")
}

func executeCommand(cmd *exec.Cmd, cmdName string) {
	if verbose != nil && *verbose {
		fmt.Println(cmdName+" cmd:", cmd.String())
	}

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
		if verbose != nil && *verbose {
			fmt.Println(cmdName + ": " + out)
		}
	}
	if err := scanner.Err(); err != nil {
		log.Fatal(err)
	}
}

type relayPacketsAction struct {
	chainA  chainID
	chainB  chainID
	port    string
	channel uint
}

func (tr TestRun) relayPackets(
	action relayPacketsAction,
	verbose bool,
) {
	if tr.useGorelayer {
		tr.relayPacketsGorelayer(action, verbose)
	} else {
		tr.relayPacketsHermes(action, verbose)
	}
}

func (tr TestRun) relayPacketsGorelayer(
	action relayPacketsAction,
	verbose bool,
) {
	pathName := tr.GetPathNameForGorelayer(action.chainA, action.chainB)

	// rly transact relay-packets [path-name] --channel [channel-id]
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, "rly", "transact", "flush",
		pathName,
		"channel-"+fmt.Sprint(action.channel),
	)
	if verbose {
		log.Println("relayPackets cmd:", cmd.String())
	}
	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

func (tr TestRun) relayPacketsHermes(
	action relayPacketsAction,
	verbose bool,
) {
	// hermes clear packets ibc0 transfer channel-13
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, "hermes", "clear", "packets",
		"--chain", string(tr.chainConfigs[action.chainA].chainId),
		"--port", action.port,
		"--channel", "channel-"+fmt.Sprint(action.channel),
	)
	if verbose {
		log.Println("relayPackets cmd:", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	tr.waitBlocks(action.chainA, 1, 30*time.Second)
}

type relayRewardPacketsToProviderAction struct {
	consumerChain chainID
	providerChain chainID
	port          string
	channel       uint
}

func (tr TestRun) relayRewardPacketsToProvider(
	action relayRewardPacketsToProviderAction,
	verbose bool,
) {
	blockPerDistribution, _ := strconv.ParseUint(strings.Trim(tr.getParam(action.consumerChain, Param{Subspace: "ccvconsumer", Key: "BlocksPerDistributionTransmission"}), "\""), 10, 64)
	currentBlock := uint64(tr.getBlockHeight(action.consumerChain))
	if currentBlock <= blockPerDistribution {
		tr.waitBlocks(action.consumerChain, uint(blockPerDistribution-currentBlock+1), 60*time.Second)
	}

	tr.relayPackets(relayPacketsAction{chainA: action.consumerChain, chainB: action.providerChain, port: action.port, channel: action.channel}, verbose)
	tr.waitBlocks(action.providerChain, 1, 10*time.Second)
}

type delegateTokensAction struct {
	chain  chainID
	from   validatorID
	to     validatorID
	amount uint
}

func (tr TestRun) delegateTokens(
	action delegateTokensAction,
	verbose bool,
) {
	toValCfg := tr.validatorConfigs[action.to]
	delegateAddr := toValCfg.valoperAddress
	if action.chain != chainID("provi") && toValCfg.useConsumerKey {
		delegateAddr = toValCfg.consumerValoperAddress
	}
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[action.chain].binaryName,

		"tx", "staking", "delegate",
		delegateAddr,
		fmt.Sprint(action.amount)+`stake`,

		`--from`, `validator`+fmt.Sprint(action.from),
		`--chain-id`, string(tr.chainConfigs[action.chain].chainId),
		`--home`, tr.getValidatorHome(action.chain, action.from),
		`--node`, tr.getValidatorNode(action.chain, action.from),
		`--keyring-backend`, `test`,
		`-b`, `block`,
		`-y`,
	)
	if verbose {
		fmt.Println("delegate cmd:", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	tr.waitBlocks(action.chain, 1, 10*time.Second)
}

type unbondTokensAction struct {
	chain      chainID
	sender     validatorID
	unbondFrom validatorID
	amount     uint
}

func (tr TestRun) unbondTokens(
	action unbondTokensAction,
	verbose bool,
) {
	unbondFrom := tr.validatorConfigs[action.unbondFrom].valoperAddress
	if tr.validatorConfigs[action.unbondFrom].useConsumerKey {
		unbondFrom = tr.validatorConfigs[action.unbondFrom].consumerValoperAddress
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[action.chain].binaryName,

		"tx", "staking", "unbond",
		unbondFrom,
		fmt.Sprint(action.amount)+`stake`,

		`--from`, `validator`+fmt.Sprint(action.sender),
		`--chain-id`, string(tr.chainConfigs[action.chain].chainId),
		`--home`, tr.getValidatorHome(action.chain, action.sender),
		`--node`, tr.getValidatorNode(action.chain, action.sender),
		`--gas`, "900000",
		`--keyring-backend`, `test`,
		`-b`, `block`,
		`-y`,
	)
	if verbose {
		fmt.Println("unbond cmd:", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	tr.waitBlocks(action.chain, 1, 10*time.Second)
}

type cancelUnbondTokensAction struct {
	chain     chainID
	delegator validatorID
	validator validatorID
	amount    uint
}

func (tr TestRun) cancelUnbondTokens(
	action cancelUnbondTokensAction,
	verbose bool,
) {
	validator := tr.validatorConfigs[action.validator].valoperAddress
	if tr.validatorConfigs[action.validator].useConsumerKey {
		validator = tr.validatorConfigs[action.validator].consumerValoperAddress
	}

	// get creation-height from state
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[action.chain].binaryName,
		"q", "staking", "unbonding-delegation",
		tr.validatorConfigs[action.delegator].delAddress,
		validator,
		`--home`, tr.getValidatorHome(action.chain, action.delegator),
		`--node`, tr.getValidatorNode(action.chain, action.delegator),
		`-o`, `json`,
	)
	if verbose {
		fmt.Println("get unbonding delegations cmd:", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
	creationHeight := gjson.Get(string(bz), "entries.0.creation_height").Int()
	if creationHeight == 0 {
		log.Fatal("invalid creation height")
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd = exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[action.chain].binaryName,
		"tx", "staking", "cancel-unbond",
		validator,
		fmt.Sprint(action.amount)+`stake`,
		fmt.Sprint(creationHeight),
		`--from`, `validator`+fmt.Sprint(action.delegator),
		`--chain-id`, string(tr.chainConfigs[action.chain].chainId),
		`--home`, tr.getValidatorHome(action.chain, action.delegator),
		`--node`, tr.getValidatorNode(action.chain, action.delegator),
		`--gas`, "900000",
		`--keyring-backend`, `test`,
		`-o`, `json`,
		`-y`,
	)

	if verbose {
		fmt.Println("unbond cmd:", cmd.String())
	}

	bz, err = cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// wait for inclusion in a block -> '--broadcast-mode block' is deprecated
	tr.waitBlocks(action.chain, 2, 20*time.Second)
}

type redelegateTokensAction struct {
	chain    chainID
	src      validatorID
	dst      validatorID
	txSender validatorID
	amount   uint
}

func (tr TestRun) redelegateTokens(action redelegateTokensAction, verbose bool) {
	srcCfg := tr.validatorConfigs[action.src]
	dstCfg := tr.validatorConfigs[action.dst]

	redelegateSrc := srcCfg.valoperAddress
	if action.chain != chainID("provi") && srcCfg.useConsumerKey {
		redelegateSrc = srcCfg.consumerValoperAddress
	}

	redelegateDst := dstCfg.valoperAddress
	if action.chain != chainID("provi") && dstCfg.useConsumerKey {
		redelegateDst = dstCfg.consumerValoperAddress
	}
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec",
		tr.containerConfig.instanceName,
		tr.chainConfigs[action.chain].binaryName,

		"tx", "staking", "redelegate",
		redelegateSrc,
		redelegateDst,
		fmt.Sprint(action.amount)+`stake`,
		`--from`, `validator`+fmt.Sprint(action.txSender),
		`--chain-id`, string(tr.chainConfigs[action.chain].chainId),
		`--home`, tr.getValidatorHome(action.chain, action.txSender),
		`--node`, tr.getValidatorNode(action.chain, action.txSender),
		// Need to manually set gas limit past default (200000), since redelegate has a lot of operations
		`--gas`, "900000",
		`--keyring-backend`, `test`,
		`-b`, `block`,
		`-y`,
	)

	if verbose {
		fmt.Println("redelegate cmd:", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

type downtimeSlashAction struct {
	chain     chainID
	validator validatorID
}

func (tr TestRun) invokeDowntimeSlash(action downtimeSlashAction, verbose bool) {
	// Bring validator down
	tr.setValidatorDowntime(action.chain, action.validator, true, verbose)
	// Wait appropriate amount of blocks for validator to be slashed
	tr.waitBlocks(action.chain, 12, 2*time.Minute)
	// Bring validator back up
	tr.setValidatorDowntime(action.chain, action.validator, false, verbose)
}

// Sets validator downtime by setting the virtual ethernet interface of a node to "up" or "down"
func (tr TestRun) setValidatorDowntime(chain chainID, validator validatorID, down, verbose bool) {
	var lastArg string
	if down {
		lastArg = "down"
	} else {
		lastArg = "up"
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command(
		"docker",
		"exec",
		tr.containerConfig.instanceName,
		"ip",
		"link",
		"set",
		string(chain)+"-"+string(validator)+"-out",
		lastArg,
	)

	if verbose {
		fmt.Println("toggle downtime cmd:", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

type unjailValidatorAction struct {
	provider  chainID
	validator validatorID
}

// Sends an unjail transaction to the provider chain
func (tr TestRun) unjailValidator(action unjailValidatorAction, verbose bool) {
	// wait a block to be sure downtime_jail_duration has elapsed
	tr.waitBlocks(action.provider, 1, time.Minute)

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec",
		tr.containerConfig.instanceName,
		tr.chainConfigs[action.provider].binaryName,
		"tx", "slashing", "unjail",
		// Validator is sender here
		`--from`, `validator`+fmt.Sprint(action.validator),
		`--chain-id`, string(tr.chainConfigs[action.provider].chainId),
		`--home`, tr.getValidatorHome(action.provider, action.validator),
		`--node`, tr.getValidatorNode(action.provider, action.validator),
		`--gas`, "900000",
		`--keyring-backend`, `test`,
		`-b`, `block`,
		`-y`,
	)
	if verbose {
		fmt.Println("unjail cmd:", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// wait for 1 blocks to make sure that tx got included
	// in a block and packets committed before proceeding
	tr.waitBlocks(action.provider, 1, time.Minute)
}

type registerRepresentativeAction struct {
	chain           chainID
	representatives []validatorID
	stakes          []uint
}

func (tr TestRun) registerRepresentative(
	action registerRepresentativeAction,
	verbose bool,
) {
	var wg sync.WaitGroup
	for i, val := range action.representatives {
		wg.Add(1)
		stake := action.stakes[i]
		go func(val validatorID, stake uint) {
			defer wg.Done()

			//#nosec G204 -- Bypass linter warning for spawning subprocess with pubKeycmd arguments.
			pubKeycmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[action.chain].binaryName,
				"tendermint", "show-validator",
				`--home`, tr.getValidatorHome(action.chain, val),
			)

			bzPubKey, err := pubKeycmd.CombinedOutput()
			if err != nil {
				log.Fatal(err, "\n", string(bzPubKey))
			}

			//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
			bz, err := exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[action.chain].binaryName,
				"tx", "staking", "create-validator",
				`--amount`, fmt.Sprint(stake)+"stake",
				`--pubkey`, string(bzPubKey),
				`--moniker`, fmt.Sprint(val),
				`--commission-rate`, "0.1",
				`--commission-max-rate`, "0.2",
				`--commission-max-change-rate`, "0.01",
				`--from`, `validator`+fmt.Sprint(val),
				`--chain-id`, string(tr.chainConfigs[action.chain].chainId),
				`--home`, tr.getValidatorHome(action.chain, val),
				`--node`, tr.getValidatorNode(action.chain, val),
				`--keyring-backend`, `test`,
				`-b`, `block`,
				`-y`,
			).CombinedOutput()
			if err != nil {
				log.Fatal(err, "\n", string(bz))
			}
		}(val, stake)
	}

	wg.Wait()
}

type submitChangeRewardDenomsProposalAction struct {
	denom   string
	deposit uint
	from    validatorID
}

func (tr TestRun) submitChangeRewardDenomsProposal(action submitChangeRewardDenomsProposalAction, verbose bool) {
	providerChain := tr.chainConfigs[chainID("provi")]

	prop := client.ChangeRewardDenomsProposalJSON{
		Summary: "Change reward denoms",
		ChangeRewardDenomsProposal: types.ChangeRewardDenomsProposal{
			Title:          "Change reward denoms",
			Description:    "Change reward denoms",
			DenomsToAdd:    []string{action.denom},
			DenomsToRemove: []string{"stake"},
		},
		Deposit: fmt.Sprint(action.deposit) + `stake`,
	}

	bz, err := json.Marshal(prop)
	if err != nil {
		log.Fatal(err)
	}

	jsonStr := string(bz)
	if strings.Contains(jsonStr, "'") {
		log.Fatal("prop json contains single quote")
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err = exec.Command("docker", "exec", tr.containerConfig.instanceName,
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, jsonStr, "/change-reward-denoms-proposal.json")).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	// CHANGE REWARDS DENOM PROPOSAL
	bz, err = exec.Command("docker", "exec", tr.containerConfig.instanceName, providerChain.binaryName,
		"tx", "gov", "submit-proposal", "change-reward-denoms", "/change-reward-denoms-proposal.json",
		`--from`, `validator`+fmt.Sprint(action.from),
		`--chain-id`, string(providerChain.chainId),
		`--home`, tr.getValidatorHome(providerChain.chainId, action.from),
		`--node`, tr.getValidatorNode(providerChain.chainId, action.from),
		`--gas`, "9000000",
		`--keyring-backend`, `test`,
		`-y`,
	).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// wait for inclusion in a block -> '--broadcast-mode block' is deprecated
	tr.waitBlocks(chainID("provi"), 2, 30*time.Second)
}

// Creates an additional node on selected chain
// by copying an existing validator's home folder
//
// Steps needed to double sign:
// - copy existing validator's state and configs
// - use existing priv_validator_key.json
// - use new node_key.json (otherwise node gets rejected)
// - reset priv_validator_state.json to initial values
// - start the new node
// Double sign should be registered within couple blocks.
type doublesignSlashAction struct {
	// start another node for this validator
	validator validatorID
	chain     chainID
}

func (tr TestRun) invokeDoublesignSlash(
	action doublesignSlashAction,
	verbose bool,
) {
	chainConfig := tr.chainConfigs[action.chain]
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", tr.containerConfig.instanceName, "/bin/bash",
		"/testnet-scripts/cause-doublesign.sh", chainConfig.binaryName, string(action.validator),
		string(chainConfig.chainId), chainConfig.ipPrefix).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
	tr.waitBlocks("provi", 10, 2*time.Minute)
}

type assignConsumerPubKeyAction struct {
	chain          chainID
	validator      validatorID
	consumerPubkey string
	// reconfigureNode will change keys the node uses and restart
	reconfigureNode bool
	// executing the action should raise an error
	expectError bool
}

func (tr TestRun) assignConsumerPubKey(action assignConsumerPubKeyAction, verbose bool) {
	valCfg := tr.validatorConfigs[action.validator]

	assignKey := fmt.Sprintf(
		`%s tx provider assign-consensus-key %s '%s' --from validator%s --chain-id %s --home %s --node %s --gas 900000 --keyring-backend test -b block -y -o json`,
		tr.chainConfigs[chainID("provi")].binaryName,
		string(tr.chainConfigs[action.chain].chainId),
		action.consumerPubkey,
		action.validator,
		tr.chainConfigs[chainID("provi")].chainId,
		tr.getValidatorHome(chainID("provi"), action.validator),
		tr.getValidatorNode(chainID("provi"), action.validator),
	)
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec",
		tr.containerConfig.instanceName,
		"/bin/bash", "-c",
		assignKey,
	)

	if verbose {
		fmt.Println("assignConsumerPubKey cmd:", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	jsonStr := string(bz)
	code := gjson.Get(jsonStr, "code")
	rawLog := gjson.Get(jsonStr, "raw_log")
	if !action.expectError && code.Int() != 0 {
		log.Fatalf("unexpected error during key assignment - code: %s, output: %s", code, jsonStr)
	}

	if action.expectError {
		if code.Int() == 0 {
		} else if verbose {
			fmt.Printf("got expected error during key assignment | code: %v | log: %s\n", code, rawLog)
		}
	}

	// node was started with provider key
	// we swap the nodes's keys for consumer keys and restart it
	if action.reconfigureNode {
		//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
		configureNodeCmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, "/bin/bash",
			"/testnet-scripts/reconfigure-node.sh", tr.chainConfigs[action.chain].binaryName,
			string(action.validator), string(action.chain),
			tr.chainConfigs[action.chain].ipPrefix, valCfg.ipSuffix,
			valCfg.consumerMnemonic, valCfg.consumerPrivValidatorKey,
			valCfg.consumerNodeKey,
		)

		if verbose {
			fmt.Println("assignConsumerPubKey - reconfigure node cmd:", configureNodeCmd.String())
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
				fmt.Println("assign key - reconfigure: " + out)
			}
			if out == done {
				break
			}
		}
		if err := scanner.Err(); err != nil {
			log.Fatal(err)
		}

		// TODO: @MSalopek refactor this so test config is not changed at runtime
		// make the validator use consumer key
		valCfg.useConsumerKey = true
		tr.validatorConfigs[action.validator] = valCfg
	}

	time.Sleep(1 * time.Second)
}

// slashThrottleDequeue polls slash queue sizes until nextQueueSize is achieved
type slashThrottleDequeue struct {
	chain            chainID
	currentQueueSize int
	nextQueueSize    int
	// panic if timeout is exceeded
	timeout time.Duration
}

func (tr TestRun) waitForSlashThrottleDequeue(
	action slashThrottleDequeue,
	verbose bool,
) {
	timeout := time.Now().Add(action.timeout)
	initialGlobalQueueSize := int(tr.getGlobalSlashQueueSize())

	if initialGlobalQueueSize != action.currentQueueSize {
		panic(fmt.Sprintf("wrong initial queue size: %d - expected global queue: %d\n", initialGlobalQueueSize, action.currentQueueSize))
	}
	for {
		globalQueueSize := int(tr.getGlobalSlashQueueSize())
		chainQueueSize := int(tr.getConsumerChainPacketQueueSize(action.chain))
		if verbose {
			fmt.Printf("waiting for packed queue size to reach: %d - current: %d\n", action.nextQueueSize, globalQueueSize)
		}

		// check if global queue size is equal to chain queue size
		if globalQueueSize == chainQueueSize && globalQueueSize == action.nextQueueSize { //nolint:gocritic // this is the comparison that we want here.
			break
		}

		if time.Now().After(timeout) {
			panic(fmt.Sprintf("\n\n\nwaitForSlashThrottleDequeuemethod has timed out after: %s\n\n", action.timeout))
		}

		time.Sleep(500 * time.Millisecond)
	}
	// wair for 2 blocks to be created
	// allowing the jailing to be incorporated into voting power
	tr.waitBlocks(action.chain, 2, time.Minute)
}

func uintPointer(i uint) *uint {
	return &i
}

// GetPathNameForGorelayer returns the name of the path between two given chains used by Gorelayer.
// Since paths are bidirectional, we need either chain to be able to be provided as first or second argument
// and still return the same name, so we sort the chain names alphabetically.
func (tr TestRun) GetPathNameForGorelayer(chainA, chainB chainID) string {
	var pathName string
	if string(chainA) < string(chainB) {
		pathName = string(chainA) + "-" + string(chainB)
	} else {
		pathName = string(chainB) + "-" + string(chainA)
	}

	return pathName
}

// Run an instance of the Hermes relayer using the "evidence" command,
// which detects evidences committed to the blocks of a consumer chain.
// Each infraction detected is reported to the provider chain using
// either a SubmitConsumerDoubleVoting or a SubmitConsumerMisbehaviour message.
type startConsumerEvidenceDetectorAction struct {
	chain chainID
}

func (tr TestRun) startConsumerEvidenceDetector(
	action startConsumerEvidenceDetectorAction,
	verbose bool,
) {
	chainConfig := tr.chainConfigs[action.chain]
	// run in detached mode so it will keep running in the background
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", "-d", tr.containerConfig.instanceName,
		"hermes", "evidence", "--chain", string(chainConfig.chainId)).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
	tr.waitBlocks("provi", 10, 2*time.Minute)
}
