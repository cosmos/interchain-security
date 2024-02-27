package main

import (
	"bufio"
	"encoding/json"
	"fmt"
	"log"
	"math"
	"os"
	"os/exec"
	"strconv"
	"strings"
	"sync"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	"github.com/tidwall/gjson"

	"github.com/cosmos/interchain-security/v4/x/ccv/provider/client"
	"github.com/cosmos/interchain-security/v4/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v4/x/ccv/types"
)

type SendTokensAction struct {
	Chain  ChainID
	From   ValidatorID
	To     ValidatorID
	Amount uint
}

const done = "done!!!!!!!!"

func (tr TestConfig) sendTokens(
	action SendTokensAction,
	target ExecutionTarget,
	verbose bool,
) {
	fromValCfg := tr.validatorConfigs[action.From]
	toValCfg := tr.validatorConfigs[action.To]
	fromAddress := fromValCfg.DelAddress
	toAddress := toValCfg.DelAddress
	if action.Chain != ChainID("provi") {
		// use binary with Bech32Prefix set to ConsumerAccountPrefix
		if fromValCfg.UseConsumerKey {
			fromAddress = fromValCfg.ConsumerDelAddress
		} else {
			// use the same address as on the provider but with different prefix
			fromAddress = fromValCfg.DelAddressOnConsumer
		}
		if toValCfg.UseConsumerKey {
			toAddress = toValCfg.ConsumerDelAddress
		} else {
			// use the same address as on the provider but with different prefix
			toAddress = toValCfg.DelAddressOnConsumer
		}
	}

	binaryName := tr.chainConfigs[action.Chain].BinaryName
	cmd := target.ExecCommand(binaryName,

		"tx", "bank", "send",
		fromAddress,
		toAddress,
		fmt.Sprint(action.Amount)+`stake`,

		`--chain-id`, string(tr.chainConfigs[action.Chain].ChainId),
		`--home`, tr.getValidatorHome(action.Chain, action.From),
		`--node`, tr.getValidatorNode(action.Chain, action.From),
		`--keyring-backend`, `test`,
		`-y`,
	)
	if verbose {
		fmt.Println("sendTokens cmd:", cmd.String())
	}
	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// wait for inclusion in a block -> '--broadcast-mode block' is deprecated
	tr.waitBlocks(action.Chain, 2, 30*time.Second)
}

type StartChainAction struct {
	Chain      ChainID
	Validators []StartChainValidator
	// Genesis changes specific to this action, appended to genesis changes defined in chain config
	GenesisChanges string
	IsConsumer     bool
}

type StartChainValidator struct {
	Id         ValidatorID
	Allocation uint
	Stake      uint
}

func (tr *TestConfig) startChain(
	action StartChainAction,
	target ExecutionTarget,
	verbose bool,
) {
	chainConfig := tr.chainConfigs[action.Chain]
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
			Mnemonic:         tr.validatorConfigs[val.Id].Mnemonic,
			NodeKey:          tr.validatorConfigs[val.Id].NodeKey,
			ValId:            fmt.Sprint(val.Id),
			PrivValidatorKey: tr.validatorConfigs[val.Id].PrivValidatorKey,
			Allocation:       fmt.Sprint(val.Allocation) + "stake",
			Stake:            fmt.Sprint(val.Stake) + "stake",
			IpSuffix:         tr.validatorConfigs[val.Id].IpSuffix,

			ConsumerMnemonic:         tr.validatorConfigs[val.Id].ConsumerMnemonic,
			ConsumerPrivValidatorKey: tr.validatorConfigs[val.Id].ConsumerPrivValidatorKey,
			// if true node will be started with consumer key for each consumer chain
			StartWithConsumerKey: tr.validatorConfigs[val.Id].UseConsumerKey,
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

	var cometmockArg string
	if tr.useCometmock {
		cometmockArg = "true"
	} else {
		cometmockArg = "false"
	}

	startChainScript := target.GetTestScriptPath(action.IsConsumer, "start-chain.sh")
	cmd := target.ExecCommand("/bin/bash",
		startChainScript, chainConfig.BinaryName, string(vals),
		string(chainConfig.ChainId), chainConfig.IpPrefix, genesisChanges,
		fmt.Sprint(action.IsConsumer),
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

	tr.addChainToRelayer(AddChainToRelayerAction{
		Chain:      action.Chain,
		Validator:  action.Validators[0].Id,
		IsConsumer: action.IsConsumer,
	}, target, verbose)

	// store the fact that we started the chain
	tr.runningChains[action.Chain] = true
	fmt.Println("Started chain", action.Chain)
	if tr.timeOffset != 0 {
		// advance time for this chain so that it is in sync with the rest of the network
		tr.AdvanceTimeForChain(action.Chain, tr.timeOffset)
	}
}

type SubmitTextProposalAction struct {
	Chain       ChainID
	From        ValidatorID
	Deposit     uint
	Title       string
	Description string
}

func (tr TestConfig) submitTextProposal(
	action SubmitTextProposalAction,
	target ExecutionTarget,
	verbose bool,
) {
	// TEXT PROPOSAL
	bz, err := target.ExecCommand(
		tr.chainConfigs[action.Chain].BinaryName,
		"tx", "gov", "submit-legacy-proposal",
		`--title`, action.Title,
		`--description`, action.Description,
		`--deposit`, fmt.Sprint(action.Deposit)+`stake`,
		`--from`, `validator`+fmt.Sprint(action.From),
		`--chain-id`, string(tr.chainConfigs[action.Chain].ChainId),
		`--home`, tr.getValidatorHome(action.Chain, action.From),
		`--node`, tr.getValidatorNode(action.Chain, action.From),
		`--keyring-backend`, `test`,
		`-y`,
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// wait for inclusion in a block -> '--broadcast-mode block' is deprecated
	tr.waitBlocks(action.Chain, 1, 10*time.Second)
}

type SubmitConsumerAdditionProposalAction struct {
	PreCCV              bool
	Chain               ChainID
	From                ValidatorID
	Deposit             uint
	ConsumerChain       ChainID
	SpawnTime           uint
	InitialHeight       clienttypes.Height
	DistributionChannel string
}

func (tr TestConfig) submitConsumerAdditionProposal(
	action SubmitConsumerAdditionProposalAction,
	target ExecutionTarget,
	verbose bool,
) {
	spawnTime := tr.containerConfig.Now.Add(time.Duration(action.SpawnTime) * time.Millisecond)
	params := ccvtypes.DefaultParams()
	prop := client.ConsumerAdditionProposalJSON{
		Title:                             "Propose the addition of a new chain",
		Summary:                           "Gonna be a great chain",
		ChainId:                           string(tr.chainConfigs[action.ConsumerChain].ChainId),
		InitialHeight:                     action.InitialHeight,
		GenesisHash:                       []byte("gen_hash"),
		BinaryHash:                        []byte("bin_hash"),
		SpawnTime:                         spawnTime,
		ConsumerRedistributionFraction:    params.ConsumerRedistributionFraction,
		BlocksPerDistributionTransmission: params.BlocksPerDistributionTransmission,
		HistoricalEntries:                 params.HistoricalEntries,
		CcvTimeoutPeriod:                  params.CcvTimeoutPeriod,
		TransferTimeoutPeriod:             params.TransferTimeoutPeriod,
		UnbondingPeriod:                   params.UnbondingPeriod,
		Deposit:                           fmt.Sprint(action.Deposit) + `stake`,
		DistributionTransmissionChannel:   action.DistributionChannel,
	}

	bz, err := json.Marshal(prop)
	if err != nil {
		log.Fatal(err)
	}

	jsonStr := string(bz)
	if strings.Contains(jsonStr, "'") {
		log.Fatal("prop json contains single quote")
	}

	//#nosec G204 -- bypass unsafe quoting warning (no production code)
	bz, err = target.ExecCommand(
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, jsonStr, "/temp-proposal.json"),
	).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// CONSUMER ADDITION PROPOSAL
	bz, err = target.ExecCommand(
		tr.chainConfigs[action.Chain].BinaryName,
		"tx", "gov", "submit-legacy-proposal", "consumer-addition", "/temp-proposal.json",
		`--from`, `validator`+fmt.Sprint(action.From),
		`--chain-id`, string(tr.chainConfigs[action.Chain].ChainId),
		`--home`, tr.getValidatorHome(action.Chain, action.From),
		`--gas`, `900000`,
		`--node`, tr.getValidatorNode(action.Chain, action.From),
		`--keyring-backend`, `test`,
		`-y`,
	).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// wait for inclusion in a block -> '--broadcast-mode block' is deprecated
	tr.waitBlocks(ChainID("provi"), 2, 10*time.Second)
}

type SubmitConsumerRemovalProposalAction struct {
	Chain          ChainID
	From           ValidatorID
	Deposit        uint
	ConsumerChain  ChainID
	StopTimeOffset time.Duration // offset from time.Now()
}

func (tr TestConfig) submitConsumerRemovalProposal(
	action SubmitConsumerRemovalProposalAction,
	target ExecutionTarget,
	verbose bool,
) {
	stopTime := tr.containerConfig.Now.Add(action.StopTimeOffset)
	prop := client.ConsumerRemovalProposalJSON{
		Title:    fmt.Sprintf("Stop the %v chain", action.ConsumerChain),
		Summary:  "It was a great chain",
		ChainId:  string(tr.chainConfigs[action.ConsumerChain].ChainId),
		StopTime: stopTime,
		Deposit:  fmt.Sprint(action.Deposit) + `stake`,
	}

	bz, err := json.Marshal(prop)
	if err != nil {
		log.Fatal(err)
	}

	jsonStr := string(bz)
	if strings.Contains(jsonStr, "'") {
		log.Fatal("prop json contains single quote")
	}

	bz, err = target.ExecCommand(
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, jsonStr, "/temp-proposal.json")).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	bz, err = target.ExecCommand(
		tr.chainConfigs[action.Chain].BinaryName,
		"tx", "gov", "submit-legacy-proposal", "consumer-removal",
		"/temp-proposal.json",
		`--from`, `validator`+fmt.Sprint(action.From),
		`--chain-id`, string(tr.chainConfigs[action.Chain].ChainId),
		`--home`, tr.getValidatorHome(action.Chain, action.From),
		`--node`, tr.getValidatorNode(action.Chain, action.From),
		`--gas`, "900000",
		`--keyring-backend`, `test`,
		`-y`,
	).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// wait for inclusion in a block -> '--broadcast-mode block' is deprecated
	tr.waitBlocks(ChainID("provi"), 2, 20*time.Second)
}

type SubmitParamChangeLegacyProposalAction struct {
	Chain    ChainID
	From     ValidatorID
	Deposit  uint
	Subspace string
	Key      string
	Value    interface{}
}

type paramChangeProposalJSON struct {
	Title       string            `json:"title"`
	Summary     string            `json:"summary"`
	Description string            `json:"description"`
	Changes     []paramChangeJSON `json:"changes"`
	Deposit     string            `json:"deposit"`
}

type paramChangeJSON struct {
	Subspace string      `json:"subspace"`
	Key      string      `json:"key"`
	Value    interface{} `json:"value"`
}

func (tr TestConfig) submitParamChangeProposal(
	action SubmitParamChangeLegacyProposalAction,
	target ExecutionTarget,
	verbose bool,
) {
	prop := paramChangeProposalJSON{
		Title:       "Legacy Param change",
		Summary:     "Changing legacy module params",
		Description: "Changing legacy module params",
		Changes:     []paramChangeJSON{{Subspace: action.Subspace, Key: action.Key, Value: action.Value}},
		Deposit:     fmt.Sprint(action.Deposit) + `stake`,
	}

	bz, err := json.Marshal(prop)
	if err != nil {
		log.Fatal(err)
	}

	jsonStr := string(bz)
	if strings.Contains(jsonStr, "'") {
		log.Fatal("prop json contains single quote")
	}

	//#nosec G204 -- bypass unsafe quoting warning (no production code)
	bz, err = target.ExecCommand(
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, jsonStr, "/params-proposal.json"),
	).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	cmd := target.ExecCommand(
		tr.chainConfigs[action.Chain].BinaryName,

		"tx", "gov", "submit-legacy-proposal", "param-change", "/params-proposal.json",

		`--from`, `validator`+fmt.Sprint(action.From),
		`--chain-id`, string(tr.chainConfigs[action.Chain].ChainId),
		`--home`, tr.getValidatorHome(action.Chain, action.From),
		`--node`, tr.getValidatorNode(action.Chain, action.From),
		`--gas`, "900000",
		`--keyring-backend`, `test`,
		`-y`,
	)

	bz, err = cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// wait for inclusion in a block -> '--broadcast-mode block' is deprecated
	tr.waitBlocks(action.Chain, 2, 60*time.Second)
}

type VoteGovProposalAction struct {
	Chain      ChainID
	From       []ValidatorID
	Vote       []string
	PropNumber uint
}

func (tr *TestConfig) voteGovProposal(
	action VoteGovProposalAction,
	target ExecutionTarget,
	verbose bool,
) {
	var wg sync.WaitGroup
	for i, val := range action.From {
		wg.Add(1)
		vote := action.Vote[i]
		go func(val ValidatorID, vote string) {
			defer wg.Done()
			bz, err := target.ExecCommand(
				tr.chainConfigs[action.Chain].BinaryName,

				"tx", "gov", "vote",
				fmt.Sprint(action.PropNumber), vote,

				`--from`, `validator`+fmt.Sprint(val),
				`--chain-id`, string(tr.chainConfigs[action.Chain].ChainId),
				`--home`, tr.getValidatorHome(action.Chain, val),
				`--node`, tr.getValidatorNode(action.Chain, val),
				`--keyring-backend`, `test`,
				`--gas`, "900000",
				`-y`,
			).CombinedOutput()
			if err != nil {
				log.Fatal(err, "\n", string(bz))
			}
		}(val, vote)
	}

	wg.Wait()
	// wait for inclusion in a block -> '--broadcast-mode block' is deprecated
	tr.waitBlocks(action.Chain, 1, 10*time.Second)
	tr.WaitTime(time.Duration(tr.chainConfigs[action.Chain].VotingWaitTime) * time.Second)
}

type StartConsumerChainAction struct {
	ConsumerChain  ChainID
	ProviderChain  ChainID
	Validators     []StartChainValidator
	GenesisChanges string
}

func (tr *TestConfig) startConsumerChain(
	action StartConsumerChainAction,
	target ExecutionTarget,
	verbose bool,
) {
	fmt.Println("Starting consumer chain ", action.ConsumerChain)
	consumerGenesis := ".app_state.ccvconsumer = " + tr.getConsumerGenesis(action.ProviderChain, action.ConsumerChain, target)
	consumerGenesisChanges := tr.chainConfigs[action.ConsumerChain].GenesisChanges
	if consumerGenesisChanges != "" {
		consumerGenesis = consumerGenesis + " | " + consumerGenesisChanges + " | " + action.GenesisChanges
	}

	tr.startChain(StartChainAction{
		Chain:          action.ConsumerChain,
		Validators:     action.Validators,
		GenesisChanges: consumerGenesis,
		IsConsumer:     true,
	}, target, verbose)
}

// Get consumer genesis from provider
func (tr *TestConfig) getConsumerGenesis(providerChain, consumerChain ChainID, target ExecutionTarget) string {
	fmt.Println("Exporting consumer genesis from provider")
	providerBinaryName := tr.chainConfigs[providerChain].BinaryName

	cmd := target.ExecCommand(
		providerBinaryName,

		"query", "provider", "consumer-genesis",
		string(tr.chainConfigs[consumerChain].ChainId),

		`--node`, tr.getQueryNode(providerChain),
		`-o`, `json`,
	)

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// only needed when consumer is running v3.3.x and later
	if tr.transformGenesis {
		return string(tr.transformConsumerGenesis(consumerChain, bz, target))
	}
	return string(bz)
}

// Transform consumer genesis content from older version
func (tr *TestConfig) transformConsumerGenesis(consumerChain ChainID, genesis []byte, target ExecutionTarget) []byte {
	fmt.Println("Transforming consumer genesis")
	fmt.Printf("Original ccv genesis: %s\n", string(genesis))

	fileName := "consumer_genesis.json"
	file, err := os.CreateTemp("", fileName)
	if err != nil {
		panic(fmt.Sprintf("failed writing ccv consumer file : %v", err))
	}
	defer file.Close()
	err = os.WriteFile(file.Name(), genesis, 0600)
	if err != nil {
		log.Fatalf("Failed writing consumer genesis to file: %v", err)
	}

	containerInstance := tr.containerConfig.InstanceName
	targetFile := fmt.Sprintf("/tmp/%s", fileName)
	sourceFile := file.Name()
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "cp", sourceFile,
		fmt.Sprintf("%s:%s", containerInstance, targetFile))
	genesis, err = cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(genesis))
	}

	consumerBinaryName := tr.chainConfigs[consumerChain].BinaryName
	cmd = target.ExecCommand(
		consumerBinaryName,
		"genesis", "transform", targetFile)
	result, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "CCV consumer genesis transformation failed: %s", string(result))
	}
	fmt.Printf("Transformed genesis is: %s\n", string(result))
	return result
}

type ChangeoverChainAction struct {
	SovereignChain ChainID
	ProviderChain  ChainID
	Validators     []StartChainValidator
	GenesisChanges string
}

func (tr TestConfig) changeoverChain(
	action ChangeoverChainAction,
	target ExecutionTarget,
	verbose bool,
) {
	// sleep until the consumer chain genesis is ready on consumer
	time.Sleep(5 * time.Second)
	cmd := target.ExecCommand(
		tr.chainConfigs[action.ProviderChain].BinaryName,

		"query", "provider", "consumer-genesis",
		string(tr.chainConfigs[action.SovereignChain].ChainId),

		`--node`, tr.getQueryNode(action.ProviderChain),
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
	consumerGenesisChanges := tr.chainConfigs[action.SovereignChain].GenesisChanges
	if consumerGenesisChanges != "" {
		consumerGenesis = consumerGenesis + " | " + consumerGenesisChanges + " | " + action.GenesisChanges
	}

	tr.startChangeover(ChangeoverChainAction{
		Validators:     action.Validators,
		GenesisChanges: consumerGenesis,
	}, target, verbose)
}

func (tr TestConfig) startChangeover(
	action ChangeoverChainAction,
	target ExecutionTarget,
	verbose bool,
) {
	chainConfig := tr.chainConfigs[ChainID("sover")]
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
			Mnemonic:         tr.validatorConfigs[val.Id].Mnemonic,
			NodeKey:          tr.validatorConfigs[val.Id].NodeKey,
			ValId:            fmt.Sprint(val.Id),
			PrivValidatorKey: tr.validatorConfigs[val.Id].PrivValidatorKey,
			Allocation:       fmt.Sprint(val.Allocation) + "stake",
			Stake:            fmt.Sprint(val.Stake) + "stake",
			IpSuffix:         tr.validatorConfigs[val.Id].IpSuffix,

			ConsumerMnemonic:         tr.validatorConfigs[val.Id].ConsumerMnemonic,
			ConsumerPrivValidatorKey: tr.validatorConfigs[val.Id].ConsumerPrivValidatorKey,
			// if true node will be started with consumer key for each consumer chain
			StartWithConsumerKey: tr.validatorConfigs[val.Id].UseConsumerKey,
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

	isConsumer := true
	changeoverScript := target.GetTestScriptPath(isConsumer, "start-changeover.sh")
	cmd := target.ExecCommand(
		"/bin/bash",
		changeoverScript, chainConfig.UpgradeBinary, string(vals),
		"sover", chainConfig.IpPrefix, genesisChanges,
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

type AddChainToRelayerAction struct {
	Chain      ChainID
	Validator  ValidatorID
	IsConsumer bool
}

const hermesChainConfigTemplate = `

[[chains]]
account_prefix = "%s"
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
		"account-prefix": "%s",
		"keyring-backend": "test",
		"gas-adjustment": 1.2,
		"gas-prices": "0.00stake",
		"debug": true,
		"timeout": "20s",
		"output-format": "json",
		"sign-mode": "direct"
	}
}`

func (tr TestConfig) addChainToRelayer(
	action AddChainToRelayerAction,
	target ExecutionTarget,
	verbose bool,
) {
	if !tr.useGorelayer {
		tr.addChainToHermes(action, target, verbose)
	} else {
		tr.addChainToGorelayer(action, target, verbose)
	}
}

func (tr TestConfig) addChainToGorelayer(
	action AddChainToRelayerAction,
	target ExecutionTarget,
	verbose bool,
) {
	queryNodeIP := tr.getQueryNodeIP(action.Chain)
	ChainId := tr.chainConfigs[action.Chain].ChainId
	rpcAddr := "http://" + queryNodeIP + ":26658"

	chainConfig := fmt.Sprintf(gorelayerChainConfigTemplate,
		ChainId,
		rpcAddr,
		tr.chainConfigs[action.Chain].AccountPrefix,
	)

	bz, err := target.ExecCommand(
		"rly", "config", "init").CombinedOutput()
	if err != nil && !strings.Contains(string(bz), "config already exists") {
		log.Fatal(err, "\n", string(bz))
	}

	chainConfigFileName := fmt.Sprintf("/root/%s_config.json", ChainId)

	bashCommand := fmt.Sprintf(`echo '%s' >> %s`, chainConfig, chainConfigFileName)
	bz, err = target.ExecCommand("bash", "-c",
		bashCommand).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	addChainCommand := target.ExecCommand("rly", "chains", "add", "--file", chainConfigFileName, string(ChainId))
	executeCommand(addChainCommand, "add chain")

	keyRestoreCommand := target.ExecCommand("rly", "keys", "restore", string(ChainId), "default", tr.validatorConfigs[action.Validator].Mnemonic)
	executeCommand(keyRestoreCommand, "restore keys")
}

func (tr TestConfig) addChainToHermes(
	action AddChainToRelayerAction,
	target ExecutionTarget,
	verbose bool,
) {
	queryNodeIP := tr.getQueryNodeIP(action.Chain)
	ChainId := tr.chainConfigs[action.Chain].ChainId
	keyName := "query"
	rpcAddr := "http://" + queryNodeIP + ":26658"
	grpcAddr := "tcp://" + queryNodeIP + ":9091"
	wsAddr := "ws://" + queryNodeIP + ":26658/websocket"

	chainConfig := fmt.Sprintf(hermesChainConfigTemplate,
		tr.chainConfigs[action.Chain].AccountPrefix,
		grpcAddr,
		ChainId,
		keyName,
		rpcAddr,
		wsAddr,
		action.IsConsumer,
	)

	bashCommand := fmt.Sprintf(`echo '%s' >> %s`, chainConfig, "/root/.hermes/config.toml")

	bz, err := target.ExecCommand("bash", "-c", bashCommand).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// Save mnemonic to file within container
	var mnemonic string
	if tr.validatorConfigs[action.Validator].UseConsumerKey && action.IsConsumer {
		mnemonic = tr.validatorConfigs[action.Validator].ConsumerMnemonic
	} else {
		mnemonic = tr.validatorConfigs[action.Validator].Mnemonic
	}

	saveMnemonicCommand := fmt.Sprintf(`echo '%s' > %s`, mnemonic, "/root/.hermes/mnemonic.txt")
	fmt.Println("Add to hermes", action.Validator)
	bz, err = target.ExecCommand("bash", "-c", saveMnemonicCommand).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	bz, err = target.ExecCommand("hermes",
		"keys", "add",
		"--chain", string(tr.chainConfigs[action.Chain].ChainId),
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

type AddIbcConnectionAction struct {
	ChainA  ChainID
	ChainB  ChainID
	ClientA uint
	ClientB uint
}

func (tr TestConfig) addIbcConnection(
	action AddIbcConnectionAction,
	target ExecutionTarget,
	verbose bool,
) {
	if !tr.useGorelayer {
		tr.addIbcConnectionHermes(action, target, verbose)
	} else {
		tr.addIbcConnectionGorelayer(action, verbose)
	}
}

func (tr TestConfig) addIbcConnectionGorelayer(
	action AddIbcConnectionAction,
	verbose bool,
) {
	pathName := tr.GetPathNameForGorelayer(action.ChainA, action.ChainB)

	pathConfig := fmt.Sprintf(gorelayerPathConfigTemplate, action.ChainA, action.ClientA, action.ChainB, action.ClientB)

	pathConfigFileName := fmt.Sprintf("/root/%s_config.json", pathName)

	bashCommand := fmt.Sprintf(`echo '%s' >> %s`, pathConfig, pathConfigFileName)
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	pathConfigCommand := exec.Command("docker", "exec", tr.containerConfig.InstanceName, "bash", "-c",
		bashCommand)
	executeCommand(pathConfigCommand, "add path config")

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	newPathCommand := exec.Command("docker", "exec", tr.containerConfig.InstanceName, "rly",
		"paths", "add",
		string(tr.chainConfigs[action.ChainA].ChainId),
		string(tr.chainConfigs[action.ChainB].ChainId),
		pathName,
		"--file", pathConfigFileName,
	)

	executeCommand(newPathCommand, "new path")

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	newClientsCommand := exec.Command("docker", "exec", tr.containerConfig.InstanceName, "rly",
		"transact", "clients",
		pathName,
	)

	executeCommand(newClientsCommand, "new clients")

	tr.waitBlocks(action.ChainA, 1, 10*time.Second)
	tr.waitBlocks(action.ChainB, 1, 10*time.Second)

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	newConnectionCommand := exec.Command("docker", "exec", tr.containerConfig.InstanceName, "rly",
		"transact", "connection",
		pathName,
	)

	executeCommand(newConnectionCommand, "new connection")

	tr.waitBlocks(action.ChainA, 1, 10*time.Second)
	tr.waitBlocks(action.ChainB, 1, 10*time.Second)
}

type CreateIbcClientsAction struct {
	ChainA ChainID
	ChainB ChainID
}

// if clients are not provided hermes will first
// create new clients and then a new connection
// otherwise, it would use client provided as CLI argument (-a-client)
func (tr TestConfig) createIbcClientsHermes(
	action CreateIbcClientsAction,
	target ExecutionTarget,
	verbose bool,
) {
	cmd := target.ExecCommand("hermes",
		"create", "connection",
		"--a-chain", string(tr.chainConfigs[action.ChainA].ChainId),
		"--b-chain", string(tr.chainConfigs[action.ChainB].ChainId),
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

func (tr TestConfig) addIbcConnectionHermes(
	action AddIbcConnectionAction,
	target ExecutionTarget,
	verbose bool,
) {
	cmd := target.ExecCommand("hermes",
		"create", "connection",
		"--a-chain", string(tr.chainConfigs[action.ChainA].ChainId),
		"--a-client", "07-tendermint-"+fmt.Sprint(action.ClientA),
		"--b-client", "07-tendermint-"+fmt.Sprint(action.ClientB),
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

type AddIbcChannelAction struct {
	ChainA      ChainID
	ChainB      ChainID
	ConnectionA uint
	PortA       string
	PortB       string
	Order       string
	Version     string
}

type StartRelayerAction struct{}

func (tr TestConfig) startRelayer(
	action StartRelayerAction,
	target ExecutionTarget,
	verbose bool,
) {
	if tr.useGorelayer {
		tr.startGorelayer(action, target, verbose)
	} else {
		tr.startHermes(action, target, verbose)
	}
}

func (tr TestConfig) startGorelayer(
	action StartRelayerAction,
	target ExecutionTarget,
	verbose bool,
) {
	// gorelayer start is running in detached mode
	cmd := target.ExecDetachedCommand("rly", "start")

	if err := cmd.Start(); err != nil {
		log.Fatal(err)
	}

	if verbose {
		fmt.Println("started gorelayer")
	}
}

func (tr TestConfig) startHermes(
	action StartRelayerAction,
	target ExecutionTarget,
	verbose bool,
) {
	// hermes start is running in detached mode
	cmd := target.ExecDetachedCommand("hermes", "start")

	if err := cmd.Start(); err != nil {
		log.Fatal(err)
	}

	if verbose {
		fmt.Println("started Hermes")
	}
}

func (tr TestConfig) addIbcChannel(
	action AddIbcChannelAction,
	target ExecutionTarget,
	verbose bool,
) {
	if tr.useGorelayer {
		tr.addIbcChannelGorelayer(action, target, verbose)
	} else {
		tr.addIbcChannelHermes(action, target, verbose)
	}
}

func (tr TestConfig) addIbcChannelGorelayer(
	action AddIbcChannelAction,
	target ExecutionTarget,
	verbose bool,
) {
	pathName := tr.GetPathNameForGorelayer(action.ChainA, action.ChainB)
	cmd := target.ExecCommand("rly",
		"transact", "channel",
		pathName,
		"--src-port", action.PortA,
		"--dst-port", action.PortB,
		"--version", tr.containerConfig.CcvVersion,
		"--order", action.Order,
		"--debug",
	)
	executeCommand(cmd, "addChannel")
}

func (tr TestConfig) addIbcChannelHermes(
	action AddIbcChannelAction,
	target ExecutionTarget,
	verbose bool,
) {
	// if version is not specified, use the default version when creating ccv connections
	// otherwise, use the provided version schema (usually it is ICS20-1 for IBC transfer)
	chanVersion := action.Version
	if chanVersion == "" {
		chanVersion = tr.containerConfig.CcvVersion
	}

	cmd := target.ExecCommand("hermes",
		"create", "channel",
		"--a-chain", string(tr.chainConfigs[action.ChainA].ChainId),
		"--a-connection", "connection-"+fmt.Sprint(action.ConnectionA),
		"--a-port", action.PortA,
		"--b-port", action.PortB,
		"--channel-version", chanVersion,
		"--order", action.Order,
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

type TransferChannelCompleteAction struct {
	ChainA      ChainID
	ChainB      ChainID
	ConnectionA uint
	PortA       string
	PortB       string
	Order       string
	ChannelA    uint
	ChannelB    uint
}

func (tr TestConfig) transferChannelComplete(
	action TransferChannelCompleteAction,
	target ExecutionTarget,
	verbose bool,
) {
	if tr.useGorelayer {
		log.Fatal("transferChannelComplete is not implemented for rly")
	}

	chanOpenTryCmd := target.ExecCommand("hermes",
		"tx", "chan-open-try",
		"--dst-chain", string(tr.chainConfigs[action.ChainB].ChainId),
		"--src-chain", string(tr.chainConfigs[action.ChainA].ChainId),
		"--dst-connection", "connection-"+fmt.Sprint(action.ConnectionA),
		"--dst-port", action.PortB,
		"--src-port", action.PortA,
		"--src-channel", "channel-"+fmt.Sprint(action.ChannelA),
	)
	executeCommand(chanOpenTryCmd, "transferChanOpenTry")

	chanOpenAckCmd := target.ExecCommand("hermes",
		"tx", "chan-open-ack",
		"--dst-chain", string(tr.chainConfigs[action.ChainA].ChainId),
		"--src-chain", string(tr.chainConfigs[action.ChainB].ChainId),
		"--dst-connection", "connection-"+fmt.Sprint(action.ConnectionA),
		"--dst-port", action.PortA,
		"--src-port", action.PortB,
		"--dst-channel", "channel-"+fmt.Sprint(action.ChannelA),
		"--src-channel", "channel-"+fmt.Sprint(action.ChannelB),
	)

	executeCommand(chanOpenAckCmd, "transferChanOpenAck")

	chanOpenConfirmCmd := target.ExecCommand("hermes",
		"tx", "chan-open-confirm",
		"--dst-chain", string(tr.chainConfigs[action.ChainB].ChainId),
		"--src-chain", string(tr.chainConfigs[action.ChainA].ChainId),
		"--dst-connection", "connection-"+fmt.Sprint(action.ConnectionA),
		"--dst-port", action.PortB,
		"--src-port", action.PortA,
		"--dst-channel", "channel-"+fmt.Sprint(action.ChannelB),
		"--src-channel", "channel-"+fmt.Sprint(action.ChannelA),
	)
	executeCommand(chanOpenConfirmCmd, "transferChanOpenConfirm")
}

func executeCommandWithVerbosity(cmd *exec.Cmd, cmdName string, verbose bool) {
	if verbose {
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
		if verbose {
			fmt.Println(cmdName + ": " + out)
		}
	}
	if err := scanner.Err(); err != nil {
		log.Fatal(err)
	}
}

// Executes a command with verbosity specified by CLI flag
func executeCommand(cmd *exec.Cmd, cmdName string) {
	executeCommandWithVerbosity(cmd, cmdName, *verbose)
}

type RelayPacketsAction struct {
	ChainA  ChainID
	ChainB  ChainID
	Port    string
	Channel uint
}

func (tr TestConfig) relayPackets(
	action RelayPacketsAction,
	target ExecutionTarget,
	verbose bool,
) {
	if tr.useGorelayer {
		tr.relayPacketsGorelayer(action, target, verbose)
	} else {
		tr.relayPacketsHermes(action, target, verbose)
	}
}

func (tr TestConfig) relayPacketsGorelayer(
	action RelayPacketsAction,
	target ExecutionTarget,
	verbose bool,
) {
	tr.waitBlocks(action.ChainA, 3, 90*time.Second)
	tr.waitBlocks(action.ChainB, 3, 90*time.Second)

	pathName := tr.GetPathNameForGorelayer(action.ChainA, action.ChainB)

	// rly transact relay-packets [path-name] --channel [channel-id]
	cmd := target.ExecCommand("rly", "transact", "flush",
		pathName,
		"channel-"+fmt.Sprint(action.Channel),
	)
	if verbose {
		log.Println("relayPackets cmd:", cmd.String())
	}
	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	tr.waitBlocks(action.ChainA, 1, 30*time.Second)
	tr.waitBlocks(action.ChainB, 1, 30*time.Second)
}

func (tr TestConfig) relayPacketsHermes(
	action RelayPacketsAction,
	target ExecutionTarget,
	verbose bool,
) {
	tr.waitBlocks(action.ChainA, 3, 90*time.Second)
	tr.waitBlocks(action.ChainB, 3, 90*time.Second)

	// hermes clear packets ibc0 transfer channel-13
	cmd := target.ExecCommand("hermes", "clear", "packets",
		"--chain", string(tr.chainConfigs[action.ChainA].ChainId),
		"--port", action.Port,
		"--channel", "channel-"+fmt.Sprint(action.Channel),
	)
	if verbose {
		log.Println("relayPackets cmd:", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	tr.waitBlocks(action.ChainA, 1, 30*time.Second)
	tr.waitBlocks(action.ChainB, 1, 30*time.Second)
}

type RelayRewardPacketsToProviderAction struct {
	ConsumerChain ChainID
	ProviderChain ChainID
	Port          string
	Channel       uint
}

func (tr TestConfig) relayRewardPacketsToProvider(
	action RelayRewardPacketsToProviderAction,
	target ExecutionTarget,
	verbose bool,
) {
	blockPerDistribution, _ := strconv.ParseUint(strings.Trim(tr.getParam(action.ConsumerChain, Param{Subspace: "ccvconsumer", Key: "BlocksPerDistributionTransmission"}), "\""), 10, 64)
	currentBlock := uint64(tr.getBlockHeight(action.ConsumerChain))
	if currentBlock <= blockPerDistribution {
		tr.waitBlocks(action.ConsumerChain, uint(blockPerDistribution-currentBlock+1), 60*time.Second)
	}

	tr.relayPackets(RelayPacketsAction{ChainA: action.ConsumerChain, ChainB: action.ProviderChain, Port: action.Port, Channel: action.Channel}, target, verbose)
	tr.waitBlocks(action.ProviderChain, 1, 10*time.Second)
}

type DelegateTokensAction struct {
	Chain  ChainID
	From   ValidatorID
	To     ValidatorID
	Amount uint
}

func (tr TestConfig) delegateTokens(
	action DelegateTokensAction,
	target ExecutionTarget,
	verbose bool,
) {
	toValCfg := tr.validatorConfigs[action.To]
	validatorAddress := toValCfg.ValoperAddress
	if action.Chain != ChainID("provi") {
		// use binary with Bech32Prefix set to ConsumerAccountPrefix
		if toValCfg.UseConsumerKey {
			validatorAddress = toValCfg.ConsumerValoperAddress
		} else {
			// use the same address as on the provider but with different prefix
			validatorAddress = toValCfg.ValoperAddressOnConsumer
		}
	}

	cmd := target.ExecCommand(tr.chainConfigs[action.Chain].BinaryName,

		"tx", "staking", "delegate",
		validatorAddress,
		fmt.Sprint(action.Amount)+`stake`,

		`--from`, `validator`+fmt.Sprint(action.From),
		`--chain-id`, string(tr.chainConfigs[action.Chain].ChainId),
		`--home`, tr.getValidatorHome(action.Chain, action.From),
		`--node`, tr.getValidatorNode(action.Chain, action.From),
		`--keyring-backend`, `test`,
		`-y`,
	)

	if verbose {
		fmt.Println("delegate cmd:", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// wait for inclusion in a block -> '--broadcast-mode block' is deprecated
	tr.waitBlocks(action.Chain, 2, 10*time.Second)
}

type UnbondTokensAction struct {
	Chain      ChainID
	Sender     ValidatorID
	UnbondFrom ValidatorID
	Amount     uint
}

func (tr TestConfig) unbondTokens(
	action UnbondTokensAction,
	target ExecutionTarget,
	verbose bool,
) {
	unbondFromValCfg := tr.validatorConfigs[action.UnbondFrom]
	validatorAddress := unbondFromValCfg.ValoperAddress
	if action.Chain != ChainID("provi") {
		// use binary with Bech32Prefix set to ConsumerAccountPrefix
		if unbondFromValCfg.UseConsumerKey {
			validatorAddress = unbondFromValCfg.ConsumerValoperAddress
		} else {
			// use the same address as on the provider but with different prefix
			validatorAddress = unbondFromValCfg.ValoperAddressOnConsumer
		}
	}

	cmd := target.ExecCommand(tr.chainConfigs[action.Chain].BinaryName,

		"tx", "staking", "unbond",
		validatorAddress,
		fmt.Sprint(action.Amount)+`stake`,

		`--from`, `validator`+fmt.Sprint(action.Sender),
		`--chain-id`, string(tr.chainConfigs[action.Chain].ChainId),
		`--home`, tr.getValidatorHome(action.Chain, action.Sender),
		`--node`, tr.getValidatorNode(action.Chain, action.Sender),
		`--gas`, "900000",
		`--keyring-backend`, `test`,
		`-y`,
	)

	if verbose {
		fmt.Println("unbond cmd:", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// wait for inclusion in a block -> '--broadcast-mode block' is deprecated
	tr.waitBlocks(action.Chain, 2, 20*time.Second)
}

type CancelUnbondTokensAction struct {
	Chain     ChainID
	Delegator ValidatorID
	Validator ValidatorID
	Amount    uint
}

func (tr TestConfig) cancelUnbondTokens(
	action CancelUnbondTokensAction,
	target ExecutionTarget,
	verbose bool,
) {
	valCfg := tr.validatorConfigs[action.Validator]
	delCfg := tr.validatorConfigs[action.Delegator]
	validatorAddress := valCfg.ValoperAddress
	delegatorAddress := delCfg.DelAddress
	if action.Chain != ChainID("provi") {
		// use binary with Bech32Prefix set to ConsumerAccountPrefix
		if valCfg.UseConsumerKey {
			validatorAddress = valCfg.ConsumerValoperAddress
		} else {
			// use the same address as on the provider but with different prefix
			validatorAddress = valCfg.ValoperAddressOnConsumer
		}
		if delCfg.UseConsumerKey {
			delegatorAddress = delCfg.ConsumerDelAddress
		} else {
			// use the same address as on the provider but with different prefix
			delegatorAddress = delCfg.DelAddressOnConsumer
		}
	}

	// get creation-height from state
	cmd := target.ExecCommand(tr.chainConfigs[action.Chain].BinaryName,
		"q", "staking", "unbonding-delegation",
		delegatorAddress,
		validatorAddress,
		`--home`, tr.getValidatorHome(action.Chain, action.Delegator),
		`--node`, tr.getValidatorNode(action.Chain, action.Delegator),
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

	cmd = target.ExecCommand(tr.chainConfigs[action.Chain].BinaryName,
		"tx", "staking", "cancel-unbond",
		validatorAddress,
		fmt.Sprint(action.Amount)+`stake`,
		fmt.Sprint(creationHeight),
		`--from`, `validator`+fmt.Sprint(action.Delegator),
		`--chain-id`, string(tr.chainConfigs[action.Chain].ChainId),
		`--home`, tr.getValidatorHome(action.Chain, action.Delegator),
		`--node`, tr.getValidatorNode(action.Chain, action.Delegator),
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
	tr.waitBlocks(action.Chain, 2, 20*time.Second)
}

type RedelegateTokensAction struct {
	Chain    ChainID
	Src      ValidatorID
	Dst      ValidatorID
	TxSender ValidatorID
	Amount   uint
}

func (tr TestConfig) redelegateTokens(action RedelegateTokensAction, target ExecutionTarget, verbose bool) {
	srcCfg := tr.validatorConfigs[action.Src]
	dstCfg := tr.validatorConfigs[action.Dst]
	redelegateSrc := srcCfg.ValoperAddress
	redelegateDst := dstCfg.ValoperAddress
	if action.Chain != ChainID("provi") {
		// use binary with Bech32Prefix set to ConsumerAccountPrefix
		if srcCfg.UseConsumerKey {
			redelegateSrc = srcCfg.ConsumerValoperAddress
		} else {
			// use the same address as on the provider but with different prefix
			redelegateSrc = srcCfg.ValoperAddressOnConsumer
		}
		if dstCfg.UseConsumerKey {
			redelegateDst = dstCfg.ConsumerValoperAddress
		} else {
			// use the same address as on the provider but with different prefix
			redelegateDst = dstCfg.ValoperAddressOnConsumer
		}
	}

	cmd := target.ExecCommand(
		tr.chainConfigs[action.Chain].BinaryName,

		"tx", "staking", "redelegate",
		redelegateSrc,
		redelegateDst,
		fmt.Sprint(action.Amount)+`stake`,
		`--from`, `validator`+fmt.Sprint(action.TxSender),
		`--chain-id`, string(tr.chainConfigs[action.Chain].ChainId),
		`--home`, tr.getValidatorHome(action.Chain, action.TxSender),
		`--node`, tr.getValidatorNode(action.Chain, action.TxSender),
		// Need to manually set gas limit past default (200000), since redelegate has a lot of operations
		`--gas`, "900000",
		`--keyring-backend`, `test`,
		`-y`,
	)

	if verbose {
		fmt.Println("redelegate cmd:", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// wait for inclusion in a block -> '--broadcast-mode block' is deprecated
	tr.waitBlocks(action.Chain, 2, 10*time.Second)
}

type DowntimeSlashAction struct {
	Chain     ChainID
	Validator ValidatorID
}

// takes a string representation of the private key like
// `{"address":"DF090A4880B54CD57B2A79E64D9E969BD7514B09","pub_key":{"type":"tendermint/PubKeyEd25519","value":"ujY14AgopV907IYgPAk/5x8c9267S4fQf89nyeCPTes="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"TRJgf7lkTjs/sj43pyweEOanyV7H7fhnVivOi0A4yjW6NjXgCCilX3TshiA8CT/nHxz3brtLh9B/z2fJ4I9N6w=="}}`
// and returns the value of the "address" field
func (tr TestConfig) getValidatorKeyAddressFromString(keystring string) string {
	var key struct {
		Address string `json:"address"`
	}
	err := json.Unmarshal([]byte(keystring), &key)
	if err != nil {
		log.Fatal(err)
	}
	return key.Address
}

func (tr TestConfig) invokeDowntimeSlash(action DowntimeSlashAction, target ExecutionTarget, verbose bool) {
	// Bring validator down
	tr.setValidatorDowntime(action.Chain, action.Validator, true, target, verbose)
	// Wait appropriate amount of blocks for validator to be slashed
	tr.waitBlocks(action.Chain, 10, 3*time.Minute)
	// Bring validator back up
	tr.setValidatorDowntime(action.Chain, action.Validator, false, target, verbose)
}

// Sets validator downtime by setting the virtual ethernet interface of a node to "up" or "down"
func (tr TestConfig) setValidatorDowntime(chain ChainID, validator ValidatorID, down bool, target ExecutionTarget, verbose bool) {
	var lastArg string
	if down {
		lastArg = "down"
	} else {
		lastArg = "up"
	}

	if tr.useCometmock {
		// send set_signing_status either to down or up for validator
		validatorPrivateKeyAddress := tr.GetValidatorPrivateKeyAddress(chain, validator)

		method := "set_signing_status"
		params := fmt.Sprintf(`{"private_key_address":"%s","status":"%s"}`, validatorPrivateKeyAddress, lastArg)
		address := tr.getQueryNodeRPCAddress(chain)

		tr.curlJsonRPCRequest(method, params, address)
		tr.waitBlocks(chain, 1, 10*time.Second)
		return
	}

	cmd := target.ExecCommand(
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

func (tr TestConfig) GetValidatorPrivateKeyAddress(chain ChainID, validator ValidatorID) string {
	var validatorPrivateKeyAddress string
	if chain == ChainID("provi") {
		validatorPrivateKeyAddress = tr.getValidatorKeyAddressFromString(tr.validatorConfigs[validator].PrivValidatorKey)
	} else {
		var valAddressString string
		if tr.validatorConfigs[validator].UseConsumerKey {
			valAddressString = tr.validatorConfigs[validator].ConsumerPrivValidatorKey
		} else {
			valAddressString = tr.validatorConfigs[validator].PrivValidatorKey
		}
		validatorPrivateKeyAddress = tr.getValidatorKeyAddressFromString(valAddressString)
	}
	return validatorPrivateKeyAddress
}

type UnjailValidatorAction struct {
	Provider  ChainID
	Validator ValidatorID
}

// Sends an unjail transaction to the provider chain
func (tr TestConfig) unjailValidator(action UnjailValidatorAction, target ExecutionTarget, verbose bool) {
	// wait until downtime_jail_duration has elapsed, to make sure the validator can be unjailed
	tr.WaitTime(61 * time.Second)

	cmd := target.ExecCommand(
		tr.chainConfigs[action.Provider].BinaryName,
		"tx", "slashing", "unjail",
		// Validator is sender here
		`--from`, `validator`+fmt.Sprint(action.Validator),
		`--chain-id`, string(tr.chainConfigs[action.Provider].ChainId),
		`--home`, tr.getValidatorHome(action.Provider, action.Validator),
		`--node`, tr.getValidatorNode(action.Provider, action.Validator),
		`--gas`, "900000",
		`--keyring-backend`, `test`,
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
	tr.waitBlocks(action.Provider, 2, time.Minute)
}

type RegisterRepresentativeAction struct {
	Chain           ChainID
	Representatives []ValidatorID
	Stakes          []uint
}

func (tr TestConfig) registerRepresentative(
	action RegisterRepresentativeAction,
	target ExecutionTarget,
	verbose bool,
) {
	var wg sync.WaitGroup
	for i, val := range action.Representatives {
		wg.Add(1)
		stake := action.Stakes[i]
		go func(val ValidatorID, stake uint) {
			defer wg.Done()

			pubKeycmd := target.ExecCommand(tr.chainConfigs[action.Chain].BinaryName,
				"tendermint", "show-validator",
				`--home`, tr.getValidatorHome(action.Chain, val),
			)

			bzPubKey, err := pubKeycmd.CombinedOutput()
			if err != nil {
				log.Fatal(err, "\n", string(bzPubKey))
			}

			bz, err := target.ExecCommand(tr.chainConfigs[action.Chain].BinaryName,
				"tx", "staking", "create-validator",
				`--amount`, fmt.Sprint(stake)+"stake",
				`--pubkey`, string(bzPubKey),
				`--moniker`, fmt.Sprint(val),
				`--commission-rate`, "0.1",
				`--commission-max-rate`, "0.2",
				`--commission-max-change-rate`, "0.01",
				`--min-self-delegation`, "1",
				`--from`, `validator`+fmt.Sprint(val),
				`--chain-id`, string(tr.chainConfigs[action.Chain].ChainId),
				`--home`, tr.getValidatorHome(action.Chain, val),
				`--node`, tr.getValidatorNode(action.Chain, val),
				`--keyring-backend`, `test`,
				`-y`,
			).CombinedOutput()
			if err != nil {
				log.Fatal(err, "\n", string(bz))
			}

			// wait for inclusion in a block -> '--broadcast-mode block' is deprecated
			tr.waitBlocks(action.Chain, 1, 10*time.Second)
		}(val, stake)
	}

	wg.Wait()
}

type SubmitChangeRewardDenomsProposalAction struct {
	Denom   string
	Deposit uint
	From    ValidatorID
}

func (tr TestConfig) submitChangeRewardDenomsProposal(action SubmitChangeRewardDenomsProposalAction, target ExecutionTarget, verbose bool) {
	providerChain := tr.chainConfigs[ChainID("provi")]

	prop := client.ChangeRewardDenomsProposalJSON{
		Summary: "Change reward denoms",
		ChangeRewardDenomsProposal: types.ChangeRewardDenomsProposal{
			Title:          "Change reward denoms",
			Description:    "Change reward denoms",
			DenomsToAdd:    []string{action.Denom},
			DenomsToRemove: []string{"stake"},
		},
		Deposit: fmt.Sprint(action.Deposit) + `stake`,
	}

	bz, err := json.Marshal(prop)
	if err != nil {
		log.Fatal(err)
	}

	jsonStr := string(bz)
	if strings.Contains(jsonStr, "'") {
		log.Fatal("prop json contains single quote")
	}

	bz, err = target.ExecCommand(
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, jsonStr, "/change-reward-denoms-proposal.json")).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// CHANGE REWARDS DENOM PROPOSAL
	bz, err = target.ExecCommand(providerChain.BinaryName,
		"tx", "gov", "submit-legacy-proposal", "change-reward-denoms", "/change-reward-denoms-proposal.json",
		`--from`, `validator`+fmt.Sprint(action.From),
		`--chain-id`, string(providerChain.ChainId),
		`--home`, tr.getValidatorHome(providerChain.ChainId, action.From),
		`--node`, tr.getValidatorNode(providerChain.ChainId, action.From),
		`--gas`, "9000000",
		`--keyring-backend`, `test`,
		`-y`,
	).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// wait for inclusion in a block -> '--broadcast-mode block' is deprecated
	tr.waitBlocks(ChainID("provi"), 2, 30*time.Second)
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
type DoublesignSlashAction struct {
	// start another node for this Validator
	Validator ValidatorID
	Chain     ChainID
}

func (tr TestConfig) invokeDoublesignSlash(
	action DoublesignSlashAction,
	target ExecutionTarget,
	verbose bool,
) {
	if !tr.useCometmock {
		chainConfig := tr.chainConfigs[action.Chain]
		doubleSignScript := target.GetTestScriptPath(false, "cause-doublesign.sh")
		bz, err := target.ExecCommand("/bin/bash",
			doubleSignScript, chainConfig.BinaryName, string(action.Validator),
			string(chainConfig.ChainId), chainConfig.IpPrefix).CombinedOutput()
		if err != nil {
			log.Fatal(err, "\n", string(bz))
		}
		tr.waitBlocks("provi", 10, 2*time.Minute)
	} else { // tr.useCometMock
		validatorPrivateKeyAddress := tr.GetValidatorPrivateKeyAddress(action.Chain, action.Validator)

		method := "cause_double_sign"
		params := fmt.Sprintf(`{"private_key_address":"%s"}`, validatorPrivateKeyAddress)

		address := tr.getQueryNodeRPCAddress(action.Chain)

		tr.curlJsonRPCRequest(method, params, address)
		tr.waitBlocks(action.Chain, 1, 10*time.Second)
		return
	}
}

// Cause light client attack evidence for a certain validator to appear on the given chain.
// The evidence will look like the validator equivocated to a light client.
// See https://github.com/cometbft/cometbft/tree/main/spec/light-client/accountability
// for more information about light client attacks.
type LightClientEquivocationAttackAction struct {
	Validator ValidatorID
	Chain     ChainID
}

func (tr TestConfig) lightClientEquivocationAttack(
	action LightClientEquivocationAttackAction,
	verbose bool,
) {
	tr.lightClientAttack(action.Validator, action.Chain, LightClientEquivocationAttack)
}

// Cause light client attack evidence for a certain validator to appear on the given chain.
// The evidence will look like the validator tried to perform an amnesia attack.
// See https://github.com/cometbft/cometbft/tree/main/spec/light-client/accountability
// for more information about light client attacks.
type LightClientAmnesiaAttackAction struct {
	Validator ValidatorID
	Chain     ChainID
}

func (tr TestConfig) lightClientAmnesiaAttack(
	action LightClientAmnesiaAttackAction,
	verbose bool,
) {
	tr.lightClientAttack(action.Validator, action.Chain, LightClientAmnesiaAttack)
}

// Cause light client attack evidence for a certain validator to appear on the given chain.
// The evidence will look like the validator tried to perform a lunatic attack.
// See https://github.com/cometbft/cometbft/tree/main/spec/light-client/accountability
// for more information about light client attacks.
type LightClientLunaticAttackAction struct {
	Validator ValidatorID
	Chain     ChainID
}

func (tr TestConfig) lightClientLunaticAttack(
	action LightClientLunaticAttackAction,
	verbose bool,
) {
	tr.lightClientAttack(action.Validator, action.Chain, LightClientLunaticAttack)
}

type LightClientAttackType string

const (
	LightClientEquivocationAttack LightClientAttackType = "Equivocation"
	LightClientAmnesiaAttack      LightClientAttackType = "Amnesia"
	LightClientLunaticAttack      LightClientAttackType = "Lunatic"
)

func (tr TestConfig) lightClientAttack(
	validator ValidatorID,
	chain ChainID,
	attackType LightClientAttackType,
) {
	if !tr.useCometmock {
		log.Fatal("light client attack is only supported with CometMock")
	}
	validatorPrivateKeyAddress := tr.GetValidatorPrivateKeyAddress(chain, validator)

	method := "cause_light_client_attack"
	params := fmt.Sprintf(`{"private_key_address":"%s", "misbehaviour_type": "%s"}`, validatorPrivateKeyAddress, attackType)

	address := tr.getQueryNodeRPCAddress(chain)

	tr.curlJsonRPCRequest(method, params, address)
	tr.waitBlocks(chain, 1, 10*time.Second)
}

type AssignConsumerPubKeyAction struct {
	Chain          ChainID
	Validator      ValidatorID
	ConsumerPubkey string
	// ReconfigureNode will change keys the node uses and restart
	ReconfigureNode bool
	// executing the action should raise an error
	ExpectError   bool
	ExpectedError string
}

func (tr TestConfig) assignConsumerPubKey(action AssignConsumerPubKeyAction, target ExecutionTarget, verbose bool) {
	valCfg := tr.validatorConfigs[action.Validator]

	// Note: to get error response reported back from this command '--gas auto' needs to be set.
	gas := "auto"
	// Unfortunately, --gas auto does not work with CometMock. so when using CometMock, just use --gas 9000000 then
	if tr.useCometmock {
		gas = "9000000"
	}
	assignKey := fmt.Sprintf(
		`%s tx provider assign-consensus-key %s '%s' --from validator%s --chain-id %s --home %s --node %s --gas %s --keyring-backend test -y -o json`,
		tr.chainConfigs[ChainID("provi")].BinaryName,
		string(tr.chainConfigs[action.Chain].ChainId),
		action.ConsumerPubkey,
		action.Validator,
		tr.chainConfigs[ChainID("provi")].ChainId,
		tr.getValidatorHome(ChainID("provi"), action.Validator),
		tr.getValidatorNode(ChainID("provi"), action.Validator),
		gas,
	)

	cmd := target.ExecCommand(
		"/bin/bash", "-c",
		assignKey,
	)

	if verbose {
		fmt.Println("assignConsumerPubKey cmd:", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if err != nil && !action.ExpectError {
		log.Fatalf("unexpected error during key assignment - output: %s, err: %s", string(bz), err)
	}

	if action.ExpectError && !tr.useCometmock { // error report only works with --gas auto, which does not work with CometMock, so ignore
		if err == nil || !strings.Contains(string(bz), action.ExpectedError) {
			log.Fatalf("expected error not raised: expected: '%s', got '%s'", action.ExpectedError, (bz))
		}

		if verbose {
			fmt.Printf("got expected error during key assignment | err: %s | output: %s \n", err, string(bz))
		}
	}

	// node was started with provider key
	// we swap the nodes's keys for consumer keys and restart it
	if action.ReconfigureNode {
		isConsumer := tr.chainConfigs[action.Chain].BinaryName != "interchain-security-pd"
		reconfigureScript := target.GetTestScriptPath(isConsumer, "reconfigure-node.sh")
		configureNodeCmd := target.ExecCommand("/bin/bash",
			reconfigureScript, tr.chainConfigs[action.Chain].BinaryName,
			string(action.Validator), string(action.Chain),
			tr.chainConfigs[action.Chain].IpPrefix, valCfg.IpSuffix,
			valCfg.ConsumerMnemonic, valCfg.ConsumerPrivValidatorKey,
			valCfg.ConsumerNodeKey,
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
		// @POfftermatt I am currently using this for downtime slashing with cometmock
		// (I need to find the currently used validator key address)Í
		valCfg.UseConsumerKey = true
		tr.validatorConfigs[action.Validator] = valCfg
	}

	// wait for inclusion in a block -> '--broadcast-mode block' is deprecated
	tr.waitBlocks(ChainID("provi"), 2, 30*time.Second)
}

// SlashMeterReplenishmentAction polls the slash meter on provider until value is achieved
type SlashMeterReplenishmentAction struct {
	TargetValue int64
	// panic if timeout is exceeded
	Timeout time.Duration
}

func (tr TestConfig) waitForSlashMeterReplenishment(
	action SlashMeterReplenishmentAction,
	verbose bool,
) {
	timeout := time.Now().Add(action.Timeout)
	initialSlashMeter := tr.getSlashMeter()

	if initialSlashMeter >= 0 {
		panic(fmt.Sprintf("No need to wait for slash meter replenishment, current value: %d", initialSlashMeter))
	}

	for {
		slashMeter := tr.getSlashMeter()
		if verbose {
			fmt.Printf("waiting for slash meter to be replenished, current value: %d\n", slashMeter)
		}

		// check if meter has reached target value
		if slashMeter >= action.TargetValue {
			break
		}

		if time.Now().After(timeout) {
			panic(fmt.Sprintf("\n\nwaitForSlashMeterReplenishment has timed out after: %s\n\n", action.Timeout))
		}

		tr.WaitTime(5 * time.Second)
	}
}

type WaitTimeAction struct {
	WaitTime time.Duration
}

func (tr TestConfig) waitForTime(
	action WaitTimeAction,
	verbose bool,
) {
	tr.WaitTime(action.WaitTime)
}

// GetPathNameForGorelayer returns the name of the path between two given chains used by Gorelayer.
// Since paths are bidirectional, we need either chain to be able to be provided as first or second argument
// and still return the same name, so we sort the chain names alphabetically.
func (tr TestConfig) GetPathNameForGorelayer(chainA, chainB ChainID) string {
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
type StartConsumerEvidenceDetectorAction struct {
	Chain ChainID
}

func (tc TestConfig) startConsumerEvidenceDetector(
	action StartConsumerEvidenceDetectorAction,
	target ExecutionTarget,
	verbose bool,
) {
	chainConfig := tc.chainConfigs[action.Chain]
	// run in detached mode so it will keep running in the background
	bz, err := target.ExecDetachedCommand(
		"hermes", "evidence", "--chain", string(chainConfig.ChainId)).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
	tc.waitBlocks("provi", 10, 2*time.Minute)
}

// WaitTime waits for the given duration.
// To make sure that the new timestamp is visible on-chain, it also waits until at least one block has been
// produced on each chain after waiting.
// The CometMock version of this takes a pointer to the TestConfig as it needs to manipulate
// information in the testrun that stores how much each chain has waited, to keep times in sync.
// Be careful that all functions calling WaitTime should therefore also take a pointer to the TestConfig.
func (tr *TestConfig) WaitTime(duration time.Duration) {
	if !tr.useCometmock {
		time.Sleep(duration)
	} else {
		tr.timeOffset += duration
		for chain, running := range tr.runningChains {
			if !running {
				continue
			}
			tr.AdvanceTimeForChain(chain, duration)
			tr.waitBlocks(chain, 1, 2*time.Second)
		}
	}
}

func (tr TestConfig) AdvanceTimeForChain(chain ChainID, duration time.Duration) {
	// cometmock avoids sleeping, and instead advances time for all chains
	method := "advance_time"
	params := fmt.Sprintf(`{"duration_in_seconds": "%d"}`, int(math.Ceil(duration.Seconds())))

	address := tr.getQueryNodeRPCAddress(chain)

	tr.curlJsonRPCRequest(method, params, address)

	// wait for 1 block of the chain to get a block with the advanced timestamp
	tr.waitBlocks(chain, 1, time.Minute)
}
