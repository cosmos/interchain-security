package v5

import (
	"bufio"
	"encoding/json"
	"fmt"
	"log"
	"math"
	"os"
	"os/exec"
	"regexp"
	"sort"
	"strings"
	"time"

	"golang.org/x/mod/semver"

	e2e "github.com/cosmos/interchain-security/v7/tests/e2e/testlib"
	"github.com/cosmos/interchain-security/v7/x/ccv/provider/client"
	ccvtypes "github.com/cosmos/interchain-security/v7/x/ccv/types"
)

const (
	done = "done!!!!!!!!"

	VLatest = "latest"
	V400    = "v4.0.0"
	V330    = "v3.3.0"
	V300    = "v3.0.0"
)

// Note: to get error response reported back from this command '--gas auto' needs to be set.
var gas = "auto"

type (
	TestConfig = e2e.TestConfig
)

// type aliases
type (
	AssignConsumerPubKeyAction          = e2e.AssignConsumerPubKeyAction
	StartChainAction                    = e2e.StartChainAction
	StartChainValidator                 = e2e.StartChainValidator
	StartConsumerChainAction            = e2e.StartConsumerChainAction
	SubmitConsumerRemovalProposalAction = e2e.SubmitConsumerRemovalProposalAction
	DelegateTokensAction                = e2e.DelegateTokensAction
	UnbondTokensAction                  = e2e.UnbondTokensAction
)

type Chain struct {
	Target     e2e.TargetDriver
	TestConfig *e2e.TestConfig
}

func (tr *Chain) StartChain(
	action StartChainAction,
	verbose bool,
) {
	chainConfig := tr.TestConfig.ChainConfigs[action.Chain]
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
			Mnemonic:         tr.TestConfig.ValidatorConfigs[val.Id].Mnemonic,
			NodeKey:          tr.TestConfig.ValidatorConfigs[val.Id].NodeKey,
			ValId:            fmt.Sprint(val.Id),
			PrivValidatorKey: tr.TestConfig.ValidatorConfigs[val.Id].PrivValidatorKey,
			Allocation:       fmt.Sprint(val.Allocation) + "stake",
			Stake:            fmt.Sprint(val.Stake) + "stake",
			IpSuffix:         tr.TestConfig.ValidatorConfigs[val.Id].IpSuffix,

			ConsumerMnemonic:         tr.TestConfig.ValidatorConfigs[val.Id].ConsumerMnemonic,
			ConsumerPrivValidatorKey: tr.TestConfig.ValidatorConfigs[val.Id].ConsumerPrivValidatorKey,
			// if true node will be started with consumer key for each consumer chain
			StartWithConsumerKey: tr.TestConfig.ValidatorConfigs[val.Id].UseConsumerKey,
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
	if tr.TestConfig.UseCometmock {
		cometmockArg = "true"
	} else {
		cometmockArg = "false"
	}

	chainHome := string(action.Chain)
	startChainScript := tr.Target.GetTestScriptPath(action.IsConsumer, "start-chain.sh")
	cmd := tr.Target.ExecCommand("/bin/bash",
		startChainScript, chainConfig.BinaryName, string(vals),
		string(chainConfig.ChainId), chainConfig.IpPrefix, genesisChanges,
		fmt.Sprint(action.IsConsumer),
		// override config/config.toml for each node on chain
		// usually timeout_commit and peer_gossip_sleep_duration are changed to vary the test run duration
		// lower timeout_commit means the blocks are produced faster making the test run shorter
		// with short timeout_commit (eg. timeout_commit = 1s) some nodes may miss blocks causing the test run to fail
		tr.TestConfig.TendermintConfigOverride,
		cometmockArg,
		chainHome,
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
	}, verbose)

	// store the fact that we started the chain
	tr.TestConfig.RunningChains[action.Chain] = true
	fmt.Println("Started chain", action.Chain)
	if tr.TestConfig.TimeOffset != 0 {
		// advance time for this chain so that it is in sync with the rest of the network
		tr.AdvanceTimeForChain(action.Chain, tr.TestConfig.TimeOffset)
	}
}

func (tr Chain) SubmitConsumerAdditionProposal(
	action e2e.SubmitConsumerAdditionProposalAction,
	verbose bool,
) {
	spawnTime := tr.TestConfig.ContainerConfig.Now.Add(time.Duration(action.SpawnTime) * time.Millisecond)
	params := ccvtypes.DefaultParams()
	prop := client.ConsumerAdditionProposalJSON{
		Title:                             "Propose the addition of a new chain",
		Summary:                           "Gonna be a great chain",
		ChainId:                           string(tr.TestConfig.ChainConfigs[action.ConsumerChain].ChainId),
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
		TopN:                              action.TopN,
		ValidatorsPowerCap:                action.ValidatorsPowerCap,
		ValidatorSetCap:                   action.ValidatorSetCap,
		Allowlist:                         action.Allowlist,
		Denylist:                          action.Denylist,
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
	cmd := tr.Target.ExecCommand(
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, jsonStr, "/temp-proposal.json"))
	bz, err = cmd.CombinedOutput()
	if verbose {
		log.Println("submitConsumerAdditionProposal cmd: ", cmd.String())
	}

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// CONSUMER ADDITION PROPOSAL
	cmd = tr.Target.ExecCommand(
		tr.TestConfig.ChainConfigs[action.Chain].BinaryName,
		"tx", "gov", "submit-legacy-proposal", "consumer-addition", "/temp-proposal.json",
		`--from`, `validator`+fmt.Sprint(action.From),
		`--chain-id`, string(tr.TestConfig.ChainConfigs[action.Chain].ChainId),
		`--home`, tr.getValidatorHome(action.Chain, action.From),
		`--gas`, `900000`,
		`--node`, tr.getValidatorNode(action.Chain, action.From),
		`--keyring-backend`, `test`,
		`-y`,
	)

	if verbose {
		fmt.Println("submitConsumerAdditionProposal cmd:", cmd.String())
		fmt.Println("submitConsumerAdditionProposal json:", jsonStr)
	}
	bz, err = cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	if verbose {
		fmt.Println("submitConsumerAdditionProposal output:", string(bz))
	}

	// wait for inclusion in a block -> '--broadcast-mode block' is deprecated
	tr.waitBlocks(ChainID("provi"), 2, 10*time.Second)
}

func (tr Chain) SubmitConsumerRemovalProposal(
	action SubmitConsumerRemovalProposalAction,
	verbose bool,
) {
	stopTime := tr.TestConfig.ContainerConfig.Now.Add(action.StopTimeOffset)
	prop := client.ConsumerRemovalProposalJSON{
		Title:    fmt.Sprintf("Stop the %v chain", action.ConsumerChain),
		Summary:  "It was a great chain",
		ChainId:  string(tr.TestConfig.ChainConfigs[action.ConsumerChain].ChainId),
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

	bz, err = tr.Target.ExecCommand(
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, jsonStr, "/temp-proposal.json")).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	bz, err = tr.Target.ExecCommand(
		tr.TestConfig.ChainConfigs[action.Chain].BinaryName,
		"tx", "gov", "submit-legacy-proposal", "consumer-removal",
		"/temp-proposal.json",
		`--from`, `validator`+fmt.Sprint(action.From),
		`--chain-id`, string(tr.TestConfig.ChainConfigs[action.Chain].ChainId),
		`--home`, tr.getValidatorHome(action.Chain, action.From),
		`--node`, tr.getValidatorNode(action.Chain, action.From),
		`--gas`, "900000",
		`--keyring-backend`, `test`,
		`-o`, `json`,
		`-y`,
	).CombinedOutput()
	if err != nil {
		log.Fatalf("error submitting consumer-removal proposal %s\n%s\n",
			err, string(bz))
	}

	// wait for inclusion in a block -> '--broadcast-mode block' is deprecated
	tr.waitForTx(ChainID("provi"), bz, 20*time.Second)
}

func (tr *Chain) StartConsumerChain(
	action StartConsumerChainAction,
	verbose bool,
) {
	fmt.Println("Starting consumer chain ", action.ConsumerChain)
	consumerGenesis := ".app_state.ccvconsumer = " + tr.getConsumerGenesis(action.ProviderChain, action.ConsumerChain)
	consumerGenesisChanges := tr.TestConfig.ChainConfigs[action.ConsumerChain].GenesisChanges
	if consumerGenesisChanges != "" {
		consumerGenesis = consumerGenesis + " | " + consumerGenesisChanges
	}
	if action.GenesisChanges != "" {
		consumerGenesis = consumerGenesis + " | " + action.GenesisChanges
	}

	tr.StartChain(StartChainAction{
		Chain:          action.ConsumerChain,
		Validators:     action.Validators,
		GenesisChanges: consumerGenesis,
		IsConsumer:     true,
	}, verbose)
}

// Get consumer genesis from provider
func (tr *Chain) getConsumerGenesis(providerChain, consumerChain ChainID) string {
	fmt.Println("Exporting consumer genesis from provider")
	providerBinaryName := tr.TestConfig.ChainConfigs[providerChain].BinaryName

	cmd := tr.Target.ExecCommand(
		providerBinaryName,

		"query", "provider", "consumer-genesis",
		string(tr.TestConfig.ChainConfigs[consumerChain].ChainId),

		`--node`, tr.Target.GetQueryNode(providerChain),
		`-o`, `json`,
	)

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	if tr.TestConfig.TransformGenesis || needsGenesisTransform(*tr.TestConfig) {
		return string(tr.transformConsumerGenesis(consumerChain, bz))
	} else {
		fmt.Println("No genesis transformation performed")
	}
	return string(bz)
}

// needsGenesisTransform tries to identify if a genesis transformation should be performed
func needsGenesisTransform(cfg TestConfig) bool {
	// no genesis transformation needed for same versions
	if cfg.ConsumerVersion == cfg.ProviderVersion {
		return false
	}

	// use v4.0.0 (after genesis transform breakages) for the checks if 'latest' is used
	consumerVersion := cfg.ConsumerVersion
	if cfg.ConsumerVersion == VLatest {
		consumerVersion = V400
	}
	providerVersion := cfg.ProviderVersion
	if cfg.ProviderVersion == VLatest {
		providerVersion = V400
	}

	if !semver.IsValid(consumerVersion) || !semver.IsValid(providerVersion) {
		fmt.Printf("unable to identify the need for genesis transformation: invalid sem-version: consumer='%s', provider='%s'",
			consumerVersion, providerVersion)
		return false
	}

	breakages := []string{V300, V330, V400}
	for _, breakage := range breakages {
		if (semver.Compare(consumerVersion, breakage) < 0 && semver.Compare(providerVersion, breakage) >= 0) ||
			(semver.Compare(providerVersion, breakage) < 0 && semver.Compare(consumerVersion, breakage) >= 0) {
			fmt.Println("genesis transformation needed for versions:", providerVersion, consumerVersion)
			return true
		}
	}
	fmt.Println("NO genesis transformation needed for versions:", providerVersion, consumerVersion)
	return false
}

// getTransformParameter identifies the needed transformation parameter for current `transformGenesis` implementation
// based on consumer and provider versions.
func getTransformParameter(consumerVersion string) (string, error) {
	switch consumerVersion {
	case "":
		// For "" (default: local workspace) use HEAD as reference point
		consumerVersion = "HEAD"
	case VLatest:
		// For 'latest' originated from latest-image use "origin/main" as ref point
		consumerVersion = "origin/main"
	}

	// Hash of breakage due to preHashKey release in version 2.x
	// ics23/go v.0.10.0 adding 'prehash_key_before_comparison' in ProofSpec
	breakage_prehash := "d4dde74b062c2fded0d3b3dbef4b3b0229e317f3" // first released in v3.2.0-consumer

	// breakage 2: split of genesis
	breakage_splitgenesisMain := "946f6ec626d3de3fe2e00cbb386ccf9c2f05d94d"
	breakage_splitgenesisV33x := "1d2641a3b2ba706ae0a307d9019b48c62d86133b"

	// breakage 3: split of genesis + delay_period
	breakage_retry_delay := "88499b7c650ea0fb2c448af2b182ad5fee94d795"

	// mapping of the accepted parameter values of the `genesis transform` command
	// to the related git refs introducing a breakage
	transformParams := map[string][]string{
		"v2.x":   {breakage_prehash},
		"v3.3.x": {breakage_splitgenesisMain, breakage_splitgenesisV33x},
		"v4.x":   {breakage_retry_delay},
	}

	// set default consumer target version to "v4.x"
	// and iterate in order of breakage history [oldest first] to identify
	// the "--to" target for consumer version used
	targetVersion := "v4.x"
	keys := make([]string, 0, len(transformParams))
	for k := range transformParams {
		keys = append(keys, k)
	}
	sort.Slice(keys, func(k, l int) bool { return keys[k] < keys[l] })

	for _, version := range keys {
		for _, breakageHash := range transformParams[version] {
			// Check if the 'breakage' is an ancestor of the 'consumerVersion'
			//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments
			cmd := exec.Command("git", "merge-base", "--is-ancestor", breakageHash, consumerVersion)
			fmt.Println("running ", cmd)
			out, err := cmd.CombinedOutput()
			if err == nil {
				// breakage is already part of the consumer version -> goto next breakage
				fmt.Println(" consumer >= breakage ", transformParams[version], " ... going to next one")
				targetVersion = version
				break
			}

			if rc, ok := err.(*exec.ExitError); ok {
				if rc.ExitCode() != 1 {
					return "", fmt.Errorf("error identifying transform parameter '%v': %s", err, string(out))
				}
				// not an ancestor -- ignore this breakage
				fmt.Println("breakage :", transformParams[version], " is not an ancestor of version ", version)
				continue
			}
			return "", fmt.Errorf("unexpected error when running '%v': %v", cmd, err) // unable to get return code
		}
	}
	// consumer > latest known breakage (use default target version 'v4.x')
	return fmt.Sprintf("--to=%s", targetVersion), nil
}

// Transform consumer genesis content from older version
func (tr *Chain) transformConsumerGenesis(consumerChain ChainID, genesis []byte) []byte {
	fmt.Println("Transforming consumer genesis")

	fileName := "consumer_genesis.json"
	file, err := os.CreateTemp("", fileName)
	if err != nil {
		panic(fmt.Sprintf("failed writing ccv consumer file : %v", err))
	}
	defer file.Close()
	err = os.WriteFile(file.Name(), genesis, 0o600)
	if err != nil {
		log.Panicf("Failed writing consumer genesis to file: %v", err)
	}

	containerInstance := tr.TestConfig.ContainerConfig.ContainerName
	targetFile := fmt.Sprintf("/tmp/%s", fileName)
	sourceFile := file.Name()
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "cp", sourceFile,
		fmt.Sprintf("%s:%s", containerInstance, targetFile))
	genesis, err = cmd.CombinedOutput()
	if err != nil {
		log.Panic(err, "\n", string(genesis))
	}

	// check if genesis transform supports --to target
	bz, err := tr.Target.ExecCommand(
		"interchain-security-transformer",
		"genesis", "transform", "--to").CombinedOutput()
	if err != nil && !strings.Contains(string(bz), "unknown flag: --to") {
		targetVersion, err := getTransformParameter(tr.TestConfig.ConsumerVersion)
		if err != nil {
			log.Panic("Failed getting genesis transformation parameter: ", err)
		}
		cmd = tr.Target.ExecCommand(
			"interchain-security-transformer",
			"genesis", "transform", targetVersion, targetFile)
	} else {
		cmd = tr.Target.ExecCommand(
			"interchain-security-transformer",
			"genesis", "transform", targetFile)
	}

	result, err := cmd.CombinedOutput()
	if err != nil {
		log.Panic(err, "CCV consumer genesis transformation failed: %s", string(result))
	}
	return result
}

type AddChainToRelayerAction struct {
	Chain      ChainID
	Validator  ValidatorID
	IsConsumer bool
}

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

func (tr Chain) addChainToRelayer(
	action AddChainToRelayerAction,
	verbose bool,
) {
	if !tr.TestConfig.UseGorelayer {
		tr.addChainToHermes(action, verbose)
	} else {
		tr.addChainToGorelayer(action, verbose)
	}
}

func (tr Chain) addChainToGorelayer(
	action AddChainToRelayerAction,
	verbose bool,
) {
	queryNodeIP := tr.Target.GetQueryNodeIP(action.Chain)
	ChainId := tr.TestConfig.ChainConfigs[action.Chain].ChainId
	rpcAddr := "http://" + queryNodeIP + ":26658"

	chainConfig := fmt.Sprintf(gorelayerChainConfigTemplate,
		ChainId,
		rpcAddr,
		tr.TestConfig.ChainConfigs[action.Chain].AccountPrefix,
	)

	bz, err := tr.Target.ExecCommand(
		"rly", "config", "init").CombinedOutput()
	if err != nil && !strings.Contains(string(bz), "config already exists") {
		log.Fatal(err, "\n", string(bz))
	}

	chainConfigFileName := fmt.Sprintf("/root/%s_config.json", ChainId)

	bashCommand := fmt.Sprintf(`echo '%s' >> %s`, chainConfig, chainConfigFileName)
	bz, err = tr.Target.ExecCommand("bash", "-c",
		bashCommand).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	addChainCommand := tr.Target.ExecCommand("rly", "chains", "add", "--file", chainConfigFileName, string(ChainId))
	e2e.ExecuteCommand(addChainCommand, "add chain", verbose)

	keyRestoreCommand := tr.Target.ExecCommand("rly", "keys", "restore", string(ChainId), "default", tr.TestConfig.ValidatorConfigs[action.Validator].Mnemonic)
	e2e.ExecuteCommand(keyRestoreCommand, "restore keys", verbose)
}

func (tr Chain) addChainToHermes(
	action AddChainToRelayerAction,
	verbose bool,
) {
	bz, err := tr.Target.ExecCommand("bash", "-c", "hermes", "version").CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n error getting hermes version", string(bz))
	}
	re := regexp.MustCompile(`hermes\s+(\d+.\d+.\d+)`)
	match := re.FindStringSubmatch(string(bz))
	if match == nil {
		log.Fatalln("error identifying hermes version from", string(bz))
	}

	hermesVersion := match[1]
	queryNodeIP := tr.Target.GetQueryNodeIP(action.Chain)
	hermesConfig := e2e.GetHermesConfig(hermesVersion, queryNodeIP, tr.TestConfig.ChainConfigs[action.Chain], action.IsConsumer)

	bashCommand := fmt.Sprintf(`echo '%s' >> %s`, hermesConfig, "/root/.hermes/config.toml")

	bz, err = tr.Target.ExecCommand("bash", "-c", bashCommand).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// Save mnemonic to file within container
	var mnemonic string
	if tr.TestConfig.ValidatorConfigs[action.Validator].UseConsumerKey && action.IsConsumer {
		mnemonic = tr.TestConfig.ValidatorConfigs[action.Validator].ConsumerMnemonic
	} else {
		mnemonic = tr.TestConfig.ValidatorConfigs[action.Validator].Mnemonic
	}

	saveMnemonicCommand := fmt.Sprintf(`echo '%s' > %s`, mnemonic, "/root/.hermes/mnemonic.txt")
	fmt.Println("Add to hermes", action.Validator)
	bz, err = tr.Target.ExecCommand("bash", "-c", saveMnemonicCommand).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	bz, err = tr.Target.ExecCommand("hermes",
		"keys", "add",
		"--chain", string(tr.TestConfig.ChainConfigs[action.Chain].ChainId),
		"--mnemonic-file", "/root/.hermes/mnemonic.txt",
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

type CreateIbcClientsAction struct {
	ChainA ChainID
	ChainB ChainID
}

func (tr Chain) DelegateTokens(
	action DelegateTokensAction,
	verbose bool,
) {
	toValCfg := tr.TestConfig.ValidatorConfigs[action.To]
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

	cmd := tr.Target.ExecCommand(tr.TestConfig.ChainConfigs[action.Chain].BinaryName,

		"tx", "staking", "delegate",
		validatorAddress,
		fmt.Sprint(action.Amount)+`stake`,
		`--from`, `validator`+fmt.Sprint(action.From),
		`--chain-id`, string(tr.TestConfig.ChainConfigs[action.Chain].ChainId),
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

func (tr Chain) UnbondTokens(
	action UnbondTokensAction,
	verbose bool,
) {
	unbondFromValCfg := tr.TestConfig.ValidatorConfigs[action.UnbondFrom]
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

	cmd := tr.Target.ExecCommand(tr.TestConfig.ChainConfigs[action.Chain].BinaryName,

		"tx", "staking", "unbond",
		validatorAddress,
		fmt.Sprint(action.Amount)+`stake`,

		`--from`, `validator`+fmt.Sprint(action.Sender),
		`--chain-id`, string(tr.TestConfig.ChainConfigs[action.Chain].ChainId),
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

// takes a string representation of the private key like
// `{"address":"DF090A4880B54CD57B2A79E64D9E969BD7514B09","pub_key":{"type":"tendermint/PubKeyEd25519","value":"ujY14AgopV907IYgPAk/5x8c9267S4fQf89nyeCPTes="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"TRJgf7lkTjs/sj43pyweEOanyV7H7fhnVivOi0A4yjW6NjXgCCilX3TshiA8CT/nHxz3brtLh9B/z2fJ4I9N6w=="}}`
// and returns the value of the "address" field
func (tr Chain) getValidatorKeyAddressFromString(keystring string) string {
	var key struct {
		Address string `json:"address"`
	}
	err := json.Unmarshal([]byte(keystring), &key)
	if err != nil {
		log.Fatal(err)
	}
	return key.Address
}

func (tr Chain) GetValidatorPrivateKeyAddress(chain ChainID, validator ValidatorID) string {
	var validatorPrivateKeyAddress string
	if chain == ChainID("provi") {
		validatorPrivateKeyAddress = tr.getValidatorKeyAddressFromString(tr.TestConfig.ValidatorConfigs[validator].PrivValidatorKey)
	} else {
		var valAddressString string
		if tr.TestConfig.ValidatorConfigs[validator].UseConsumerKey {
			valAddressString = tr.TestConfig.ValidatorConfigs[validator].ConsumerPrivValidatorKey
		} else {
			valAddressString = tr.TestConfig.ValidatorConfigs[validator].PrivValidatorKey
		}
		validatorPrivateKeyAddress = tr.getValidatorKeyAddressFromString(valAddressString)
	}
	return validatorPrivateKeyAddress
}

func (tr Chain) AssignConsumerPubKey(action e2e.AssignConsumerPubKeyAction, verbose bool) {
	valCfg := tr.TestConfig.ValidatorConfigs[action.Validator]

	// Unfortunately, --gas auto does not work with CometMock. so when using CometMock, just use --gas 9000000 then
	if tr.TestConfig.UseCometmock {
		gas = "9000000"
	}
	assignKey := fmt.Sprintf(
		`%s tx provider assign-consensus-key %s '%s' --from validator%s --chain-id %s --home %s --node %s --gas %s --keyring-backend test -y -o json`,
		tr.TestConfig.ChainConfigs[ChainID("provi")].BinaryName,
		string(tr.TestConfig.ChainConfigs[action.Chain].ChainId),
		action.ConsumerPubkey,
		action.Validator,
		tr.TestConfig.ChainConfigs[ChainID("provi")].ChainId,
		tr.getValidatorHome(ChainID("provi"), action.Validator),
		tr.getValidatorNode(ChainID("provi"), action.Validator),
		gas,
	)

	cmd := tr.Target.ExecCommand(
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

	if action.ExpectError && !tr.TestConfig.UseCometmock { // error report only works with --gas auto, which does not work with CometMock, so ignore
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
		isConsumer := tr.TestConfig.ChainConfigs[action.Chain].BinaryName != "interchain-security-pd"
		reconfigureScript := tr.Target.GetTestScriptPath(isConsumer, "reconfigure-node.sh")
		configureNodeCmd := tr.Target.ExecCommand("/bin/bash",
			reconfigureScript, tr.TestConfig.ChainConfigs[action.Chain].BinaryName,
			string(action.Validator), string(action.Chain),
			tr.TestConfig.ChainConfigs[action.Chain].IpPrefix, valCfg.IpSuffix,
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
		tr.TestConfig.ValidatorConfigs[action.Validator] = valCfg
	}

	// wait for inclusion in a block -> '--broadcast-mode block' is deprecated
	tr.waitBlocks(ChainID("provi"), 2, 30*time.Second)
}

// GetPathNameForGorelayer returns the name of the path between two given chains used by Gorelayer.
// Since paths are bidirectional, we need either chain to be able to be provided as first or second argument
// and still return the same name, so we sort the chain names alphabetically.
func (tr Chain) GetPathNameForGorelayer(chainA, chainB ChainID) string {
	var pathName string
	if string(chainA) < string(chainB) {
		pathName = string(chainA) + "-" + string(chainB)
	} else {
		pathName = string(chainB) + "-" + string(chainA)
	}

	return pathName
}

// WaitTime waits for the given duration.
// To make sure that the new timestamp is visible on-chain, it also waits until at least one block has been
// produced on each chain after waiting.
// The CometMock version of this takes a pointer to the TestConfig as it needs to manipulate
// information in the testrun that stores how much each chain has waited, to keep times in sync.
// Be careful that all functions calling WaitTime should therefore also take a pointer to the TestConfig.
func (tr *Chain) WaitTime(duration time.Duration) {
	if !tr.TestConfig.UseCometmock {
		time.Sleep(duration)
	} else {
		tr.TestConfig.TimeOffset += duration
		for chain, running := range tr.TestConfig.RunningChains {
			if !running {
				continue
			}
			tr.AdvanceTimeForChain(chain, duration)
			tr.waitBlocks(chain, 1, 2*time.Second)
		}
	}
}

func (tr Chain) AdvanceTimeForChain(chain ChainID, duration time.Duration) {
	// cometmock avoids sleeping, and instead advances time for all chains
	method := "advance_time"
	params := fmt.Sprintf(`{"duration_in_seconds": "%d"}`, int(math.Ceil(duration.Seconds())))

	address := tr.Target.GetQueryNodeRPCAddress(chain)

	tr.curlJsonRPCRequest(method, params, address)

	// wait for 1 block of the chain to get a block with the advanced timestamp
	tr.waitBlocks(chain, 1, time.Minute)
}

func (tr Chain) getValidatorNode(chain ChainID, validator ValidatorID) string {
	// for CometMock, validatorNodes are all the same address as the query node (which is CometMocks address)
	if tr.TestConfig.UseCometmock {
		return tr.Target.GetQueryNode(chain)
	}

	return "tcp://" + tr.getValidatorIP(chain, validator) + ":26658"
}

func (tr Chain) getValidatorIP(chain ChainID, validator ValidatorID) string {
	return tr.TestConfig.ChainConfigs[chain].IpPrefix + "." + tr.TestConfig.ValidatorConfigs[validator].IpSuffix
}

func (tr Chain) getValidatorHome(chain ChainID, validator ValidatorID) string {
	return `/` + string(chain) + `/validator` + fmt.Sprint(validator)
}

func (tr Chain) curlJsonRPCRequest(method, params, address string) {
	cmd_template := `curl -H 'Content-Type: application/json' -H 'Accept:application/json' --data '{"jsonrpc":"2.0","method":"%s","params":%s,"id":1}' %s`

	cmd := tr.Target.ExecCommand("bash", "-c", fmt.Sprintf(cmd_template, method, params, address))

	verbosity := false
	e2e.ExecuteCommand(cmd, "curlJsonRPCRequest", verbosity)
}

// waitForTx waits until a transaction is seen in a block or panics if a timeout occurs
func (tr Chain) waitForTx(chain ChainID, txResponse []byte, timeout time.Duration) e2e.TxResponse {
	// remove any gas estimate as when command is run with gas=auto the output contains gas estimation mixed with json output
	re := regexp.MustCompile("gas estimate: [0-9]+")
	txResponse = re.ReplaceAll(txResponse, []byte{})

	// check transaction
	response := e2e.GetTxResponse(txResponse)
	if response.Code != 0 {
		log.Fatalf("sending transaction failed with error code %d, Log:'%s'", response.Code, response.RawLog)
	}

	// wait for the transaction
	start := time.Now()
	for {
		res, err := tr.Target.QueryTransaction(chain, response.TxHash)
		if err == nil {
			return e2e.GetTxResponse(res)
		}
		if time.Since(start) > timeout {
			log.Printf("query transaction failed with err=%s, resp=%s", err.Error(), res)
			panic(fmt.Sprintf("\n\nwaitForTx on chain '%s' has timed out after: %s\n\n", chain, timeout))
		}
	}
}

func (tr Chain) waitBlocks(chain ChainID, blocks uint, timeout time.Duration) {
	if tr.TestConfig.UseCometmock {
		// call advance_blocks method on cometmock
		// curl -H 'Content-Type: application/json' -H 'Accept:application/json' --data '{"jsonrpc":"2.0","method":"advance_blocks","params":{"num_blocks": "36000000"},"id":1}' 127.0.0.1:22331
		tcpAddress := tr.Target.GetQueryNodeRPCAddress(chain)
		method := "advance_blocks"
		params := fmt.Sprintf(`{"num_blocks": "%d"}`, blocks)

		tr.curlJsonRPCRequest(method, params, tcpAddress)
		return
	}
	startBlock := tr.Target.GetBlockHeight(chain)

	start := time.Now()
	for {
		thisBlock := tr.Target.GetBlockHeight(chain)
		if thisBlock >= startBlock+blocks {
			return
		}
		if time.Since(start) > timeout {
			panic(fmt.Sprintf("\n\n\nwaitBlocks method on chain '%s' has timed out after: %s\n\n", chain, timeout))
		}
		time.Sleep(time.Second)
	}
}
