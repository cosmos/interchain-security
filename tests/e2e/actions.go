package main

import (
	"bufio"
	"encoding/base64"
	"encoding/json"
	"fmt"
	"log"
	"math"
	"os"
	"os/exec"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"sync"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	"github.com/tidwall/gjson"
	"golang.org/x/mod/semver"

	e2e "github.com/cosmos/interchain-security/v5/tests/e2e/testlib"
	"github.com/cosmos/interchain-security/v5/x/ccv/provider/client"
	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
	ccvtypes "github.com/cosmos/interchain-security/v5/x/ccv/types"
)

const (
	done = "done!!!!!!!!"

	VLatest = "latest"
	V400    = "v4.0.0"
	V330    = "v3.3.0"
	V300    = "v3.0.0"
)

type SendTokensAction struct {
	Chain  ChainID
	From   ValidatorID
	To     ValidatorID
	Amount uint
}

func (tr Chain) sendTokens(
	action SendTokensAction,
	verbose bool,
) {
	fromValCfg := tr.testConfig.validatorConfigs[action.From]
	toValCfg := tr.testConfig.validatorConfigs[action.To]
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

	binaryName := tr.testConfig.chainConfigs[action.Chain].BinaryName
	cmd := tr.target.ExecCommand(binaryName,

		"tx", "bank", "send",
		fromAddress,
		toAddress,
		fmt.Sprint(action.Amount)+`stake`,

		`--chain-id`, string(tr.testConfig.chainConfigs[action.Chain].ChainId),
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

func (tr *Chain) startChain(
	action StartChainAction,
	verbose bool,
) {
	chainConfig := tr.testConfig.chainConfigs[action.Chain]
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
			Mnemonic:         tr.testConfig.validatorConfigs[val.Id].Mnemonic,
			NodeKey:          tr.testConfig.validatorConfigs[val.Id].NodeKey,
			ValId:            fmt.Sprint(val.Id),
			PrivValidatorKey: tr.testConfig.validatorConfigs[val.Id].PrivValidatorKey,
			Allocation:       fmt.Sprint(val.Allocation) + "stake",
			Stake:            fmt.Sprint(val.Stake) + "stake",
			IpSuffix:         tr.testConfig.validatorConfigs[val.Id].IpSuffix,

			ConsumerMnemonic:         tr.testConfig.validatorConfigs[val.Id].ConsumerMnemonic,
			ConsumerPrivValidatorKey: tr.testConfig.validatorConfigs[val.Id].ConsumerPrivValidatorKey,
			// if true node will be started with consumer key for each consumer chain
			StartWithConsumerKey: tr.testConfig.validatorConfigs[val.Id].UseConsumerKey,
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
	if tr.testConfig.useCometmock {
		cometmockArg = "true"
	} else {
		cometmockArg = "false"
	}

	startChainScript := tr.target.GetTestScriptPath(action.IsConsumer, "start-chain.sh")
	cmd := tr.target.ExecCommand("/bin/bash",
		startChainScript, chainConfig.BinaryName, string(vals),
		string(chainConfig.ChainId), chainConfig.IpPrefix, genesisChanges,
		fmt.Sprint(action.IsConsumer),
		// override config/config.toml for each node on chain
		// usually timeout_commit and peer_gossip_sleep_duration are changed to vary the test run duration
		// lower timeout_commit means the blocks are produced faster making the test run shorter
		// with short timeout_commit (eg. timeout_commit = 1s) some nodes may miss blocks causing the test run to fail
		tr.testConfig.tendermintConfigOverride,
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
	}, verbose)

	// store the fact that we started the chain
	tr.testConfig.runningChains[action.Chain] = true
	fmt.Println("Started chain", action.Chain)
	if tr.testConfig.timeOffset != 0 {
		// advance time for this chain so that it is in sync with the rest of the network
		tr.AdvanceTimeForChain(action.Chain, tr.testConfig.timeOffset)
	}
}

type SubmitTextProposalAction struct {
	Chain       ChainID
	From        ValidatorID
	Deposit     uint
	Title       string
	Description string
}

func (tr Chain) submitTextProposal(
	action SubmitTextProposalAction,
	verbose bool,
) {
	// TEXT PROPOSAL
	bz, err := tr.target.ExecCommand(
		tr.testConfig.chainConfigs[action.Chain].BinaryName,
		"tx", "gov", "submit-legacy-proposal",
		`--title`, action.Title,
		`--description`, action.Description,
		`--deposit`, fmt.Sprint(action.Deposit)+`stake`,
		`--from`, `validator`+fmt.Sprint(action.From),
		`--chain-id`, string(tr.testConfig.chainConfigs[action.Chain].ChainId),
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
	TopN                uint32
	ValidatorsPowerCap  uint32
	ValidatorSetCap     uint32
	Allowlist           []string
	Denylist            []string
	MinStake            uint64
	AllowInactiveVals   bool
}

func (tr Chain) submitConsumerAdditionProposal(
	action SubmitConsumerAdditionProposalAction,
	verbose bool,
) {
	spawnTime := tr.testConfig.containerConfig.Now.Add(time.Duration(action.SpawnTime) * time.Millisecond)
	params := ccvtypes.DefaultParams()
	template := `
	{
 "messages": [
  {
   "@type": "/interchain_security.ccv.provider.v1.MsgConsumerAddition",
   "chain_id": "%s",
   "initial_height": {
    "revision_number": "%d",
    "revision_height": "%d"
   },
   "genesis_hash": "%s",
   "binary_hash": "%s",
   "spawn_time": "%s",
   "unbonding_period": "%s",
   "ccv_timeout_period": "%s",
   "transfer_timeout_period": "%s",
   "consumer_redistribution_fraction": "%s",
   "blocks_per_distribution_transmission": "%d",
   "historical_entries": "%d",
   "distribution_transmission_channel": "%s",
   "top_N": %d,
   "validators_power_cap": %d,
   "validator_set_cap": %d,
   "allowlist": %s,
   "denylist": %s,
   "authority": "cosmos10d07y265gmmuvt4z0w9aw880jnsr700j6zn9kn"
  }
 ],
"metadata": "ipfs://CID",
"deposit": "%dstake",
"title": "Propose the addition of a new chain",
"summary": "Gonna be a great chain",
"expedited": false
}`
	jsonStr := fmt.Sprintf(template,
		string(tr.testConfig.chainConfigs[action.ConsumerChain].ChainId),
		action.InitialHeight.RevisionNumber,
		action.InitialHeight.RevisionHeight,
		base64.StdEncoding.EncodeToString([]byte("gen_hash")),
		base64.StdEncoding.EncodeToString([]byte("bin_hash")),
		spawnTime.Local().Format(time.RFC3339Nano),
		params.UnbondingPeriod,
		params.CcvTimeoutPeriod,
		params.TransferTimeoutPeriod,
		params.ConsumerRedistributionFraction,
		params.BlocksPerDistributionTransmission,
		params.HistoricalEntries,
		action.DistributionChannel,
		action.TopN,
		action.ValidatorsPowerCap,
		action.ValidatorSetCap,
		action.Allowlist,
		action.Denylist,
		action.Deposit)

	//#nosec G204 -- bypass unsafe quoting warning (no production code)
	proposalFile := "/consumer-addition.proposal"
	bz, err := tr.target.ExecCommand(
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, jsonStr, proposalFile),
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// CONSUMER ADDITION PROPOSAL
	cmd := tr.target.ExecCommand(
		tr.testConfig.chainConfigs[action.Chain].BinaryName,
		"tx", "gov", "submit-proposal", proposalFile,
		`--from`, `validator`+fmt.Sprint(action.From),
		`--chain-id`, string(tr.testConfig.chainConfigs[action.Chain].ChainId),
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
		log.Fatal("submit-proposal failed:", err, "\n", string(bz))
	}

	if verbose {
		fmt.Println("submitConsumerAdditionProposal output:", string(bz))
	}

	// wait for inclusion in a block -> '--broadcast-mode block' is deprecated
	tr.waitBlocks(action.Chain, 2, 10*time.Second)
}

func (tr Chain) submitConsumerAdditionLegacyProposal(
	action SubmitConsumerAdditionProposalAction,
	verbose bool,
) {
	spawnTime := tr.testConfig.containerConfig.Now.Add(time.Duration(action.SpawnTime) * time.Millisecond)
	params := ccvtypes.DefaultParams()
	prop := client.ConsumerAdditionProposalJSON{
		Title:                             "Propose the addition of a new chain",
		Summary:                           "Gonna be a great chain",
		ChainId:                           string(tr.testConfig.chainConfigs[action.ConsumerChain].ChainId),
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
		MinStake:                          action.MinStake,
		AllowInactiveVals:                 action.AllowInactiveVals,
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
	cmd := tr.target.ExecCommand(
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, jsonStr, "/temp-proposal.json"))
	bz, err = cmd.CombinedOutput()
	if verbose {
		log.Println("submitConsumerAdditionProposal cmd: ", cmd.String())
	}

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// CONSUMER ADDITION PROPOSAL
	cmd = tr.target.ExecCommand(
		tr.testConfig.chainConfigs[action.Chain].BinaryName,
		"tx", "gov", "submit-legacy-proposal", "consumer-addition", "/temp-proposal.json",
		`--from`, `validator`+fmt.Sprint(action.From),
		`--chain-id`, string(tr.testConfig.chainConfigs[action.Chain].ChainId),
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

type SubmitConsumerRemovalProposalAction struct {
	Chain          ChainID
	From           ValidatorID
	Deposit        uint
	ConsumerChain  ChainID
	StopTimeOffset time.Duration // offset from time.Now()
}

func (tr Chain) submitConsumerRemovalProposal(
	action SubmitConsumerRemovalProposalAction,
	verbose bool,
) {
	template := `
	{
		"messages": [
		 {
		  "@type": "/interchain_security.ccv.provider.v1.MsgConsumerRemoval",
		  "chain_id": "%s",
		  "stop_time": "%s",
		  "authority": "cosmos10d07y265gmmuvt4z0w9aw880jnsr700j6zn9kn"
		 }
		],
		"metadata": "ipfs://CID",
		"deposit": "%dstake",
		"title": "%s",
		"summary": "It was a great chain",
		"expedited": false
	   }
`
	title := fmt.Sprintf("Stop the %v chain", action.ConsumerChain)
	stopTime := tr.testConfig.containerConfig.Now.Add(action.StopTimeOffset).Format(time.RFC3339Nano)

	jsonStr := fmt.Sprintf(template,
		string(tr.testConfig.chainConfigs[action.ConsumerChain].ChainId),
		stopTime,
		action.Deposit,
		title)

	// #nosec G204 -- bypass unsafe quoting warning (no production code)
	proposalFile := "/consumer-removal.proposal"
	bz, err := tr.target.ExecCommand(
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, jsonStr, proposalFile),
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// CONSUMER REMOVAL PROPOSAL
	cmd := tr.target.ExecCommand(
		tr.testConfig.chainConfigs[action.Chain].BinaryName,
		"tx", "gov", "submit-proposal", proposalFile,
		`--from`, `validator`+fmt.Sprint(action.From),
		`--chain-id`, string(tr.testConfig.chainConfigs[action.Chain].ChainId),
		`--home`, tr.getValidatorHome(action.Chain, action.From),
		`--gas`, `900000`,
		`--node`, tr.getValidatorNode(action.Chain, action.From),
		`--keyring-backend`, `test`,
		`-y`,
	)

	if verbose {
		fmt.Println("submitConsumerRemovalProposal cmd:", cmd.String())
		fmt.Println("submitConsumerRemovalProposal json:", jsonStr)
	}
	bz, err = cmd.CombinedOutput()
	if err != nil {
		log.Fatal("submit consumer removal proposal failed:", err, "\n", string(bz))
	}

	if verbose {
		fmt.Println("submitConsumerRemovalProposal output:", string(bz))
	}

	// wait for inclusion in a block -> '--broadcast-mode block' is deprecated
	tr.waitBlocks(ChainID("provi"), 2, 20*time.Second)
}

func (tr Chain) submitConsumerRemovalLegacyProposal(
	action SubmitConsumerRemovalProposalAction,
	verbose bool,
) {
	stopTime := tr.testConfig.containerConfig.Now.Add(action.StopTimeOffset)
	prop := client.ConsumerRemovalProposalJSON{
		Title:    fmt.Sprintf("Stop the %v chain", action.ConsumerChain),
		Summary:  "It was a great chain",
		ChainId:  string(tr.testConfig.chainConfigs[action.ConsumerChain].ChainId),
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

	bz, err = tr.target.ExecCommand(
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, jsonStr, "/temp-proposal.json")).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	bz, err = tr.target.ExecCommand(
		tr.testConfig.chainConfigs[action.Chain].BinaryName,
		"tx", "gov", "submit-legacy-proposal", "consumer-removal",
		"/temp-proposal.json",
		`--from`, `validator`+fmt.Sprint(action.From),
		`--chain-id`, string(tr.testConfig.chainConfigs[action.Chain].ChainId),
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

type SubmitConsumerModificationProposalAction struct {
	Chain              ChainID
	From               ValidatorID
	Deposit            uint
	ConsumerChain      ChainID
	TopN               uint32
	ValidatorsPowerCap uint32
	ValidatorSetCap    uint32
	Allowlist          []string
	Denylist           []string
}

func (tr Chain) submitConsumerModificationProposal(
	action SubmitConsumerModificationProposalAction,
	verbose bool,
) {

	template := `

{
"messages": [
  {
    "@type": "/interchain_security.ccv.provider.v1.MsgConsumerModification",
	"title": "Propose the modification of the PSS parameters of a chain",
	"description": "description of the consumer modification proposal",
	"chain_id": "%s",
	"top_N": %d,
	"validators_power_cap": %d,
	"validator_set_cap": %d,
	"allowlist": %s,
	"denylist": %s,
    "authority": "cosmos10d07y265gmmuvt4z0w9aw880jnsr700j6zn9kn",
    "min_stake": "0",
    "allow_inactive_vals": false
  }
 ],
"metadata": "ipfs://CID",
"deposit": "%sstake",
"title": "Propose the modification of the PSS parameters of a chain",
"summary": "summary of a modification proposal",
"expedited": false
 }
`

	jsonStr := fmt.Sprintf(template,
		string(tr.testConfig.chainConfigs[action.ConsumerChain].ChainId),
		action.TopN,
		action.ValidatorsPowerCap,
		action.ValidatorSetCap,
		action.Allowlist,
		action.Denylist,
		action.Deposit,
	)

	// #nosec G204 -- bypass unsafe quoting warning (no production code)
	proposalFile := "/consumer-mod.proposal"
	bz, err := tr.target.ExecCommand(
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, jsonStr, proposalFile),
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// CONSUMER MODIFICATION PROPOSAL
	cmd := tr.target.ExecCommand(
		tr.testConfig.chainConfigs[action.Chain].BinaryName,
		"tx", "gov", "submit-proposal", proposalFile,
		`--from`, `validator`+fmt.Sprint(action.From),
		`--chain-id`, string(tr.testConfig.chainConfigs[action.Chain].ChainId),
		`--home`, tr.getValidatorHome(action.Chain, action.From),
		`--gas`, `900000`,
		`--node`, tr.getValidatorNode(action.Chain, action.From),
		`--keyring-backend`, `test`,
		`-y`,
	)

	if verbose {
		fmt.Println("submitConsumerModificationProposal cmd:", cmd.String())
		fmt.Println("submitConsumerModificationProposal json:", jsonStr)
	}
	bz, err = cmd.CombinedOutput()
	if err != nil {
		log.Fatal("submit consumer modification proposal failed:", err, "\n", string(bz))
	}

	if verbose {
		fmt.Println("submitConsumerModificationProposal output:", string(bz))
	}

	// wait for inclusion in a block -> '--broadcast-mode block' is deprecated
	tr.waitBlocks(ChainID("provi"), 2, 10*time.Second)
}

func (tr Chain) submitConsumerModificationLegacyProposal(
	action SubmitConsumerModificationProposalAction,
	verbose bool,
) {
	prop := client.ConsumerModificationProposalJSON{
		Title:              "Propose the modification of the PSS parameters of a chain",
		Summary:            "summary of a modification proposal",
		ChainId:            string(tr.testConfig.chainConfigs[action.ConsumerChain].ChainId),
		Deposit:            fmt.Sprint(action.Deposit) + `stake`,
		TopN:               action.TopN,
		ValidatorsPowerCap: action.ValidatorsPowerCap,
		ValidatorSetCap:    action.ValidatorSetCap,
		Allowlist:          action.Allowlist,
		Denylist:           action.Denylist,
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
	bz, err = tr.target.ExecCommand(
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, jsonStr, "/temp-proposal.json"),
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// CONSUMER MODIFICATION PROPOSAL
	cmd := tr.target.ExecCommand(
		tr.testConfig.chainConfigs[action.Chain].BinaryName,
		"tx", "gov", "submit-legacy-proposal", "consumer-modification", "/temp-proposal.json",
		`--from`, `validator`+fmt.Sprint(action.From),
		`--chain-id`, string(tr.testConfig.chainConfigs[action.Chain].ChainId),
		`--home`, tr.getValidatorHome(action.Chain, action.From),
		`--gas`, `900000`,
		`--node`, tr.getValidatorNode(action.Chain, action.From),
		`--keyring-backend`, `test`,
		`-y`,
	)
	if verbose {
		log.Println("submitConsumerModificationProposal cmd: ", cmd.String())
		log.Println("submitConsumerModificationProposal json: ", jsonStr)
	}

	bz, err = cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	if verbose {
		log.Println("submitConsumerModificationProposal output: ", string(bz))
	}

	// wait for inclusion in a block -> '--broadcast-mode block' is deprecated
	tr.waitBlocks(ChainID("provi"), 2, 10*time.Second)
}

type SubmitEnableTransfersProposalAction struct {
	Chain   ChainID
	From    ValidatorID
	Title   string
	Deposit uint
}

func (tr Chain) submitEnableTransfersProposalAction(
	action SubmitEnableTransfersProposalAction,
	verbose bool,
) {
	// gov signed address got by checking the gov module acc address in the test container
	// interchain-security-cdd q auth module-account gov --node tcp://7.7.9.253:26658
	template := `
	{
		"messages": [
		 {
		  "@type": "/ibc.applications.transfer.v1.MsgUpdateParams",
		  "signer": "consumer10d07y265gmmuvt4z0w9aw880jnsr700jlh7295",
		  "params": {
		   "send_enabled": true,
		   "receive_enabled": true
		  }
		 }
		],
		"metadata": "ipfs://CID",
		"deposit": "%dstake",
		"title": "%s",
		"summary": "Enable transfer send",
		"expedited": false
	   }
	`
	jsonStr := fmt.Sprintf(template, action.Deposit, action.Title)

	//#nosec G204 -- bypass unsafe quoting warning (no production code)
	bz, err := tr.target.ExecCommand(
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, jsonStr, "/params-proposal.json"),
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	cmd := tr.target.ExecCommand(
		tr.testConfig.chainConfigs[action.Chain].BinaryName,
		"tx", "gov", "submit-proposal", "/params-proposal.json",
		`--from`, `validator`+fmt.Sprint(action.From),
		`--chain-id`, string(tr.testConfig.chainConfigs[action.Chain].ChainId),
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

func (tr *Chain) voteGovProposal(
	action VoteGovProposalAction,
	verbose bool,
) {
	var wg sync.WaitGroup
	for i, val := range action.From {
		wg.Add(1)
		vote := action.Vote[i]
		go func(val ValidatorID, vote string) {
			defer wg.Done()
			bz, err := tr.target.ExecCommand(
				tr.testConfig.chainConfigs[action.Chain].BinaryName,

				"tx", "gov", "vote",
				fmt.Sprint(action.PropNumber), vote,

				`--from`, `validator`+fmt.Sprint(val),
				`--chain-id`, string(tr.testConfig.chainConfigs[action.Chain].ChainId),
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
	tr.WaitTime(time.Duration(tr.testConfig.chainConfigs[action.Chain].VotingWaitTime) * time.Second)
}

type StartConsumerChainAction struct {
	ConsumerChain  ChainID
	ProviderChain  ChainID
	Validators     []StartChainValidator
	GenesisChanges string
}

func (tr *Chain) startConsumerChain(
	action StartConsumerChainAction,
	verbose bool,
) {
	fmt.Println("Starting consumer chain ", action.ConsumerChain)
	consumerGenesis := ".app_state.ccvconsumer = " + tr.getConsumerGenesis(action.ProviderChain, action.ConsumerChain)
	consumerGenesisChanges := tr.testConfig.chainConfigs[action.ConsumerChain].GenesisChanges
	if consumerGenesisChanges != "" {
		consumerGenesis = consumerGenesis + " | " + consumerGenesisChanges
	}
	if action.GenesisChanges != "" {
		consumerGenesis = consumerGenesis + " | " + action.GenesisChanges
	}

	tr.startChain(StartChainAction{
		Chain:          action.ConsumerChain,
		Validators:     action.Validators,
		GenesisChanges: consumerGenesis,
		IsConsumer:     true,
	}, verbose)
}

// Get consumer genesis from provider
func (tr *Chain) getConsumerGenesis(providerChain, consumerChain ChainID) string {
	fmt.Println("Exporting consumer genesis from provider")
	providerBinaryName := tr.testConfig.chainConfigs[providerChain].BinaryName

	cmd := tr.target.ExecCommand(
		providerBinaryName,

		"query", "provider", "consumer-genesis",
		string(tr.testConfig.chainConfigs[consumerChain].ChainId),

		`--node`, tr.target.GetQueryNode(providerChain),
		`-o`, `json`,
	)

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	if tr.testConfig.transformGenesis || needsGenesisTransform(tr.testConfig) {
		return string(tr.transformConsumerGenesis(consumerChain, bz))
	} else {
		fmt.Println("No genesis transformation performed")
	}
	return string(bz)
}

// needsGenesisTransform tries to identify if a genesis transformation should be performed
func needsGenesisTransform(cfg TestConfig) bool {
	// no genesis transformation needed for same versions
	if cfg.consumerVersion == cfg.providerVersion {
		return false
	}

	// use v4.0.0 (after genesis transform breakages) for the checks if 'latest' is used
	consumerVersion := cfg.consumerVersion
	if cfg.consumerVersion == VLatest {
		consumerVersion = V400
	}
	providerVersion := cfg.providerVersion
	if cfg.providerVersion == VLatest {
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

	containerInstance := tr.testConfig.containerConfig.InstanceName
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
	bz, err := tr.target.ExecCommand(
		"interchain-security-transformer",
		"genesis", "transform", "--to").CombinedOutput()
	if err != nil && !strings.Contains(string(bz), "unknown flag: --to") {
		targetVersion, err := getTransformParameter(tr.testConfig.consumerVersion)
		if err != nil {
			log.Panic("Failed getting genesis transformation parameter: ", err)
		}
		cmd = tr.target.ExecCommand(
			"interchain-security-transformer",
			"genesis", "transform", targetVersion, targetFile)
	} else {
		cmd = tr.target.ExecCommand(
			"interchain-security-transformer",
			"genesis", "transform", targetFile)
	}

	result, err := cmd.CombinedOutput()
	if err != nil {
		log.Panic(err, "CCV consumer genesis transformation failed: %s", string(result))
	}
	return result
}

type ChangeoverChainAction struct {
	SovereignChain ChainID
	ProviderChain  ChainID
	Validators     []StartChainValidator
	GenesisChanges string
}

func (tr Chain) changeoverChain(
	action ChangeoverChainAction,
	verbose bool,
) {
	// sleep until the consumer chain genesis is ready on consumer
	time.Sleep(5 * time.Second)
	cmd := tr.target.ExecCommand(
		tr.testConfig.chainConfigs[action.ProviderChain].BinaryName,

		"query", "provider", "consumer-genesis",
		string(tr.testConfig.chainConfigs[action.SovereignChain].ChainId),

		`--node`, tr.target.GetQueryNode(action.ProviderChain),
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
	consumerGenesisChanges := tr.testConfig.chainConfigs[action.SovereignChain].GenesisChanges
	if consumerGenesisChanges != "" {
		consumerGenesis = consumerGenesis + " | " + consumerGenesisChanges
	}
	if action.GenesisChanges != "" {
		consumerGenesis = consumerGenesis + " | " + action.GenesisChanges
	}

	tr.startChangeover(ChangeoverChainAction{
		Validators:     action.Validators,
		GenesisChanges: consumerGenesis,
	}, verbose)
}

func (tr Chain) startChangeover(
	action ChangeoverChainAction,
	verbose bool,
) {
	chainConfig := tr.testConfig.chainConfigs[ChainID("sover")]
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
			Mnemonic:         tr.testConfig.validatorConfigs[val.Id].Mnemonic,
			NodeKey:          tr.testConfig.validatorConfigs[val.Id].NodeKey,
			ValId:            fmt.Sprint(val.Id),
			PrivValidatorKey: tr.testConfig.validatorConfigs[val.Id].PrivValidatorKey,
			Allocation:       fmt.Sprint(val.Allocation) + "stake",
			Stake:            fmt.Sprint(val.Stake) + "stake",
			IpSuffix:         tr.testConfig.validatorConfigs[val.Id].IpSuffix,

			ConsumerMnemonic:         tr.testConfig.validatorConfigs[val.Id].ConsumerMnemonic,
			ConsumerPrivValidatorKey: tr.testConfig.validatorConfigs[val.Id].ConsumerPrivValidatorKey,
			// if true node will be started with consumer key for each consumer chain
			StartWithConsumerKey: tr.testConfig.validatorConfigs[val.Id].UseConsumerKey,
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
	changeoverScript := tr.target.GetTestScriptPath(isConsumer, "start-changeover.sh")
	cmd := tr.target.ExecCommand(
		"/bin/bash",
		changeoverScript, chainConfig.UpgradeBinary, string(vals),
		"sover", chainConfig.IpPrefix, genesisChanges,
		tr.testConfig.tendermintConfigOverride,
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
	if !tr.testConfig.useGorelayer {
		tr.addChainToHermes(action, verbose)
	} else {
		tr.addChainToGorelayer(action, verbose)
	}
}

func (tr Chain) addChainToGorelayer(
	action AddChainToRelayerAction,
	verbose bool,
) {
	queryNodeIP := tr.target.GetQueryNodeIP(action.Chain)
	ChainId := tr.testConfig.chainConfigs[action.Chain].ChainId
	rpcAddr := "http://" + queryNodeIP + ":26658"

	chainConfig := fmt.Sprintf(gorelayerChainConfigTemplate,
		ChainId,
		rpcAddr,
		tr.testConfig.chainConfigs[action.Chain].AccountPrefix,
	)

	bz, err := tr.target.ExecCommand(
		"rly", "config", "init").CombinedOutput()
	if err != nil && !strings.Contains(string(bz), "config already exists") {
		log.Fatal(err, "\n", string(bz))
	}

	chainConfigFileName := fmt.Sprintf("/root/%s_config.json", ChainId)

	bashCommand := fmt.Sprintf(`echo '%s' >> %s`, chainConfig, chainConfigFileName)
	bz, err = tr.target.ExecCommand("bash", "-c",
		bashCommand).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	addChainCommand := tr.target.ExecCommand("rly", "chains", "add", "--file", chainConfigFileName, string(ChainId))
	e2e.ExecuteCommand(addChainCommand, "add chain", verbose)

	keyRestoreCommand := tr.target.ExecCommand("rly", "keys", "restore", string(ChainId), "default", tr.testConfig.validatorConfigs[action.Validator].Mnemonic)
	e2e.ExecuteCommand(keyRestoreCommand, "restore keys", verbose)
}

func (tr Chain) addChainToHermes(
	action AddChainToRelayerAction,
	verbose bool,
) {
	bz, err := tr.target.ExecCommand("bash", "-c", "hermes", "version").CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n error getting hermes version", string(bz))
	}
	re := regexp.MustCompile(`hermes\s+(\d+.\d+.\d+)`)
	match := re.FindStringSubmatch(string(bz))
	if match == nil {
		log.Fatalln("error identifying hermes version from", string(bz))
	}

	hermesVersion := match[1]
	queryNodeIP := tr.target.GetQueryNodeIP(action.Chain)
	hermesConfig := GetHermesConfig(hermesVersion, queryNodeIP, tr.testConfig.chainConfigs[action.Chain], action.IsConsumer)

	bashCommand := fmt.Sprintf(`echo '%s' >> %s`, hermesConfig, "/root/.hermes/config.toml")

	bz, err = tr.target.ExecCommand("bash", "-c", bashCommand).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// Save mnemonic to file within container
	var mnemonic string
	if tr.testConfig.validatorConfigs[action.Validator].UseConsumerKey && action.IsConsumer {
		mnemonic = tr.testConfig.validatorConfigs[action.Validator].ConsumerMnemonic
	} else {
		mnemonic = tr.testConfig.validatorConfigs[action.Validator].Mnemonic
	}

	saveMnemonicCommand := fmt.Sprintf(`echo '%s' > %s`, mnemonic, "/root/.hermes/mnemonic.txt")
	fmt.Println("Add to hermes", action.Validator)
	bz, err = tr.target.ExecCommand("bash", "-c", saveMnemonicCommand).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	bz, err = tr.target.ExecCommand("hermes",
		"keys", "add",
		"--chain", string(tr.testConfig.chainConfigs[action.Chain].ChainId),
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

func (tr Chain) addIbcConnection(
	action AddIbcConnectionAction,
	verbose bool,
) {
	if !tr.testConfig.useGorelayer {
		tr.addIbcConnectionHermes(action, verbose)
	} else {
		tr.addIbcConnectionGorelayer(action, verbose)
	}
}

func (tr Chain) addIbcConnectionGorelayer(
	action AddIbcConnectionAction,
	verbose bool,
) {
	pathName := tr.GetPathNameForGorelayer(action.ChainA, action.ChainB)

	pathConfig := fmt.Sprintf(gorelayerPathConfigTemplate, action.ChainA, action.ClientA, action.ChainB, action.ClientB)

	pathConfigFileName := fmt.Sprintf("/root/%s_config.json", pathName)

	bashCommand := fmt.Sprintf(`echo '%s' >> %s`, pathConfig, pathConfigFileName)

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	pathConfigCommand := tr.target.ExecCommand("bash", "-c", bashCommand)
	e2e.ExecuteCommand(pathConfigCommand, "add path config", verbose)

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	newPathCommand := tr.target.ExecCommand("rly",
		"paths", "add",
		string(tr.testConfig.chainConfigs[action.ChainA].ChainId),
		string(tr.testConfig.chainConfigs[action.ChainB].ChainId),
		pathName,
		"--file", pathConfigFileName,
	)

	e2e.ExecuteCommand(newPathCommand, "new path", verbose)

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	newClientsCommand := tr.target.ExecCommand("rly", "transact", "clients", pathName)

	e2e.ExecuteCommand(newClientsCommand, "new clients", verbose)

	tr.waitBlocks(action.ChainA, 1, 10*time.Second)
	tr.waitBlocks(action.ChainB, 1, 10*time.Second)

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	newConnectionCommand := tr.target.ExecCommand("rly", "transact", "connection", pathName)

	e2e.ExecuteCommand(newConnectionCommand, "new connection", verbose)

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
func (tr Chain) createIbcClientsHermes(
	action CreateIbcClientsAction,
	verbose bool,
) {
	cmd := tr.target.ExecCommand("hermes",
		"create", "connection",
		"--a-chain", string(tr.testConfig.chainConfigs[action.ChainA].ChainId),
		"--b-chain", string(tr.testConfig.chainConfigs[action.ChainB].ChainId),
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

func (tr Chain) addIbcConnectionHermes(
	action AddIbcConnectionAction,
	verbose bool,
) {
	cmd := tr.target.ExecCommand("hermes",
		"create", "connection",
		"--a-chain", string(tr.testConfig.chainConfigs[action.ChainA].ChainId),
		"--a-client", "07-tendermint-"+fmt.Sprint(action.ClientA),
		"--b-client", "07-tendermint-"+fmt.Sprint(action.ClientB),
	)
	fmt.Println("running: ", cmd)
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

func (tr Chain) startRelayer(
	action StartRelayerAction,
	verbose bool,
) {
	if tr.testConfig.useGorelayer {
		tr.startGorelayer(action, verbose)
	} else {
		tr.startHermes(action, verbose)
	}
}

func (tr Chain) startGorelayer(
	action StartRelayerAction,
	verbose bool,
) {
	// gorelayer start is running in detached mode
	cmd := tr.target.ExecDetachedCommand("rly", "start")

	if err := cmd.Start(); err != nil {
		log.Fatal(err)
	}

	if verbose {
		fmt.Println("started gorelayer")
	}
}

func (tr Chain) startHermes(
	action StartRelayerAction,
	verbose bool,
) {
	// hermes start is running in detached mode
	cmd := tr.target.ExecDetachedCommand("hermes", "start")

	if err := cmd.Start(); err != nil {
		log.Fatal(err)
	}

	if verbose {
		fmt.Println("started Hermes")
	}
}

func (tr Chain) addIbcChannel(
	action AddIbcChannelAction,
	verbose bool,
) {
	if tr.testConfig.useGorelayer {
		tr.addIbcChannelGorelayer(action, verbose)
	} else {
		tr.addIbcChannelHermes(action, verbose)
	}
}

func (tr Chain) addIbcChannelGorelayer(
	action AddIbcChannelAction,
	verbose bool,
) {
	pathName := tr.GetPathNameForGorelayer(action.ChainA, action.ChainB)
	cmd := tr.target.ExecCommand("rly",
		"transact", "channel",
		pathName,
		"--src-port", action.PortA,
		"--dst-port", action.PortB,
		"--version", tr.testConfig.containerConfig.CcvVersion,
		"--order", action.Order,
		"--debug",
	)
	e2e.ExecuteCommand(cmd, "addChannel", verbose)
}

func (tr Chain) addIbcChannelHermes(
	action AddIbcChannelAction,
	verbose bool,
) {
	// if version is not specified, use the default version when creating ccv connections
	// otherwise, use the provided version schema (usually it is ICS20-1 for IBC transfer)
	chanVersion := action.Version
	if chanVersion == "" {
		chanVersion = tr.testConfig.containerConfig.CcvVersion
	}

	cmd := tr.target.ExecCommand("hermes",
		"create", "channel",
		"--a-chain", string(tr.testConfig.chainConfigs[action.ChainA].ChainId),
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

func (tr Chain) transferChannelComplete(
	action TransferChannelCompleteAction,
	verbose bool,
) {
	if tr.testConfig.useGorelayer {
		log.Fatal("transferChannelComplete is not implemented for rly")
	}

	chanOpenTryCmd := tr.target.ExecCommand("hermes", "tx", "chan-open-try",
		"--dst-chain", string(tr.testConfig.chainConfigs[action.ChainB].ChainId),
		"--src-chain", string(tr.testConfig.chainConfigs[action.ChainA].ChainId),
		"--dst-connection", "connection-"+fmt.Sprint(action.ConnectionA),
		"--dst-port", action.PortB,
		"--src-port", action.PortA,
		"--src-channel", "channel-"+fmt.Sprint(action.ChannelA),
	)

	e2e.ExecuteCommand(chanOpenTryCmd, "transferChanOpenTry", verbose)

	chanOpenAckCmd := tr.target.ExecCommand("hermes",
		"tx", "chan-open-ack",
		"--dst-chain", string(tr.testConfig.chainConfigs[action.ChainA].ChainId),
		"--src-chain", string(tr.testConfig.chainConfigs[action.ChainB].ChainId),
		"--dst-connection", "connection-"+fmt.Sprint(action.ConnectionA),
		"--dst-port", action.PortA,
		"--src-port", action.PortB,
		"--dst-channel", "channel-"+fmt.Sprint(action.ChannelA),
		"--src-channel", "channel-"+fmt.Sprint(action.ChannelB),
	)

	e2e.ExecuteCommand(chanOpenAckCmd, "transferChanOpenAck", verbose)

	chanOpenConfirmCmd := tr.target.ExecCommand("hermes",
		"tx", "chan-open-confirm",
		"--dst-chain", string(tr.testConfig.chainConfigs[action.ChainB].ChainId),
		"--src-chain", string(tr.testConfig.chainConfigs[action.ChainA].ChainId),
		"--dst-connection", "connection-"+fmt.Sprint(action.ConnectionA),
		"--dst-port", action.PortB,
		"--src-port", action.PortA,
		"--dst-channel", "channel-"+fmt.Sprint(action.ChannelB),
		"--src-channel", "channel-"+fmt.Sprint(action.ChannelA),
	)
	e2e.ExecuteCommand(chanOpenConfirmCmd, "transferChanOpenConfirm", verbose)
}

type RelayPacketsAction struct {
	ChainA  ChainID
	ChainB  ChainID
	Port    string
	Channel uint
}

func (tr Chain) relayPackets(
	action RelayPacketsAction,
	verbose bool,
) {
	if tr.testConfig.useGorelayer {
		tr.relayPacketsGorelayer(action, verbose)
	} else {
		tr.relayPacketsHermes(action, verbose)
	}
}

func (tr Chain) relayPacketsGorelayer(
	action RelayPacketsAction,
	verbose bool,
) {
	// Because `.app_state.provider.params.blocks_per_epoch` is set to 3 in the E2E tests, we wait 3 blocks
	// before relaying the packets to guarantee that at least one epoch passes and hence any `VSCPacket`s get
	// queued and are subsequently relayed.
	tr.waitBlocks(action.ChainA, 3, 90*time.Second)
	tr.waitBlocks(action.ChainB, 3, 90*time.Second)

	pathName := tr.GetPathNameForGorelayer(action.ChainA, action.ChainB)

	// rly transact relay-packets [path-name] --channel [channel-id]
	cmd := tr.target.ExecCommand("rly", "transact", "flush",
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

func (tr Chain) relayPacketsHermes(
	action RelayPacketsAction,
	verbose bool,
) {
	// Because `.app_state.provider.params.blocks_per_epoch` is set to 3 in the E2E tests, we wait 3 blocks
	// before relaying the packets to guarantee that at least one epoch passes and hence any `VSCPacket`s get
	// queued and are subsequently relayed.
	tr.waitBlocks(action.ChainA, 3, 90*time.Second)
	tr.waitBlocks(action.ChainB, 3, 90*time.Second)

	// hermes clear packets ibc0 transfer channel-13
	cmd := tr.target.ExecCommand("hermes", "clear", "packets",
		"--chain", string(tr.testConfig.chainConfigs[action.ChainA].ChainId),
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

func (tr Chain) relayRewardPacketsToProvider(
	action RelayRewardPacketsToProviderAction,
	verbose bool,
) {
	blockPerDistribution, _ := strconv.ParseUint(strings.Trim(tr.target.GetParam(action.ConsumerChain, Param{Subspace: "ccvconsumer", Key: "BlocksPerDistributionTransmission"}), "\""), 10, 64)
	currentBlock := uint64(tr.target.GetBlockHeight(action.ConsumerChain))
	if currentBlock <= blockPerDistribution {
		tr.waitBlocks(action.ConsumerChain, uint(blockPerDistribution-currentBlock+1), 60*time.Second)
	}

	tr.relayPackets(RelayPacketsAction{ChainA: action.ConsumerChain, ChainB: action.ProviderChain, Port: action.Port, Channel: action.Channel}, verbose)
	tr.waitBlocks(action.ProviderChain, 1, 10*time.Second)
}

type DelegateTokensAction struct {
	Chain  ChainID
	From   ValidatorID
	To     ValidatorID
	Amount uint
}

func (tr Chain) delegateTokens(
	action DelegateTokensAction,
	verbose bool,
) {
	toValCfg := tr.testConfig.validatorConfigs[action.To]
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

	cmd := tr.target.ExecCommand(tr.testConfig.chainConfigs[action.Chain].BinaryName,

		"tx", "staking", "delegate",
		validatorAddress,
		fmt.Sprint(action.Amount)+`stake`,
		`--from`, `validator`+fmt.Sprint(action.From),
		`--chain-id`, string(tr.testConfig.chainConfigs[action.Chain].ChainId),
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

func (tr Chain) unbondTokens(
	action UnbondTokensAction,
	verbose bool,
) {
	unbondFromValCfg := tr.testConfig.validatorConfigs[action.UnbondFrom]
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

	cmd := tr.target.ExecCommand(tr.testConfig.chainConfigs[action.Chain].BinaryName,

		"tx", "staking", "unbond",
		validatorAddress,
		fmt.Sprint(action.Amount)+`stake`,

		`--from`, `validator`+fmt.Sprint(action.Sender),
		`--chain-id`, string(tr.testConfig.chainConfigs[action.Chain].ChainId),
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

func (tr Chain) cancelUnbondTokens(
	action CancelUnbondTokensAction,
	verbose bool,
) {
	valCfg := tr.testConfig.validatorConfigs[action.Validator]
	delCfg := tr.testConfig.validatorConfigs[action.Delegator]
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
	cmd := tr.target.ExecCommand(tr.testConfig.chainConfigs[action.Chain].BinaryName,
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
	creationHeight := gjson.Get(string(bz), "unbond.entries.0.creation_height").Int()
	if creationHeight == 0 {
		log.Fatal("invalid creation height")
	}

	cmd = tr.target.ExecCommand(tr.testConfig.chainConfigs[action.Chain].BinaryName,
		"tx", "staking", "cancel-unbond",
		validatorAddress,
		fmt.Sprint(action.Amount)+`stake`,
		fmt.Sprint(creationHeight),
		`--from`, `validator`+fmt.Sprint(action.Delegator),
		`--chain-id`, string(tr.testConfig.chainConfigs[action.Chain].ChainId),
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

func (tr Chain) redelegateTokens(action RedelegateTokensAction, verbose bool) {
	srcCfg := tr.testConfig.validatorConfigs[action.Src]
	dstCfg := tr.testConfig.validatorConfigs[action.Dst]
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

	cmd := tr.target.ExecCommand(
		tr.testConfig.chainConfigs[action.Chain].BinaryName,

		"tx", "staking", "redelegate",
		redelegateSrc,
		redelegateDst,
		fmt.Sprint(action.Amount)+`stake`,
		`--from`, `validator`+fmt.Sprint(action.TxSender),
		`--chain-id`, string(tr.testConfig.chainConfigs[action.Chain].ChainId),
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

func (tr Chain) invokeDowntimeSlash(action DowntimeSlashAction, verbose bool) {
	// Bring validator down
	tr.setValidatorDowntime(action.Chain, action.Validator, true, verbose)
	// Wait appropriate amount of blocks for validator to be slashed
	tr.waitBlocks(action.Chain, 11, 3*time.Minute)
	// Bring validator back up
	tr.setValidatorDowntime(action.Chain, action.Validator, false, verbose)
}

// Sets validator downtime by setting the virtual ethernet interface of a node to "up" or "down"
func (tr Chain) setValidatorDowntime(chain ChainID, validator ValidatorID, down bool, verbose bool) {
	var lastArg string
	if down {
		lastArg = "down"
	} else {
		lastArg = "up"
	}

	if tr.testConfig.useCometmock {
		// send set_signing_status either to down or up for validator
		validatorPrivateKeyAddress := tr.GetValidatorPrivateKeyAddress(chain, validator)

		method := "set_signing_status"
		params := fmt.Sprintf(`{"private_key_address":"%s","status":"%s"}`, validatorPrivateKeyAddress, lastArg)
		address := tr.target.GetQueryNodeRPCAddress(chain)

		tr.curlJsonRPCRequest(method, params, address)
		tr.waitBlocks(chain, 1, 10*time.Second)
		return
	}

	cmd := tr.target.ExecCommand(
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

func (tr Chain) GetValidatorPrivateKeyAddress(chain ChainID, validator ValidatorID) string {
	var validatorPrivateKeyAddress string
	if chain == ChainID("provi") {
		validatorPrivateKeyAddress = tr.getValidatorKeyAddressFromString(tr.testConfig.validatorConfigs[validator].PrivValidatorKey)
	} else {
		var valAddressString string
		if tr.testConfig.validatorConfigs[validator].UseConsumerKey {
			valAddressString = tr.testConfig.validatorConfigs[validator].ConsumerPrivValidatorKey
		} else {
			valAddressString = tr.testConfig.validatorConfigs[validator].PrivValidatorKey
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
func (tr Chain) unjailValidator(action UnjailValidatorAction, verbose bool) {
	// wait until downtime_jail_duration has elapsed, to make sure the validator can be unjailed
	tr.WaitTime(61 * time.Second)

	cmd := tr.target.ExecCommand(
		tr.testConfig.chainConfigs[action.Provider].BinaryName,
		"tx", "slashing", "unjail",
		// Validator is sender here
		`--from`, `validator`+fmt.Sprint(action.Validator),
		`--chain-id`, string(tr.testConfig.chainConfigs[action.Provider].ChainId),
		`--home`, tr.getValidatorHome(action.Provider, action.Validator),
		`--node`, tr.getValidatorNode(action.Provider, action.Validator),
		`--gas`, "900000",
		`--keyring-backend`, `test`,
		`--keyring-dir`, tr.getValidatorHome(action.Provider, action.Validator),
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

func (tr Chain) registerRepresentative(
	action RegisterRepresentativeAction,
	verbose bool,
) {
	fileTempl := `{
		"pubkey": %s,
		"amount": "%s",
		"moniker": "%s",
		"identity": "",
		"website": "",
		"security": "",
		"details": "",
		"commission-rate": "0.1",
		"commission-max-rate": "0.2",
		"commission-max-change-rate": "0.01",
		"min-self-delegation": "1"
	}`
	var wg sync.WaitGroup
	for i, val := range action.Representatives {
		wg.Add(1)
		stake := action.Stakes[i]
		go func(val ValidatorID, stake uint) {
			defer wg.Done()

			pubKeycmd := tr.target.ExecCommand(tr.testConfig.chainConfigs[action.Chain].BinaryName,
				"tendermint", "show-validator",
				`--home`, tr.getValidatorHome(action.Chain, val),
			)

			bzPubKey, err := pubKeycmd.CombinedOutput()
			if err != nil {
				log.Fatal(err, "\n", string(bzPubKey))
			}

			fileContent := fmt.Sprintf(fileTempl, string(bzPubKey), fmt.Sprint(stake)+"stake", fmt.Sprint(val))
			fileName := fmt.Sprintf("%s_democracy_representative.json", val)
			file, err := os.CreateTemp("", fileName)
			if err != nil {
				panic(fmt.Sprintf("failed writing ccv consumer file : %v", err))
			}
			defer file.Close()
			err = os.WriteFile(file.Name(), []byte(fileContent), 0o600)
			if err != nil {
				log.Fatalf("Failed writing consumer genesis to file: %v", err)
			}

			containerInstance := tr.testConfig.containerConfig.InstanceName
			targetFile := fmt.Sprintf("/tmp/%s", fileName)
			sourceFile := file.Name()
			//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
			copyCmd := exec.Command("docker", "cp", sourceFile,
				fmt.Sprintf("%s:%s", containerInstance, targetFile))
			writeResult, err := copyCmd.CombinedOutput()
			if err != nil {
				log.Fatal(err, "\n", string(writeResult))
			}

			cmd := tr.target.ExecCommand(tr.testConfig.chainConfigs[action.Chain].BinaryName,
				"tx", "staking", "create-validator",
				targetFile,
				`--from`, `validator`+fmt.Sprint(val),
				`--chain-id`, string(tr.testConfig.chainConfigs[action.Chain].ChainId),
				`--home`, tr.getValidatorHome(action.Chain, val),
				`--node`, tr.getValidatorNode(action.Chain, val),
				`--keyring-backend`, `test`,
				`-y`,
			)

			if verbose {
				fmt.Println("register representative cmd:", cmd.String())
				fmt.Println("Tx json:", fileContent)
			}

			bz, err := cmd.CombinedOutput()
			if err != nil {
				log.Fatal(err, "\n", string(bz))
			}

			// wait for inclusion in a block -> '--broadcast-mode block' is deprecated
			tr.waitBlocks(action.Chain, 2, 10*time.Second)
		}(val, stake)
	}

	wg.Wait()
}

type SubmitChangeRewardDenomsProposalAction struct {
	Chain   ChainID
	Denom   string
	Deposit uint
	From    ValidatorID
}

func (tr Chain) submitChangeRewardDenomsProposal(action SubmitChangeRewardDenomsProposalAction, verbose bool) {
	template := `
{
 "messages": [
  {
   "@type": "/interchain_security.ccv.provider.v1.MsgChangeRewardDenoms",
   "denoms_to_add": %s,
   "denoms_to_remove": %s,
   "authority": "cosmos10d07y265gmmuvt4z0w9aw880jnsr700j6zn9kn"
  }
 ],
 "metadata": "ipfs://CID",
 "deposit": "%dstake",
 "title": "change reward denoms",
 "summary": "Proposal to change reward denoms",
 "expedited": false
}`

	denomsToAdd := []string{action.Denom}
	denomsToRemove := []string{"stake"}
	jsonStr := fmt.Sprintf(template,
		denomsToAdd,
		denomsToRemove,
		action.Deposit)

	//#nosec G204 -- bypass unsafe quoting warning (no production code)
	proposalFile := "/consumer-addition.proposal"
	bz, err := tr.target.ExecCommand(
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, jsonStr, proposalFile),
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// CHANGE REWARDS DENOM PROPOSAL
	cmd := tr.target.ExecCommand(
		tr.testConfig.chainConfigs[action.Chain].BinaryName,
		"tx", "gov", "submit-proposal", proposalFile,
		`--from`, `validator`+fmt.Sprint(action.From),
		`--chain-id`, string(tr.testConfig.chainConfigs[action.Chain].ChainId),
		`--home`, tr.getValidatorHome(action.Chain, action.From),
		`--gas`, `900000`,
		`--node`, tr.getValidatorNode(action.Chain, action.From),
		`--keyring-backend`, `test`,
		`-y`,
	)

	if verbose {
		fmt.Println("change rewards denom props cmd:", cmd.String())
		fmt.Println("change rewards denom props json:", jsonStr)
	}
	bz, err = cmd.CombinedOutput()
	if err != nil {
		log.Fatal("submit-proposal failed:", err, "\n", string(bz))
	}

	if verbose {
		fmt.Println("change rewards denom props output:", string(bz))
	}

	// wait for inclusion in a block -> '--broadcast-mode block' is deprecated
	tr.waitBlocks(ChainID("provi"), 2, 30*time.Second)
}

func (tr Chain) submitChangeRewardDenomsLegacyProposal(action SubmitChangeRewardDenomsProposalAction, verbose bool) {
	providerChain := tr.testConfig.chainConfigs[action.Chain]

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

	bz, err = tr.target.ExecCommand(
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, jsonStr, "/change-reward-denoms-proposal.json")).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// CHANGE REWARDS DENOM PROPOSAL
	bz, err = tr.target.ExecCommand(providerChain.BinaryName,
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

func (tr Chain) invokeDoublesignSlash(
	action DoublesignSlashAction,
	verbose bool,
) {
	if !tr.testConfig.useCometmock {
		chainConfig := tr.testConfig.chainConfigs[action.Chain]
		doubleSignScript := tr.target.GetTestScriptPath(false, "cause-doublesign.sh")
		bz, err := tr.target.ExecCommand("/bin/bash",
			doubleSignScript, chainConfig.BinaryName, string(action.Validator),
			string(chainConfig.ChainId), chainConfig.IpPrefix).CombinedOutput()
		if err != nil {
			log.Fatal(err, "\n", string(bz))
		}
		tr.waitBlocks("provi", 20, 4*time.Minute)
	} else { // tr.useCometMock
		validatorPrivateKeyAddress := tr.GetValidatorPrivateKeyAddress(action.Chain, action.Validator)

		method := "cause_double_sign"
		params := fmt.Sprintf(`{"private_key_address":"%s"}`, validatorPrivateKeyAddress)

		address := tr.target.GetQueryNodeRPCAddress(action.Chain)

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

func (tr Chain) lightClientEquivocationAttack(
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

func (tr Chain) lightClientAmnesiaAttack(
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

func (tr Chain) lightClientLunaticAttack(
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

func (tr Chain) lightClientAttack(
	validator ValidatorID,
	chain ChainID,
	attackType LightClientAttackType,
) {
	if !tr.testConfig.useCometmock {
		log.Fatal("light client attack is only supported with CometMock")
	}
	validatorPrivateKeyAddress := tr.GetValidatorPrivateKeyAddress(chain, validator)

	method := "cause_light_client_attack"
	params := fmt.Sprintf(`{"private_key_address":"%s", "misbehaviour_type": "%s"}`, validatorPrivateKeyAddress, attackType)

	address := tr.target.GetQueryNodeRPCAddress(chain)

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

func (tr Chain) assignConsumerPubKey(action AssignConsumerPubKeyAction, verbose bool) {
	valCfg := tr.testConfig.validatorConfigs[action.Validator]

	// Note: to get error response reported back from this command '--gas auto' needs to be set.
	gas := "auto"
	// Unfortunately, --gas auto does not work with CometMock. so when using CometMock, just use --gas 9000000 then
	if tr.testConfig.useCometmock {
		gas = "9000000"
	}
	assignKey := fmt.Sprintf(
		`%s tx provider assign-consensus-key %s '%s' --from validator%s --chain-id %s --home %s --node %s --gas %s --keyring-backend test -y -o json`,
		tr.testConfig.chainConfigs[ChainID("provi")].BinaryName,
		string(tr.testConfig.chainConfigs[action.Chain].ChainId),
		action.ConsumerPubkey,
		action.Validator,
		tr.testConfig.chainConfigs[ChainID("provi")].ChainId,
		tr.getValidatorHome(ChainID("provi"), action.Validator),
		tr.getValidatorNode(ChainID("provi"), action.Validator),
		gas,
	)

	cmd := tr.target.ExecCommand(
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

	if action.ExpectError && !tr.testConfig.useCometmock { // error report only works with --gas auto, which does not work with CometMock, so ignore
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
		isConsumer := tr.testConfig.chainConfigs[action.Chain].BinaryName != "interchain-security-pd"
		reconfigureScript := tr.target.GetTestScriptPath(isConsumer, "reconfigure-node.sh")
		configureNodeCmd := tr.target.ExecCommand("/bin/bash",
			reconfigureScript, tr.testConfig.chainConfigs[action.Chain].BinaryName,
			string(action.Validator), string(action.Chain),
			tr.testConfig.chainConfigs[action.Chain].IpPrefix, valCfg.IpSuffix,
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
		tr.testConfig.validatorConfigs[action.Validator] = valCfg
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

func (tr Chain) waitForSlashMeterReplenishment(
	action SlashMeterReplenishmentAction,
	verbose bool,
) {
	timeout := time.Now().Add(action.Timeout)
	initialSlashMeter := tr.target.GetSlashMeter()

	if initialSlashMeter >= 0 {
		panic(fmt.Sprintf("No need to wait for slash meter replenishment, current value: %d", initialSlashMeter))
	}

	for {
		slashMeter := tr.target.GetSlashMeter()
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

func (tr Chain) waitForTime(
	action WaitTimeAction,
	verbose bool,
) {
	tr.WaitTime(action.WaitTime)
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

// Run an instance of the Hermes relayer using the "evidence" command,
// which detects evidences committed to the blocks of a consumer chain.
// Each infraction detected is reported to the provider chain using
// either a SubmitConsumerDoubleVoting or a SubmitConsumerMisbehaviour message.
type StartConsumerEvidenceDetectorAction struct {
	Chain ChainID
}

func (tr Chain) startConsumerEvidenceDetector(
	action StartConsumerEvidenceDetectorAction,
	verbose bool,
) {
	chainConfig := tr.testConfig.chainConfigs[action.Chain]
	// run in detached mode so it will keep running in the background
	bz, err := tr.target.ExecDetachedCommand(
		"hermes", "evidence", "--chain", string(chainConfig.ChainId)).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
	tr.waitBlocks("provi", 10, 2*time.Minute)
}

type OptInAction struct {
	Chain     ChainID
	Validator ValidatorID
}

func (tr Chain) optIn(action OptInAction, target ExecutionTarget, verbose bool) {
	// Note: to get error response reported back from this command '--gas auto' needs to be set.
	gas := "auto"
	// Unfortunately, --gas auto does not work with CometMock. so when using CometMock, just use --gas 9000000 then
	if tr.testConfig.useCometmock {
		gas = "9000000"
	}

	// Use: "opt-in [consumer-chain-id] [consumer-pubkey]",
	optIn := fmt.Sprintf(
		`%s tx provider opt-in %s --from validator%s --chain-id %s --home %s --node %s --gas %s --keyring-backend test -y -o json`,
		tr.testConfig.chainConfigs[ChainID("provi")].BinaryName,
		string(tr.testConfig.chainConfigs[action.Chain].ChainId),
		action.Validator,
		tr.testConfig.chainConfigs[ChainID("provi")].ChainId,
		tr.getValidatorHome(ChainID("provi"), action.Validator),
		tr.getValidatorNode(ChainID("provi"), action.Validator),
		gas,
	)

	cmd := target.ExecCommand(
		"/bin/bash", "-c",
		optIn,
	)

	if verbose {
		fmt.Println("optIn cmd:", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	if !tr.testConfig.useCometmock { // error report only works with --gas auto, which does not work with CometMock, so ignore
		if err != nil && verbose {
			fmt.Printf("got error during opt in | err: %s | output: %s \n", err, string(bz))
		}
	}

	// wait for inclusion in a block -> '--broadcast-mode block' is deprecated
	tr.waitBlocks(ChainID("provi"), 2, 30*time.Second)
}

type OptOutAction struct {
	Chain       ChainID
	Validator   ValidatorID
	ExpectError bool
}

func (tr Chain) optOut(action OptOutAction, target ExecutionTarget, verbose bool) {
	// Note: to get error response reported back from this command '--gas auto' needs to be set.
	gas := "auto"
	// Unfortunately, --gas auto does not work with CometMock. so when using CometMock, just use --gas 9000000 then
	if tr.testConfig.useCometmock {
		gas = "9000000"
	}

	// Use: "opt-out [consumer-chain-id]",
	optOut := fmt.Sprintf(
		`%s tx provider opt-out %s --from validator%s --chain-id %s --home %s --node %s --gas %s --keyring-backend test -y -o json`,
		tr.testConfig.chainConfigs[ChainID("provi")].BinaryName,
		string(tr.testConfig.chainConfigs[action.Chain].ChainId),
		action.Validator,
		tr.testConfig.chainConfigs[ChainID("provi")].ChainId,
		tr.getValidatorHome(ChainID("provi"), action.Validator),
		tr.getValidatorNode(ChainID("provi"), action.Validator),
		gas,
	)

	cmd := target.ExecCommand(
		"/bin/bash", "-c",
		optOut,
	)

	if verbose {
		fmt.Println("optOut cmd:", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if action.ExpectError {
		if err != nil {
			if verbose {
				fmt.Printf("got expected error during opt out | err: %s | output: %s \n", err, string(bz))
			}
		} else {
			log.Fatal("expected error during opt-out but got none")
		}
	} else {
		if err != nil {
			log.Fatal(err, "\n", string(bz))
		}
	}

	// wait for inclusion in a block -> '--broadcast-mode block' is deprecated
	tr.waitBlocks(ChainID("provi"), 2, 30*time.Second)
}

type SetConsumerCommissionRateAction struct {
	Chain          ChainID
	Validator      ValidatorID
	CommissionRate float64

	// depending on the execution, this action might throw an error (e.g., when no consumer chain exists)
	ExpectError   bool
	ExpectedError string
}

func (tr Chain) setConsumerCommissionRate(action SetConsumerCommissionRateAction, target ExecutionTarget, verbose bool) {
	// Note: to get error response reported back from this command '--gas auto' needs to be set.
	gas := "auto"
	// Unfortunately, --gas auto does not work with CometMock. so when using CometMock, just use --gas 9000000 then
	if tr.testConfig.useCometmock {
		gas = "9000000"
	}

	// Use: "set-consumer-commission-rate [consumer-chain-id] [commission-rate]"
	setCommissionRate := fmt.Sprintf(
		`%s tx provider set-consumer-commission-rate %s %f --from validator%s --chain-id %s --home %s --node %s --gas %s --keyring-backend test -y -o json`,
		tr.testConfig.chainConfigs[ChainID("provi")].BinaryName,
		string(tr.testConfig.chainConfigs[action.Chain].ChainId),
		action.CommissionRate,
		action.Validator,
		tr.testConfig.chainConfigs[ChainID("provi")].ChainId,
		tr.getValidatorHome(ChainID("provi"), action.Validator),
		tr.getValidatorNode(ChainID("provi"), action.Validator),
		gas,
	)

	cmd := target.ExecCommand(
		"/bin/bash", "-c",
		setCommissionRate,
	)

	if verbose {
		fmt.Println("setConsumerCommissionRate cmd:", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if err != nil && !action.ExpectError {
		log.Fatalf("unexpected error during commssion rate set - output: %s, err: %s", string(bz), err)
	}

	if action.ExpectError && !tr.testConfig.useCometmock { // error report only works with --gas auto, which does not work with CometMock, so ignore
		if err == nil || !strings.Contains(string(bz), action.ExpectedError) {
			log.Fatalf("expected error not raised: expected: '%s', got '%s'", action.ExpectedError, (bz))
		}

		if verbose {
			fmt.Printf("got expected error during commssion rate set | err: %s | output: %s \n", err, string(bz))
		}
	}

	if !tr.testConfig.useCometmock { // error report only works with --gas auto, which does not work with CometMock, so ignore
		if err != nil && verbose {
			fmt.Printf("got error during commssion rate set | err: %s | output: %s \n", err, string(bz))
		}
	}

	// wait for inclusion in a block -> '--broadcast-mode block' is deprecated
	tr.waitBlocks(ChainID("provi"), 2, 30*time.Second)
}

// WaitTime waits for the given duration.
// To make sure that the new timestamp is visible on-chain, it also waits until at least one block has been
// produced on each chain after waiting.
// The CometMock version of this takes a pointer to the TestConfig as it needs to manipulate
// information in the testrun that stores how much each chain has waited, to keep times in sync.
// Be careful that all functions calling WaitTime should therefore also take a pointer to the TestConfig.
func (tr *Chain) WaitTime(duration time.Duration) {
	if !tr.testConfig.useCometmock {
		time.Sleep(duration)
	} else {
		tr.testConfig.timeOffset += duration
		for chain, running := range tr.testConfig.runningChains {
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

	address := tr.target.GetQueryNodeRPCAddress(chain)

	tr.curlJsonRPCRequest(method, params, address)

	// wait for 1 block of the chain to get a block with the advanced timestamp
	tr.waitBlocks(chain, 1, time.Minute)
}
