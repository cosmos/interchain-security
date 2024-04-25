package main

import (
	"bufio"
	"encoding/json"
	"fmt"
	"log"
	"os/exec"
	"regexp"
	"strconv"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	e2e "github.com/cosmos/interchain-security/v5/tests/e2e/testlib"
	"github.com/kylelemons/godebug/pretty"
	"github.com/tidwall/gjson"
	"gopkg.in/yaml.v2"
)

// type aliases
type (
	ChainState                = e2e.ChainState
	Proposal                  = e2e.Proposal
	Rewards                   = e2e.Rewards
	TextProposal              = e2e.TextProposal
	UpgradeProposal           = e2e.UpgradeProposal
	ConsumerAdditionProposal  = e2e.ConsumerAdditionProposal
	ConsumerRemovalProposal   = e2e.ConsumerRemovalProposal
	IBCTransferParams         = e2e.IBCTransferParams
	IBCTransferParamsProposal = e2e.IBCTransferParamsProposal
	Param                     = e2e.Param
	ParamsProposal            = e2e.ParamsProposal
	TargetDriver              = e2e.TargetDriver
)

type State map[ChainID]ChainState

type Chain struct {
	target     e2e.TargetDriver
	testConfig TestConfig
}

func (tr Chain) GetChainState(chain ChainID, modelState ChainState) ChainState {

	chainState := ChainState{}

	if modelState.ValBalances != nil {
		valBalances := tr.GetBalances(chain, *modelState.ValBalances)
		chainState.ValBalances = &valBalances
	}

	if modelState.Proposals != nil {
		proposals := tr.GetProposals(chain, *modelState.Proposals)
		chainState.Proposals = &proposals
	}

	if modelState.ProposedConsumerChains != nil {
		proposedConsumerChains := tr.GetProposedConsumerChains(chain)
		chainState.ProposedConsumerChains = &proposedConsumerChains
	}

	if modelState.ValPowers != nil {
		tr.waitBlocks(chain, 1, 10*time.Second)
		powers := tr.GetValPowers(chain, *modelState.ValPowers)
		chainState.ValPowers = &powers
	}

	if modelState.StakedTokens != nil {
		representPowers := tr.GetStakedTokens(chain, *modelState.StakedTokens)
		chainState.StakedTokens = &representPowers
	}

	if modelState.IBCTransferParams != nil {
		params := tr.target.GetIBCTransferParams(chain)
		chainState.IBCTransferParams = &params
	}

	if modelState.Rewards != nil {
		rewards := tr.GetRewards(chain, *modelState.Rewards)
		chainState.Rewards = &rewards
	}

	if modelState.ConsumerChains != nil {
		chains := tr.target.GetConsumerChains(chain)
		chainState.ConsumerChains = &chains
	}

	if modelState.AssignedKeys != nil {
		assignedKeys := tr.GetConsumerAddresses(chain, *modelState.AssignedKeys)
		chainState.AssignedKeys = &assignedKeys
	}

	if modelState.ProviderKeys != nil {
		providerKeys := tr.GetProviderAddresses(chain, *modelState.ProviderKeys)
		chainState.ProviderKeys = &providerKeys
	}

	if modelState.RegisteredConsumerRewardDenoms != nil {
		registeredConsumerRewardDenoms := tr.target.GetRegisteredConsumerRewardDenoms(chain)
		chainState.RegisteredConsumerRewardDenoms = &registeredConsumerRewardDenoms
	}

	if modelState.ClientsFrozenHeights != nil {
		chainClientsFrozenHeights := map[string]clienttypes.Height{}
		for id := range *modelState.ClientsFrozenHeights {
			chainClientsFrozenHeights[id] = tr.GetClientFrozenHeight(chain, id)
		}
		chainState.ClientsFrozenHeights = &chainClientsFrozenHeights
	}

	if modelState.ConsumerPendingPacketQueueSize != nil {
		pendingPacketQueueSize := tr.target.GetPendingPacketQueueSize(chain)
		chainState.ConsumerPendingPacketQueueSize = &pendingPacketQueueSize
	}

	if *verbose {
		log.Println("Done getting chain state:\n" + pretty.Sprint(chainState))
	}

	return chainState
}

func (tr Chain) waitBlocks(chain ChainID, blocks uint, timeout time.Duration) {
	if tr.testConfig.useCometmock {
		// call advance_blocks method on cometmock
		// curl -H 'Content-Type: application/json' -H 'Accept:application/json' --data '{"jsonrpc":"2.0","method":"advance_blocks","params":{"num_blocks": "36000000"},"id":1}' 127.0.0.1:22331
		tcpAddress := tr.target.GetQueryNodeRPCAddress(chain)
		method := "advance_blocks"
		params := fmt.Sprintf(`{"num_blocks": "%d"}`, blocks)

		tr.curlJsonRPCRequest(method, params, tcpAddress)
		return
	}
	startBlock := tr.target.GetBlockHeight(chain)

	start := time.Now()
	for {
		thisBlock := tr.target.GetBlockHeight(chain)
		if thisBlock >= startBlock+blocks {
			return
		}
		if time.Since(start) > timeout {
			panic(fmt.Sprintf("\n\n\nwaitBlocks method has timed out after: %s\n\n", timeout))
		}
		time.Sleep(time.Second)
	}
}

func (tr Chain) waitUntilBlock(chain ChainID, block uint, timeout time.Duration) {
	start := time.Now()
	for {
		thisBlock := tr.target.GetBlockHeight(chain)
		if thisBlock >= block {
			return
		}
		if time.Since(start) > timeout {
			panic(fmt.Sprintf("\n\n\nwaitBlocks method has timed out after: %s\n\n", timeout))
		}
		time.Sleep(500 * time.Millisecond)
	}
}

func (tr Chain) GetBalances(chain ChainID, modelState map[ValidatorID]uint) map[ValidatorID]uint {
	actualState := map[ValidatorID]uint{}
	for k := range modelState {
		actualState[k] = tr.target.GetBalance(chain, k)
	}

	return actualState
}

func (tr Chain) GetClientFrozenHeight(chain ChainID, clientID string) clienttypes.Height {
	revNumber, revHeight := tr.target.GetClientFrozenHeight(chain, clientID)
	return clienttypes.Height{RevisionHeight: uint64(revHeight), RevisionNumber: uint64(revNumber)}
}

func (tr Chain) GetProposedConsumerChains(chain ChainID) []string {
	tr.waitBlocks(chain, 1, 10*time.Second)
	return tr.target.GetProposedConsumerChains(chain)
}

func (tr Chain) GetProposals(chain ChainID, modelState map[uint]Proposal) map[uint]Proposal {
	actualState := map[uint]Proposal{}
	for k := range modelState {
		actualState[k] = tr.target.GetProposal(chain, k)
	}

	return actualState
}

func (tr Chain) GetValPowers(chain ChainID, modelState map[ValidatorID]uint) map[ValidatorID]uint {
	actualState := map[ValidatorID]uint{}
	validatorConfigs := tr.testConfig.validatorConfigs
	for k := range modelState {
		valAddresses := map[string]bool{}
		if chain == ChainID("provi") {
			// use binary with Bech32Prefix set to ProviderAccountPrefix
			valAddresses[validatorConfigs[k].ValconsAddress] = true
		} else {
			// use binary with Bech32Prefix set to ConsumerAccountPrefix
			valAddresses[validatorConfigs[k].ValconsAddressOnConsumer] = true
			valAddresses[validatorConfigs[k].ConsumerValconsAddress] = true
		}
		actualState[k] = tr.target.GetValPower(chain, k)
	}

	return actualState
}

func (tr Chain) GetStakedTokens(chain ChainID, modelState map[ValidatorID]uint) map[ValidatorID]uint {
	actualState := map[ValidatorID]uint{}
	for validator := range modelState {
		validatorConfigs := tr.testConfig.validatorConfigs
		valoperAddress := validatorConfigs[validator].ValoperAddress
		if chain != ChainID("provi") {
			// use binary with Bech32Prefix set to ConsumerAccountPrefix
			if validatorConfigs[validator].UseConsumerKey {
				valoperAddress = validatorConfigs[validator].ConsumerValoperAddress
			} else {
				// use the same address as on the provider but with different prefix
				valoperAddress = validatorConfigs[validator].ValoperAddressOnConsumer
			}
		}

		actualState[validator] = tr.target.GetValStakedTokens(chain, valoperAddress)
	}

	return actualState
}

func (tr Chain) GetRewards(chain ChainID, modelState Rewards) Rewards {
	receivedRewards := map[ValidatorID]bool{}

	currentBlock := tr.target.GetBlockHeight(chain)
	tr.waitBlocks(chain, 1, 10*time.Second)
	nextBlock := tr.target.GetBlockHeight(chain)
	tr.waitBlocks(chain, 1, 10*time.Second)

	if !modelState.IsIncrementalReward {
		currentBlock = 1
	}
	for k := range modelState.IsRewarded {
		receivedRewards[k] = tr.target.GetReward(chain, k, nextBlock, modelState.IsNativeDenom) > tr.target.GetReward(chain, k, currentBlock, modelState.IsNativeDenom)
	}

	return Rewards{IsRewarded: receivedRewards, IsIncrementalReward: modelState.IsIncrementalReward, IsNativeDenom: modelState.IsNativeDenom}
}

func (tr Chain) GetConsumerAddresses(chain ChainID, modelState map[ValidatorID]string) map[ValidatorID]string {
	actualState := map[ValidatorID]string{}
	for k := range modelState {
		actualState[k] = tr.target.GetConsumerAddress(chain, k)
	}

	return actualState
}

func (tr Chain) GetProviderAddresses(chain ChainID, modelState map[ValidatorID]string) map[ValidatorID]string {
	actualState := map[ValidatorID]string{}
	for k := range modelState {
		actualState[k] = tr.target.GetProviderAddressFromConsumer(chain, k)
	}

	return actualState
}

func (tr Chain) getValidatorNode(chain ChainID, validator ValidatorID) string {
	// for CometMock, validatorNodes are all the same address as the query node (which is CometMocks address)
	if tr.testConfig.useCometmock {
		return tr.target.GetQueryNode(chain)
	}

	return "tcp://" + tr.getValidatorIP(chain, validator) + ":26658"
}

func (tr Chain) getValidatorIP(chain ChainID, validator ValidatorID) string {
	return tr.testConfig.chainConfigs[chain].IpPrefix + "." + tr.testConfig.validatorConfigs[validator].IpSuffix
}

func (tr Chain) getValidatorHome(chain ChainID, validator ValidatorID) string {
	return `/` + string(tr.testConfig.chainConfigs[chain].ChainId) + `/validator` + fmt.Sprint(validator)
}

func (tr Chain) curlJsonRPCRequest(method, params, address string) {
	cmd_template := `curl -H 'Content-Type: application/json' -H 'Accept:application/json' --data '{"jsonrpc":"2.0","method":"%s","params":%s,"id":1}' %s`

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//cmd := exec.Command("docker", "exec", tr.testConfig.containerConfig.InstanceName, "bash", "-c", fmt.Sprintf(cmd_template, method, params, address))
	cmd := tr.target.ExecCommand("bash", "-c", fmt.Sprintf(cmd_template, method, params, address))

	verbosity := false
	e2e.ExecuteCommandWithVerbosity(cmd, "curlJsonRPCRequest", verbosity)
}

func uintPtr(i uint) *uint {
	return &i
}

type DriverV5 struct {
	containerConfig  ContainerConfig // FIXME only needed for 'Now' time tracking
	validatorConfigs map[ValidatorID]ValidatorConfig
	chainConfigs     map[ChainID]ChainConfig
	target           e2e.PlatformDriver
}

func (tr DriverV5) ExecCommand(name string, arg ...string) *exec.Cmd {
	return tr.target.ExecCommand(name, arg...)
}

func (tr DriverV5) ExecDetachedCommand(name string, args ...string) *exec.Cmd {
	return tr.target.ExecDetachedCommand(name, args...)
}

func (tr DriverV5) GetTestScriptPath(isConsumer bool, script string) string {
	return tr.target.GetTestScriptPath(isConsumer, script)
}

func (tr DriverV5) GetBlockHeight(chain ChainID) uint {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//bz, err := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,
	binaryName := tr.chainConfigs[chain].BinaryName
	bz, err := tr.target.ExecCommand(binaryName,

		"query", "tendermint-validator-set",

		`--node`, tr.GetQueryNode(chain),
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	blockHeightRegex := regexp.MustCompile(`block_height: "(\d+)"`)
	blockHeight, err := strconv.Atoi(blockHeightRegex.FindStringSubmatch(string(bz))[1])
	if err != nil {
		log.Fatal(err)
	}

	return uint(blockHeight)
}

func (tr DriverV5) GetReward(chain ChainID, validator ValidatorID, blockHeight uint, isNativeDenom bool) float64 {
	valCfg := tr.validatorConfigs[validator]
	delAddresss := valCfg.DelAddress
	if chain != ChainID("provi") {
		// use binary with Bech32Prefix set to ConsumerAccountPrefix
		if valCfg.UseConsumerKey {
			delAddresss = valCfg.ConsumerDelAddress
		} else {
			// use the same address as on the provider but with different prefix
			delAddresss = valCfg.DelAddressOnConsumer
		}
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,
	binaryName := tr.chainConfigs[chain].BinaryName
	cmd := tr.target.ExecCommand(binaryName,
		"query", "distribution", "delegation-total-rewards",
		"--delegator-address", delAddresss,
		`--height`, fmt.Sprint(blockHeight),
		`--node`, tr.GetQueryNode(chain),
		`-o`, `json`,
	)

	bz, err := cmd.CombinedOutput()

	if err != nil {
		log.Fatal("failed getting rewards: ", err, "\n", string(bz))
	}

	denomCondition := `total.#(denom!="stake").amount`
	if isNativeDenom {
		denomCondition = `total.#(denom=="stake").amount`
	}

	return gjson.Get(string(bz), denomCondition).Float()
}

// interchain-securityd query gov proposals
func (tr DriverV5) GetProposal(chain ChainID, proposal uint) Proposal {
	var noProposalRegex = regexp.MustCompile(`doesn't exist: key not found`)
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//bz, err := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,
	binaryName := tr.chainConfigs[chain].BinaryName
	bz, err := tr.target.ExecCommand(binaryName,
		"query", "gov", "proposal",
		fmt.Sprint(proposal),
		`--node`, tr.GetQueryNode(chain),
		`-o`, `json`,
	).CombinedOutput()

	prop := TextProposal{}

	if err != nil {
		if noProposalRegex.Match(bz) {
			return prop
		}

		log.Fatal(err, "\n", string(bz))
	}

	// for legacy proposal types submitted using "tx submit-legacyproposal" (cosmos-sdk/v1/MsgExecLegacyContent)
	propType := gjson.Get(string(bz), `proposal.messages.0.value.content.type`).String()
	rawContent := gjson.Get(string(bz), `proposal.messages.0.value.content.value`)

	// for current (>= v47) prop types submitted using "tx submit-proposal"
	if propType == "" {
		propType = gjson.Get(string(bz), `proposal.messages.0.type`).String()
		rawContent = gjson.Get(string(bz), `proposal.messages.0.value`)
	}

	title := gjson.Get(string(bz), `proposal.title`).String()
	deposit := gjson.Get(string(bz), `proposal.total_deposit.#(denom=="stake").amount`).Uint()
	status := gjson.Get(string(bz), `proposal.status`).String()

	switch propType {
	case "/cosmos.gov.v1beta1.TextProposal":
		title := rawContent.Get("title").String()
		description := rawContent.Get("description").String()

		return TextProposal{
			Deposit:     uint(deposit),
			Status:      status,
			Title:       title,
			Description: description,
		}
	case "/interchain_security.ccv.provider.v1.ConsumerAdditionProposal":
		chainId := rawContent.Get("chain_id").String()
		spawnTime := rawContent.Get("spawn_time").Time().Sub(tr.containerConfig.Now)

		var chain ChainID
		for i, conf := range tr.chainConfigs {
			if string(conf.ChainId) == chainId {
				chain = i
				break
			}
		}

		return ConsumerAdditionProposal{
			Deposit:   uint(deposit),
			Status:    status,
			Chain:     chain,
			SpawnTime: int(spawnTime.Milliseconds()),
			InitialHeight: clienttypes.Height{
				RevisionNumber: rawContent.Get("initial_height.revision_number").Uint(),
				RevisionHeight: rawContent.Get("initial_height.revision_height").Uint(),
			},
		}
	case "/cosmos.upgrade.v1beta1.SoftwareUpgradeProposal":
		height := rawContent.Get("plan.height").Uint()
		title := rawContent.Get("plan.name").String()
		return UpgradeProposal{
			Deposit:       uint(deposit),
			Status:        status,
			UpgradeHeight: height,
			Title:         title,
			Type:          "/cosmos.upgrade.v1beta1.SoftwareUpgradeProposal",
		}
	case "/interchain_security.ccv.provider.v1.ConsumerRemovalProposal":
		chainId := rawContent.Get("chain_id").String()
		stopTime := rawContent.Get("stop_time").Time().Sub(tr.containerConfig.Now)

		var chain ChainID
		for i, conf := range tr.chainConfigs {
			if string(conf.ChainId) == chainId {
				chain = i
				break
			}
		}

		return ConsumerRemovalProposal{
			Deposit:  uint(deposit),
			Status:   status,
			Chain:    chain,
			StopTime: int(stopTime.Milliseconds()),
		}
	case "/ibc.applications.transfer.v1.MsgUpdateParams":
		var params IBCTransferParams
		if err := json.Unmarshal([]byte(rawContent.Get("params").String()), &params); err != nil {
			log.Fatal("cannot unmarshal ibc-transfer params: ", err, "\n", string(bz))
		}

		return IBCTransferParamsProposal{
			Deposit: uint(deposit),
			Status:  status,
			Title:   title,
			Params:  params,
		}
	}

	log.Fatal("received unknown proposal type: ", propType, "proposal JSON:", string(bz))

	return nil
}

type TmValidatorSetYaml struct {
	BlockHeight string `yaml:"block_height"`
	Pagination  struct {
		NextKey string `yaml:"next_key"`
		Total   string `yaml:"total"`
	} `yaml:"pagination"`
	Validators []struct {
		Address     string    `yaml:"address"`
		VotingPower string    `yaml:"voting_power"`
		PubKey      ValPubKey `yaml:"pub_key"`
	}
}

type ValPubKey struct {
	Value string `yaml:"value"`
}

// TODO (mpoke) Return powers for multiple validators
func (tr DriverV5) GetValPower(chain ChainID, validator ValidatorID) uint {
	if *verbose {
		log.Println("getting validator power for chain: ", chain, " validator: ", validator)
	}
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//command := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,
	binaryName := tr.chainConfigs[chain].BinaryName
	command := tr.target.ExecCommand(binaryName,

		"query", "tendermint-validator-set",

		`--node`, tr.GetQueryNode(chain),
	)
	bz, err := command.CombinedOutput()
	if err != nil {
		log.Fatalf("encountered an error when executing command '%s': %v, output: %s", command.String(), err, string(bz))
	}

	valset := TmValidatorSetYaml{}

	err = yaml.Unmarshal(bz, &valset)
	if err != nil {
		log.Fatalf("yaml.Unmarshal returned an error while unmarshalling validator set: %v, input: %s", err, string(bz))
	}

	total, err := strconv.Atoi(valset.Pagination.Total)
	if err != nil {
		log.Fatalf("strconv.Atoi returned an error while coonverting total for validator set: %v, input: %s, validator set: %s", err, valset.Pagination.Total, pretty.Sprint(valset))
	}

	if total != len(valset.Validators) {
		log.Fatalf("Total number of validators %v does not match number of validators in list %v. Probably a query pagination issue. Validator set: %v",
			valset.Pagination.Total, uint(len(valset.Validators)), pretty.Sprint(valset))
	}

	for _, val := range valset.Validators {
		if chain == ChainID("provi") {
			// use binary with Bech32Prefix set to ProviderAccountPrefix
			if val.Address != tr.validatorConfigs[validator].ValconsAddress {
				continue
			}
		} else {
			// use binary with Bech32Prefix set to ConsumerAccountPrefix
			if val.Address != tr.validatorConfigs[validator].ValconsAddressOnConsumer &&
				val.Address != tr.validatorConfigs[validator].ConsumerValconsAddress {
				continue
			}
		}

		votingPower, err := strconv.Atoi(val.VotingPower)
		if err != nil {
			log.Fatalf("strconv.Atoi returned an error while converting validator voting power: %v, voting power string: %s, validator set: %s", err, val.VotingPower, pretty.Sprint(valset))
		}

		return uint(votingPower)
	}

	// Validator not in set, its validator power is zero.
	return 0
}

func (tr DriverV5) GetBalance(chain ChainID, validator ValidatorID) uint {
	valCfg := tr.validatorConfigs[validator]
	valDelAddress := valCfg.DelAddress
	if chain != ChainID("provi") {
		// use binary with Bech32Prefix set to ConsumerAccountPrefix
		if valCfg.UseConsumerKey {
			valDelAddress = valCfg.ConsumerDelAddress
		} else {
			// use the same address as on the provider but with different prefix
			valDelAddress = valCfg.DelAddressOnConsumer
		}
	}
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,
	binaryName := tr.chainConfigs[chain].BinaryName
	cmd := tr.target.ExecCommand(binaryName,

		"query", "bank", "balances",
		valDelAddress,

		`--node`, tr.GetQueryNode(chain),
		`-o`, `json`,
	)
	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal("getBalance() failed: ", cmd, ": ", err, "\n", string(bz))
	}

	amount := gjson.Get(string(bz), `balances.#(denom=="stake").amount`)

	return uint(amount.Uint())
}

func (tr DriverV5) GetValStakedTokens(chain ChainID, valoperAddress string) uint {

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//bz, err := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,
	binaryName := tr.chainConfigs[chain].BinaryName
	bz, err := tr.target.ExecCommand(binaryName,

		"query", "staking", "validator",
		valoperAddress,

		`--node`, tr.GetQueryNode(chain),
		`-o`, `json`,
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	amount := gjson.Get(string(bz), `validator.tokens`)

	return uint(amount.Uint())
}

func (tr DriverV5) GetParam(chain ChainID, param Param) string {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//bz, err := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,

	binaryName := tr.chainConfigs[chain].BinaryName
	bz, err := tr.target.ExecCommand(binaryName,
		"query", "params", "subspace",
		param.Subspace,
		param.Key,

		`--node`, tr.GetQueryNode(chain),
		`-o`, `json`,
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	value := gjson.Get(string(bz), `value`)

	return value.String()
}

func (tr DriverV5) GetIBCTransferParams(chain ChainID) IBCTransferParams {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//bz, err := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,
	binaryName := tr.chainConfigs[chain].BinaryName
	bz, err := tr.target.ExecCommand(binaryName,
		"query", "ibc-transfer", "params",
		`--node`, tr.GetQueryNode(chain),
		`-o`, `json`,
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	var params IBCTransferParams
	if err := json.Unmarshal(bz, &params); err != nil {
		log.Fatal("cannot unmarshal ibc-transfer params: ", err, "\n", string(bz))
	}

	return params
}

// GetConsumerChains returns a list of consumer chains that're being secured by the provider chain,
// determined by querying the provider chain.
func (tr DriverV5) GetConsumerChains(chain ChainID) map[ChainID]bool {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,
	binaryName := tr.chainConfigs[chain].BinaryName
	cmd := tr.target.ExecCommand(binaryName,

		"query", "provider", "list-consumer-chains",
		`--node`, tr.GetQueryNode(chain),
		`-o`, `json`,
	)

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	arr := gjson.Get(string(bz), "chains").Array()
	chains := make(map[ChainID]bool)
	for _, c := range arr {
		id := c.Get("chain_id").String()
		chains[ChainID(id)] = true
	}

	return chains
}

func (tr DriverV5) GetConsumerAddress(consumerChain ChainID, validator ValidatorID) string {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[ChainID("provi")].BinaryName,

	binaryName := tr.chainConfigs[ChainID("provi")].BinaryName
	cmd := tr.target.ExecCommand(binaryName,

		"query", "provider", "validator-consumer-key",
		string(consumerChain), tr.validatorConfigs[validator].ValconsAddress,
		`--node`, tr.GetQueryNode(ChainID("provi")),
		`-o`, `json`,
	)
	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	addr := gjson.Get(string(bz), "consumer_address").String()
	return addr
}

func (tr DriverV5) GetProviderAddressFromConsumer(consumerChain ChainID, validator ValidatorID) string {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[ChainID("provi")].BinaryName,
	binaryName := tr.chainConfigs[ChainID("provi")].BinaryName

	cmd := tr.target.ExecCommand(binaryName,

		"query", "provider", "validator-provider-key",
		string(consumerChain), tr.validatorConfigs[validator].ConsumerValconsAddressOnProvider,
		`--node`, tr.GetQueryNode(ChainID("provi")),
		`-o`, `json`,
	)

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Println("error running ", cmd)
		log.Fatal(err, "\n", string(bz))
	}

	addr := gjson.Get(string(bz), "provider_address").String()
	return addr
}

func (tr DriverV5) GetSlashMeter() int64 {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//cmd := exec.Command("docker", "exec",
	binaryName := tr.chainConfigs[ChainID("provi")].BinaryName

	cmd := tr.target.ExecCommand(binaryName,

		"query", "provider", "throttle-state",
		`--node`, tr.GetQueryNode(ChainID("provi")),
		`-o`, `json`,
	)
	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	slashMeter := gjson.Get(string(bz), "slash_meter")
	return slashMeter.Int()
}

func (tr DriverV5) GetRegisteredConsumerRewardDenoms(chain ChainID) []string {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,
	binaryName := tr.chainConfigs[chain].BinaryName

	cmd := tr.target.ExecCommand(binaryName,

		"query", "provider", "registered-consumer-reward-denoms",
		`--node`, tr.GetQueryNode(chain),
		`-o`, `json`,
	)
	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	denoms := gjson.Get(string(bz), "denoms").Array()
	rewardDenoms := make([]string, len(denoms))
	for i, d := range denoms {
		rewardDenoms[i] = d.String()
	}

	return rewardDenoms
}

func (tr DriverV5) GetPendingPacketQueueSize(chain ChainID) uint {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,
	binaryName := tr.chainConfigs[chain].BinaryName
	cmd := tr.target.ExecCommand(binaryName,

		"query", "ccvconsumer", "throttle-state",
		`--node`, tr.GetQueryNode(chain),
		`-o`, `json`,
	)
	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	if !gjson.ValidBytes(bz) {
		panic("invalid json response from query ccvconsumer throttle-state: " + string(bz))
	}

	packetData := gjson.Get(string(bz), "packet_data_queue").Array()
	return uint(len(packetData))
}

// GetClientFrozenHeight returns the frozen height for a client with the given client ID
// by querying the hosting chain with the given chainID
func (tr DriverV5) GetClientFrozenHeight(chain ChainID, clientID string) (uint64, uint64) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[ChainID("provi")].BinaryName,
	binaryName := tr.chainConfigs[ChainID("provi")].BinaryName
	cmd := tr.target.ExecCommand(binaryName,
		"query", "ibc", "client", "state", clientID,
		`--node`, tr.GetQueryNode(ChainID("provi")),
		`-o`, `json`,
	)

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	frozenHeight := gjson.Get(string(bz), "client_state.frozen_height")

	revHeight, err := strconv.Atoi(frozenHeight.Get("revision_height").String())
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	revNumber, err := strconv.Atoi(frozenHeight.Get("revision_number").String())
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	return uint64(revHeight), uint64(revNumber)
}

func (tr DriverV5) GetTrustedHeight(
	chain ChainID,
	clientID string,
	index int,
) (uint64, uint64) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//configureNodeCmd := exec.Command("docker", "exec", tc.testConfig.containerConfig.InstanceName, "hermes",
	configureNodeCmd := tr.target.ExecCommand("hermes",
		"--json", "query", "client", "consensus", "--chain", string(chain),
		`--client`, clientID,
	)

	cmdReader, err := configureNodeCmd.StdoutPipe()
	if err != nil {
		log.Fatal(err)
	}

	configureNodeCmd.Stderr = configureNodeCmd.Stdout

	if err := configureNodeCmd.Start(); err != nil {
		log.Fatal(err)
	}

	scanner := bufio.NewScanner(cmdReader)

	var trustedHeight gjson.Result
	// iterate on the relayer's response
	// and parse the the command "result"
	for scanner.Scan() {
		out := scanner.Text()
		if len(gjson.Get(out, "result").Array()) > 0 {
			trustedHeight = gjson.Get(out, "result").Array()[index]
			break
		}
	}

	revHeight, err := strconv.Atoi(trustedHeight.Get("revision_height").String())
	if err != nil {
		log.Fatal(err)
	}

	revNumber, err := strconv.Atoi(trustedHeight.Get("revision_number").String())
	if err != nil {
		log.Fatal(err)
	}
	return uint64(revHeight), uint64(revNumber)
}

func (tr DriverV5) GetProposedConsumerChains(chain ChainID) []string {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//bz, err := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,
	binaryName := tr.chainConfigs[chain].BinaryName
	bz, err := tr.target.ExecCommand(binaryName,
		"query", "provider", "list-proposed-consumer-chains",
		`--node`, tr.GetQueryNode(chain),
		`-o`, `json`,
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	arr := gjson.Get(string(bz), "proposedChains").Array()
	chains := []string{}
	for _, c := range arr {
		cid := c.Get("chainID").String()
		chains = append(chains, cid)
	}

	return chains
}

// getQueryNode returns query node tcp address on chain.
func (tr DriverV5) GetQueryNode(chain ChainID) string {
	return fmt.Sprintf("tcp://%s", tr.GetQueryNodeRPCAddress(chain))
}

func (tr DriverV5) GetQueryNodeRPCAddress(chain ChainID) string {
	return fmt.Sprintf("%s:26658", tr.GetQueryNodeIP(chain))
}

// getQueryNodeIP returns query node IP for chain,
// ipSuffix is hardcoded to be 253 on all query nodes
// except for "sover" chain where there's only one node
func (tr DriverV5) GetQueryNodeIP(chain ChainID) string {
	if chain == ChainID("sover") {
		// return address of first and only validator
		return fmt.Sprintf("%s.%s",
			tr.chainConfigs[chain].IpPrefix,
			tr.validatorConfigs[ValidatorID("alice")].IpSuffix)
	}
	return fmt.Sprintf("%s.253", tr.chainConfigs[chain].IpPrefix)
}
