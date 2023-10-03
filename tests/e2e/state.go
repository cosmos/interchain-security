package main

import (
	"bufio"
	"fmt"
	"log"
	"os/exec"
	"regexp"
	"strconv"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	"github.com/kylelemons/godebug/pretty"
	"github.com/tidwall/gjson"
	"gopkg.in/yaml.v2"
)

type State map[ChainID]ChainState

type ChainState struct {
	ValBalances                    *map[ValidatorID]uint
	Proposals                      *map[uint]Proposal
	ValPowers                      *map[ValidatorID]uint
	StakedTokens                   *map[ValidatorID]uint
	Params                         *[]Param
	Rewards                        *Rewards
	ConsumerChains                 *map[ChainID]bool
	AssignedKeys                   *map[ValidatorID]string
	ProviderKeys                   *map[ValidatorID]string // validatorID: validator provider key
	ConsumerChainQueueSizes        *map[ChainID]uint
	GlobalSlashQueueSize           *uint
	RegisteredConsumerRewardDenoms *[]string
	ClientsFrozenHeights           *map[string]clienttypes.Height
}

type Proposal interface {
	isProposal()
}
type TextProposal struct {
	Title       string
	Description string
	Deposit     uint
	Status      string
}

func (p TextProposal) isProposal() {}

type ConsumerAdditionProposal struct {
	Deposit       uint
	Chain         ChainID
	SpawnTime     int
	InitialHeight clienttypes.Height
	Status        string
}

type UpgradeProposal struct {
	Title         string
	Description   string
	UpgradeHeight uint64
	Type          string
	Deposit       uint
	Status        string
}

func (p UpgradeProposal) isProposal() {}

func (p ConsumerAdditionProposal) isProposal() {}

type ConsumerRemovalProposal struct {
	Deposit  uint
	Chain    ChainID
	StopTime int
	Status   string
}

func (p ConsumerRemovalProposal) isProposal() {}

type Rewards struct {
	IsRewarded map[ValidatorID]bool
	// if true it will calculate if the validator/delegator is rewarded between 2 successive blocks,
	// otherwise it will calculate if it received any rewards since the 1st block
	IsIncrementalReward bool
	// if true checks rewards for "stake" token, otherwise checks rewards from
	// other chains (e.g. false is used to check if provider received rewards from a consumer chain)
	IsNativeDenom bool
}

type ParamsProposal struct {
	Deposit  uint
	Status   string
	Subspace string
	Key      string
	Value    string
}

func (p ParamsProposal) isProposal() {}

type Param struct {
	Subspace string
	Key      string
	Value    string
}

func (tr TestConfig) getState(modelState State) State {
	systemState := State{}
	for k, modelState := range modelState {
		log.Println("Getting model state for chain: ", k)
		systemState[k] = tr.getChainState(k, modelState)
	}

	return systemState
}

func (tr TestConfig) getChainState(chain ChainID, modelState ChainState) ChainState {
	chainState := ChainState{}

	if modelState.ValBalances != nil {
		valBalances := tr.getBalances(chain, *modelState.ValBalances)
		chainState.ValBalances = &valBalances
	}

	if modelState.Proposals != nil {
		proposals := tr.getProposals(chain, *modelState.Proposals)
		chainState.Proposals = &proposals
	}

	if modelState.ValPowers != nil {
		tr.waitBlocks(chain, 1, 10*time.Second)
		powers := tr.getValPowers(chain, *modelState.ValPowers)
		chainState.ValPowers = &powers
	}

	if modelState.StakedTokens != nil {
		representPowers := tr.getStakedTokens(chain, *modelState.StakedTokens)
		chainState.StakedTokens = &representPowers
	}

	if modelState.Params != nil {
		params := tr.getParams(chain, *modelState.Params)
		chainState.Params = &params
	}

	if modelState.Rewards != nil {
		rewards := tr.getRewards(chain, *modelState.Rewards)
		chainState.Rewards = &rewards
	}

	if modelState.ConsumerChains != nil {
		chains := tr.getConsumerChains(chain)
		chainState.ConsumerChains = &chains
	}

	if modelState.AssignedKeys != nil {
		assignedKeys := tr.getConsumerAddresses(chain, *modelState.AssignedKeys)
		chainState.AssignedKeys = &assignedKeys
	}

	if modelState.ProviderKeys != nil {
		providerKeys := tr.getProviderAddresses(chain, *modelState.ProviderKeys)
		chainState.ProviderKeys = &providerKeys
	}

	if modelState.GlobalSlashQueueSize != nil {
		globalQueueSize := tr.getGlobalSlashQueueSize()
		chainState.GlobalSlashQueueSize = &globalQueueSize
	}

	if modelState.ConsumerChainQueueSizes != nil {
		consumerChainQueueSizes := map[ChainID]uint{}
		for c := range *modelState.ConsumerChainQueueSizes {
			consumerChainQueueSizes[c] = tr.getConsumerChainPacketQueueSize(c)
		}
		chainState.ConsumerChainQueueSizes = &consumerChainQueueSizes
	}

	if modelState.RegisteredConsumerRewardDenoms != nil {
		registeredConsumerRewardDenoms := tr.getRegisteredConsumerRewardDenoms(chain)
		chainState.RegisteredConsumerRewardDenoms = &registeredConsumerRewardDenoms
	}

	if modelState.ClientsFrozenHeights != nil {
		chainClientsFrozenHeights := map[string]clienttypes.Height{}
		for id := range *modelState.ClientsFrozenHeights {
			chainClientsFrozenHeights[id] = tr.getClientFrozenHeight(chain, id)
		}
		chainState.ClientsFrozenHeights = &chainClientsFrozenHeights
	}

	if *verbose {
		log.Println("Done getting chain state:\n" + pretty.Sprint(chainState))
	}

	return chainState
}

var blockHeightRegex = regexp.MustCompile(`block_height: "(\d+)"`)

func (tr TestConfig) getBlockHeight(chain ChainID) uint {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,

		"query", "tendermint-validator-set",

		`--node`, tr.getQueryNode(chain),
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	blockHeight, err := strconv.Atoi(blockHeightRegex.FindStringSubmatch(string(bz))[1])
	if err != nil {
		log.Fatal(err)
	}

	return uint(blockHeight)
}

func (tr TestConfig) waitBlocks(chain ChainID, blocks uint, timeout time.Duration) {
	if tr.useCometmock {
		// call advance_blocks method on cometmock
		// curl -H 'Content-Type: application/json' -H 'Accept:application/json' --data '{"jsonrpc":"2.0","method":"advance_blocks","params":{"num_blocks": "36000000"},"id":1}' 127.0.0.1:22331
		tcpAddress := tr.getQueryNodeRPCAddress(chain)
		method := "advance_blocks"
		params := fmt.Sprintf(`{"num_blocks": "%d"}`, blocks)

		tr.curlJsonRPCRequest(method, params, tcpAddress)
		return
	}
	startBlock := tr.getBlockHeight(chain)

	start := time.Now()
	for {
		thisBlock := tr.getBlockHeight(chain)
		if thisBlock >= startBlock+blocks {
			return
		}
		if time.Since(start) > timeout {
			panic(fmt.Sprintf("\n\n\nwaitBlocks method has timed out after: %s\n\n", timeout))
		}
		time.Sleep(time.Second)
	}
}

func (tr TestConfig) waitUntilBlock(chain ChainID, block uint, timeout time.Duration) {
	start := time.Now()
	for {
		thisBlock := tr.getBlockHeight(chain)
		if thisBlock >= block {
			return
		}
		if time.Since(start) > timeout {
			panic(fmt.Sprintf("\n\n\nwaitBlocks method has timed out after: %s\n\n", timeout))
		}
		time.Sleep(500 * time.Millisecond)
	}
}

func (tr TestConfig) getBalances(chain ChainID, modelState map[ValidatorID]uint) map[ValidatorID]uint {
	actualState := map[ValidatorID]uint{}
	for k := range modelState {
		actualState[k] = tr.getBalance(chain, k)
	}

	return actualState
}

func (tr TestConfig) getProposals(chain ChainID, modelState map[uint]Proposal) map[uint]Proposal {
	actualState := map[uint]Proposal{}
	for k := range modelState {
		actualState[k] = tr.getProposal(chain, k)
	}

	return actualState
}

func (tr TestConfig) getValPowers(chain ChainID, modelState map[ValidatorID]uint) map[ValidatorID]uint {
	actualState := map[ValidatorID]uint{}
	for k := range modelState {
		actualState[k] = tr.getValPower(chain, k)
	}

	return actualState
}

func (tr TestConfig) getStakedTokens(chain ChainID, modelState map[ValidatorID]uint) map[ValidatorID]uint {
	actualState := map[ValidatorID]uint{}
	for k := range modelState {
		actualState[k] = tr.getValStakedTokens(chain, k)
	}

	return actualState
}

func (tr TestConfig) getParams(chain ChainID, modelState []Param) []Param {
	actualState := []Param{}
	for _, p := range modelState {
		actualState = append(actualState, Param{Subspace: p.Subspace, Key: p.Key, Value: tr.getParam(chain, p)})
	}

	return actualState
}

func (tr TestConfig) getRewards(chain ChainID, modelState Rewards) Rewards {
	receivedRewards := map[ValidatorID]bool{}

	currentBlock := tr.getBlockHeight(chain)
	tr.waitBlocks(chain, 1, 10*time.Second)
	nextBlock := tr.getBlockHeight(chain)
	tr.waitBlocks(chain, 1, 10*time.Second)

	if !modelState.IsIncrementalReward {
		currentBlock = 1
	}
	for k := range modelState.IsRewarded {
		receivedRewards[k] = tr.getReward(chain, k, nextBlock, modelState.IsNativeDenom) > tr.getReward(chain, k, currentBlock, modelState.IsNativeDenom)
	}

	return Rewards{IsRewarded: receivedRewards, IsIncrementalReward: modelState.IsIncrementalReward, IsNativeDenom: modelState.IsNativeDenom}
}

func (tr TestConfig) getReward(chain ChainID, validator ValidatorID, blockHeight uint, isNativeDenom bool) float64 {
	delAddresss := tr.validatorConfigs[validator].DelAddress
	if chain != ChainID("provi") && tr.validatorConfigs[validator].UseConsumerKey {
		delAddresss = tr.validatorConfigs[validator].ConsumerDelAddress
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,

		"query", "distribution", "rewards",
		delAddresss,

		`--height`, fmt.Sprint(blockHeight),
		`--node`, tr.getQueryNode(chain),
		`-o`, `json`,
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	denomCondition := `total.#(denom!="stake").amount`
	if isNativeDenom {
		denomCondition = `total.#(denom=="stake").amount`
	}

	return gjson.Get(string(bz), denomCondition).Float()
}

func (tr TestConfig) getBalance(chain ChainID, validator ValidatorID) uint {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	valDelAddress := tr.validatorConfigs[validator].DelAddress
	if chain != ChainID("provi") && tr.validatorConfigs[validator].UseConsumerKey {
		valDelAddress = tr.validatorConfigs[validator].ConsumerDelAddress
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,

		"query", "bank", "balances",
		valDelAddress,

		`--node`, tr.getQueryNode(chain),
		`-o`, `json`,
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	amount := gjson.Get(string(bz), `balances.#(denom=="stake").amount`)

	return uint(amount.Uint())
}

var noProposalRegex = regexp.MustCompile(`doesn't exist: key not found`)

// interchain-securityd query gov proposals
func (tr TestConfig) getProposal(chain ChainID, proposal uint) Proposal {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,

		"query", "gov", "proposal",
		fmt.Sprint(proposal),

		`--node`, tr.getQueryNode(chain),
		`-o`, `json`,
	).CombinedOutput()

	prop := TextProposal{}

	if err != nil {
		if noProposalRegex.Match(bz) {
			return prop
		}

		log.Fatal(err, "\n", string(bz))
	}

	propType := gjson.Get(string(bz), `messages.0.content.@type`).String()
	deposit := gjson.Get(string(bz), `total_deposit.#(denom=="stake").amount`).Uint()
	status := gjson.Get(string(bz), `status`).String()

	switch propType {
	case "/cosmos.gov.v1beta1.TextProposal":
		title := gjson.Get(string(bz), `content.title`).String()
		description := gjson.Get(string(bz), `content.description`).String()

		return TextProposal{
			Deposit:     uint(deposit),
			Status:      status,
			Title:       title,
			Description: description,
		}
	case "/interchain_security.ccv.provider.v1.ConsumerAdditionProposal":
		chainId := gjson.Get(string(bz), `messages.0.content.chain_id`).String()
		spawnTime := gjson.Get(string(bz), `messages.0.content.spawn_time`).Time().Sub(tr.containerConfig.Now)

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
				RevisionNumber: gjson.Get(string(bz), `messages.0.content.initial_height.revision_number`).Uint(),
				RevisionHeight: gjson.Get(string(bz), `messages.0.content.initial_height.revision_height`).Uint(),
			},
		}
	case "/cosmos.upgrade.v1beta1.SoftwareUpgradeProposal":
		height := gjson.Get(string(bz), `messages.0.content.plan.height`).Uint()
		title := gjson.Get(string(bz), `messages.0.content.plan.name`).String()
		return UpgradeProposal{
			Deposit:       uint(deposit),
			Status:        status,
			UpgradeHeight: height,
			Title:         title,
			Type:          "/cosmos.upgrade.v1beta1.SoftwareUpgradeProposal",
		}
	case "/interchain_security.ccv.provider.v1.ConsumerRemovalProposal":
		chainId := gjson.Get(string(bz), `messages.0.content.chain_id`).String()
		stopTime := gjson.Get(string(bz), `messages.0.content.stop_time`).Time().Sub(tr.containerConfig.Now)

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
	case "/cosmos.params.v1beta1.ParameterChangeProposal":
		return ParamsProposal{
			Deposit:  uint(deposit),
			Status:   status,
			Subspace: gjson.Get(string(bz), `messages.0.content.changes.0.subspace`).String(),
			Key:      gjson.Get(string(bz), `messages.0.content.changes.0.key`).String(),
			Value:    gjson.Get(string(bz), `messages.0.content.changes.0.value`).String(),
		}
	}

	log.Fatal("unknown proposal type", string(bz))

	return nil
}

type TmValidatorSetYaml struct {
	Total      string `yaml:"total"`
	Validators []struct {
		Address     string    `yaml:"address"`
		VotingPower string    `yaml:"voting_power"`
		PubKey      ValPubKey `yaml:"pub_key"`
	}
}

type ValPubKey struct {
	Value string `yaml:"value"`
}

func (tr TestConfig) getValPower(chain ChainID, validator ValidatorID) uint {
	if *verbose {
		log.Println("getting validator power for chain: ", chain, " validator: ", validator)
	}
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	command := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,

		"query", "tendermint-validator-set",

		`--node`, tr.getQueryNode(chain),
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

	total, err := strconv.Atoi(valset.Total)
	if err != nil {
		log.Fatalf("strconv.Atoi returned an error while coonverting total for validator set: %v, input: %s, validator set: %s", err, valset.Total, pretty.Sprint(valset))
	}

	if total != len(valset.Validators) {
		log.Fatalf("Total number of validators %v does not match number of validators in list %v. Probably a query pagination issue. Validator set: %v",
			valset.Total, uint(len(valset.Validators)), pretty.Sprint(valset))
	}

	for _, val := range valset.Validators {
		if val.Address == tr.validatorConfigs[validator].ValconsAddress ||
			val.Address == tr.validatorConfigs[validator].ConsumerValconsAddress {

			votingPower, err := strconv.Atoi(val.VotingPower)
			if err != nil {
				log.Fatalf("strconv.Atoi returned an error while convering validator voting power: %v, voting power string: %s, validator set: %s", err, val.VotingPower, pretty.Sprint(valset))
			}

			return uint(votingPower)
		}
	}

	// Validator not in set, its validator power is zero.
	return 0
}

func (tr TestConfig) getValStakedTokens(chain ChainID, validator ValidatorID) uint {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,

		"query", "staking", "validator",
		tr.validatorConfigs[validator].ValoperAddress,

		`--node`, tr.getQueryNode(chain),
		`-o`, `json`,
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	amount := gjson.Get(string(bz), `tokens`)

	return uint(amount.Uint())
}

func (tr TestConfig) getParam(chain ChainID, param Param) string {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,

		"query", "params", "subspace",
		param.Subspace,
		param.Key,

		`--node`, tr.getQueryNode(chain),
		`-o`, `json`,
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	value := gjson.Get(string(bz), `value`)

	return value.String()
}

// getConsumerChains returns a list of consumer chains that're being secured by the provider chain,
// determined by querying the provider chain.
func (tr TestConfig) getConsumerChains(chain ChainID) map[ChainID]bool {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,

		"query", "provider", "list-consumer-chains",
		`--node`, tr.getQueryNode(chain),
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

func (tr TestConfig) getConsumerAddresses(chain ChainID, modelState map[ValidatorID]string) map[ValidatorID]string {
	actualState := map[ValidatorID]string{}
	for k := range modelState {
		actualState[k] = tr.getConsumerAddress(chain, k)
	}

	return actualState
}

func (tr TestConfig) getProviderAddresses(chain ChainID, modelState map[ValidatorID]string) map[ValidatorID]string {
	actualState := map[ValidatorID]string{}
	for k := range modelState {
		actualState[k] = tr.getProviderAddressFromConsumer(chain, k)
	}

	return actualState
}

func (tr TestConfig) getConsumerAddress(consumerChain ChainID, validator ValidatorID) string {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[ChainID("provi")].BinaryName,

		"query", "provider", "validator-consumer-key",
		string(consumerChain), tr.validatorConfigs[validator].ValconsAddress,
		`--node`, tr.getQueryNode(ChainID("provi")),
		`-o`, `json`,
	)
	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	addr := gjson.Get(string(bz), "consumer_address").String()
	return addr
}

func (tr TestConfig) getProviderAddressFromConsumer(consumerChain ChainID, validator ValidatorID) string {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[ChainID("provi")].BinaryName,

		"query", "provider", "validator-provider-key",
		string(consumerChain), tr.validatorConfigs[validator].ConsumerValconsAddress,
		`--node`, tr.getQueryNode(ChainID("provi")),
		`-o`, `json`,
	)

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	addr := gjson.Get(string(bz), "provider_address").String()
	return addr
}

func (tr TestConfig) getGlobalSlashQueueSize() uint {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[ChainID("provi")].BinaryName,

		"query", "provider", "throttle-state",
		`--node`, tr.getQueryNode(ChainID("provi")),
		`-o`, `json`,
	)
	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	packets := gjson.Get(string(bz), "packets").Array()
	return uint(len(packets))
}

func (tr TestConfig) getConsumerChainPacketQueueSize(consumerChain ChainID) uint {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[ChainID("provi")].BinaryName,

		"query", "provider", "throttled-consumer-packet-data",
		string(consumerChain),
		`--node`, tr.getQueryNode(ChainID("provi")),
		`-o`, `json`,
	)
	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	size := gjson.Get(string(bz), "size").Uint()
	return uint(size)
}

func (tr TestConfig) getRegisteredConsumerRewardDenoms(chain ChainID) []string {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,

		"query", "provider", "registered-consumer-reward-denoms",
		`--node`, tr.getQueryNode(chain),
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

func (tr TestConfig) getValidatorNode(chain ChainID, validator ValidatorID) string {
	// for CometMock, validatorNodes are all the same address as the query node (which is CometMocks address)
	if tr.useCometmock {
		return tr.getQueryNode(chain)
	}

	return "tcp://" + tr.getValidatorIP(chain, validator) + ":26658"
}

func (tr TestConfig) getValidatorIP(chain ChainID, validator ValidatorID) string {
	return tr.chainConfigs[chain].IpPrefix + "." + tr.validatorConfigs[validator].IpSuffix
}

func (tr TestConfig) getValidatorHome(chain ChainID, validator ValidatorID) string {
	return `/` + string(tr.chainConfigs[chain].ChainId) + `/validator` + fmt.Sprint(validator)
}

// getQueryNode returns query node tcp address on chain.
func (tr TestConfig) getQueryNode(chain ChainID) string {
	return fmt.Sprintf("tcp://%s", tr.getQueryNodeRPCAddress(chain))
}

func (tr TestConfig) getQueryNodeRPCAddress(chain ChainID) string {
	return fmt.Sprintf("%s:26658", tr.getQueryNodeIP(chain))
}

// getQueryNodeIP returns query node IP for chain,
// ipSuffix is hardcoded to be 253 on all query nodes
// except for "sover" chain where there's only one node
func (tr TestConfig) getQueryNodeIP(chain ChainID) string {
	if chain == ChainID("sover") {
		// return address of first and only validator
		return fmt.Sprintf("%s.%s",
			tr.chainConfigs[chain].IpPrefix,
			tr.validatorConfigs[ValidatorID("alice")].IpSuffix)
	}
	return fmt.Sprintf("%s.253", tr.chainConfigs[chain].IpPrefix)
}

func (tr TestConfig) curlJsonRPCRequest(method, params, address string) {
	cmd_template := `curl -H 'Content-Type: application/json' -H 'Accept:application/json' --data '{"jsonrpc":"2.0","method":"%s","params":%s,"id":1}' %s`

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, "bash", "-c", fmt.Sprintf(cmd_template, method, params, address))

	verbosity := false
	executeCommandWithVerbosity(cmd, "curlJsonRPCRequest", verbosity)
}

// getClientFrozenHeight returns the frozen height for a client with the given client ID
// by querying the hosting chain with the given chainID
func (tc TestConfig) getClientFrozenHeight(chain ChainID, clientID string) clienttypes.Height {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tc.containerConfig.InstanceName, tc.chainConfigs[ChainID("provi")].BinaryName,
		"query", "ibc", "client", "state", clientID,
		`--node`, tc.getQueryNode(ChainID("provi")),
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

	return clienttypes.Height{RevisionHeight: uint64(revHeight), RevisionNumber: uint64(revNumber)}
}

func (tc TestConfig) getTrustedHeight(
	chain ChainID,
	clientID string,
	index int,
) clienttypes.Height {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	configureNodeCmd := exec.Command("docker", "exec", tc.containerConfig.InstanceName, "hermes",
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
	return clienttypes.Height{RevisionHeight: uint64(revHeight), RevisionNumber: uint64(revNumber)}
}
