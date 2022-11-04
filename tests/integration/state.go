package main

import (
	"fmt"
	"log"
	"os/exec"
	"regexp"
	"strconv"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	"github.com/tidwall/gjson"
	"gopkg.in/yaml.v2"
)

type State map[chainID]ChainState

type ChainState struct {
	ValBalances          *map[validatorID]uint
	Proposals            *map[uint]Proposal
	ValPowers            *map[validatorID]uint
	RepresentativePowers *map[validatorID]uint
	Params               *[]Param
	Rewards              *Rewards
	ConsumerChains       *map[chainID]bool
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
	Chain         chainID
	SpawnTime     int
	InitialHeight clienttypes.Height
	Status        string
}

func (p ConsumerAdditionProposal) isProposal() {}

type ConsumerRemovalProposal struct {
	Deposit  uint
	Chain    chainID
	StopTime int
	Status   string
}

func (p ConsumerRemovalProposal) isProposal() {}

type Rewards struct {
	IsRewarded map[validatorID]bool
	//if true it will calculate if the validator/delegator is rewarded between 2 successive blocks,
	//otherwise it will calculate if it received any rewards since the 1st block
	IsIncrementalReward bool
	//if true checks rewards for "stake" token, otherwise checks rewards from
	//other chains (e.g. false is used to check if provider received rewards from a consumer chain)
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

func (tr TestRun) getState(modelState State) State {
	systemState := State{}
	for k, modelState := range modelState {
		systemState[k] = tr.getChainState(k, modelState)
	}

	return systemState
}

func (tr TestRun) getChainState(chain chainID, modelState ChainState) ChainState {
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

	if modelState.RepresentativePowers != nil {
		representPowers := tr.getRepresentativePowers(chain, *modelState.RepresentativePowers)
		chainState.RepresentativePowers = &representPowers
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

	return chainState
}

var blockHeightRegex = regexp.MustCompile(`block_height: "(\d+)"`)

func (tr TestRun) getBlockHeight(chain chainID) uint {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[chain].binaryName,

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

func (tr TestRun) waitBlocks(chain chainID, blocks uint, timeout time.Duration) {
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
		time.Sleep(500 * time.Millisecond)
	}
}

func (tr TestRun) getBalances(chain chainID, modelState map[validatorID]uint) map[validatorID]uint {
	actualState := map[validatorID]uint{}
	for k := range modelState {
		actualState[k] = tr.getBalance(chain, k)
	}

	return actualState
}

func (tr TestRun) getProposals(chain chainID, modelState map[uint]Proposal) map[uint]Proposal {
	actualState := map[uint]Proposal{}
	for k := range modelState {
		actualState[k] = tr.getProposal(chain, k)
	}

	return actualState
}

func (tr TestRun) getValPowers(chain chainID, modelState map[validatorID]uint) map[validatorID]uint {
	actualState := map[validatorID]uint{}
	for k := range modelState {
		actualState[k] = tr.getValPower(chain, k)
	}

	return actualState
}

func (tr TestRun) getRepresentativePowers(chain chainID, modelState map[validatorID]uint) map[validatorID]uint {
	actualState := map[validatorID]uint{}
	for k := range modelState {
		actualState[k] = tr.getRepresentativePower(chain, k)
	}

	return actualState
}

func (tr TestRun) getParams(chain chainID, modelState []Param) []Param {
	actualState := []Param{}
	for _, p := range modelState {
		actualState = append(actualState, Param{Subspace: p.Subspace, Key: p.Key, Value: tr.getParam(chain, p)})
	}

	return actualState
}

func (tr TestRun) getRewards(chain chainID, modelState Rewards) Rewards {
	receivedRewards := map[validatorID]bool{}

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

func (tr TestRun) getReward(chain chainID, validator validatorID, blockHeight uint, isNativeDenom bool) float64 {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[chain].binaryName,

		"query", "distribution", "rewards",
		tr.validatorConfigs[validator].delAddress,

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

func (tr TestRun) getBalance(chain chainID, validator validatorID) uint {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[chain].binaryName,

		"query", "bank", "balances",
		tr.validatorConfigs[validator].delAddress,

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
func (tr TestRun) getProposal(chain chainID, proposal uint) Proposal {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[chain].binaryName,

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

	propType := gjson.Get(string(bz), `content.@type`).String()
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
		chainId := gjson.Get(string(bz), `content.chain_id`).String()
		spawnTime := gjson.Get(string(bz), `content.spawn_time`).Time().Sub(tr.containerConfig.now)

		var chain chainID
		for i, conf := range tr.chainConfigs {
			if string(conf.chainId) == chainId {
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
				RevisionNumber: gjson.Get(string(bz), `content.initial_height.revision_number`).Uint(),
				RevisionHeight: gjson.Get(string(bz), `content.initial_height.revision_height`).Uint(),
			},
		}
	case "/interchain_security.ccv.provider.v1.ConsumerRemovalProposal":
		chainId := gjson.Get(string(bz), `content.chain_id`).String()
		stopTime := gjson.Get(string(bz), `content.stop_time`).Time().Sub(tr.containerConfig.now)

		var chain chainID
		for i, conf := range tr.chainConfigs {
			if string(conf.chainId) == chainId {
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
			Subspace: gjson.Get(string(bz), `content.changes.0.subspace`).String(),
			Key:      gjson.Get(string(bz), `content.changes.0.key`).String(),
			Value:    gjson.Get(string(bz), `content.changes.0.value`).String(),
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

func (tr TestRun) getValPower(chain chainID, validator validatorID) uint {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[chain].binaryName,

		"query", "tendermint-validator-set",

		`--node`, tr.getQueryNode(chain),
	).CombinedOutput()

	if err != nil {
		log.Fatalf("error: %v", err)
	}

	valset := TmValidatorSetYaml{}

	err = yaml.Unmarshal(bz, &valset)
	if err != nil {
		log.Fatalf("error: %v", err)
	}

	total, err := strconv.Atoi(valset.Total)
	if err != nil {
		log.Fatalf("error: %v", err)
	}

	if total != len(valset.Validators) {
		log.Fatalf("Total number of validators %v does not match number of validators in list %v. Probably a query pagination issue.",
			valset.Total, uint(len(valset.Validators)))
	}

	for _, val := range valset.Validators {
		if val.Address == tr.validatorConfigs[validator].valconsAddress {
			votingPower, err := strconv.Atoi(val.VotingPower)
			if err != nil {
				log.Fatalf("error: %v", err)
			}

			return uint(votingPower)
		}
	}

	// Validator not in set, its validator power is zero.
	return 0
}

func (tr TestRun) getRepresentativePower(chain chainID, validator validatorID) uint {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[chain].binaryName,

		"query", "staking", "validator",
		tr.validatorConfigs[validator].valoperAddress,

		`--node`, tr.getQueryNode(chain),
		`-o`, `json`,
	).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	amount := gjson.Get(string(bz), `tokens`)

	return uint(amount.Uint())
}

func (tr TestRun) getParam(chain chainID, param Param) string {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[chain].binaryName,

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
func (tr TestRun) getConsumerChains(chain chainID) map[chainID]bool {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[chain].binaryName,

		"query", "provider", "list-consumer-chains",
		`--node`, tr.getQueryNode(chain),
		`-o`, `json`,
	)

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	arr := gjson.Get(string(bz), "chains").Array()
	chains := make(map[chainID]bool)
	for _, c := range arr {
		id := c.Get("chain_id").String()
		chains[chainID(id)] = true
	}

	return chains
}

func (tr TestRun) getValidatorNode(chain chainID, validator validatorID) string {
	return "tcp://" + tr.getValidatorIP(chain, validator) + ":26658"
}

func (tr TestRun) getValidatorIP(chain chainID, validator validatorID) string {
	return tr.chainConfigs[chain].ipPrefix + "." + tr.validatorConfigs[validator].ipSuffix
}

func (tr TestRun) getValidatorHome(chain chainID, validator validatorID) string {
	return `/` + string(tr.chainConfigs[chain].chainId) + `/validator` + fmt.Sprint(validator)
}

// getQueryNode returns query node tcp address on chain.
func (tr TestRun) getQueryNode(chain chainID) string {
	return fmt.Sprintf("tcp://%s:26658", tr.getQueryNodeIP(chain))
}

// getQueryNodeIP returns query node IP for chain,
// ipSuffix is hardcoded to be 253 on all query nodes.
func (tr TestRun) getQueryNodeIP(chain chainID) string {
	return fmt.Sprintf("%s.253", tr.chainConfigs[chain].ipPrefix)
}
