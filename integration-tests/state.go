package main

import (
	"fmt"
	"log"
	"os/exec"
	"regexp"
	"strconv"
	"strings"
	"time"

	clienttypes "github.com/cosmos/ibc-go/modules/core/02-client/types"
	"github.com/tidwall/gjson"
	"gopkg.in/yaml.v2"
)

type State map[chainID]ChainState

type ChainState struct {
	ValBalances *map[validatorID]uint
	Proposals   *map[uint]Proposal
	ValPowers   *map[validatorID]uint
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

type ConsumerProposal struct {
	Deposit       uint
	Chain         chainID
	SpawnTime     int
	InitialHeight clienttypes.Height
	Status        string
}

func (p ConsumerProposal) isProposal() {}

func (s TestRun) getState(modelState State) State {
	TestRunState := State{}
	for k, modelState := range modelState {
		TestRunState[k] = s.getChainState(k, modelState)
	}

	return TestRunState
}

func (s TestRun) getChainState(chain chainID, modelState ChainState) ChainState {
	chainState := ChainState{}

	if modelState.ValBalances != nil {
		valBalances := s.getBalances(chain, *modelState.ValBalances)
		chainState.ValBalances = &valBalances
	}

	if modelState.Proposals != nil {
		proposals := s.getProposals(chain, *modelState.Proposals)
		chainState.Proposals = &proposals
	}

	if modelState.ValPowers != nil {
		s.waitBlocks(chain, 1)
		powers := s.getValPowers(chain, *modelState.ValPowers)
		chainState.ValPowers = &powers
	}

	return chainState
}

var blockHeightRegex = regexp.MustCompile(`block_height: "(\d+)"`)

func (s TestRun) getBlockHeight(chain chainID) uint {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", s.containerConfig.instanceName, s.chainConfigs[chain].binaryName,

		"query", "tendermint-validator-set",

		`--node`, s.getValidatorNode(chain, s.getDefaultValId(chain)),
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

func (s TestRun) waitBlocks(chain chainID, blocks uint) {
	startBlock := s.getBlockHeight(chain)

	for {
		thisBlock := s.getBlockHeight(chain)
		if thisBlock >= startBlock+blocks {
			return
		}
		time.Sleep(100 * time.Millisecond)
	}
}

func (s TestRun) getBalances(chain chainID, modelState map[validatorID]uint) map[validatorID]uint {
	actualState := map[validatorID]uint{}
	for k := range modelState {
		actualState[k] = s.getBalance(chain, k)
	}

	return actualState
}

// TODO: should these maps be strings?
func (s TestRun) getProposals(chain chainID, modelState map[uint]Proposal) map[uint]Proposal {
	actualState := map[uint]Proposal{}
	for k := range modelState {
		actualState[k] = s.getProposal(chain, k)
	}

	return actualState
}

func (s TestRun) getValPowers(chain chainID, modelState map[validatorID]uint) map[validatorID]uint {
	actualState := map[validatorID]uint{}
	for k := range modelState {
		actualState[k] = s.getValPower(chain, k)
	}

	return actualState
}

func (s TestRun) getBalance(chain chainID, val validatorID) uint {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", s.containerConfig.instanceName, s.chainConfigs[chain].binaryName,

		"query", "bank", "balances",
		s.validatorConfigs[val].delAddress,

		`--node`, s.getValidatorNode(chain, s.getDefaultValId(chain)),
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
func (s TestRun) getProposal(chain chainID, proposal uint) Proposal {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", s.containerConfig.instanceName, s.chainConfigs[chain].binaryName,

		"query", "gov", "proposal",
		fmt.Sprint(proposal),

		`--node`, s.getValidatorNode(chain, s.getDefaultValId(chain)),
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
	case "/interchain_security.ccv.provider.v1.CreateConsumerChainProposal":
		chainId := gjson.Get(string(bz), `content.chain_id`).String()
		spawnTime := gjson.Get(string(bz), `content.spawn_time`).Time().Sub(s.containerConfig.now)

		var chain chainID
		for i, conf := range s.chainConfigs {
			if string(conf.chainId) == chainId {
				chain = i
				break
			}
		}

		return ConsumerProposal{
			Deposit:   uint(deposit),
			Status:    status,
			Chain:     chain,
			SpawnTime: int(spawnTime.Milliseconds()),
			InitialHeight: clienttypes.Height{
				RevisionNumber: gjson.Get(string(bz), `content.initial_height.revision_number`).Uint(),
				RevisionHeight: gjson.Get(string(bz), `content.initial_height.revision_height`).Uint(),
			},
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

func (s TestRun) getValPower(chain chainID, valID validatorID) uint {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", s.containerConfig.instanceName, s.chainConfigs[chain].binaryName,

		"query", "tendermint-validator-set",

		`--node`, s.getValidatorNode(chain, s.getDefaultValId(chain)),
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
		if val.Address == s.validatorConfigs[valID].valconsAddress {
			votingPower, err := strconv.Atoi(val.VotingPower)
			if err != nil {
				log.Fatalf("error: %v", err)
			}

			return uint(votingPower)
		}
	}

	log.Fatalf("Validator %v not in tendermint validator set", valID)

	return 0
}

// Obtains the validator corresponding to the first subdirectory (validator node home dir)
// in the specified chain's directory within the docker container
//
// TODO: A better solution to returning a arbitrary validator to fulfill queries is to
// dedicate a full node outside of consensus to fulfill queries.
// See https://github.com/cosmos/interchain-security/issues/263
//
// TODO: It's still possible this method doesn't work as-is. Do more testing
func (s TestRun) getDefaultValId(chain chainID) validatorID {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", s.containerConfig.instanceName, "bash", "-c", `cd /`+string(chain)+`; ls -d */ | awk '{print $1}' | head -n 1`).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// Returned string will be of format: "validator<validator-name>/"
	bzPrefixTrimmed := strings.TrimPrefix(string(bz), "validator")
	bzFullyTrimmed := strings.TrimSuffix(bzPrefixTrimmed, "/")
	if bzPrefixTrimmed == string(bz) || bzFullyTrimmed == string(bz) {
		log.Fatal("unexpected validator subdirectory name: ", bz)
	}

	return validatorID(bzFullyTrimmed)
}

// TODO: panic with err message if string not found in maps
func (s TestRun) getValidatorNode(chain chainID, val validatorID) string {
	return "tcp://" + s.chainConfigs[chain].ipPrefix + "." +
		fmt.Sprint(s.validatorConfigs[val].ipSuffix) + ":26658"
}

// TODO: panic with err message if string not found in maps
func (s TestRun) getValidatorHome(chain chainID, val validatorID) string {
	return `/` + string(chain) + `/validator` + string(val)
}
