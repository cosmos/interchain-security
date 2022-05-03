package main

import (
	"fmt"
	"log"
	"os/exec"
	"regexp"
	"strconv"
	"time"

	clienttypes "github.com/cosmos/ibc-go/modules/core/02-client/types"
	"github.com/tidwall/gjson"
	"gopkg.in/yaml.v2"
)

type State map[uint]ChainState

type ChainState struct {
	ValBalances *map[uint]uint
	Proposals   *map[uint]Proposal
	ValPowers   *map[uint]uint
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
	Chain         uint
	SpawnTime     int
	InitialHeight clienttypes.Height
	Status        string
}

func (p ConsumerProposal) isProposal() {}

type ConsumerGenesis struct {
}

func (s System) getState(modelState State) State {
	systemState := State{}
	for k, modelState := range modelState {
		systemState[k] = s.getChainState(k, modelState)
	}

	return systemState
}

func (s System) getChainState(chain uint, modelState ChainState) ChainState {
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

func (s System) getBlockHeight(chain uint) uint {
	bz, err := exec.Command("docker", "exec", s.containerConfig.instanceName, s.containerConfig.binaryName,

		"query", "tendermint-validator-set",

		`--node`, s.getValidatorNode(chain, s.getValidatorNum(chain)),
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

func (s System) waitBlocks(chain uint, blocks uint) {
	startBlock := s.getBlockHeight(chain)

	for {
		thisBlock := s.getBlockHeight(chain)
		if thisBlock >= startBlock+blocks {
			return
		}
		time.Sleep(100 * time.Millisecond)
	}
}

func (s System) getBalances(chain uint, modelState map[uint]uint) map[uint]uint {
	systemState := map[uint]uint{}
	for k := range modelState {
		systemState[k] = s.getBalance(chain, k)
	}

	return systemState
}

func (s System) getProposals(chain uint, modelState map[uint]Proposal) map[uint]Proposal {
	systemState := map[uint]Proposal{}
	for k := range modelState {
		systemState[k] = s.getProposal(chain, k)
	}

	return systemState
}

func (s System) getValPowers(chain uint, modelState map[uint]uint) map[uint]uint {
	systemState := map[uint]uint{}
	for k := range modelState {
		systemState[k] = s.getValPower(chain, k)
	}

	return systemState
}

func (s System) getBalance(chain uint, validator uint) uint {
	bz, err := exec.Command("docker", "exec", s.containerConfig.instanceName, s.containerConfig.binaryName,

		"query", "bank", "balances",
		s.validatorConfigs[validator].delAddress,

		`--node`, s.getValidatorNode(chain, s.getValidatorNum(chain)),
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
func (s System) getProposal(chain uint, proposal uint) Proposal {
	bz, err := exec.Command("docker", "exec", s.containerConfig.instanceName, s.containerConfig.binaryName,

		"query", "gov", "proposal",
		fmt.Sprint(proposal),

		`--node`, s.getValidatorNode(chain, s.getValidatorNum(chain)),
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

		var chain uint
		for i, conf := range s.chainConfigs {
			if conf.chainId == chainId {
				chain = uint(i)
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

func (s System) getValPower(chain uint, validator uint) uint {
	bz, err := exec.Command("docker", "exec", s.containerConfig.instanceName, s.containerConfig.binaryName,

		"query", "tendermint-validator-set",

		`--node`, s.getValidatorNode(chain, s.getValidatorNum(chain)),
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
		if val.Address == s.validatorConfigs[validator].valconsAddress {
			votingPower, err := strconv.Atoi(val.VotingPower)
			if err != nil {
				log.Fatalf("error: %v", err)
			}

			return uint(votingPower)
		}
	}

	log.Fatalf("Validator %v not in tendermint validator set", validator)

	return 0
}
