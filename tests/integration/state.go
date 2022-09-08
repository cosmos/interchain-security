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

	return chainState
}

var blockHeightRegex = regexp.MustCompile(`block_height: "(\d+)"`)

func (tr TestRun) getBlockHeight(chain chainID) uint {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[chain].binaryName,

		"query", "tendermint-validator-set",

		`--node`, tr.getValidatorNode(chain, tr.getDefaultValidator(chain)),
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

func (tr TestRun) getBalance(chain chainID, validator validatorID) uint {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[chain].binaryName,

		"query", "bank", "balances",
		tr.validatorConfigs[validator].delAddress,

		`--node`, tr.getValidatorNode(chain, tr.getDefaultValidator(chain)),
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

		`--node`, tr.getValidatorNode(chain, tr.getDefaultValidator(chain)),
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

func (tr TestRun) getValPower(chain chainID, validator validatorID) uint {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[chain].binaryName,

		"query", "tendermint-validator-set",

		`--node`, tr.getValidatorNode(chain, tr.getDefaultValidator(chain)),
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

// Gets a default validator for txs and queries using the first subdirectory
// of the directory of the input chain, which will be the home directory
// of one of the validators.
// TODO: Best solution for default validator fulfilling queries etc. is a dedicated, non validating, full node.
// See https://github.com/cosmos/interchain-security/issues/263
func (s TestRun) getDefaultValidator(chain chainID) validatorID {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", s.containerConfig.instanceName, "bash", "-c",
		`cd /`+string(s.chainConfigs[chain].chainId)+
			`; ls -d */ | awk '{print $1}' | head -n 1`).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// Returned string will be of format: "validator<valID literal>/"
	bzPrefixTrimmed := strings.TrimPrefix(string(bz), "validator")
	bzFullyTrimmed := bzPrefixTrimmed[:len(bzPrefixTrimmed)-2]
	if bzPrefixTrimmed == string(bz) || bzFullyTrimmed == string(bz) {
		log.Fatal("unexpected validator subdirectory name: ", bz)
	}

	return validatorID(bzFullyTrimmed)
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
