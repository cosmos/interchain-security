package main

import (
	"bufio"
	"encoding/json"
	"fmt"
	"log"
	"os/exec"
	"regexp"
	"sort"
	"strconv"
	"strings"

	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	"github.com/kylelemons/godebug/pretty"
	"github.com/tidwall/gjson"
	"gopkg.in/yaml.v2"

	e2e "github.com/cosmos/interchain-security/v6/tests/e2e/testlib"
	"github.com/cosmos/interchain-security/v6/x/ccv/provider/types"
)

// Commands contains a collection of commands which can executed
// on the current implementation of the provider/consumer
// Note: for different versions see e2e/v*
type Commands struct {
	Verbose          bool
	ContainerConfig  *e2e.ContainerConfig
	ValidatorConfigs map[ValidatorID]ValidatorConfig
	ChainConfigs     map[ChainID]ChainConfig
	Target           e2e.PlatformDriver
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

func (tr Commands) UseCometMock() bool {
	return tr.Target.UseCometMock()
}

func (tr Commands) ExecCommand(name string, arg ...string) *exec.Cmd {
	return tr.Target.ExecCommand(name, arg...)
}

func (tr Commands) ExecDetachedCommand(name string, args ...string) *exec.Cmd {
	return tr.Target.ExecDetachedCommand(name, args...)
}

func (tr Commands) GetTestScriptPath(isConsumer bool, script string) string {
	return tr.Target.GetTestScriptPath(isConsumer, script)
}

func (tr Commands) GetBlockHeight(chain ChainID) uint {
	binaryName := tr.ChainConfigs[chain].BinaryName
	bz, err := tr.Target.ExecCommand(binaryName,

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

func (tr Commands) GetReward(chain ChainID, validator ValidatorID, blockHeight uint, denom string) float64 {
	valCfg := tr.ValidatorConfigs[validator]
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

	binaryName := tr.ChainConfigs[chain].BinaryName
	cmd := tr.Target.ExecCommand(binaryName,
		"query", "distribution", "rewards",
		delAddresss,
		`--height`, fmt.Sprint(blockHeight),
		`--node`, tr.GetQueryNode(chain),
		`-o`, `json`,
	)

	if *verbose {
		log.Println("getting rewards for chain: ", chain, " validator: ", validator, " blockHeight: ", blockHeight)
		log.Println(cmd)
	}

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Println("running cmd: ", cmd)
		log.Fatal("failed getting rewards: ", err, "\n", string(bz))
	}

	denomCondition := fmt.Sprintf(`total.#(%%"*%s*")`, denom)
	amount := strings.Split(gjson.Get(string(bz), denomCondition).String(), denom)[0]

	res := float64(0)
	if amount != "" {
		res, err = strconv.ParseFloat(amount, 64)
		if err != nil {
			log.Fatal("failed parsing consumer reward:", err)
		}
	}

	return res
}

// interchain-securityd query gov proposals
func (tr Commands) GetProposal(chain ChainID, proposal uint) Proposal {
	noProposalRegex := regexp.MustCompile(`doesn't exist: key not found`)

	binaryName := tr.ChainConfigs[chain].BinaryName
	cmd := tr.Target.ExecCommand(binaryName,
		"query", "gov", "proposal",
		fmt.Sprint(proposal),
		`--node`, tr.GetQueryNode(chain),
		`-o`, `json`)
	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Println("Error getting governance proposal", proposal, "\n\t cmd: ", cmd, "\n\t err:", err, "\n\t out: ", string(bz))
	}

	prop := TextProposal{}
	propRaw := string(bz)
	if err != nil {
		if noProposalRegex.Match(bz) {
			return prop
		}

		log.Fatal(err, "\n", propRaw)
	}

	// for legacy proposal types submitted using "tx submit-legacyproposal" (cosmos-sdk/v1/MsgExecLegacyContent)
	propType := gjson.Get(propRaw, `proposal.messages.0.value.content.type`).String()
	rawContent := gjson.Get(propRaw, `proposal.messages.0.value.content.value`)

	// for current (>= v47) prop types submitted using "tx submit-proposal"
	if propType == "" {
		propType = gjson.Get(propRaw, `proposal.messages.0.type`).String()
		rawContent = gjson.Get(propRaw, `proposal.messages.0.value`)
	}

	title := gjson.Get(propRaw, `proposal.title`).String()
	deposit := gjson.Get(propRaw, `proposal.total_deposit.#(denom=="stake").amount`).Uint()
	status := gjson.Get(propRaw, `proposal.status`).String()

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
	case "/interchain_security.ccv.provider.v1.MsgUpdateConsumer":
		consumerId := rawContent.Get("consumer_id").String()
		consumerChainId := ChainID("")
		for _, chainCfg := range tr.ChainConfigs {
			if chainCfg.ConsumerId == e2e.ConsumerID(consumerId) {
				consumerChainId = chainCfg.ChainId
				break
			}
		}

		updateProposal := ConsumerAdditionProposal{
			Deposit: uint(deposit),
			Chain:   consumerChainId,
			Status:  status,
		}
		if rawContent.Get("initialization_parameters").Exists() {
			spawnTime := rawContent.Get("initialization_parameters.spawn_time").Time().Sub(tr.ContainerConfig.Now)
			updateProposal.SpawnTime = int(spawnTime.Milliseconds())
			updateProposal.InitialHeight = clienttypes.Height{
				RevisionNumber: rawContent.Get("initialization_parameters.initial_height.revision_number").Uint(),
				RevisionHeight: rawContent.Get("initialization_parameters.initial_height.revision_height").Uint(),
			}
		}
		return updateProposal
	case "/interchain_security.ccv.provider.v1.MsgConsumerAddition":
		chainId := rawContent.Get("chain_id").String()
		spawnTime := rawContent.Get("spawn_time").Time().Sub(tr.ContainerConfig.Now)

		var chain ChainID
		for i, conf := range tr.ChainConfigs {
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
	case "cosmos-sdk/MsgSoftwareUpgrade":
		height := rawContent.Get("plan.height").Uint()
		title := rawContent.Get("plan.name").String()
		return UpgradeProposal{
			Deposit:       uint(deposit),
			Status:        status,
			UpgradeHeight: height,
			Title:         title,
			Type:          "/cosmos.upgrade.v1beta1.SoftwareUpgradeProposal",
		}
	case "/interchain_security.ccv.provider.v1.MsgRemoveConsumer":
		consumerId := rawContent.Get("consumer_id").String()

		var chain ChainID
		for i, conf := range tr.ChainConfigs {
			if string(conf.ConsumerId) == consumerId {
				chain = i
				break
			}
		}

		return ConsumerRemovalProposal{
			Deposit: uint(deposit),
			Status:  status,
			Chain:   chain,
		}
	case "/ibc.applications.transfer.v1.MsgUpdateParams":
		var params IBCTransferParams
		if err := json.Unmarshal([]byte(rawContent.Get("params").String()), &params); err != nil {
			log.Fatal("cannot unmarshal ibc-transfer params: ", err, "\n", propRaw)
		}

		return IBCTransferParamsProposal{
			Deposit: uint(deposit),
			Status:  status,
			Title:   title,
			Params:  params,
		}

	case "/interchain_security.ccv.provider.v1.MsgConsumerModification":
		chainId := rawContent.Get("chain_id").String()

		var chain ChainID
		for i, conf := range tr.ChainConfigs {
			if string(conf.ChainId) == chainId {
				chain = i
				break
			}
		}

		return ConsumerModificationProposal{
			Deposit: uint(deposit),
			Status:  status,
			Chain:   chain,
		}
	case "/cosmos.params.v1beta1.ParameterChangeProposal":
		return ParamsProposal{
			Deposit:  uint(deposit),
			Status:   status,
			Subspace: gjson.Get(propRaw, `messages.0.content.changes.0.subspace`).String(),
			Key:      gjson.Get(propRaw, `messages.0.content.changes.0.key`).String(),
			Value:    gjson.Get(propRaw, `messages.0.content.changes.0.value`).String(),
		}
	}

	log.Fatal("received unknown proposal type: '", propType, "', proposal JSON:", propRaw)

	return nil
}

// TODO (mpoke) Return powers for multiple validators
func (tr Commands) GetValPower(chain ChainID, validator ValidatorID) uint {
	if *verbose {
		log.Println("getting validator power for chain: ", chain, " validator: ", validator)
	}
	binaryName := tr.ChainConfigs[chain].BinaryName
	command := tr.Target.ExecCommand(binaryName,

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
		log.Fatalf("strconv.Atoi returned an error while converting total for validator set: %v, input: %s, validator set: %s, src:%s",
			err, valset.Pagination.Total, pretty.Sprint(valset), string(bz))
	}

	if total != len(valset.Validators) {
		log.Fatalf("Total number of validators %v does not match number of validators in list %v. Probably a query pagination issue. Validator set: %v",
			valset.Pagination.Total, uint(len(valset.Validators)), pretty.Sprint(valset))
	}

	for _, val := range valset.Validators {
		if chain == ChainID("provi") {
			// use binary with Bech32Prefix set to ProviderAccountPrefix
			if val.Address != tr.ValidatorConfigs[validator].ValconsAddress {
				continue
			}
		} else {
			// use binary with Bech32Prefix set to ConsumerAccountPrefix
			if val.Address != tr.ValidatorConfigs[validator].ValconsAddressOnConsumer &&
				val.Address != tr.ValidatorConfigs[validator].ConsumerValconsAddress {
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

func (tr Commands) GetBalance(chain ChainID, validator ValidatorID) uint {
	valCfg := tr.ValidatorConfigs[validator]
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

	binaryName := tr.ChainConfigs[chain].BinaryName
	cmd := tr.Target.ExecCommand(binaryName,

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

func (tr Commands) GetValStakedTokens(chain ChainID, valoperAddress string) uint {
	binaryName := tr.ChainConfigs[chain].BinaryName
	bz, err := tr.Target.ExecCommand(binaryName,

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

func (tr Commands) GetParam(chain ChainID, param Param) string {
	binaryName := tr.ChainConfigs[chain].BinaryName
	bz, err := tr.Target.ExecCommand(binaryName,
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

func (tr Commands) GetIBCTransferParams(chain ChainID) IBCTransferParams {
	binaryName := tr.ChainConfigs[chain].BinaryName
	bz, err := tr.Target.ExecCommand(binaryName,
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
func (tr Commands) GetConsumerChains(chain ChainID) map[ChainID]bool {
	binaryName := tr.ChainConfigs[chain].BinaryName
	cmd := tr.Target.ExecCommand(binaryName,
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
		phase := c.Get("phase").String()
		if phase == types.ConsumerPhase_name[int32(types.CONSUMER_PHASE_INITIALIZED)] ||
			phase == types.ConsumerPhase_name[int32(types.CONSUMER_PHASE_REGISTERED)] ||
			phase == types.ConsumerPhase_name[int32(types.CONSUMER_PHASE_LAUNCHED)] {
			id := c.Get("consumer_id").String()
			for chainRef, cfg := range tr.ChainConfigs {
				if cfg.ConsumerId == ConsumerID(id) {
					// note: 'chainRef' is the reference the test uses and not necessarily matching chain id
					chains[chainRef] = true
				}
			}
		}
	}

	return chains
}

func (tr Commands) GetConsumerAddress(consumerChain ChainID, validator ValidatorID) string {
	binaryName := tr.ChainConfigs[ChainID("provi")].BinaryName
	consumerId := tr.ChainConfigs[consumerChain].ConsumerId
	cmd := tr.Target.ExecCommand(binaryName,

		"query", "provider", "validator-consumer-key",
		string(consumerId), tr.ValidatorConfigs[validator].ValconsAddress,
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

func (tr Commands) GetProviderAddressFromConsumer(consumerChain ChainID, validator ValidatorID) string {
	binaryName := tr.ChainConfigs[ChainID("provi")].BinaryName
	consumerId := tr.ChainConfigs[consumerChain].ConsumerId

	cmd := tr.Target.ExecCommand(binaryName,

		"query", "provider", "validator-provider-key",
		string(consumerId), tr.ValidatorConfigs[validator].ConsumerValconsAddressOnProvider,
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

func (tr Commands) GetSlashMeter() int64 {
	binaryName := tr.ChainConfigs[ChainID("provi")].BinaryName
	cmd := tr.Target.ExecCommand(binaryName,

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

func (tr Commands) GetRegisteredConsumerRewardDenoms(chain ChainID) []string {
	binaryName := tr.ChainConfigs[chain].BinaryName
	cmd := tr.Target.ExecCommand(binaryName,

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

func (tr Commands) GetPendingPacketQueueSize(chain ChainID) uint {
	binaryName := tr.ChainConfigs[chain].BinaryName
	cmd := tr.Target.ExecCommand(binaryName,

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
func (tr Commands) GetClientFrozenHeight(chain ChainID, clientID string) (uint64, uint64) {
	binaryName := tr.ChainConfigs[ChainID("provi")].BinaryName
	cmd := tr.Target.ExecCommand(binaryName,
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

	return uint64(revNumber), uint64(revHeight)
}

func (tr Commands) GetHasToValidate(
	validatorId ValidatorID,
) []ChainID {
	binaryName := tr.ChainConfigs[ChainID("provi")].BinaryName
	bz, err := tr.Target.ExecCommand(binaryName,
		"query", "provider", "has-to-validate",
		tr.ValidatorConfigs[validatorId].ValconsAddress,
		`--node`, tr.GetQueryNode(ChainID("provi")),
		`-o`, `json`,
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	arr := gjson.Get(string(bz), "consumer_ids").Array()
	chains := []ChainID{}
	for _, c := range arr {
		for chainRef, chain := range tr.ChainConfigs {
			if chain.ConsumerId == ConsumerID(c.String()) {
				// we report the test chain reference which might not match the chain ID
				// to support testing consumer chains with same chain ID
				chains = append(chains, chainRef)
				break
			}
		}
	}

	return chains
}

func (tr Commands) GetInflationRate(
	chain ChainID,
) float64 {
	binaryName := tr.ChainConfigs[chain].BinaryName
	bz, err := tr.Target.ExecCommand(binaryName,
		"query", "mint", "inflation",
		`--node`, tr.GetQueryNode(chain),
		`-o`, `json`,
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	inflationRate := gjson.Get(string(bz), "inflation").Float()
	return inflationRate
}

func (tr Commands) GetTrustedHeight(
	chain ChainID,
	clientID string,
	index int,
) (uint64, uint64) {
	configureNodeCmd := tr.Target.ExecCommand("hermes",
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
	// and parse the command "result"
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

func (tr Commands) GetProposedConsumerChains(chain ChainID) []string {
	binaryName := tr.ChainConfigs[chain].BinaryName
	cmd := tr.Target.ExecCommand(binaryName,
		"query", "provider", "list-consumer-chains",
		`--node`, tr.GetQueryNode(chain),
		`-o`, `json`,
	)
	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	arr := gjson.Get(string(bz), "chains").Array()
	chains := []string{}
	for _, c := range arr {
		phase := c.Get("phase").String()
		if phase == types.ConsumerPhase_name[int32(types.CONSUMER_PHASE_INITIALIZED)] ||
			phase == types.ConsumerPhase_name[int32(types.CONSUMER_PHASE_REGISTERED)] {
			cid := ConsumerID(c.Get("consumer_id").String())
			for chainRef, chainCfg := range tr.ChainConfigs {
				if chainCfg.ConsumerId == cid {
					chains = append(chains, string(chainRef))
				}
			}
		}
	}

	sort.Slice(chains, func(i, j int) bool {
		return chains[i] < chains[j]
	})
	return chains
}

// GetQueryNode returns query node tcp address on chain.
func (tr Commands) GetQueryNode(chain ChainID) string {
	return fmt.Sprintf("tcp://%s", tr.GetQueryNodeRPCAddress(chain))
}

func (tr Commands) GetQueryNodeRPCAddress(chain ChainID) string {
	return fmt.Sprintf("%s:26658", tr.GetQueryNodeIP(chain))
}

// getQueryNodeIP returns query node IP for chain,
// ipSuffix is hardcoded to be 253 on all query nodes
// except for "sover" chain where there's only one node
func (tr Commands) GetQueryNodeIP(chain ChainID) string {
	if chain == ChainID("sover") {
		// return address of first and only validator
		return fmt.Sprintf("%s.%s",
			tr.ChainConfigs[chain].IpPrefix,
			tr.ValidatorConfigs[ValidatorID("alice")].IpSuffix)
	}
	return fmt.Sprintf("%s.253", tr.ChainConfigs[chain].IpPrefix)
}

// GetConsumerCommissionRate returns the commission rate of the given validator on the given consumerChain
func (tr Commands) GetConsumerCommissionRate(consumerChain ChainID, validator ValidatorID) float64 {
	binaryName := tr.ChainConfigs[ChainID("provi")].BinaryName
	consumerId := tr.ChainConfigs[consumerChain].ConsumerId

	cmd := tr.Target.ExecCommand(binaryName,
		"query", "provider", "validator-consumer-commission-rate",
		string(consumerId), tr.ValidatorConfigs[validator].ValconsAddress,
		`--node`, tr.GetQueryNode(ChainID("provi")),
		`-o`, `json`,
	)
	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	rate, err := strconv.ParseFloat(gjson.Get(string(bz), "rate").String(), 64)
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
	return rate
}

// QueryTransaction returns the content of the transaction or an error e.g. when a transaction coudl
func (tr Commands) QueryTransaction(chain ChainID, txhash string) ([]byte, error) {
	binaryName := tr.ChainConfigs[chain].BinaryName
	cmd := tr.Target.ExecCommand(binaryName,
		"query", "tx", txhash,
		`--node`, tr.GetQueryNode(chain),
		`-o`, `json`,
	)
	return cmd.CombinedOutput()
}

// SubmitGovProposal sends a gov proposal transaction with given command and proposal content
func (tr Commands) SubmitGovProposal(chain ChainID, from ValidatorID, command string, proposal string, verbose bool) ([]byte, error) {
	// #nosec G204 -- bypass unsafe quoting warning (no production code)
	proposalFile := "/temp-proposal.json"
	bz, err := tr.Target.ExecCommand(
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, proposal, proposalFile),
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	providerCfg := tr.ChainConfigs[chain]
	cmd := tr.Target.ExecCommand(
		tr.ChainConfigs[chain].BinaryName,
		"tx", "gov", "submit-proposal", proposalFile,
		`--from`, `validator`+fmt.Sprint(from),
		`--chain-id`, string(providerCfg.ChainId),
		`--home`, tr.GetValidatorHome(providerCfg.ChainId, from),
		`--gas`, `900000`,
		`--node`, tr.GetValidatorNode(providerCfg.ChainId, from),
		`--keyring-backend`, `test`,
		`-o json`,
		`-y`,
	)

	if verbose {
		fmt.Printf("submit gov proposal \n\tcmd: %s\n\tcontent: %s", cmd.String(), proposal)
	}
	return cmd.CombinedOutput()
}

// CreateConsumer creates a consumer chain and returns its consumer-id
func (tr Commands) CreateConsumer(
	providerChain,
	consumerChain ChainID,
	validator ValidatorID,
	metadata types.ConsumerMetadata,
	initParams *types.ConsumerInitializationParameters,
	powerShapingParams *types.PowerShapingParameters,
) ([]byte, error) {

	msg := types.MsgCreateConsumer{
		ChainId:                  string(consumerChain),
		Metadata:                 metadata,
		InitializationParameters: initParams,
		PowerShapingParameters:   powerShapingParams,
	}

	content, err := json.Marshal(msg)
	if err != nil {
		log.Fatalf("failed marshalling MsgCreateConsumer: %s", err.Error())
	}
	jsonFile := "/create-consumer.json"
	bz, err := tr.Target.ExecCommand(
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, content, jsonFile),
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// Send consumer chain creation
	cmd := tr.Target.ExecCommand(
		tr.ChainConfigs[providerChain].BinaryName,
		"tx", "provider", "create-consumer", jsonFile,
		`--from`, `validator`+fmt.Sprint(validator),
		`--chain-id`, string(tr.ChainConfigs[providerChain].ChainId),
		`--home`, tr.GetValidatorHome(providerChain, validator),
		`--gas`, `900000`,
		`--node`, tr.GetValidatorNode(providerChain, validator),
		`--keyring-backend`, `test`,
		"--output", "json",
		`-y`,
	)

	return cmd.CombinedOutput()
}

func (tr Commands) UpdateConsumer(providerChain ChainID, validator ValidatorID, update types.MsgUpdateConsumer, verbose bool) ([]byte, error) {
	content, err := json.Marshal(update)
	if err != nil {
		log.Fatal("failed marshalling MsgUpdateConsumer: ", err.Error())
	}
	jsonFile := "/update-consumer.json"
	bz, err := tr.Target.ExecCommand(
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, content, jsonFile),
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// Send consumer chain update
	cmd := tr.Target.ExecCommand(
		tr.ChainConfigs[providerChain].BinaryName,
		"tx", "provider", "update-consumer", jsonFile,
		`--from`, `validator`+fmt.Sprint(validator),
		`--chain-id`, string(tr.ChainConfigs[providerChain].ChainId),
		`--home`, tr.GetValidatorHome(providerChain, validator),
		`--gas`, `900000`,
		`--node`, tr.GetValidatorNode(providerChain, validator),
		`--keyring-backend`, `test`,
		"--output", "json",
		`-y`,
	)

	return cmd.CombinedOutput()
}

func (tr Commands) AssignConsumerPubKey(identifier string, pubKey string, from ValidatorID, gas, home, node string, verbose bool) ([]byte, error) {
	consumerId := identifier
	binaryName := tr.ChainConfigs[ChainID("provi")].BinaryName
	cmd := tr.Target.ExecCommand(
		binaryName,

		"tx", "provider", "assign-consensus-key",
		consumerId,
		pubKey,
		`--from`, fmt.Sprintf("validator%s", from),
		`--chain-id`, string(tr.ChainConfigs[ChainID("provi")].ChainId),
		`--home`, home,
		`--node`, node,
		`--gas`, gas,
		`--keyring-backend`, `test`,
		`-y`,
		`-o`, `json`,
	)

	if verbose {
		fmt.Println("assignConsumerPubKey cmd:", cmd.String())
	}

	return cmd.CombinedOutput()
}

// TODO: refactor the following APIs as they are not version dependent commands on the target
func (tr Commands) GetValidatorHome(chain ChainID, validator ValidatorID) string {
	return `/` + string(chain) + `/validator` + fmt.Sprint(validator)
}

func (tr Commands) GetValidatorIP(chain ChainID, validator ValidatorID) string {
	return tr.ChainConfigs[chain].IpPrefix + "." + tr.ValidatorConfigs[validator].IpSuffix
}

func (tr Commands) GetValidatorNode(chain ChainID, validator ValidatorID) string {
	// for CometMock, validatorNodes are all the same address as the query node (which is CometMocks address)
	if tr.UseCometMock() {
		return tr.GetQueryNode(chain)
	}
	return "tcp://" + tr.GetValidatorIP(chain, validator) + ":26658"
}
