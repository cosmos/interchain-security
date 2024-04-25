package v4

import (
	"bufio"
	"fmt"
	"log"
	"os/exec"
	"regexp"
	"strconv"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v8/modules/core/02-client/types"
	e2e "github.com/cosmos/interchain-security/v5/tests/e2e/testlib"
	"gopkg.in/yaml.v2"

	"github.com/kylelemons/godebug/pretty"
	"github.com/tidwall/gjson"
)

type (
	ChainID                   = e2e.ChainID
	ValidatorID               = e2e.ValidatorID
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
	ValidatorConfig           = e2e.ValidatorConfig
	ChainConfig               = e2e.ChainConfig
	ContainerConfig           = e2e.ContainerConfig
	TargetDriver              = e2e.TargetDriver
)

type State map[ChainID]ChainState

type DriverV4 struct {
	ContainerConfig  ContainerConfig // FIXME only needed for 'Now' time tracking
	ValidatorConfigs map[ValidatorID]ValidatorConfig
	ChainConfigs     map[ChainID]ChainConfig
	Target           e2e.PlatformDriver
}

func (tr DriverV4) ExecCommand(name string, arg ...string) *exec.Cmd {
	return tr.Target.ExecCommand(name, arg...)
}

func (tr DriverV4) ExecDetachedCommand(name string, args ...string) *exec.Cmd {
	return tr.Target.ExecDetachedCommand(name, args...)
}

func (tr DriverV4) GetTestScriptPath(isConsumer bool, script string) string {
	return tr.Target.GetTestScriptPath(isConsumer, script)
}

func (tr DriverV4) GetBlockHeight(chain ChainID) uint {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//bz, err := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,
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

func (tr DriverV4) waitUntilBlock(chain ChainID, block uint, timeout time.Duration) {
	start := time.Now()
	for {
		thisBlock := tr.GetBlockHeight(chain)
		if thisBlock >= block {
			return
		}
		if time.Since(start) > timeout {
			panic(fmt.Sprintf("\n\n\nwaitBlocks method has timed out after: %s\n\n", timeout))
		}
		time.Sleep(500 * time.Millisecond)
	}
}

func (tr DriverV4) GetValPower(chain ChainID, validator ValidatorID) uint {
	/* 	if *verbose {
	   		log.Println("getting validator power for chain: ", chain, " validator: ", validator)
	   	}
	*/ //#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//command := exec.Command("docker", "exec", st.containerConfig.InstanceName, st.chainConfigs[chain].BinaryName,
	binaryName := tr.ChainConfigs[chain].BinaryName
	command := tr.Target.ExecCommand(binaryName,

		"query", "tendermint-validator-set",

		`--node`, tr.GetQueryNode(chain),
	)
	bz, err := command.CombinedOutput()
	if err != nil {
		log.Fatalf("encountered an error when executing command '%s': %v, output: %s", command.String(), err, string(bz))
	}

	type ValPubKey struct {
		Value string `yaml:"value"`
	}

	type TmValidatorSetYaml_v5 struct {
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

	valset := TmValidatorSetYaml_v5{}

	err = yaml.Unmarshal(bz, &valset)
	if err != nil {
		log.Fatalf("yaml.Unmarshal returned an error while unmarshalling validator set: %v, input: %s", err, string(bz))
	}

	total, err := strconv.Atoi(valset.Pagination.Total)
	if err != nil {
		log.Fatalf("strconv.Atoi returned an error while converting total for validator set: %v, input: %s, validator set: %s", err, valset.Pagination.Total, pretty.Sprint(valset))
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

func (tr DriverV4) GetReward(chain ChainID, validator ValidatorID, blockHeight uint, isNativeDenom bool) float64 {
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

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//bz, err := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,
	binaryName := tr.ChainConfigs[chain].BinaryName
	bz, err := tr.Target.ExecCommand(binaryName,

		"query", "distribution", "rewards",
		delAddresss,

		`--height`, fmt.Sprint(blockHeight),
		`--node`, tr.GetQueryNode(chain),
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

func (tr DriverV4) GetBalance(chain ChainID, validator ValidatorID) uint {
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
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,
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

// interchain-securityd query gov proposals
func (tr DriverV4) GetProposal(chain ChainID, proposal uint) Proposal {
	var noProposalRegex = regexp.MustCompile(`doesn't exist: key not found`)
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//bz, err := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,
	binaryName := tr.ChainConfigs[chain].BinaryName
	bz, err := tr.Target.ExecCommand(binaryName,

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

	propType := gjson.Get(string(bz), `messages.0.content.@type`).String()
	deposit := gjson.Get(string(bz), `total_deposit.#(denom=="stake").amount`).Uint()
	status := gjson.Get(string(bz), `status`).String()

	chainConfigs := tr.ChainConfigs
	containerConfig := tr.ContainerConfig

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
		spawnTime := gjson.Get(string(bz), `messages.0.content.spawn_time`).Time().Sub(containerConfig.Now)

		var chain ChainID
		for i, conf := range chainConfigs {
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
		stopTime := gjson.Get(string(bz), `messages.0.content.stop_time`).Time().Sub(containerConfig.Now)

		var chain ChainID
		for i, conf := range chainConfigs {
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

func (tr DriverV4) GetValStakedTokens(chain ChainID, valoperAddress string) uint {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//bz, err := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,
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

	amount := gjson.Get(string(bz), `tokens`)

	return uint(amount.Uint())
}

func (tr DriverV4) GetParam(chain ChainID, param Param) string {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//bz, err := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,

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

// GetConsumerChains returns a list of consumer chains that're being secured by the provider chain,
// determined by querying the provider chain.
func (tr DriverV4) GetConsumerChains(chain ChainID) map[ChainID]bool {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,
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
		id := c.Get("chain_id").String()
		chains[ChainID(id)] = true
	}

	return chains
}
func (tr DriverV4) GetConsumerAddress(consumerChain ChainID, validator ValidatorID) string {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[ChainID("provi")].BinaryName,

	binaryName := tr.ChainConfigs[ChainID("provi")].BinaryName
	cmd := tr.Target.ExecCommand(binaryName,

		"query", "provider", "validator-consumer-key",
		string(consumerChain), tr.ValidatorConfigs[validator].ValconsAddress,
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

func (tr DriverV4) GetProviderAddressFromConsumer(consumerChain ChainID, validator ValidatorID) string {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[ChainID("provi")].BinaryName,
	binaryName := tr.ChainConfigs[ChainID("provi")].BinaryName

	cmd := tr.Target.ExecCommand(binaryName,

		"query", "provider", "validator-provider-key",
		string(consumerChain), tr.ValidatorConfigs[validator].ConsumerValconsAddressOnProvider,
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

func (tr DriverV4) GetSlashMeter() int64 {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//cmd := exec.Command("docker", "exec",
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

func (tr DriverV4) GetRegisteredConsumerRewardDenoms(chain ChainID) []string {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,
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

func (tr DriverV4) GetPendingPacketQueueSize(chain ChainID) uint {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,
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

func (tr DriverV4) GetValidatorIP(chain ChainID, validator ValidatorID) string {
	return tr.ChainConfigs[chain].IpPrefix + "." + tr.ValidatorConfigs[validator].IpSuffix
}

// getQueryNode returns query node tcp address on chain.
func (tr DriverV4) GetQueryNode(chain ChainID) string {
	return fmt.Sprintf("tcp://%s", tr.GetQueryNodeRPCAddress(chain))
}

func (tr DriverV4) GetQueryNodeRPCAddress(chain ChainID) string {
	return fmt.Sprintf("%s:26658", tr.GetQueryNodeIP(chain))
}

// getQueryNodeIP returns query node IP for chain,
// ipSuffix is hardcoded to be 253 on all query nodes
// except for "sover" chain where there's only one node
func (tr DriverV4) GetQueryNodeIP(chain ChainID) string {
	if chain == ChainID("sover") {
		// return address of first and only validator
		return fmt.Sprintf("%s.%s",
			tr.ChainConfigs[chain].IpPrefix,
			tr.ValidatorConfigs[ValidatorID("alice")].IpSuffix)
	}
	return fmt.Sprintf("%s.253", tr.ChainConfigs[chain].IpPrefix)
}

func (tr DriverV4) curlJsonRPCRequest(method, params, address string) {
	cmd_template := `curl -H 'Content-Type: application/json' -H 'Accept:application/json' --data '{"jsonrpc":"2.0","method":"%s","params":%s,"id":1}' %s`

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//cmd := exec.Command("docker", "exec", tr.testConfig.containerConfig.InstanceName, "bash", "-c", fmt.Sprintf(cmd_template, method, params, address))
	cmd := tr.Target.ExecCommand("bash", "-c", fmt.Sprintf(cmd_template, method, params, address))

	verbosity := false
	e2e.ExecuteCommandWithVerbosity(cmd, "curlJsonRPCRequest", verbosity)
}

// GetClientFrozenHeight returns the frozen height for a client with the given client ID
// by querying the hosting chain with the given chainID
func (tr DriverV4) GetClientFrozenHeight(chain ChainID, clientID string) (uint64, uint64) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[ChainID("provi")].BinaryName,
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

	return uint64(revHeight), uint64(revNumber)
}

func (tr DriverV4) GetTrustedHeight(
	chain ChainID,
	clientID string,
	index int,
) (uint64, uint64) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//configureNodeCmd := exec.Command("docker", "exec", tc.testConfig.containerConfig.InstanceName, "hermes",
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

func (tr DriverV4) GetProposedConsumerChains(chain ChainID) []string {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	//bz, err := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[chain].BinaryName,
	binaryName := tr.ChainConfigs[chain].BinaryName
	bz, err := tr.Target.ExecCommand(binaryName,
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

// Breaking forward compatibility
func (tr DriverV4) GetIBCTransferParams(chain ChainID) IBCTransferParams {
	panic("'GetIBCTransferParams' is not implemented in this version")
}

func uintPtr(i uint) *uint {
	return &i
}
