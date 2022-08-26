package main

import (
	"bufio"
	"encoding/json"
	"fmt"
	"log"
	"os/exec"
	"regexp"
	"strconv"
	"sync"
	"time"

	clienttypes "github.com/cosmos/ibc-go/modules/core/02-client/types"
)

type SendTokensAction struct {
	chain  uint
	from   uint
	to     uint
	amount uint
}

func (s System) sendTokens(
	action SendTokensAction,
	verbose bool,
) {
	binaryName := s.chainConfigs[action.chain].binaryName
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", s.containerConfig.instanceName, binaryName,

		"tx", "bank", "send",
		s.validatorConfigs[action.from].delAddress,
		s.validatorConfigs[action.to].delAddress,
		fmt.Sprint(action.amount)+`stake`,

		`--chain-id`, s.chainConfigs[action.chain].chainId,
		`--home`, s.getValidatorHome(action.chain, action.from),
		`--node`, s.getValidatorNode(action.chain, action.from),
		`--keyring-backend`, `test`,
		`-b`, `block`,
		`-y`,
	)
	if verbose {
		fmt.Println("sendTokens cmd:", cmd.String())
	}
	bz, err := cmd.CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

type StartChainAction struct {
	chain          uint
	validators     []StartChainValidator
	genesisChanges string
	skipGentx      bool
}

type StartChainValidator struct {
	id         uint
	allocation uint
	stake      uint
}

func (s System) startChain(
	action StartChainAction,
	verbose bool,
) {
	chainConfig := s.chainConfigs[action.chain]
	type jsonValAttrs struct {
		Mnemonic         string `json:"mnemonic"`
		Allocation       string `json:"allocation"`
		Stake            string `json:"stake"`
		ValId            string `json:"val_id"`
		PrivValidatorKey string `json:"priv_validator_key"`
		NodeKey          string `json:"node_key"`
		IpSuffix         string `json:"ip_suffix"`
	}

	var validators []jsonValAttrs
	for _, val := range action.validators {
		validators = append(validators, jsonValAttrs{
			Mnemonic:         s.validatorConfigs[val.id].mnemonic,
			NodeKey:          s.validatorConfigs[val.id].nodeKey,
			ValId:            fmt.Sprint(val.id), // TODO: make this actual id
			PrivValidatorKey: s.validatorConfigs[val.id].privValidatorKey,
			Allocation:       fmt.Sprint(val.allocation) + "stake",
			Stake:            fmt.Sprint(val.stake) + "stake",
			IpSuffix:         s.validatorConfigs[val.id].IpSuffix,
		})
	}

	vals, err := json.Marshal(validators)
	if err != nil {
		log.Fatal(err)
	}

	var genesisChanges string
	if action.genesisChanges != "" {
		genesisChanges = chainConfig.genesisChanges + " | " + action.genesisChanges
	} else {
		genesisChanges = chainConfig.genesisChanges
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", s.containerConfig.instanceName, "/bin/bash",
		"/testnet-scripts/start-chain.sh", chainConfig.binaryName, string(vals),
		chainConfig.chainId, chainConfig.ipPrefix, genesisChanges,
		fmt.Sprint(action.skipGentx),
		`s/timeout_commit = "5s"/timeout_commit = "1s"/;`+
			`s/peer_gossip_sleep_duration = "100ms"/peer_gossip_sleep_duration = "50ms"/;`,
		// `s/flush_throttle_timeout = "100ms"/flush_throttle_timeout = "10ms"/`,
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
		if out == "done!!!!!!!!" {
			break
		}
	}
	if err := scanner.Err(); err != nil {
		log.Fatal(err)
	}

	s.addChainToRelayer(AddChainToRelayerAction{
		chain:     action.chain,
		validator: action.validators[0].id,
	}, verbose)
}

type SubmitTextProposalAction struct {
	chain       uint
	from        uint
	deposit     uint
	propType    string
	title       string
	description string
}

func (s System) submitTextProposal(
	action SubmitTextProposalAction,
	verbose bool,
) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", s.containerConfig.instanceName, s.chainConfigs[action.chain].binaryName,

		"tx", "gov", "submit-proposal",
		`--title`, action.title,
		`--description`, action.description,
		`--type`, action.propType,
		`--deposit`, fmt.Sprint(action.deposit)+`stake`,

		`--from`, `validator`+fmt.Sprint(action.from),
		`--chain-id`, s.chainConfigs[action.chain].chainId,
		`--home`, s.getValidatorHome(action.chain, action.from),
		`--node`, s.getValidatorNode(action.chain, action.from),
		`--keyring-backend`, `test`,
		`-b`, `block`,
		`-y`,
	).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

type SubmitConsumerProposalAction struct {
	chain         uint
	from          uint
	deposit       uint
	consumerChain uint
	spawnTime     uint
	initialHeight clienttypes.Height
}

// TODO: import this directly from the module once it is merged
type CreateConsumerChainProposalJSON struct {
	Title         string             `json:"title"`
	Description   string             `json:"description"`
	ChainId       string             `json:"chain_id"`
	InitialHeight clienttypes.Height `json:"initial_height"`
	GenesisHash   []byte             `json:"genesis_hash"`
	BinaryHash    []byte             `json:"binary_hash"`
	SpawnTime     time.Time          `json:"spawn_time"`
	Deposit       string             `json:"deposit"`
}

func (s System) submitConsumerProposal(
	action SubmitConsumerProposalAction,
	verbose bool,
) {
	spawnTime := s.containerConfig.now.Add(time.Duration(action.spawnTime) * time.Millisecond)
	prop := CreateConsumerChainProposalJSON{
		Title:         "Create a chain",
		Description:   "Gonna be a great chain",
		ChainId:       s.chainConfigs[action.consumerChain].chainId,
		InitialHeight: action.initialHeight,
		GenesisHash:   []byte("gen_hash"),
		BinaryHash:    []byte("bin_hash"),
		SpawnTime:     spawnTime,
		Deposit:       fmt.Sprint(action.deposit) + `stake`,
	}

	bz, err := json.Marshal(prop)
	if err != nil {
		log.Fatal(err)
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err = exec.Command("docker", "exec", s.containerConfig.instanceName, "/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, string(bz), "/temp-proposal.json")).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err = exec.Command("docker", "exec", s.containerConfig.instanceName, s.chainConfigs[action.chain].binaryName,

		"tx", "gov", "submit-proposal", "create-consumer-chain",
		"/temp-proposal.json",

		`--from`, `validator`+fmt.Sprint(action.from),
		`--chain-id`, s.chainConfigs[action.chain].chainId,
		`--home`, s.getValidatorHome(action.chain, action.from),
		`--node`, s.getValidatorNode(action.chain, action.from),
		`--keyring-backend`, `test`,
		`-b`, `block`,
		`-y`,
	).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

type VoteGovProposalAction struct {
	chain      uint
	from       []uint
	vote       []string
	propNumber uint
}

func (s System) voteGovProposal(
	action VoteGovProposalAction,
	verbose bool,
) {
	var wg sync.WaitGroup
	for i, val := range action.from {
		wg.Add(1)
		vote := action.vote[i]
		go func(val uint, vote string) {
			defer wg.Done()
			//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
			bz, err := exec.Command("docker", "exec", s.containerConfig.instanceName, s.chainConfigs[action.chain].binaryName,

				"tx", "gov", "vote",
				fmt.Sprint(action.propNumber), vote,

				`--from`, `validator`+fmt.Sprint(val),
				`--chain-id`, s.chainConfigs[action.chain].chainId,
				`--home`, s.getValidatorHome(action.chain, val),
				`--node`, s.getValidatorNode(action.chain, val),
				`--keyring-backend`, `test`,
				`-b`, `block`,
				`-y`,
			).CombinedOutput()

			if err != nil {
				log.Fatal(err, "\n", string(bz))
			}
		}(val, vote)
	}

	wg.Wait()
	time.Sleep(time.Duration(s.chainConfigs[action.chain].votingWaitTime) * time.Second)
}

type StartConsumerChainAction struct {
	consumerChain uint
	providerChain uint
	validators    []StartChainValidator
}

func (s System) startConsumerChain(
	action StartConsumerChainAction,
	verbose bool,
) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", s.containerConfig.instanceName, s.chainConfigs[action.providerChain].binaryName,

		"query", "provider", "consumer-genesis",
		s.chainConfigs[action.consumerChain].chainId,

		`--node`, s.getValidatorNode(action.providerChain, s.getValidatorNum(action.providerChain)),
		`-o`, `json`,
	)

	if verbose {
		log.Println("startConsumerChain cmd: ", cmd.String())
	}

	bz, err := cmd.CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	s.startChain(StartChainAction{
		chain:          1,
		validators:     action.validators,
		genesisChanges: ".app_state.ccvconsumer = " + string(bz),
		skipGentx:      true,
	}, verbose)
}

type AddChainToRelayerAction struct {
	chain     uint
	validator uint
}

const hermesChainConfigTemplate = `

[[chains]]
account_prefix = "cosmos"
clock_drift = "5s"
gas_multiplier = 1.1
grpc_addr = "%s"
id = "%s"
key_name = "%s"
max_gas = 2000000
rpc_addr = "%s"
rpc_timeout = "10s"
store_prefix = "ibc"
trusting_period = "14days"
websocket_addr = "%s"

[chains.gas_price]
	denom = "stake"
	price = 0.00

[chains.trust_threshold]
	denominator = "3"
	numerator = "1"
`

func (s System) addChainToRelayer(
	action AddChainToRelayerAction,
	verbose bool,
) {
	valIp := s.getValidatorIP(action.chain, action.validator)
	chainId := s.chainConfigs[action.chain].chainId
	keyName := "validator" + fmt.Sprint(action.validator)
	rpcAddr := "http://" + valIp + ":26658"
	grpcAddr := "tcp://" + valIp + ":9091"
	wsAddr := "ws://" + valIp + ":26657/websocket"

	chainConfig := fmt.Sprintf(hermesChainConfigTemplate,
		grpcAddr,
		chainId,
		keyName,
		rpcAddr,
		wsAddr,
	)

	bashCommand := fmt.Sprintf(`echo '%s' >> %s`, chainConfig, "/root/.hermes/config.toml")

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", s.containerConfig.instanceName, "bash", "-c",
		bashCommand,
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// Save mnemonic to file within container
	saveMnemonicCommand := fmt.Sprintf(`echo '%s' > %s`, s.validatorConfigs[action.validator].mnemonic, "/root/.hermes/mnemonic.txt")
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err = exec.Command("docker", "exec", s.containerConfig.instanceName, "bash", "-c",
		saveMnemonicCommand,
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err = exec.Command("docker", "exec", s.containerConfig.instanceName, "hermes",
		"keys", "add",
		"--chain", s.chainConfigs[action.chain].chainId,
		"--mnemonic-file", "/root/.hermes/mnemonic.txt",
	).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

type AddIbcConnectionAction struct {
	chainA  uint
	chainB  uint
	clientA uint
	clientB uint
	order   string
}

func (s System) addIbcConnection(
	action AddIbcConnectionAction,
	verbose bool,
) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", s.containerConfig.instanceName, "hermes",
		"create", "connection",
		"--a-chain", s.chainConfigs[action.chainA].chainId,
		"--a-client", "07-tendermint-"+fmt.Sprint(action.clientA),
		"--b-client", "07-tendermint-"+fmt.Sprint(action.clientB),
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
			fmt.Println("addIbcConnection: " + out)
		}
		if out == "done!!!!!!!!" {
			break
		}
	}
	if err := scanner.Err(); err != nil {
		log.Fatal(err)
	}
}

type AddIbcChannelAction struct {
	chainA      uint
	chainB      uint
	connectionA uint
	portA       string
	portB       string
	order       string
}

func (s System) addIbcChannel(
	action AddIbcChannelAction,
	verbose bool,
) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", s.containerConfig.instanceName, "hermes",
		"create", "channel",
		"--a-chain", s.chainConfigs[action.chainA].chainId,
		"--a-connection", "connection-"+fmt.Sprint(action.connectionA),
		"--a-port", action.portA,
		"--b-port", action.portB,
		"--channel-version", s.containerConfig.ccvVersion,
		"--order", action.order,
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
		if out == "done!!!!!!!!" {
			break
		}
	}
	if err := scanner.Err(); err != nil {
		log.Fatal(err)
	}
}

type RelayPacketsAction struct {
	chain   uint
	port    string
	channel uint
}

func (s System) relayPackets(
	action RelayPacketsAction,
	verbose bool,
) {
	// hermes clear packets ibc0 transfer channel-13
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", s.containerConfig.instanceName, "hermes", "clear", "packets",
		"--chain", s.chainConfigs[action.chain].chainId,
		"--port", action.port,
		"--channel", "channel-"+fmt.Sprint(action.channel),
	)
	if verbose {
		log.Println("relayPackets cmd:", cmd.String())
	}
	bz, err := cmd.CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

type DelegateTokensAction struct {
	chain  uint
	from   uint
	to     uint
	amount uint
}

func (s System) delegateTokens(
	action DelegateTokensAction,
	verbose bool,
) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", s.containerConfig.instanceName, s.chainConfigs[action.chain].binaryName,

		"tx", "staking", "delegate",
		s.validatorConfigs[action.to].valoperAddress,
		fmt.Sprint(action.amount)+`stake`,

		`--from`, `validator`+fmt.Sprint(action.from),
		`--chain-id`, s.chainConfigs[action.chain].chainId,
		`--home`, s.getValidatorHome(action.chain, action.from),
		`--node`, s.getValidatorNode(action.chain, action.from),
		`--keyring-backend`, `test`,
		`-b`, `block`,
		`-y`,
	)
	if verbose {
		fmt.Println("delegate cmd:", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

type UnbondTokensAction struct {
	chain      uint
	sender     uint
	unbondFrom uint
	amount     uint
}

func (s System) unbondTokens(
	action UnbondTokensAction,
	verbose bool,
) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", s.containerConfig.instanceName, s.chainConfigs[action.chain].binaryName,

		"tx", "staking", "unbond",
		s.validatorConfigs[action.unbondFrom].valoperAddress,
		fmt.Sprint(action.amount)+`stake`,

		`--from`, `validator`+fmt.Sprint(action.sender),
		`--chain-id`, s.chainConfigs[action.chain].chainId,
		`--home`, s.getValidatorHome(action.chain, action.sender),
		`--node`, s.getValidatorNode(action.chain, action.sender),
		`--keyring-backend`, `test`,
		`-b`, `block`,
		`-y`,
	)
	if verbose {
		fmt.Println("unbond cmd:", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

var queryValidatorRegex = regexp.MustCompile(`(\d+)`)

func (s System) getValidatorNum(chain uint) uint {
	// Get first subdirectory of the directory of this chain, which will be the home directory of one of the validators
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", s.containerConfig.instanceName, "bash", "-c", `cd /`+s.chainConfigs[chain].chainId+`; ls -d */ | awk '{print $1}' | head -n 1`).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	validator, err := strconv.Atoi(queryValidatorRegex.FindString(string(bz)))
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	return uint(validator)
}

func (s System) getValidatorNode(chain uint, validator uint) string {
	return "tcp://" + s.getValidatorIP(chain, validator) + ":26658"
}

func (s System) getValidatorIP(chain uint, validator uint) string {
	return s.chainConfigs[chain].ipPrefix + "." + s.validatorConfigs[validator].IpSuffix
}

func (s System) getValidatorHome(chain uint, validator uint) string {
	return `/` + s.chainConfigs[chain].chainId + `/validator` + fmt.Sprint(validator)
}
