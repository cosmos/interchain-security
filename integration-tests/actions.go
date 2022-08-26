package main

import (
	"bufio"
	"encoding/json"
	"fmt"
	"log"
	"os/exec"
	"sync"
	"time"

	clienttypes "github.com/cosmos/ibc-go/modules/core/02-client/types"
)

type SendTokensAction struct {
	chain  chainID
	from   validatorID
	to     validatorID
	amount uint
}

func (s TestRun) sendTokens(
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

		`--chain-id`, string(action.chain),
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
	chain          chainID
	validators     []StartChainValidator
	genesisChanges string
	skipGentx      bool
}

type StartChainValidator struct {
	// Validator id defined in config.go
	id         validatorID
	allocation uint
	stake      uint
}

func (s TestRun) startChain(
	action StartChainAction,
	verbose bool,
) {
	chainConfig := s.chainConfigs[action.chain]
	type jsonValAttrs struct {
		Id               string `json:"id"`
		IpSuffix         string `json:"ip_suffix"`
		Mnemonic         string `json:"mnemonic"`
		Allocation       string `json:"allocation"`
		Stake            string `json:"stake"`
		PrivValidatorKey string `json:"priv_validator_key"`
		NodeKey          string `json:"node_key"`
	}

	var valsToMarshal []jsonValAttrs
	for _, val := range action.validators {

		valConfig, found := s.validatorConfigs[val.id]
		if !found {
			panic(fmt.Sprintf("validator config not found from val id of: %v\n", val.id))
		}

		valsToMarshal = append(valsToMarshal, jsonValAttrs{
			Id:               fmt.Sprint(val.id),
			IpSuffix:         fmt.Sprint(valConfig.ipSuffix),
			Mnemonic:         s.validatorConfigs[val.id].mnemonic,
			Allocation:       fmt.Sprint(val.allocation) + "stake",
			Stake:            fmt.Sprint(val.stake) + "stake",
			PrivValidatorKey: s.validatorConfigs[val.id].privValidatorKey,
			NodeKey:          s.validatorConfigs[val.id].nodeKey,
		})
	}

	vals, err := json.Marshal(valsToMarshal)
	if err != nil {
		log.Fatal(err)
	}

	// TODO: here is some more genesis changes
	var genesisChanges string
	if action.genesisChanges != "" {
		genesisChanges = chainConfig.genesisChanges + " | " + action.genesisChanges
	} else {
		genesisChanges = chainConfig.genesisChanges
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", s.containerConfig.instanceName, "/bin/bash",
		"/testnet-scripts/start-chain.sh", chainConfig.binaryName, string(vals),
		string(chainConfig.chainId), chainConfig.ipPrefix, genesisChanges,
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
	chain       chainID
	from        validatorID
	deposit     string
	propType    string
	title       string
	description string
}

func (s TestRun) submitTextProposal(
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
		`--chain-id`, string(action.chain),
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
	providerChain chainID
	from          validatorID
	deposit       uint
	consumerChain chainID
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

func (s TestRun) submitConsumerProposal(
	action SubmitConsumerProposalAction,
	verbose bool,
) {
	spawnTime := s.containerConfig.now.Add(time.Duration(action.spawnTime) * time.Millisecond)
	prop := CreateConsumerChainProposalJSON{
		Title:         "Create a chain",
		Description:   "Gonna be a great chain",
		ChainId:       string(action.consumerChain),
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
	bz, err = exec.Command("docker", "exec", s.containerConfig.instanceName, s.chainConfigs[action.providerChain].binaryName,

		"tx", "gov", "submit-proposal", "create-consumer-chain",
		"/temp-proposal.json",

		`--from`, `validator`+fmt.Sprint(action.from),
		`--chain-id`, string(action.providerChain),
		`--home`, s.getValidatorHome(action.providerChain, action.from),
		`--node`, s.getValidatorNode(action.providerChain, action.from),
		`--keyring-backend`, `test`,
		`-b`, `block`,
		`-y`,
	).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

type VoteGovProposalAction struct {
	providerChain chainID
	from          []validatorID
	vote          []string
	propNumber    uint
}

func (s TestRun) voteGovProposal(
	action VoteGovProposalAction,
	verbose bool,
) {
	var wg sync.WaitGroup
	for i, val := range action.from {
		wg.Add(1)
		vote := action.vote[i]
		go func(val validatorID, vote string) {
			defer wg.Done()
			//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
			bz, err := exec.Command("docker", "exec", s.containerConfig.instanceName, s.chainConfigs[action.providerChain].binaryName,

				"tx", "gov", "vote",
				fmt.Sprint(action.propNumber), vote,

				`--from`, `validator`+fmt.Sprint(val),
				`--chain-id`, string(action.providerChain),
				`--home`, s.getValidatorHome(action.providerChain, val),
				`--node`, s.getValidatorNode(action.providerChain, val),
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
	time.Sleep(time.Duration(s.chainConfigs[action.providerChain].votingWaitTime) * time.Second)
}

type StartConsumerChainAction struct {
	consumerChain chainID
	providerChain chainID
	validators    []StartChainValidator
}

func (s TestRun) startConsumerChain(
	action StartConsumerChainAction,
	verbose bool,
) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", s.containerConfig.instanceName, s.chainConfigs[action.providerChain].binaryName,

		"query", "provider", "consumer-genesis",
		string(action.consumerChain),

		`--node`, s.getValidatorNode(action.providerChain, s.getDefaultValId(action.providerChain)),
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
		chain:          action.consumerChain,
		validators:     action.validators,
		genesisChanges: ".app_state.ccvconsumer = " + string(bz),
		skipGentx:      true,
	}, verbose)
}

type AddChainToRelayerAction struct {
	chain     chainID
	validator validatorID
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

func (s TestRun) addChainToRelayer(
	action AddChainToRelayerAction,
	verbose bool,
) {
	valIp := s.chainConfigs[action.chain].ipPrefix + `.` + fmt.Sprint(action.validator)
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
		"--chain", string(action.chain),
		"--mnemonic-file", "/root/.hermes/mnemonic.txt",
	).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

type AddIbcConnectionAction struct {
	chainA  chainID
	chainB  chainID
	clientA uint
	clientB uint
	order   string
}

func (s TestRun) addIbcConnection(
	action AddIbcConnectionAction,
	verbose bool,
) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", s.containerConfig.instanceName, "hermes",
		"create", "connection",
		"--a-chain", string(action.chainA),
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
	chainA      chainID
	chainB      chainID
	connectionA uint
	portA       string
	portB       string
	order       string
}

func (s TestRun) addIbcChannel(
	action AddIbcChannelAction,
	verbose bool,
) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", s.containerConfig.instanceName, "hermes",
		"create", "channel",
		"--a-chain", string(action.chainA),
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
	chain   chainID
	port    string
	channel uint
}

func (s TestRun) relayPackets(
	action RelayPacketsAction,
	verbose bool,
) {
	// hermes clear packets ibc0 transfer channel-13
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", s.containerConfig.instanceName, "hermes", "clear", "packets",
		"--chain", string(action.chain),
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
	chain  chainID
	from   validatorID
	to     validatorID
	amount uint
}

func (s TestRun) delegateTokens(
	action DelegateTokensAction,
	verbose bool,
) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", s.containerConfig.instanceName, s.chainConfigs[action.chain].binaryName,

		"tx", "staking", "delegate",
		s.validatorConfigs[action.to].valoperAddress,
		fmt.Sprint(action.amount)+`stake`,

		`--from`, `validator`+fmt.Sprint(action.from),
		`--chain-id`, string(action.chain),
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
	chain      chainID
	sender     validatorID
	unbondFrom validatorID
	amount     uint
}

func (s TestRun) unbondTokens(
	action UnbondTokensAction,
	verbose bool,
) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", s.containerConfig.instanceName, s.chainConfigs[action.chain].binaryName,

		"tx", "staking", "unbond",
		s.validatorConfigs[action.unbondFrom].valoperAddress,
		fmt.Sprint(action.amount)+`stake`,

		`--from`, `validator`+fmt.Sprint(action.sender),
		`--chain-id`, string(action.chain),
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
