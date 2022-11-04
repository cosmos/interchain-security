package main

import (
	"bufio"
	"encoding/json"
	"fmt"
	"log"
	"os/exec"
	"strconv"
	"strings"
	"sync"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/client"
)

type SendTokensAction struct {
	chain  chainID
	from   validatorID
	to     validatorID
	amount uint
}

func (tr TestRun) sendTokens(
	action SendTokensAction,
	verbose bool,
) {
	binaryName := tr.chainConfigs[action.chain].binaryName
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, binaryName,

		"tx", "bank", "send",
		tr.validatorConfigs[action.from].delAddress,
		tr.validatorConfigs[action.to].delAddress,
		fmt.Sprint(action.amount)+`stake`,

		`--chain-id`, string(tr.chainConfigs[action.chain].chainId),
		`--home`, tr.getValidatorHome(action.chain, action.from),
		`--node`, tr.getValidatorNode(action.chain, action.from),
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
	chain      chainID
	validators []StartChainValidator
	// Genesis changes specific to this action, appended to genesis changes defined in chain config
	genesisChanges string
	skipGentx      bool
}

type StartChainValidator struct {
	id         validatorID
	allocation uint
	stake      uint
}

func (tr TestRun) startChain(
	action StartChainAction,
	verbose bool,
) {
	chainConfig := tr.chainConfigs[action.chain]
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
			Mnemonic:         tr.validatorConfigs[val.id].mnemonic,
			NodeKey:          tr.validatorConfigs[val.id].nodeKey,
			ValId:            fmt.Sprint(val.id),
			PrivValidatorKey: tr.validatorConfigs[val.id].privValidatorKey,
			Allocation:       fmt.Sprint(val.allocation) + "stake",
			Stake:            fmt.Sprint(val.stake) + "stake",
			IpSuffix:         tr.validatorConfigs[val.id].ipSuffix,
		})
	}

	vals, err := json.Marshal(validators)
	if err != nil {
		log.Fatal(err)
	}

	// Concat genesis changes defined in chain config, with any custom genesis changes for this chain instantiation
	var genesisChanges string
	if action.genesisChanges != "" {
		genesisChanges = chainConfig.genesisChanges + " | " + action.genesisChanges
	} else {
		genesisChanges = chainConfig.genesisChanges
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, "/bin/bash",
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

	tr.addChainToRelayer(addChainToRelayerAction{
		chain:     action.chain,
		validator: action.validators[0].id,
	}, verbose)
}

type submitTextProposalAction struct {
	chain       chainID
	from        validatorID
	deposit     uint
	propType    string
	title       string
	description string
}

func (tr TestRun) submitTextProposal(
	action submitTextProposalAction,
	verbose bool,
) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[action.chain].binaryName,

		"tx", "gov", "submit-proposal",
		`--title`, action.title,
		`--description`, action.description,
		`--type`, action.propType,
		`--deposit`, fmt.Sprint(action.deposit)+`stake`,

		`--from`, `validator`+fmt.Sprint(action.from),
		`--chain-id`, string(tr.chainConfigs[action.chain].chainId),
		`--home`, tr.getValidatorHome(action.chain, action.from),
		`--node`, tr.getValidatorNode(action.chain, action.from),
		`--keyring-backend`, `test`,
		`-b`, `block`,
		`-y`,
	).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

type submitConsumerAdditionProposalAction struct {
	chain         chainID
	from          validatorID
	deposit       uint
	consumerChain chainID
	spawnTime     uint
	initialHeight clienttypes.Height
}

func (tr TestRun) submitConsumerAdditionProposal(
	action submitConsumerAdditionProposalAction,
	verbose bool,
) {
	spawnTime := tr.containerConfig.now.Add(time.Duration(action.spawnTime) * time.Millisecond)
	prop := client.ConsumerAdditionProposalJSON{
		Title:         "Propose the addition of a new chain",
		Description:   "Gonna be a great chain",
		ChainId:       string(tr.chainConfigs[action.consumerChain].chainId),
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

	jsonStr := string(bz)
	if strings.Contains(jsonStr, "'") {
		log.Fatal("prop json contains single quote")
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err = exec.Command("docker", "exec", tr.containerConfig.instanceName,
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, jsonStr, "/temp-proposal.json")).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err = exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[action.chain].binaryName,

		"tx", "gov", "submit-proposal", "consumer-addition",
		"/temp-proposal.json",

		`--from`, `validator`+fmt.Sprint(action.from),
		`--chain-id`, string(tr.chainConfigs[action.chain].chainId),
		`--home`, tr.getValidatorHome(action.chain, action.from),
		`--node`, tr.getValidatorNode(action.chain, action.from),
		`--keyring-backend`, `test`,
		`-b`, `block`,
		`-y`,
	).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

type submitConsumerRemovalProposalAction struct {
	chain          chainID
	from           validatorID
	deposit        uint
	consumerChain  chainID
	stopTimeOffset time.Duration // offset from time.Now()
}

func (tr TestRun) submitConsumerRemovalProposal(
	action submitConsumerRemovalProposalAction,
	verbose bool,
) {
	stopTime := tr.containerConfig.now.Add(action.stopTimeOffset)
	prop := client.ConsumerRemovalProposalJSON{
		Title:       fmt.Sprintf("Stop the %v chain", action.consumerChain),
		Description: "It was a great chain",
		ChainId:     string(tr.chainConfigs[action.consumerChain].chainId),
		StopTime:    stopTime,
		Deposit:     fmt.Sprint(action.deposit) + `stake`,
	}

	bz, err := json.Marshal(prop)
	if err != nil {
		log.Fatal(err)
	}

	jsonStr := string(bz)
	if strings.Contains(jsonStr, "'") {
		log.Fatal("prop json contains single quote")
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err = exec.Command("docker", "exec", tr.containerConfig.instanceName,
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, jsonStr, "/temp-proposal.json")).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err = exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[action.chain].binaryName,

		"tx", "gov", "submit-proposal", "consumer-removal",
		"/temp-proposal.json",

		`--from`, `validator`+fmt.Sprint(action.from),
		`--chain-id`, string(tr.chainConfigs[action.chain].chainId),
		`--home`, tr.getValidatorHome(action.chain, action.from),
		`--node`, tr.getValidatorNode(action.chain, action.from),
		`--keyring-backend`, `test`,
		`-b`, `block`,
		`-y`,
	).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

type submitParamChangeProposalAction struct {
	chain    chainID
	from     validatorID
	deposit  uint
	subspace string
	key      string
	value    interface{}
}

type paramChangeProposalJSON struct {
	Title       string            `json:"title"`
	Description string            `json:"description"`
	Changes     []paramChangeJSON `json:"changes"`
	Deposit     string            `json:"deposit"`
}

type paramChangeJSON struct {
	Subspace string      `json:"subspace"`
	Key      string      `json:"key"`
	Value    interface{} `json:"value"`
}

func (tr TestRun) submitParamChangeProposal(
	action submitParamChangeProposalAction,
	verbose bool,
) {
	prop := paramChangeProposalJSON{
		Title:       "Param change",
		Description: "Changing module params",
		Changes:     []paramChangeJSON{{Subspace: action.subspace, Key: action.key, Value: action.value}},
		Deposit:     fmt.Sprint(action.deposit) + `stake`,
	}

	bz, err := json.Marshal(prop)
	if err != nil {
		log.Fatal(err)
	}

	jsonStr := string(bz)
	if strings.Contains(jsonStr, "'") {
		log.Fatal("prop json contains single quote")
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err = exec.Command("docker", "exec", tr.containerConfig.instanceName,
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, jsonStr, "/params-proposal.json")).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err = exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[action.chain].binaryName,

		"tx", "gov", "submit-proposal", "param-change",
		"/params-proposal.json",

		`--from`, `validator`+fmt.Sprint(action.from),
		`--chain-id`, string(tr.chainConfigs[action.chain].chainId),
		`--home`, tr.getValidatorHome(action.chain, action.from),
		`--node`, tr.getValidatorNode(action.chain, action.from),
		`--keyring-backend`, `test`,
		`-b`, `block`,
		`-y`,
	).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

type voteGovProposalAction struct {
	chain      chainID
	from       []validatorID
	vote       []string
	propNumber uint
}

func (tr TestRun) voteGovProposal(
	action voteGovProposalAction,
	verbose bool,
) {
	var wg sync.WaitGroup
	for i, val := range action.from {
		wg.Add(1)
		vote := action.vote[i]
		go func(val validatorID, vote string) {
			defer wg.Done()
			//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
			bz, err := exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[action.chain].binaryName,

				"tx", "gov", "vote",
				fmt.Sprint(action.propNumber), vote,

				`--from`, `validator`+fmt.Sprint(val),
				`--chain-id`, string(tr.chainConfigs[action.chain].chainId),
				`--home`, tr.getValidatorHome(action.chain, val),
				`--node`, tr.getValidatorNode(action.chain, val),
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
	time.Sleep(time.Duration(tr.chainConfigs[action.chain].votingWaitTime) * time.Second)
}

type startConsumerChainAction struct {
	consumerChain chainID
	providerChain chainID
	validators    []StartChainValidator
}

func (tr TestRun) startConsumerChain(
	action startConsumerChainAction,
	verbose bool,
) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[action.providerChain].binaryName,

		"query", "provider", "consumer-genesis",
		string(tr.chainConfigs[action.consumerChain].chainId),

		`--node`, tr.getQueryNode(action.providerChain),
		`-o`, `json`,
	)

	if verbose {
		log.Println("startConsumerChain cmd: ", cmd.String())
	}

	bz, err := cmd.CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	consumerGenesis := ".app_state.ccvconsumer = " + string(bz)
	consumerGenesisChanges := tr.chainConfigs[action.consumerChain].genesisChanges
	if consumerGenesisChanges != "" {
		consumerGenesis = consumerGenesis + " | " + consumerGenesisChanges
	}

	tr.startChain(StartChainAction{
		chain:          action.consumerChain,
		validators:     action.validators,
		genesisChanges: consumerGenesis,
		skipGentx:      true,
	}, verbose)
}

type addChainToRelayerAction struct {
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

func (tr TestRun) addChainToRelayer(
	action addChainToRelayerAction,
	verbose bool,
) {
	queryNodeIP := tr.getQueryNodeIP(action.chain)
	chainId := tr.chainConfigs[action.chain].chainId
	keyName := "query"
	rpcAddr := "http://" + queryNodeIP + ":26658"
	grpcAddr := "tcp://" + queryNodeIP + ":9091"
	wsAddr := "ws://" + queryNodeIP + ":26657/websocket"

	chainConfig := fmt.Sprintf(hermesChainConfigTemplate,
		grpcAddr,
		chainId,
		keyName,
		rpcAddr,
		wsAddr,
	)

	bashCommand := fmt.Sprintf(`echo '%s' >> %s`, chainConfig, "/root/.hermes/config.toml")

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", tr.containerConfig.instanceName, "bash", "-c",
		bashCommand,
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// Save mnemonic to file within container
	saveMnemonicCommand := fmt.Sprintf(`echo '%s' > %s`, tr.validatorConfigs[action.validator].mnemonic, "/root/.hermes/mnemonic.txt")
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err = exec.Command("docker", "exec", tr.containerConfig.instanceName, "bash", "-c",
		saveMnemonicCommand,
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err = exec.Command("docker", "exec", tr.containerConfig.instanceName, "hermes",
		"keys", "add",
		"--chain", string(tr.chainConfigs[action.chain].chainId),
		"--mnemonic-file", "/root/.hermes/mnemonic.txt",
	).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

type addIbcConnectionAction struct {
	chainA  chainID
	chainB  chainID
	clientA uint
	clientB uint
	order   string
}

func (tr TestRun) addIbcConnection(
	action addIbcConnectionAction,
	verbose bool,
) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, "hermes",
		"create", "connection",
		"--a-chain", string(tr.chainConfigs[action.chainA].chainId),
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

type addIbcChannelAction struct {
	chainA      chainID
	chainB      chainID
	connectionA uint
	portA       string
	portB       string
	order       string
}

func (tr TestRun) addIbcChannel(
	action addIbcChannelAction,
	verbose bool,
) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, "hermes",
		"create", "channel",
		"--a-chain", string(tr.chainConfigs[action.chainA].chainId),
		"--a-connection", "connection-"+fmt.Sprint(action.connectionA),
		"--a-port", action.portA,
		"--b-port", action.portB,
		"--channel-version", tr.containerConfig.ccvVersion,
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

type transferChannelCompleteAction struct {
	chainA      chainID
	chainB      chainID
	connectionA uint
	portA       string
	portB       string
	order       string
	channelA    uint
	channelB    uint
}

func (tr TestRun) transferChannelComplete(
	action transferChannelCompleteAction,
	verbose bool,
) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with chanOpenTryCmd arguments.
	chanOpenTryCmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, "hermes",
		"tx", "chan-open-try",
		"--dst-chain", string(tr.chainConfigs[action.chainB].chainId),
		"--src-chain", string(tr.chainConfigs[action.chainA].chainId),
		"--dst-connection", "connection-"+fmt.Sprint(action.connectionA),
		"--dst-port", action.portB,
		"--src-port", action.portA,
		"--src-channel", "channel-"+fmt.Sprint(action.channelA),
	)
	executeCommand(chanOpenTryCmd, "transferChanOpenTry")

	//#nosec G204 -- Bypass linter warning for spawning subprocess with chanOpenAckCmd arguments.
	chanOpenAckCmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, "hermes",
		"tx", "chan-open-ack",
		"--dst-chain", string(tr.chainConfigs[action.chainA].chainId),
		"--src-chain", string(tr.chainConfigs[action.chainB].chainId),
		"--dst-connection", "connection-"+fmt.Sprint(action.connectionA),
		"--dst-port", action.portA,
		"--src-port", action.portB,
		"--dst-channel", "channel-"+fmt.Sprint(action.channelA),
		"--src-channel", "channel-"+fmt.Sprint(action.channelB),
	)
	executeCommand(chanOpenAckCmd, "transferChanOpenAck")

	//#nosec G204 -- Bypass linter warning for spawning subprocess with chanOpenConfirmCmd arguments.
	chanOpenConfirmCmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, "hermes",
		"tx", "chan-open-confirm",
		"--dst-chain", string(tr.chainConfigs[action.chainB].chainId),
		"--src-chain", string(tr.chainConfigs[action.chainA].chainId),
		"--dst-connection", "connection-"+fmt.Sprint(action.connectionA),
		"--dst-port", action.portB,
		"--src-port", action.portA,
		"--dst-channel", "channel-"+fmt.Sprint(action.channelB),
		"--src-channel", "channel-"+fmt.Sprint(action.channelA),
	)
	executeCommand(chanOpenConfirmCmd, "transferChanOpenConfirm")
}

func executeCommand(cmd *exec.Cmd, cmdName string) {
	if verbose != nil && *verbose {
		fmt.Println(cmdName+" cmd:", cmd.String())
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
		if verbose != nil && *verbose {
			fmt.Println(cmdName + ": " + out)
		}
	}
	if err := scanner.Err(); err != nil {
		log.Fatal(err)
	}
}

type relayPacketsAction struct {
	chain   chainID
	port    string
	channel uint
}

func (tr TestRun) relayPackets(
	action relayPacketsAction,
	verbose bool,
) {
	// hermes clear packets ibc0 transfer channel-13
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, "hermes", "clear", "packets",
		"--chain", string(tr.chainConfigs[action.chain].chainId),
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

type relayRewardPacketsToProviderAction struct {
	consumerChain chainID
	providerChain chainID
	port          string
	channel       uint
}

func (tr TestRun) relayRewardPacketsToProvider(
	action relayRewardPacketsToProviderAction,
	verbose bool,
) {
	blockPerDistribution, _ := strconv.ParseUint(strings.Trim(tr.getParam(action.consumerChain, Param{Subspace: "ccvconsumer", Key: "BlocksPerDistributionTransmission"}), "\""), 10, 64)
	currentBlock := uint64(tr.getBlockHeight(action.consumerChain))
	if currentBlock <= blockPerDistribution {
		tr.waitBlocks(action.consumerChain, uint(blockPerDistribution-currentBlock+1), 60*time.Second)
	}

	tr.relayPackets(relayPacketsAction{chain: action.consumerChain, port: action.port, channel: action.channel}, verbose)
	tr.waitBlocks(action.providerChain, 1, 10*time.Second)
}

type delegateTokensAction struct {
	chain  chainID
	from   validatorID
	to     validatorID
	amount uint
}

func (tr TestRun) delegateTokens(
	action delegateTokensAction,
	verbose bool,
) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[action.chain].binaryName,

		"tx", "staking", "delegate",
		tr.validatorConfigs[action.to].valoperAddress,
		fmt.Sprint(action.amount)+`stake`,

		`--from`, `validator`+fmt.Sprint(action.from),
		`--chain-id`, string(tr.chainConfigs[action.chain].chainId),
		`--home`, tr.getValidatorHome(action.chain, action.from),
		`--node`, tr.getValidatorNode(action.chain, action.from),
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

type unbondTokensAction struct {
	chain      chainID
	sender     validatorID
	unbondFrom validatorID
	amount     uint
}

func (tr TestRun) unbondTokens(
	action unbondTokensAction,
	verbose bool,
) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[action.chain].binaryName,

		"tx", "staking", "unbond",
		tr.validatorConfigs[action.unbondFrom].valoperAddress,
		fmt.Sprint(action.amount)+`stake`,

		`--from`, `validator`+fmt.Sprint(action.sender),
		`--chain-id`, string(tr.chainConfigs[action.chain].chainId),
		`--home`, tr.getValidatorHome(action.chain, action.sender),
		`--node`, tr.getValidatorNode(action.chain, action.sender),
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

type redelegateTokensAction struct {
	chain    chainID
	src      validatorID
	dst      validatorID
	txSender validatorID
	amount   uint
}

func (tr TestRun) redelegateTokens(action redelegateTokensAction, verbose bool) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec",
		tr.containerConfig.instanceName,
		tr.chainConfigs[action.chain].binaryName,

		"tx", "staking", "redelegate",
		tr.validatorConfigs[action.src].valoperAddress,
		tr.validatorConfigs[action.dst].valoperAddress,
		fmt.Sprint(action.amount)+`stake`,
		`--from`, `validator`+fmt.Sprint(action.txSender),
		`--chain-id`, string(tr.chainConfigs[action.chain].chainId),
		`--home`, tr.getValidatorHome(action.chain, action.txSender),
		`--node`, tr.getValidatorNode(action.chain, action.txSender),
		// Need to manually set gas limit past default (200000), since redelegate has a lot of operations
		`--gas`, "900000",
		`--keyring-backend`, `test`,
		`-b`, `block`,
		`-y`,
	)

	if verbose {
		fmt.Println("redelegate cmd:", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

type downtimeSlashAction struct {
	chain     chainID
	validator validatorID
}

func (tr TestRun) invokeDowntimeSlash(action downtimeSlashAction, verbose bool) {
	// Bring validator down
	tr.setValidatorDowntime(action.chain, action.validator, true, verbose)
	// Wait appropriate amount of blocks for validator to be slashed
	tr.waitBlocks(action.chain, 3, time.Minute)
	// Bring validator back up
	tr.setValidatorDowntime(action.chain, action.validator, false, verbose)
}

// Sets validator downtime by setting the virtual ethernet interface of a node to "up" or "down"
func (tr TestRun) setValidatorDowntime(chain chainID, validator validatorID, down bool, verbose bool) {

	var lastArg string
	if down {
		lastArg = "down"
	} else {
		lastArg = "up"
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command(
		"docker",
		"exec",
		tr.containerConfig.instanceName,
		"ip",
		"link",
		"set",
		string(chain)+"-"+string(validator)+"-out",
		lastArg,
	)

	if verbose {
		fmt.Println("toggle downtime cmd:", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

type unjailValidatorAction struct {
	provider  chainID
	validator validatorID
}

// Sends an unjail transaction to the provider chain
func (tr TestRun) unjailValidator(action unjailValidatorAction, verbose bool) {

	// Wait just past the downtime_jail_duration set in config.go
	time.Sleep(3 * time.Second)

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec",
		tr.containerConfig.instanceName,
		tr.chainConfigs[action.provider].binaryName,
		"tx", "slashing", "unjail",
		// Validator is sender here
		`--from`, `validator`+fmt.Sprint(action.validator),
		`--chain-id`, string(tr.chainConfigs[action.provider].chainId),
		`--home`, tr.getValidatorHome(action.provider, action.validator),
		`--node`, tr.getValidatorNode(action.provider, action.validator),
		`--keyring-backend`, `test`,
		`-b`, `block`,
		`-y`,
	)
	if verbose {
		fmt.Println("unjail cmd:", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

type registerRepresentativeAction struct {
	chain           chainID
	representatives []validatorID
	stakes          []uint
}

func (tr TestRun) registerRepresentative(
	action registerRepresentativeAction,
	verbose bool,
) {
	var wg sync.WaitGroup
	for i, val := range action.representatives {
		wg.Add(1)
		stake := action.stakes[i]
		go func(val validatorID, stake uint) {
			defer wg.Done()

			//#nosec G204 -- Bypass linter warning for spawning subprocess with pubKeycmd arguments.
			pubKeycmd := exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[action.chain].binaryName,
				"tendermint", "show-validator",
				`--home`, tr.getValidatorHome(action.chain, val),
			)

			bzPubKey, err := pubKeycmd.CombinedOutput()
			if err != nil {
				log.Fatal(err, "\n", string(bzPubKey))
			}

			//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
			bz, err := exec.Command("docker", "exec", tr.containerConfig.instanceName, tr.chainConfigs[action.chain].binaryName,
				"tx", "staking", "create-validator",
				`--amount`, fmt.Sprint(stake)+"stake",
				`--pubkey`, string(bzPubKey),
				`--moniker`, fmt.Sprint(val),
				`--commission-rate`, "0.1",
				`--commission-max-rate`, "0.2",
				`--commission-max-change-rate`, "0.01",
				`--min-self-delegation`, "1",
				`--from`, `validator`+fmt.Sprint(val),
				`--chain-id`, string(tr.chainConfigs[action.chain].chainId),
				`--home`, tr.getValidatorHome(action.chain, val),
				`--node`, tr.getValidatorNode(action.chain, val),
				`--keyring-backend`, `test`,
				`-b`, `block`,
				`-y`,
			).CombinedOutput()

			if err != nil {
				log.Fatal(err, "\n", string(bz))
			}
		}(val, stake)
	}

	wg.Wait()
}

// Creates an additional node on selected chain
// by copying an existing validator's home folder
//
// Steps needed to double sign:
// - copy existing validator's state and configs
// - use existing priv_validator_key.json
// - use new node_key.json (otherwise node gets rejected)
// - reset priv_validator_state.json to initial values
// - start the new node
// Double sign should be registered within couple blocks.
type doublesignSlashAction struct {
	// start another node for this validator
	validator validatorID
	chain     chainID
}

func (tr TestRun) invokeDoublesignSlash(
	action doublesignSlashAction,
	verbose bool,
) {
	chainConfig := tr.chainConfigs[action.chain]
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", tr.containerConfig.instanceName, "/bin/bash",
		"/testnet-scripts/cause-doublesign.sh", chainConfig.binaryName, string(action.validator),
		string(chainConfig.chainId), chainConfig.ipPrefix).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
	tr.waitBlocks("provi", 10, 2*time.Minute)
}
