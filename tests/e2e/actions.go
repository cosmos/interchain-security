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

	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"
	clienttypes "github.com/cosmos/ibc-go/v4/modules/core/02-client/types"
	consumertypes "github.com/cosmos/interchain-security/x/ccv/consumer/types"

	"github.com/cosmos/interchain-security/x/ccv/provider/client"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
	"github.com/tidwall/gjson"
)

type SendTokensAction struct {
	Chain  ChainID
	From   ValidatorID
	To     ValidatorID
	Amount uint
}

const done = "done!!!!!!!!"

func (tr TestRun) sendTokens(
	action SendTokensAction,
	verbose bool,
) {
	binaryName := tr.chainConfigs[action.Chain].BinaryName
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, binaryName,

		"tx", "bank", "send",
		tr.validatorConfigs[action.From].DelAddress,
		tr.validatorConfigs[action.To].DelAddress,
		fmt.Sprint(action.Amount)+`stake`,

		`--chain-id`, string(tr.chainConfigs[action.Chain].ChainId),
		`--home`, tr.getValidatorHome(action.Chain, action.From),
		`--node`, tr.getValidatorNode(action.Chain, action.From),
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
	Chain      ChainID
	Validators []StartChainValidator
	// Genesis changes specific to this action, appended to genesis changes defined in chain config
	GenesisChanges string
	SkipGentx      bool
}

type StartChainValidator struct {
	Id         ValidatorID
	Allocation uint
	Stake      uint
}

func (tr TestRun) startChain(
	action StartChainAction,
	verbose bool,
) {
	chainConfig := tr.chainConfigs[action.Chain]
	type jsonValAttrs struct {
		Mnemonic         string `json:"mnemonic"`
		Allocation       string `json:"allocation"`
		Stake            string `json:"stake"`
		ValId            string `json:"val_id"`
		PrivValidatorKey string `json:"priv_validator_key"`
		NodeKey          string `json:"node_key"`
		IpSuffix         string `json:"ip_suffix"`

		ConsumerMnemonic         string `json:"consumer_mnemonic"`
		ConsumerPrivValidatorKey string `json:"consumer_priv_validator_key"`
		StartWithConsumerKey     bool   `json:"start_with_consumer_key"`
	}

	var validators []jsonValAttrs
	for _, val := range action.Validators {
		validators = append(validators, jsonValAttrs{
			Mnemonic:         tr.validatorConfigs[val.Id].Mnemonic,
			NodeKey:          tr.validatorConfigs[val.Id].NodeKey,
			ValId:            fmt.Sprint(val.Id),
			PrivValidatorKey: tr.validatorConfigs[val.Id].PrivValidatorKey,
			Allocation:       fmt.Sprint(val.Allocation) + "stake",
			Stake:            fmt.Sprint(val.Stake) + "stake",
			IpSuffix:         tr.validatorConfigs[val.Id].IpSuffix,

			ConsumerMnemonic:         tr.validatorConfigs[val.Id].ConsumerMnemonic,
			ConsumerPrivValidatorKey: tr.validatorConfigs[val.Id].ConsumerPrivValidatorKey,
			// if true node will be started with consumer key for each consumer chain
			StartWithConsumerKey: tr.validatorConfigs[val.Id].UseConsumerKey,
		})
	}

	vals, err := json.Marshal(validators)
	if err != nil {
		log.Fatal(err)
	}

	// Concat genesis changes defined in chain config, with any custom genesis changes for this chain instantiation
	var genesisChanges string
	if action.GenesisChanges != "" {
		genesisChanges = chainConfig.GenesisChanges + " | " + action.GenesisChanges
	} else {
		genesisChanges = chainConfig.GenesisChanges
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, "/bin/bash",
		"/testnet-scripts/start-chain.sh", chainConfig.BinaryName, string(vals),
		string(chainConfig.ChainId), chainConfig.IpPrefix, genesisChanges,
		fmt.Sprint(action.SkipGentx),
		// override config/config.toml for each node on chain
		// usually timeout_commit and peer_gossip_sleep_duration are changed to vary the test run duration
		// lower timeout_commit means the blocks are produced faster making the test run shorter
		// with short timeout_commit (eg. timeout_commit = 1s) some nodes may miss blocks causing the test run to fail
		tr.tendermintConfigOverride,
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
		if out == done {
			break
		}
	}
	if err := scanner.Err(); err != nil {
		log.Fatal(err)
	}

	tr.addChainToRelayer(addChainToRelayerAction{
		Chain:     action.Chain,
		Validator: action.Validators[0].Id,
	}, verbose)
}

type submitTextProposalAction struct {
	Chain       ChainID
	From        ValidatorID
	Deposit     uint
	PropType    string
	Title       string
	Description string
}

func (tr TestRun) submitTextProposal(
	action submitTextProposalAction,
	verbose bool,
) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[action.Chain].BinaryName,

		"tx", "gov", "submit-proposal",
		`--title`, action.Title,
		`--description`, action.Description,
		`--type`, action.PropType,
		`--deposit`, fmt.Sprint(action.Deposit)+`stake`,

		`--from`, `validator`+fmt.Sprint(action.From),
		`--chain-id`, string(tr.chainConfigs[action.Chain].ChainId),
		`--home`, tr.getValidatorHome(action.Chain, action.From),
		`--node`, tr.getValidatorNode(action.Chain, action.From),
		`--keyring-backend`, `test`,
		`-b`, `block`,
		`-y`,
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

type submitConsumerAdditionProposalAction struct {
	Chain         ChainID
	From          ValidatorID
	Deposit       uint
	ConsumerChain ChainID
	SpawnTime     uint
	InitialHeight clienttypes.Height
}

func (tr TestRun) submitConsumerAdditionProposal(
	action submitConsumerAdditionProposalAction,
	verbose bool,
) {
	spawnTime := tr.containerConfig.Now.Add(time.Duration(action.SpawnTime) * time.Millisecond)
	params := consumertypes.DefaultParams()
	prop := client.ConsumerAdditionProposalJSON{
		Title:                             "Propose the addition of a new chain",
		Description:                       "Gonna be a great chain",
		ChainId:                           string(tr.chainConfigs[action.ConsumerChain].ChainId),
		InitialHeight:                     action.InitialHeight,
		GenesisHash:                       []byte("gen_hash"),
		BinaryHash:                        []byte("bin_hash"),
		SpawnTime:                         spawnTime,
		ConsumerRedistributionFraction:    params.ConsumerRedistributionFraction,
		BlocksPerDistributionTransmission: params.BlocksPerDistributionTransmission,
		HistoricalEntries:                 params.HistoricalEntries,
		CcvTimeoutPeriod:                  params.CcvTimeoutPeriod,
		TransferTimeoutPeriod:             params.TransferTimeoutPeriod,
		UnbondingPeriod:                   params.UnbondingPeriod,
		Deposit:                           fmt.Sprint(action.Deposit) + `stake`,
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
	bz, err = exec.Command("docker", "exec", tr.containerConfig.InstanceName,
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, jsonStr, "/temp-proposal.json")).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err = exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[action.Chain].BinaryName,

		"tx", "gov", "submit-proposal", "consumer-addition",
		"/temp-proposal.json",

		`--from`, `validator`+fmt.Sprint(action.From),
		`--chain-id`, string(tr.chainConfigs[action.Chain].ChainId),
		`--home`, tr.getValidatorHome(action.Chain, action.From),
		`--gas`, `900000`,
		`--node`, tr.getValidatorNode(action.Chain, action.From),
		`--keyring-backend`, `test`,
		`-b`, `block`,
		`-y`,
	).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

type submitConsumerRemovalProposalAction struct {
	Chain          ChainID
	From           ValidatorID
	Deposit        uint
	ConsumerChain  ChainID
	StopTimeOffset time.Duration // offset from time.Now()
}

func (tr TestRun) submitConsumerRemovalProposal(
	action submitConsumerRemovalProposalAction,
	verbose bool,
) {
	stopTime := tr.containerConfig.Now.Add(action.StopTimeOffset)
	prop := client.ConsumerRemovalProposalJSON{
		Title:       fmt.Sprintf("Stop the %v chain", action.ConsumerChain),
		Description: "It was a great chain",
		ChainId:     string(tr.chainConfigs[action.ConsumerChain].ChainId),
		StopTime:    stopTime,
		Deposit:     fmt.Sprint(action.Deposit) + `stake`,
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
	bz, err = exec.Command("docker", "exec", tr.containerConfig.InstanceName,
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, jsonStr, "/temp-proposal.json")).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err = exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[action.Chain].BinaryName,

		"tx", "gov", "submit-proposal", "consumer-removal",
		"/temp-proposal.json",

		`--from`, `validator`+fmt.Sprint(action.From),
		`--chain-id`, string(tr.chainConfigs[action.Chain].ChainId),
		`--home`, tr.getValidatorHome(action.Chain, action.From),
		`--node`, tr.getValidatorNode(action.Chain, action.From),
		`--keyring-backend`, `test`,
		`-b`, `block`,
		`-y`,
	).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

type submitParamChangeProposalAction struct {
	Chain    ChainID
	From     ValidatorID
	Deposit  uint
	Subspace string
	Key      string
	Value    interface{}
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
		Changes:     []paramChangeJSON{{Subspace: action.Subspace, Key: action.Key, Value: action.Value}},
		Deposit:     fmt.Sprint(action.Deposit) + `stake`,
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
	bz, err = exec.Command("docker", "exec", tr.containerConfig.InstanceName,
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, jsonStr, "/params-proposal.json")).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err = exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[action.Chain].BinaryName,

		"tx", "gov", "submit-proposal", "param-change",
		"/params-proposal.json",

		`--from`, `validator`+fmt.Sprint(action.From),
		`--chain-id`, string(tr.chainConfigs[action.Chain].ChainId),
		`--home`, tr.getValidatorHome(action.Chain, action.From),
		`--node`, tr.getValidatorNode(action.Chain, action.From),
		`--gas`, "900000",
		`--keyring-backend`, `test`,
		`-b`, `block`,
		`-y`,
	).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

type submitEquivocationProposalAction struct {
	Chain     ChainID
	Height    int64
	Time      time.Time
	Power     int64
	Validator ValidatorID
	Deposit   uint
	From      ValidatorID
}

func (tr TestRun) submitEquivocationProposal(action submitEquivocationProposalAction, verbose bool) {
	val := tr.validatorConfigs[action.Validator]
	providerChain := tr.chainConfigs[ChainID("provi")]

	prop := client.EquivocationProposalJSON{
		EquivocationProposal: types.EquivocationProposal{
			Title:       "Validator equivocation!",
			Description: fmt.Sprintf("Validator: %s has committed an equivocation infraction on chainID: %s", action.Validator, action.Chain),
			Equivocations: []*evidencetypes.Equivocation{
				{
					Height:           action.Height,
					Time:             action.Time,
					Power:            action.Power,
					ConsensusAddress: val.ValconsAddress,
				},
			},
		},
		Deposit: fmt.Sprint(action.Deposit) + `stake`,
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
	bz, err = exec.Command("docker", "exec", tr.containerConfig.InstanceName,
		"/bin/bash", "-c", fmt.Sprintf(`echo '%s' > %s`, jsonStr, "/equivocation-proposal.json")).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err = exec.Command("docker", "exec", tr.containerConfig.InstanceName, providerChain.BinaryName,

		"tx", "gov", "submit-proposal", "equivocation",
		"/equivocation-proposal.json",

		`--from`, `validator`+fmt.Sprint(action.From),
		`--chain-id`, string(providerChain.ChainId),
		`--home`, tr.getValidatorHome(providerChain.ChainId, action.From),
		`--node`, tr.getValidatorNode(providerChain.ChainId, action.From),
		`--gas`, "9000000",
		`--keyring-backend`, `test`,
		`-b`, `block`,
		`-y`,
	).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

type voteGovProposalAction struct {
	Chain      ChainID
	From       []ValidatorID
	Vote       []string
	PropNumber uint
}

func (tr TestRun) voteGovProposal(
	action voteGovProposalAction,
	verbose bool,
) {
	var wg sync.WaitGroup
	for i, val := range action.From {
		wg.Add(1)
		vote := action.Vote[i]
		go func(val ValidatorID, vote string) {
			defer wg.Done()
			//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
			bz, err := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[action.Chain].BinaryName,

				"tx", "gov", "vote",
				fmt.Sprint(action.PropNumber), vote,

				`--from`, `validator`+fmt.Sprint(val),
				`--chain-id`, string(tr.chainConfigs[action.Chain].ChainId),
				`--home`, tr.getValidatorHome(action.Chain, val),
				`--node`, tr.getValidatorNode(action.Chain, val),
				`--keyring-backend`, `test`,
				`--gas`, "900000",
				`-b`, `block`,
				`-y`,
			).CombinedOutput()
			if err != nil {
				log.Fatal(err, "\n", string(bz))
			}
		}(val, vote)
	}

	wg.Wait()
	time.Sleep(time.Duration(tr.chainConfigs[action.Chain].VotingWaitTime) * time.Second)
}

type startConsumerChainAction struct {
	ConsumerChain  ChainID
	ProviderChain  ChainID
	Validators     []StartChainValidator
	GenesisChanges string
}

func (tr TestRun) startConsumerChain(
	action startConsumerChainAction,
	verbose bool,
) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[action.ProviderChain].BinaryName,

		"query", "provider", "consumer-genesis",
		string(tr.chainConfigs[action.ConsumerChain].ChainId),

		`--node`, tr.getQueryNode(action.ProviderChain),
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
	consumerGenesisChanges := tr.chainConfigs[action.ConsumerChain].GenesisChanges
	if consumerGenesisChanges != "" {
		consumerGenesis = consumerGenesis + " | " + consumerGenesisChanges + " | " + action.GenesisChanges
	}

	tr.startChain(StartChainAction{
		Chain:          action.ConsumerChain,
		Validators:     action.Validators,
		GenesisChanges: consumerGenesis,
		SkipGentx:      true,
	}, verbose)
}

type addChainToRelayerAction struct {
	Chain     ChainID
	Validator ValidatorID
}

const hermesChainConfigTemplate = `

[[chains]]
account_prefix = "cosmos"
clock_drift = "5s"
gas_multiplier = 1.1
grpc_addr = "%s"
id = "%s"
key_name = "%s"
max_gas = 20000000
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
	queryNodeIP := tr.getQueryNodeIP(action.Chain)
	chainId := tr.chainConfigs[action.Chain].ChainId
	keyName := "query"
	rpcAddr := "http://" + queryNodeIP + ":26658"
	grpcAddr := "tcp://" + queryNodeIP + ":9091"
	wsAddr := "ws://" + queryNodeIP + ":26658/websocket"

	chainConfig := fmt.Sprintf(hermesChainConfigTemplate,
		grpcAddr,
		chainId,
		keyName,
		rpcAddr,
		wsAddr,
	)

	bashCommand := fmt.Sprintf(`echo '%s' >> %s`, chainConfig, "/root/.hermes/config.toml")

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", tr.containerConfig.InstanceName, "bash", "-c",
		bashCommand,
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	// Save mnemonic to file within container
	saveMnemonicCommand := fmt.Sprintf(`echo '%s' > %s`, tr.validatorConfigs[action.Validator].Mnemonic, "/root/.hermes/mnemonic.txt")
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err = exec.Command("docker", "exec", tr.containerConfig.InstanceName, "bash", "-c",
		saveMnemonicCommand,
	).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err = exec.Command("docker", "exec", tr.containerConfig.InstanceName, "hermes",
		"keys", "add",
		"--chain", string(tr.chainConfigs[action.Chain].ChainId),
		"--mnemonic-file", "/root/.hermes/mnemonic.txt",
	).CombinedOutput()

	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
}

type addIbcConnectionAction struct {
	ChainA  ChainID
	ChainB  ChainID
	ClientA uint
	ClientB uint
}

func (tr TestRun) addIbcConnection(
	action addIbcConnectionAction,
	verbose bool,
) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, "hermes",
		"create", "connection",
		"--a-chain", string(tr.chainConfigs[action.ChainA].ChainId),
		"--a-client", "07-tendermint-"+fmt.Sprint(action.ClientA),
		"--b-client", "07-tendermint-"+fmt.Sprint(action.ClientB),
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
		if out == done {
			break
		}
	}
	if err := scanner.Err(); err != nil {
		log.Fatal(err)
	}
}

type addIbcChannelAction struct {
	ChainA      ChainID
	ChainB      ChainID
	ConnectionA uint
	PortA       string
	PortB       string
	Order       string
}

type startHermesAction struct{}

func (tr TestRun) startHermes(
	action startHermesAction,
	verbose bool,
) {
	// hermes start is running in detached mode
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", "-d", tr.containerConfig.InstanceName, "hermes",
		"start",
	)

	if err := cmd.Start(); err != nil {
		log.Fatal(err)
	}

	if verbose {
		fmt.Println("started Hermes")
	}
}

func (tr TestRun) addIbcChannel(
	action addIbcChannelAction,
	verbose bool,
) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, "hermes",
		"create", "channel",
		"--a-chain", string(tr.chainConfigs[action.ChainA].ChainId),
		"--a-connection", "connection-"+fmt.Sprint(action.ConnectionA),
		"--a-port", action.PortA,
		"--b-port", action.PortB,
		"--channel-version", tr.containerConfig.CcvVersion,
		"--order", action.Order,
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
		if out == done {
			break
		}
	}
	if err := scanner.Err(); err != nil {
		log.Fatal(err)
	}
}

type transferChannelCompleteAction struct {
	ChainA      ChainID
	ChainB      ChainID
	ConnectionA uint
	PortA       string
	PortB       string
	Order       string
	ChannelA    uint
	ChannelB    uint
}

func (tr TestRun) transferChannelComplete(
	action transferChannelCompleteAction,
	verbose bool,
) {
	//#nosec G204 -- Bypass linter warning for spawning subprocess with chanOpenTryCmd arguments.
	chanOpenTryCmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, "hermes",
		"tx", "chan-open-try",
		"--dst-chain", string(tr.chainConfigs[action.ChainB].ChainId),
		"--src-chain", string(tr.chainConfigs[action.ChainA].ChainId),
		"--dst-connection", "connection-"+fmt.Sprint(action.ConnectionA),
		"--dst-port", action.PortB,
		"--src-port", action.PortA,
		"--src-channel", "channel-"+fmt.Sprint(action.ChannelA),
	)
	executeCommand(chanOpenTryCmd, "transferChanOpenTry")

	//#nosec G204 -- Bypass linter warning for spawning subprocess with chanOpenAckCmd arguments.
	chanOpenAckCmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, "hermes",
		"tx", "chan-open-ack",
		"--dst-chain", string(tr.chainConfigs[action.ChainA].ChainId),
		"--src-chain", string(tr.chainConfigs[action.ChainB].ChainId),
		"--dst-connection", "connection-"+fmt.Sprint(action.ConnectionA),
		"--dst-port", action.PortA,
		"--src-port", action.PortB,
		"--dst-channel", "channel-"+fmt.Sprint(action.ChannelA),
		"--src-channel", "channel-"+fmt.Sprint(action.ChannelB),
	)
	executeCommand(chanOpenAckCmd, "transferChanOpenAck")

	//#nosec G204 -- Bypass linter warning for spawning subprocess with chanOpenConfirmCmd arguments.
	chanOpenConfirmCmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, "hermes",
		"tx", "chan-open-confirm",
		"--dst-chain", string(tr.chainConfigs[action.ChainB].ChainId),
		"--src-chain", string(tr.chainConfigs[action.ChainA].ChainId),
		"--dst-connection", "connection-"+fmt.Sprint(action.ConnectionA),
		"--dst-port", action.PortB,
		"--src-port", action.PortA,
		"--dst-channel", "channel-"+fmt.Sprint(action.ChannelB),
		"--src-channel", "channel-"+fmt.Sprint(action.ChannelA),
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
	Chain   ChainID
	Port    string
	Channel uint
}

func (tr TestRun) relayPackets(
	action relayPacketsAction,
	verbose bool,
) {
	// hermes clear packets ibc0 transfer channel-13
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, "hermes", "clear", "packets",
		"--chain", string(tr.chainConfigs[action.Chain].ChainId),
		"--port", action.Port,
		"--channel", "channel-"+fmt.Sprint(action.Channel),
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
	consumerChain ChainID
	providerChain ChainID
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

	tr.relayPackets(relayPacketsAction{Chain: action.consumerChain, Port: action.port, Channel: action.channel}, verbose)
	tr.waitBlocks(action.providerChain, 1, 10*time.Second)
}

type delegateTokensAction struct {
	Chain  ChainID
	From   ValidatorID
	To     ValidatorID
	Amount uint
}

func (tr TestRun) delegateTokens(
	action delegateTokensAction,
	verbose bool,
) {
	toValCfg := tr.validatorConfigs[action.To]
	delegateAddr := toValCfg.ValoperAddress
	if action.Chain != ChainID("provi") && toValCfg.UseConsumerKey {
		delegateAddr = toValCfg.ConsumerValoperAddress
	}
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[action.Chain].BinaryName,

		"tx", "staking", "delegate",
		delegateAddr,
		fmt.Sprint(action.Amount)+`stake`,

		`--from`, `validator`+fmt.Sprint(action.From),
		`--chain-id`, string(tr.chainConfigs[action.Chain].ChainId),
		`--home`, tr.getValidatorHome(action.Chain, action.From),
		`--node`, tr.getValidatorNode(action.Chain, action.From),
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
	Chain      ChainID
	Sender     ValidatorID
	UnbondFrom ValidatorID
	Amount     uint
}

func (tr TestRun) unbondTokens(
	action unbondTokensAction,
	verbose bool,
) {
	unbondFrom := tr.validatorConfigs[action.UnbondFrom].ValoperAddress
	if tr.validatorConfigs[action.UnbondFrom].UseConsumerKey {
		unbondFrom = tr.validatorConfigs[action.UnbondFrom].ConsumerValoperAddress
	}

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[action.Chain].BinaryName,

		"tx", "staking", "unbond",
		unbondFrom,
		fmt.Sprint(action.Amount)+`stake`,

		`--from`, `validator`+fmt.Sprint(action.Sender),
		`--chain-id`, string(tr.chainConfigs[action.Chain].ChainId),
		`--home`, tr.getValidatorHome(action.Chain, action.Sender),
		`--node`, tr.getValidatorNode(action.Chain, action.Sender),
		`--gas`, "900000",
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
	Chain    ChainID
	Src      ValidatorID
	Dst      ValidatorID
	TxSender ValidatorID
	Amount   uint
}

func (tr TestRun) redelegateTokens(action redelegateTokensAction, verbose bool) {
	srcCfg := tr.validatorConfigs[action.Src]
	dstCfg := tr.validatorConfigs[action.Dst]

	redelegateSrc := srcCfg.ValoperAddress
	if action.Chain != ChainID("provi") && srcCfg.UseConsumerKey {
		redelegateSrc = srcCfg.ConsumerValoperAddress
	}

	redelegateDst := dstCfg.ValoperAddress
	if action.Chain != ChainID("provi") && dstCfg.UseConsumerKey {
		redelegateDst = dstCfg.ConsumerValoperAddress
	}
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec",
		tr.containerConfig.InstanceName,
		tr.chainConfigs[action.Chain].BinaryName,

		"tx", "staking", "redelegate",
		redelegateSrc,
		redelegateDst,
		fmt.Sprint(action.Amount)+`stake`,
		`--from`, `validator`+fmt.Sprint(action.TxSender),
		`--chain-id`, string(tr.chainConfigs[action.Chain].ChainId),
		`--home`, tr.getValidatorHome(action.Chain, action.TxSender),
		`--node`, tr.getValidatorNode(action.Chain, action.TxSender),
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
	Chain     ChainID
	Validator ValidatorID
}

func (tr TestRun) invokeDowntimeSlash(action downtimeSlashAction, verbose bool) {
	// Bring validator down
	tr.setValidatorDowntime(action.Chain, action.Validator, true, verbose)
	// Wait appropriate amount of blocks for validator to be slashed
	tr.waitBlocks(action.Chain, 12, 2*time.Minute)
	// Bring validator back up
	tr.setValidatorDowntime(action.Chain, action.Validator, false, verbose)
}

// Sets validator downtime by setting the virtual ethernet interface of a node to "up" or "down"
func (tr TestRun) setValidatorDowntime(chain ChainID, validator ValidatorID, down bool, verbose bool) {
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
		tr.containerConfig.InstanceName,
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
	Provider  ChainID
	Validator ValidatorID
}

// Sends an unjail transaction to the provider chain
func (tr TestRun) unjailValidator(action unjailValidatorAction, verbose bool) {
	// wait a block to be sure downtime_jail_duration has elapsed
	tr.waitBlocks(action.Provider, 1, time.Minute)

	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec",
		tr.containerConfig.InstanceName,
		tr.chainConfigs[action.Provider].BinaryName,
		"tx", "slashing", "unjail",
		// Validator is sender here
		`--from`, `validator`+fmt.Sprint(action.Validator),
		`--chain-id`, string(tr.chainConfigs[action.Provider].ChainId),
		`--home`, tr.getValidatorHome(action.Provider, action.Validator),
		`--node`, tr.getValidatorNode(action.Provider, action.Validator),
		`--gas`, "900000",
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

	// wait for 1 blocks to make sure that tx got included
	// in a block and packets committed before proceeding
	tr.waitBlocks(action.Provider, 1, time.Minute)
}

type registerRepresentativeAction struct {
	Chain           ChainID
	Representatives []ValidatorID
	Stakes          []uint
}

func (tr TestRun) registerRepresentative(
	action registerRepresentativeAction,
	verbose bool,
) {
	var wg sync.WaitGroup
	for i, val := range action.Representatives {
		wg.Add(1)
		stake := action.Stakes[i]
		go func(val ValidatorID, stake uint) {
			defer wg.Done()

			//#nosec G204 -- Bypass linter warning for spawning subprocess with pubKeycmd arguments.
			pubKeycmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[action.Chain].BinaryName,
				"tendermint", "show-validator",
				`--home`, tr.getValidatorHome(action.Chain, val),
			)

			bzPubKey, err := pubKeycmd.CombinedOutput()
			if err != nil {
				log.Fatal(err, "\n", string(bzPubKey))
			}

			//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
			bz, err := exec.Command("docker", "exec", tr.containerConfig.InstanceName, tr.chainConfigs[action.Chain].BinaryName,
				"tx", "staking", "create-validator",
				`--amount`, fmt.Sprint(stake)+"stake",
				`--pubkey`, string(bzPubKey),
				`--moniker`, fmt.Sprint(val),
				`--commission-rate`, "0.1",
				`--commission-max-rate`, "0.2",
				`--commission-max-change-rate`, "0.01",
				`--min-self-delegation`, "1",
				`--from`, `validator`+fmt.Sprint(val),
				`--chain-id`, string(tr.chainConfigs[action.Chain].ChainId),
				`--home`, tr.getValidatorHome(action.Chain, val),
				`--node`, tr.getValidatorNode(action.Chain, val),
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
	// start another node for this Validator
	Validator ValidatorID
	Chain     ChainID
}

func (tr TestRun) invokeDoublesignSlash(
	action doublesignSlashAction,
	verbose bool,
) {
	chainConfig := tr.chainConfigs[action.Chain]
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	bz, err := exec.Command("docker", "exec", tr.containerConfig.InstanceName, "/bin/bash",
		"/testnet-scripts/cause-doublesign.sh", chainConfig.BinaryName, string(action.Validator),
		string(chainConfig.ChainId), chainConfig.IpPrefix).CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}
	tr.waitBlocks("provi", 10, 2*time.Minute)
}

type assignConsumerPubKeyAction struct {
	Chain          ChainID
	Validator      ValidatorID
	ConsumerPubkey string
	// ReconfigureNode will change keys the node uses and restart
	ReconfigureNode bool
	// executing the action should raise an error
	ExpectError bool
}

func (tr TestRun) assignConsumerPubKey(action assignConsumerPubKeyAction, verbose bool) {
	valCfg := tr.validatorConfigs[action.Validator]

	assignKey := fmt.Sprintf(
		`%s tx provider assign-consensus-key %s '%s' --from validator%s --chain-id %s --home %s --node %s --gas 900000 --keyring-backend test -b block -y -o json`,
		tr.chainConfigs[ChainID("provi")].BinaryName,
		string(tr.chainConfigs[action.Chain].ChainId),
		action.ConsumerPubkey,
		action.Validator,
		tr.chainConfigs[ChainID("provi")].ChainId,
		tr.getValidatorHome(ChainID("provi"), action.Validator),
		tr.getValidatorNode(ChainID("provi"), action.Validator),
	)
	//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
	cmd := exec.Command("docker", "exec",
		tr.containerConfig.InstanceName,
		"/bin/bash", "-c",
		assignKey,
	)

	if verbose {
		fmt.Println("assignConsumerPubKey cmd:", cmd.String())
	}

	bz, err := cmd.CombinedOutput()
	if err != nil {
		log.Fatal(err, "\n", string(bz))
	}

	jsonStr := string(bz)
	code := gjson.Get(jsonStr, "code")
	rawLog := gjson.Get(jsonStr, "raw_log")
	if !action.ExpectError && code.Int() != 0 {
		log.Fatalf("unexpected error during key assignment - code: %s, output: %s", code, jsonStr)
	}

	if action.ExpectError {
		if code.Int() == 0 {
		} else if verbose {
			fmt.Printf("got expected error during key assignment | code: %v | log: %s\n", code, rawLog)
		}
	}

	// node was started with provider key
	// we swap the nodes's keys for consumer keys and restart it
	if action.ReconfigureNode {
		//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments.
		configureNodeCmd := exec.Command("docker", "exec", tr.containerConfig.InstanceName, "/bin/bash",
			"/testnet-scripts/reconfigure-node.sh", tr.chainConfigs[action.Chain].BinaryName,
			string(action.Validator), string(action.Chain),
			tr.chainConfigs[action.Chain].IpPrefix, valCfg.IpSuffix,
			valCfg.ConsumerMnemonic, valCfg.ConsumerPrivValidatorKey,
			valCfg.ConsumerNodeKey,
		)

		if verbose {
			fmt.Println("assignConsumerPubKey - reconfigure node cmd:", configureNodeCmd.String())
		}

		cmdReader, err := configureNodeCmd.StdoutPipe()
		if err != nil {
			log.Fatal(err)
		}
		configureNodeCmd.Stderr = configureNodeCmd.Stdout

		if err := configureNodeCmd.Start(); err != nil {
			log.Fatal(err)
		}

		scanner := bufio.NewScanner(cmdReader)

		for scanner.Scan() {
			out := scanner.Text()
			if verbose {
				fmt.Println("assign key - reconfigure: " + out)
			}
			if out == done {
				break
			}
		}
		if err := scanner.Err(); err != nil {
			log.Fatal(err)
		}

		// TODO: @MSalopek refactor this so test config is not changed at runtime
		// make the validator use consumer key
		valCfg.UseConsumerKey = true
		tr.validatorConfigs[action.Validator] = valCfg
	}
}

// slashThrottleDequeue polls slash queue sizes until nextQueueSize is achieved
type slashThrottleDequeue struct {
	Chain            ChainID
	CurrentQueueSize int
	NextQueueSize    int
	// panic if Timeout is exceeded
	Timeout time.Duration
}

func (tr TestRun) waitForSlashThrottleDequeue(
	action slashThrottleDequeue,
	verbose bool,
) {
	timeout := time.Now().Add(action.Timeout)
	initialGlobalQueueSize := int(tr.getGlobalSlashQueueSize())

	if initialGlobalQueueSize != action.CurrentQueueSize {
		panic(fmt.Sprintf("wrong initial queue size: %d - expected global queue: %d\n", initialGlobalQueueSize, action.CurrentQueueSize))
	}
	for {
		globalQueueSize := int(tr.getGlobalSlashQueueSize())
		chainQueueSize := int(tr.getConsumerChainPacketQueueSize(action.Chain))
		if verbose {
			fmt.Printf("waiting for packed queue size to reach: %d - current: %d\n", action.NextQueueSize, globalQueueSize)
		}

		// check if global queue size is equal to chain queue size
		if globalQueueSize == chainQueueSize && globalQueueSize == action.NextQueueSize { //nolint:gocritic // this is the comparison that we want here.
			break
		}

		if time.Now().After(timeout) {
			panic(fmt.Sprintf("\n\n\nwaitForSlashThrottleDequeuemethod has timed out after: %s\n\n", action.Timeout))
		}

		time.Sleep(500 * time.Millisecond)
	}
	// wair for 2 blocks to be created
	// allowing the jailing to be incorporated into voting power
	tr.waitBlocks(action.Chain, 2, time.Minute)
}

func uintPointer(i uint) *uint {
	return &i
}
