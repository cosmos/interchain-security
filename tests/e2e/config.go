package main

import (
	"fmt"
	"log"
	"os/exec"
	"strconv"
	"time"

	"golang.org/x/mod/semver"
)

var (
	ProviderAccountPrefix = "cosmos"
	ConsumerAccountPrefix = "consumer"
)

// hermesTemplates maps hermes configuration templates to hermes versions
var hermesTemplates = map[string]string{
	"v1.4": `

	[[chains]]
	account_prefix = "%s"
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
		price = 0.000

	[chains.trust_threshold]
		denominator = "3"
		numerator = "1"
	`,
	// introduction of event_source
	"v1.6": `

	[[chains]]
	account_prefix = "%s"
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
	event_source = { mode = "push", url = "%s", batch_delay = "50ms" }
	ccv_consumer_chain = %v

	[chains.gas_price]
		denom = "stake"
		price = 0.000

	[chains.trust_threshold]
		denominator = "3"
		numerator = "1"
	`,
}

// TODO: Determine if user defined type (wrapping a primitive string) is desired in long run
type (
	ChainID     string
	ValidatorID string
)

// Supported Test configurations to be used with GetTestConfig
type TestConfigType string

const (
	DefaultTestCfg              TestConfigType = "default"
	ChangeoverTestCfg           TestConfigType = "changeover"
	DemocracyTestCfg            TestConfigType = "democracy"
	DemocracyRewardTestCfg      TestConfigType = "democracy-reward"
	SlashThrottleTestCfg        TestConfigType = "slash-throttling"
	MulticonsumerTestCfg        TestConfigType = "multi-consumer"
	ConsumerMisbehaviourTestCfg TestConfigType = "consumer-misbehaviour"
	CompatibilityTestCfg        TestConfigType = "compatibility"
)

// Attributes that are unique to a validator. Allows us to map (part of)
// the set of strings defined above to a set of viable validators
type ValidatorConfig struct {
	// Seed phrase to generate a secp256k1 key used by the validator on the provider
	Mnemonic string
	// Validator account address on provider marshaled to string using Bech32
	// with Bech32Prefix = ProviderAccountPrefix
	DelAddress string
	// Validator account address on provider marshaled to string using Bech32
	// with Bech32Prefix = ConsumerAccountPrefix
	DelAddressOnConsumer string
	// Validator operator address on provider marshaled to string using Bech32
	// with Bech32Prefix = ProviderAccountPrefix
	ValoperAddress string
	// Validator operator address on provider marshaled to string using Bech32
	// with Bech32Prefix = ConsumerAccountPrefix
	ValoperAddressOnConsumer string
	// Validator consensus address on provider marshaled to string using Bech32
	// with Bech32Prefix = ProviderAccountPrefix. It matches the PrivValidatorKey below.
	ValconsAddress string
	// Validator consensus address on provider marshaled to string using Bech32
	// with Bech32Prefix = ConsumerAccountPrefix.
	ValconsAddressOnConsumer string
	// Key used for consensus on provider
	PrivValidatorKey string
	NodeKey          string
	// Must be an integer greater than 0 and less than 253
	IpSuffix string

	// consumer chain key assignment data
	// keys are used on a new node

	// Seed phrase to generate a secp256k1 key used by the validator on the consumer
	ConsumerMnemonic string
	// Validator account address on consumer marshaled to string using Bech32
	// with Bech32Prefix = ConsumerAccountPrefix
	ConsumerDelAddress string
	// Validator account address on consumer marshaled to string using Bech32
	// with Bech32Prefix = ProviderAccountPrefix
	ConsumerDelAddressOnProvider string
	// Validator operator address on consumer marshaled to string using Bech32
	// with Bech32Prefix = ConsumerAccountPrefix
	ConsumerValoperAddress string
	// Validator operator address on consumer marshaled to string using Bech32
	// with Bech32Prefix = ProviderAccountPrefix
	ConsumerValoperAddressOnProvider string
	// Validator consensus address on consumer marshaled to string using Bech32
	// with Bech32Prefix = ConsumerAccountPrefix. It matches the PrivValidatorKey below.
	ConsumerValconsAddress string
	// Validator consensus address on consumer marshaled to string using Bech32
	// with Bech32Prefix = ProviderAccountPrefix.
	ConsumerValconsAddressOnProvider string
	ConsumerValPubKey                string
	// Key used for consensus on consumer
	ConsumerPrivValidatorKey string
	ConsumerNodeKey          string
	UseConsumerKey           bool // if true the validator node will start with consumer key
}

// Attributes that are unique to a chain. Allows us to map (part of)
// the set of strings defined above to a set of viable chains
type ChainConfig struct {
	ChainId ChainID
	// The account prefix configured on the chain. For example, on the Hub, this is "cosmos"
	AccountPrefix string
	// Must be unique per chain
	IpPrefix       string
	VotingWaitTime uint
	// Any transformations to apply to the genesis file of all chains instantiated with this chain config, as a jq string.
	// Example: ".app_state.gov.params.voting_period = \"5s\" | .app_state.slashing.params.signed_blocks_window = \"2\" | .app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\""
	GenesisChanges string
	BinaryName     string

	// binary to use after upgrade height
	UpgradeBinary string
}

type ContainerConfig struct {
	ContainerName string
	InstanceName  string
	CcvVersion    string
	Now           time.Time
}

type TargetConfig struct {
	gaiaTag         string
	localSdkPath    string
	useGaia         bool
	providerVersion string
	consumerVersion string
}

type TestConfig struct {
	// These are the non altered values during a typical test run, where multiple test runs can exist
	// to validate different action sequences and corresponding state checks.
	containerConfig  ContainerConfig
	validatorConfigs map[ValidatorID]ValidatorConfig
	chainConfigs     map[ChainID]ChainConfig
	providerVersion  string
	consumerVersion  string
	// override config.toml parameters
	// usually used to override timeout_commit
	// having shorter timeout_commit reduces the test runtime because blocks are produced faster
	// lengthening the timeout_commit increases the test runtime because blocks are produced slower but the test is more reliable
	tendermintConfigOverride string
	useCometmock             bool // if false, nodes run CometBFT
	useGorelayer             bool // if false, Hermes is used as the relayer
	// chains which are running, i.e. producing blocks, at the moment
	runningChains map[ChainID]bool
	// Used with CometMock. The time by which chains have been advanced. Used to keep chains in sync: when a new chain is started, advance its time by this value to keep chains in sync.
	timeOffset       time.Duration
	transformGenesis bool
	name             string
}

// Initialize initializes the TestConfig instance by setting the runningChains field to an empty map.
func (tr *TestConfig) Initialize() {
	tr.runningChains = make(map[ChainID]bool)
}

// getIcsVersion returns earliest ICS version (relevant to config) a git reference is part of
// This is needed for version dependent configs as CompatibilityConfig.
// Note: if no matching version is found an empty string is returned
func getIcsVersion(reference string) string {
	icsVersion := ""
	if reference == "" {
		return icsVersion
	}
	if semver.IsValid(reference) {
		// remove build suffix
		return semver.Canonical(reference)
	}
	for _, tag := range []string{"v2.0.0", "v2.4.0", "v2.4.0-lsm", "v3.1.0", "v3.2.0", "v3.3.0", "v4.0.0"} {
		//#nosec G204 -- Bypass linter warning for spawning subprocess with cmd arguments
		cmd := exec.Command("git", "merge-base", "--is-ancestor", reference, tag)
		out, err := cmd.CombinedOutput()
		if err == nil {
			icsVersion = tag
		}

		if rc, ok := err.(*exec.ExitError); ok {
			if rc.ExitCode() != 1 {
				log.Printf("error identifying config version to use '%v': %s", err, string(out))
				return ""
			}
			// reference is not part of this tag, try next one
		}
	}
	return semver.Canonical(icsVersion)
}

// GetTestConfig returns the TestConfig for a given type of test
func GetTestConfig(cfgType TestConfigType, providerVersion, consumerVersion string) TestConfig {
	pv := getIcsVersion(providerVersion)
	cv := getIcsVersion(consumerVersion)
	fmt.Println("Config version for provider :", pv)
	fmt.Println("Config version for consumer :", cv)
	var testCfg TestConfig
	switch cfgType {
	case DefaultTestCfg:
		testCfg = DefaultTestConfig()
	case ChangeoverTestCfg:
		testCfg = ChangeoverTestConfig()
	case DemocracyTestCfg:
		testCfg = DemocracyTestConfig(false)
	case DemocracyRewardTestCfg:
		testCfg = DemocracyTestConfig(true)
	case SlashThrottleTestCfg:
		testCfg = SlashThrottleTestConfig()
	case MulticonsumerTestCfg:
		testCfg = MultiConsumerTestConfig()
	case ConsumerMisbehaviourTestCfg:
		testCfg = ConsumerMisbehaviourTestConfig()
	case CompatibilityTestCfg:
		testCfg = CompatibilityTestConfig(pv, cv)
	default:
		panic(fmt.Sprintf("Invalid test config: %s", cfgType))
	}
	testCfg.consumerVersion = consumerVersion
	testCfg.providerVersion = providerVersion
	return testCfg
}

func getDefaultValidators() map[ValidatorID]ValidatorConfig {
	return map[ValidatorID]ValidatorConfig{
		ValidatorID("alice"): {
			Mnemonic:                 "pave immune ethics wrap gain ceiling always holiday employ earth tumble real ice engage false unable carbon equal fresh sick tattoo nature pupil nuclear",
			DelAddress:               "cosmos19pe9pg5dv9k5fzgzmsrgnw9rl9asf7ddwhu7lm",
			DelAddressOnConsumer:     "consumer19pe9pg5dv9k5fzgzmsrgnw9rl9asf7ddtz33vu",
			ValoperAddress:           "cosmosvaloper19pe9pg5dv9k5fzgzmsrgnw9rl9asf7ddtrgtng",
			ValoperAddressOnConsumer: "consumervaloper19pe9pg5dv9k5fzgzmsrgnw9rl9asf7ddy6jwzg",
			ValconsAddress:           "cosmosvalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xw4mceq",
			ValconsAddressOnConsumer: "consumervalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xpvpagq",
			PrivValidatorKey:         `{"address":"06C0F3E47CC5C748269088DC2F36411D3AAA27C6","pub_key":{"type":"tendermint/PubKeyEd25519","value":"RrclQz9bIhkIy/gfL485g3PYMeiIku4qeo495787X10="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"uX+ZpDMg89a6gtqs/+MQpCTSqlkZ0nJQJOhLlCJvwvdGtyVDP1siGQjL+B8vjzmDc9gx6IiS7ip6jj3nvztfXQ=="}}`,
			NodeKey:                  `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"fjw4/DAhyRPnwKgXns5SV7QfswRSXMWJpHS7TyULDmJ8ofUc5poQP8dgr8bZRbCV5RV8cPqDq3FPdqwpmUbmdA=="}}`,
			IpSuffix:                 "4",

			// consumer chain assigned key
			ConsumerMnemonic:                 "exile install vapor thing little toss immune notable lounge december final easy strike title end program interest quote cloth forget forward job october twenty",
			ConsumerDelAddress:               "consumer1eeeggku6dzk3mv7wph3zq035rhtd890sh9rl32",
			ConsumerDelAddressOnProvider:     "cosmos1eeeggku6dzk3mv7wph3zq035rhtd890sjswszd",
			ConsumerValoperAddress:           "consumervaloper1eeeggku6dzk3mv7wph3zq035rhtd890scaqql7",
			ConsumerValoperAddressOnProvider: "cosmosvaloper1eeeggku6dzk3mv7wph3zq035rhtd890shy69w7",
			ConsumerValconsAddress:           "consumervalcons1muys5jyqk4xd27e208nym85kn0t4zjcfk9q5ce",
			ConsumerValconsAddressOnProvider: "cosmosvalcons1muys5jyqk4xd27e208nym85kn0t4zjcfeu63fe",
			ConsumerValPubKey:                `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"ujY14AgopV907IYgPAk/5x8c9267S4fQf89nyeCPTes="}`,
			ConsumerPrivValidatorKey:         `{"address":"DF090A4880B54CD57B2A79E64D9E969BD7514B09","pub_key":{"type":"tendermint/PubKeyEd25519","value":"ujY14AgopV907IYgPAk/5x8c9267S4fQf89nyeCPTes="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"TRJgf7lkTjs/sj43pyweEOanyV7H7fhnVivOi0A4yjW6NjXgCCilX3TshiA8CT/nHxz3brtLh9B/z2fJ4I9N6w=="}}`,
			ConsumerNodeKey:                  `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"F966RL9pi20aXRzEBe4D0xRQJtZt696Xxz44XUON52cFc83FMn1WXJbP6arvA2JPyn2LA3DLKCFHSgALrCGXGA=="}}`,
			UseConsumerKey:                   false,
		},
		ValidatorID("bob"): {
			Mnemonic:                 "glass trip produce surprise diamond spin excess gaze wash drum human solve dress minor artefact canoe hard ivory orange dinner hybrid moral potato jewel",
			DelAddress:               "cosmos1dkas8mu4kyhl5jrh4nzvm65qz588hy9qcz08la",
			DelAddressOnConsumer:     "consumer1dkas8mu4kyhl5jrh4nzvm65qz588hy9qahzgv6",
			ValoperAddress:           "cosmosvaloper1dkas8mu4kyhl5jrh4nzvm65qz588hy9qakmjnw",
			ValoperAddressOnConsumer: "consumervaloper1dkas8mu4kyhl5jrh4nzvm65qz588hy9qj0phzw",
			ValconsAddress:           "cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39",
			ValconsAddressOnConsumer: "consumervalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klhuqtq9",
			PrivValidatorKey:         `{"address":"99BD3A72EF12CD024E7584B3AC900AE3743C6ADF","pub_key":{"type":"tendermint/PubKeyEd25519","value":"mAN6RXYxSM4MNGSIriYiS7pHuwAcOHDQAy9/wnlSzOI="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"QePcwfWtOavNK7pBJrtoLMzarHKn6iBWfWPFeyV+IdmYA3pFdjFIzgw0ZIiuJiJLuke7ABw4cNADL3/CeVLM4g=="}}`,
			NodeKey:                  `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"TQ4vHcO/vKdzGtWpelkX53WdMQd4kTsWGFrdcatdXFvWyO215Rewn5IRP0FszPLWr2DqPzmuH8WvxYGk5aeOXw=="}}`,
			IpSuffix:                 "5",

			// consumer chain assigned key
			ConsumerMnemonic:                 "grunt list hour endless observe better spoil penalty lab duck only layer vague fantasy satoshi record demise topple space shaft solar practice donor sphere",
			ConsumerDelAddress:               "consumer1q90l6j6lzzgt460ehjj56azknlt5yrd44y2uke",
			ConsumerDelAddressOnProvider:     "cosmos1q90l6j6lzzgt460ehjj56azknlt5yrd4s38n97",
			ConsumerValoperAddress:           "consumervaloper1q90l6j6lzzgt460ehjj56azknlt5yrd46ufrcd",
			ConsumerValoperAddressOnProvider: "cosmosvaloper1q90l6j6lzzgt460ehjj56azknlt5yrd449nxfd",
			ConsumerValconsAddress:           "consumervalcons1uuec3cjxajv5te08p220usrjhkfhg9wyref26m",
			ConsumerValconsAddressOnProvider: "cosmosvalcons1uuec3cjxajv5te08p220usrjhkfhg9wyvqn0tm",
			ConsumerValPubKey:                `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"QlG+iYe6AyYpvY1z9RNJKCVlH14Q/qSz4EjGdGCru3o="}`,
			ConsumerPrivValidatorKey:         `{"address":"E73388E246EC9945E5E70A94FE4072BD937415C4","pub_key":{"type":"tendermint/PubKeyEd25519","value":"QlG+iYe6AyYpvY1z9RNJKCVlH14Q/qSz4EjGdGCru3o="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"OFR4w+FC6EMw5fAGTrHVexyPrjzQ7QfqgZOMgVf0izlCUb6Jh7oDJim9jXP1E0koJWUfXhD+pLPgSMZ0YKu7eg=="}}`,
			ConsumerNodeKey:                  `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"uhPCqnL2KE8m/8OFNLQ5bN3CJr6mds+xfBi0E4umT/s2uWiJhet+vbYx88DHSdof3gGFNTIzAIxSppscBKX96w=="}}`,
			UseConsumerKey:                   false,
		},
		ValidatorID("carol"): {
			Mnemonic:                 "sight similar better jar bitter laptop solve fashion father jelly scissors chest uniform play unhappy convince silly clump another conduct behave reunion marble animal",
			DelAddress:               "cosmos19hz4m226ztankqramvt4a7t0shejv4dc79gp9u",
			DelAddressOnConsumer:     "consumer19hz4m226ztankqramvt4a7t0shejv4dcms9wkm",
			ValoperAddress:           "cosmosvaloper19hz4m226ztankqramvt4a7t0shejv4dcm3u5f0",
			ValoperAddressOnConsumer: "consumervaloper19hz4m226ztankqramvt4a7t0shejv4dc5gx3c0",
			ValconsAddress:           "cosmosvalcons1ezyrq65s3gshhx5585w6mpusq3xsj3ayzf4uv6",
			ValconsAddressOnConsumer: "consumervalcons1ezyrq65s3gshhx5585w6mpusq3xsj3ayds0ea6",
			PrivValidatorKey:         `{"address":"C888306A908A217B9A943D1DAD8790044D0947A4","pub_key":{"type":"tendermint/PubKeyEd25519","value":"IHo4QEikWZfIKmM0X+N+BjKttz8HOzGs2npyjiba3Xk="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"z08bmSB91uFVpVmR3t2ewd/bDjZ/AzwQpe5rKjWiPG0gejhASKRZl8gqYzRf434GMq23Pwc7MazaenKOJtrdeQ=="}}`,
			NodeKey:                  `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"WLTcHEjbwB24Wp3z5oBSYTvtGQonz/7IQabOFw85BN0UkkyY5HDf38o8oHlFxVI26f+DFVeICuLbe9aXKGnUeg=="}}`,
			IpSuffix:                 "6",

			// consumer chain assigned key
			ConsumerMnemonic:                 "clip choose cake west range gun slam cry village receive juice galaxy lend ritual range provide ritual can since verify breeze vacant play dragon",
			ConsumerDelAddress:               "consumer1sx6j9g2rh324a342a5f0rnx7me34r9nwduz5te",
			ConsumerDelAddressOnProvider:     "cosmos1sx6j9g2rh324a342a5f0rnx7me34r9nwgf0mc7",
			ConsumerValoperAddress:           "consumervaloper1sx6j9g2rh324a342a5f0rnx7me34r9nwzypt9d",
			ConsumerValoperAddressOnProvider: "cosmosvaloper1sx6j9g2rh324a342a5f0rnx7me34r9nwdamw5d",
			ConsumerValconsAddress:           "consumervalcons1kswr5sq599365kcjmhgufevfps9njf43kv9tuk",
			ConsumerValconsAddressOnProvider: "cosmosvalcons1kswr5sq599365kcjmhgufevfps9njf43e4lwdk",
			ConsumerValPubKey:                `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"Ui5Gf1+mtWUdH8u3xlmzdKID+F3PK0sfXZ73GZ6q6is="}`,
			ConsumerPrivValidatorKey:         `{"address":"B41C3A40142963AA5B12DDD1C4E5890C0B3926B1","pub_key":{"type":"tendermint/PubKeyEd25519","value":"Ui5Gf1+mtWUdH8u3xlmzdKID+F3PK0sfXZ73GZ6q6is="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"3YaBAZLA+sl/E73lLfbFbG0u6DYm33ayr/0UpCt/vFBSLkZ/X6a1ZR0fy7fGWbN0ogP4Xc8rSx9dnvcZnqrqKw=="}}`,
			ConsumerNodeKey:                  `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"rxBzFedtD3pqgfJQblbxGusKOr47oBfr8ba0Iz14gobtDRZQZlSZ/UGP4pSHkVf+4vtkrkO1vRHBYJobuiP+7A=="}}`,
			UseConsumerKey:                   true,
		},
	}
}

func SlashThrottleTestConfig() TestConfig {
	tr := TestConfig{
		name: string(SlashThrottleTestCfg),
		containerConfig: ContainerConfig{
			ContainerName: "interchain-security-slash-container",
			InstanceName:  "interchain-security-slash-instance",
			CcvVersion:    "1",
			Now:           time.Now(),
		},
		validatorConfigs: getDefaultValidators(),
		chainConfigs: map[ChainID]ChainConfig{
			ChainID("provi"): {
				ChainId:        ChainID("provi"),
				AccountPrefix:  ProviderAccountPrefix,
				BinaryName:     "interchain-security-pd",
				IpPrefix:       "7.7.7",
				VotingWaitTime: 20,
				GenesisChanges: ".app_state.gov.params.voting_period = \"20s\" | " +
					".app_state.gov.params.expedited_voting_period = \"10s\" | " +
					// Custom slashing parameters for testing validator downtime functionality
					// See https://docs.cosmos.network/main/modules/slashing/04_begin_block.html#uptime-tracking
					".app_state.slashing.params.signed_blocks_window = \"10\" | " +
					".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
					".app_state.slashing.params.downtime_jail_duration = \"60s\" | " +
					".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\" | " +
					".app_state.provider.params.slash_meter_replenish_fraction = \"0.10\" | " +
					".app_state.provider.params.slash_meter_replenish_period = \"20s\" | " +
					".app_state.provider.params.blocks_per_epoch = 3",
			},
			ChainID("consu"): {
				ChainId:        ChainID("consu"),
				AccountPrefix:  ConsumerAccountPrefix,
				BinaryName:     "interchain-security-cd",
				IpPrefix:       "7.7.8",
				VotingWaitTime: 20,
				GenesisChanges: ".app_state.gov.params.voting_period = \"20s\" | " +
					".app_state.slashing.params.signed_blocks_window = \"20\" | " +
					".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
					".app_state.slashing.params.downtime_jail_duration = \"60s\" | " +
					".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\" | " +
					".app_state.ccvconsumer.params.retry_delay_period = \"30s\"",
			},
		},
		tendermintConfigOverride: `s/timeout_commit = "5s"/timeout_commit = "1s"/;` +
			`s/peer_gossip_sleep_duration = "100ms"/peer_gossip_sleep_duration = "50ms"/;`,
	}
	tr.Initialize()
	return tr
}

// CompatibilityTestConfig returns a test configuration for a given version of a consumer and provider
func CompatibilityTestConfig(providerVersion, consumerVersion string) TestConfig {
	// Base configuration is the default
	testCfg := DefaultTestConfig()

	// get version dependent validator configs
	testCfg.validatorConfigs = getValidatorConfigFromVersion(providerVersion, consumerVersion)

	var providerConfig, consumerConfig ChainConfig
	if !semver.IsValid(consumerVersion) {
		fmt.Println("Using default provider chain config")
		consumerConfig = testCfg.chainConfigs[ChainID("consu")]
	} else if semver.Compare(consumerVersion, "v3.0.0") < 0 {
		fmt.Println("Using consumer chain config for v2.0.0")
		consumerConfig = ChainConfig{
			ChainId:        ChainID("consu"),
			AccountPrefix:  "cosmos",
			BinaryName:     "interchain-security-cd",
			IpPrefix:       "7.7.8",
			VotingWaitTime: 20,
			GenesisChanges: ".app_state.gov.voting_params.voting_period = \"20s\" | " +
				".app_state.slashing.params.signed_blocks_window = \"15\" | " +
				".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
				".app_state.slashing.params.downtime_jail_duration = \"2s\" | " +
				".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\"",
		}
	} else if semver.Compare(consumerVersion, "v4.0.0") < 0 {
		fmt.Println("Using consumer chain config for v3.x.x")
		consumerConfig = ChainConfig{
			ChainId:        ChainID("consu"),
			AccountPrefix:  "cosmos",
			BinaryName:     "interchain-security-cd",
			IpPrefix:       "7.7.8",
			VotingWaitTime: 20,
			GenesisChanges: ".app_state.gov.params.voting_period = \"20s\" | " +
				".app_state.slashing.params.signed_blocks_window = \"15\" | " +
				".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
				".app_state.slashing.params.downtime_jail_duration = \"60s\" | " +
				".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\"",
		}
	} else {
		fmt.Println("Using default consumer chain config")
		consumerConfig = testCfg.chainConfigs[ChainID("consu")]
	}

	// Get the provider chain config for a specific version
	if !semver.IsValid(providerVersion) {
		fmt.Println("Using default provider chain config")
		providerConfig = testCfg.chainConfigs[ChainID("provi")]
	} else if semver.Compare(providerVersion, "v3.0.0") < 0 {
		fmt.Println("Using provider chain config for v2.x.x")
		providerConfig = ChainConfig{
			ChainId:        ChainID("provi"),
			AccountPrefix:  "cosmos",
			BinaryName:     "interchain-security-pd",
			IpPrefix:       "7.7.7",
			VotingWaitTime: 20,
			GenesisChanges: ".app_state.gov.voting_params.voting_period = \"20s\" | " +
				// Custom slashing parameters for testing validator downtime functionality
				// See https://docs.cosmos.network/main/modules/slashing/04_begin_block.html#uptime-tracking
				".app_state.slashing.params.signed_blocks_window = \"10\" | " +
				".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
				".app_state.slashing.params.downtime_jail_duration = \"2s\" | " +
				".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\" | " +
				".app_state.provider.params.slash_meter_replenish_fraction = \"1.0\" | " + // This disables slash packet throttling
				".app_state.provider.params.slash_meter_replenish_period = \"3s\"",
		}
	} else if semver.Compare(providerVersion, "v4.0.0") <= 0 {
		fmt.Println("Using provider chain config for v3.x.x")
		providerConfig = ChainConfig{
			ChainId:        ChainID("provi"),
			AccountPrefix:  "cosmos",
			BinaryName:     "interchain-security-pd",
			IpPrefix:       "7.7.7",
			VotingWaitTime: 20,
			GenesisChanges: ".app_state.gov.params.voting_period = \"20s\" | " +
				// Custom slashing parameters for testing validator downtime functionality
				// See https://docs.cosmos.network/main/modules/slashing/04_begin_block.html#uptime-tracking
				".app_state.slashing.params.signed_blocks_window = \"10\" | " +
				".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
				".app_state.slashing.params.downtime_jail_duration = \"60s\" | " +
				".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\" | " +
				".app_state.provider.params.slash_meter_replenish_fraction = \"1.0\" | " + // This disables slash packet throttling
				".app_state.provider.params.slash_meter_replenish_period = \"3s\"",
		}
	} else {
		fmt.Println("Using default provider chain config")
		providerConfig = testCfg.chainConfigs[ChainID("provi")]
	}

	testCfg.chainConfigs[ChainID("consu")] = consumerConfig
	testCfg.chainConfigs[ChainID("provi")] = providerConfig
	testCfg.name = string(CompatibilityTestCfg)
	testCfg.containerConfig.InstanceName = fmt.Sprintf("%s_%s-%s",
		testCfg.containerConfig.InstanceName,
		consumerVersion, providerVersion)
	return testCfg
}

func DefaultTestConfig() TestConfig {
	tr := TestConfig{
		name: string(DefaultTestCfg),
		containerConfig: ContainerConfig{
			ContainerName: "interchain-security-container",
			InstanceName:  "interchain-security-instance",
			CcvVersion:    "1",
			Now:           time.Now(),
		},
		validatorConfigs: getDefaultValidators(),
		chainConfigs: map[ChainID]ChainConfig{
			ChainID("provi"): {
				ChainId:        ChainID("provi"),
				AccountPrefix:  ProviderAccountPrefix,
				BinaryName:     "interchain-security-pd",
				IpPrefix:       "7.7.7",
				VotingWaitTime: 20,
				GenesisChanges: ".app_state.gov.params.voting_period = \"20s\" | " +
					".app_state.gov.params.expedited_voting_period = \"10s\" | " +
					// Custom slashing parameters for testing validator downtime functionality
					// See https://docs.cosmos.network/main/modules/slashing/04_begin_block.html#uptime-tracking
					".app_state.slashing.params.signed_blocks_window = \"10\" | " +
					".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
					".app_state.slashing.params.downtime_jail_duration = \"60s\" | " +
					".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\" | " +
					".app_state.provider.params.slash_meter_replenish_fraction = \"1.0\" | " + // This disables slash packet throttling
					".app_state.provider.params.slash_meter_replenish_period = \"3s\" | " +
					".app_state.provider.params.blocks_per_epoch = 3",
			},
			ChainID("consu"): {
				ChainId:        ChainID("consu"),
				AccountPrefix:  ConsumerAccountPrefix,
				BinaryName:     "interchain-security-cd",
				IpPrefix:       "7.7.8",
				VotingWaitTime: 20,
				GenesisChanges: ".app_state.gov.params.voting_period = \"20s\" | " +
					".app_state.slashing.params.signed_blocks_window = \"20\" | " +
					".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
					".app_state.slashing.params.downtime_jail_duration = \"60s\" | " +
					".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\"",
			},
		},
		tendermintConfigOverride: `s/timeout_commit = "5s"/timeout_commit = "1s"/;` +
			`s/peer_gossip_sleep_duration = "100ms"/peer_gossip_sleep_duration = "50ms"/;`,
	}
	tr.Initialize()
	return tr
}

func DemocracyTestConfig(allowReward bool) TestConfig {
	consumerGenChanges := ".app_state.ccvconsumer.params.blocks_per_distribution_transmission = \"20\" | " +
		".app_state.gov.params.voting_period = \"10s\" | " +
		".app_state.slashing.params.signed_blocks_window = \"10\" | " +
		".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
		".app_state.slashing.params.downtime_jail_duration = \"60s\" | " +
		".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\" | " +
		".app_state.transfer.params.send_enabled = false"
	name := string(DemocracyTestCfg)
	if allowReward {
		// This allows the consumer chain to send rewards in the stake denom
		consumerGenChanges += " | .app_state.ccvconsumer.params.reward_denoms = [\"stake\"]"
		name = string(DemocracyRewardTestCfg)
	}

	tr := TestConfig{
		name: name,
		containerConfig: ContainerConfig{
			ContainerName: "interchain-security-democ-container",
			InstanceName:  "interchain-security-democ-instance",
			CcvVersion:    "1",
			Now:           time.Now(),
		},
		validatorConfigs: getDefaultValidators(),
		chainConfigs: map[ChainID]ChainConfig{
			ChainID("provi"): {
				ChainId:        ChainID("provi"),
				AccountPrefix:  ProviderAccountPrefix,
				BinaryName:     "interchain-security-pd",
				IpPrefix:       "7.7.7",
				VotingWaitTime: 20,
				GenesisChanges: ".app_state.gov.params.voting_period = \"20s\" | " +
					".app_state.gov.params.expedited_voting_period = \"10s\" | " +
					// Custom slashing parameters for testing validator downtime functionality
					// See https://docs.cosmos.network/main/modules/slashing/04_begin_block.html#uptime-tracking
					".app_state.slashing.params.signed_blocks_window = \"10\" | " +
					".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
					".app_state.slashing.params.downtime_jail_duration = \"60s\" | " +
					".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\" | " +
					".app_state.provider.params.slash_meter_replenish_fraction = \"1.0\" | " + // This disables slash packet throttling
					".app_state.provider.params.blocks_per_epoch = 3",
			},
			ChainID("democ"): {
				ChainId:        ChainID("democ"),
				AccountPrefix:  ConsumerAccountPrefix,
				BinaryName:     "interchain-security-cdd",
				IpPrefix:       "7.7.9",
				VotingWaitTime: 20,
				GenesisChanges: consumerGenChanges,
			},
		},
		tendermintConfigOverride: `s/timeout_commit = "5s"/timeout_commit = "1s"/;` +
			`s/peer_gossip_sleep_duration = "100ms"/peer_gossip_sleep_duration = "50ms"/;`,
	}
	tr.Initialize()
	return tr
}

func MultiConsumerTestConfig() TestConfig {
	tr := TestConfig{
		name: string(MulticonsumerTestCfg),
		containerConfig: ContainerConfig{
			ContainerName: "interchain-security-multic-container",
			InstanceName:  "interchain-security-multic-instance",
			CcvVersion:    "1",
			Now:           time.Now(),
		},
		validatorConfigs: getDefaultValidators(),
		chainConfigs: map[ChainID]ChainConfig{
			ChainID("provi"): {
				ChainId:        ChainID("provi"),
				AccountPrefix:  ProviderAccountPrefix,
				BinaryName:     "interchain-security-pd",
				IpPrefix:       "7.7.7",
				VotingWaitTime: 20,
				GenesisChanges: ".app_state.gov.params.voting_period = \"30s\" | " +
					".app_state.gov.params.expedited_voting_period = \"10s\" | " +
					// Custom slashing parameters for testing validator downtime functionality
					// See https://docs.cosmos.network/main/modules/slashing/04_begin_block.html#uptime-tracking
					".app_state.slashing.params.signed_blocks_window = \"10\" | " +
					".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
					".app_state.slashing.params.downtime_jail_duration = \"60s\" | " +
					".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\" | " +
					".app_state.provider.params.slash_meter_replenish_fraction = \"1.0\" | " + // This disables slash packet throttling
					".app_state.provider.params.blocks_per_epoch = 3",
			},
			ChainID("consu"): {
				ChainId:        ChainID("consu"),
				AccountPrefix:  ConsumerAccountPrefix,
				BinaryName:     "interchain-security-cd",
				IpPrefix:       "7.7.8",
				VotingWaitTime: 20,
				GenesisChanges: ".app_state.gov.params.voting_period = \"20s\" | " +
					".app_state.slashing.params.signed_blocks_window = \"20\" | " +
					".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
					".app_state.slashing.params.downtime_jail_duration = \"60s\" | " +
					".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\"",
			},
			ChainID("densu"): {
				ChainId:        ChainID("densu"),
				AccountPrefix:  ConsumerAccountPrefix,
				BinaryName:     "interchain-security-cd",
				IpPrefix:       "7.7.9",
				VotingWaitTime: 20,
				GenesisChanges: ".app_state.gov.params.voting_period = \"20s\" | " +
					".app_state.slashing.params.signed_blocks_window = \"20\" | " +
					".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
					".app_state.slashing.params.downtime_jail_duration = \"60s\" | " +
					".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\"",
			},
		},
		tendermintConfigOverride: `s/timeout_commit = "5s"/timeout_commit = "3s"/;` +
			`s/peer_gossip_sleep_duration = "100ms"/peer_gossip_sleep_duration = "100ms"/;`,
	}
	tr.Initialize()
	return tr
}

func ChangeoverTestConfig() TestConfig {
	tr := TestConfig{
		name: string(ChangeoverTestCfg),
		containerConfig: ContainerConfig{
			ContainerName: "interchain-security-changeover-container",
			InstanceName:  "interchain-security-changeover-instance",
			CcvVersion:    "1",
			Now:           time.Now(),
		},
		validatorConfigs: getDefaultValidators(),
		chainConfigs: map[ChainID]ChainConfig{
			ChainID("provi"): {
				ChainId:        ChainID("provi"),
				AccountPrefix:  ProviderAccountPrefix,
				BinaryName:     "interchain-security-pd",
				IpPrefix:       "7.7.7",
				VotingWaitTime: 20,
				GenesisChanges: ".app_state.gov.params.voting_period = \"20s\" | " +
					".app_state.gov.params.expedited_voting_period = \"10s\" | " +
					// Custom slashing parameters for testing validator downtime functionality
					// See https://docs.cosmos.network/main/modules/slashing/04_begin_block.html#uptime-tracking
					".app_state.slashing.params.signed_blocks_window = \"10\" | " +
					".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
					".app_state.slashing.params.downtime_jail_duration = \"60s\" | " +
					".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\" | " +
					".app_state.provider.params.slash_meter_replenish_fraction = \"1.0\" | " + // This disables slash packet throttling
					".app_state.provider.params.slash_meter_replenish_period = \"3s\" | " +
					".app_state.provider.params.blocks_per_epoch = 3",
			},
			ChainID("sover"): {
				ChainId:        ChainID("sover"),
				AccountPrefix:  ConsumerAccountPrefix,
				BinaryName:     "interchain-security-sd",
				UpgradeBinary:  "interchain-security-cdd",
				IpPrefix:       "7.7.8",
				VotingWaitTime: 20,
				GenesisChanges: ".app_state.gov.params.voting_period = \"20s\" | " +
					".app_state.slashing.params.signed_blocks_window = \"20\" | " +
					".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
					".app_state.slashing.params.downtime_jail_duration = \"60s\" | " +
					".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\" | " +
					".app_state.staking.params.unbonding_time = \"1728000s\"", // making the genesis unbonding time equal to unbonding time in the consumer addition proposal
			},
		},
		tendermintConfigOverride: `s/timeout_commit = "5s"/timeout_commit = "1s"/;` +
			`s/peer_gossip_sleep_duration = "100ms"/peer_gossip_sleep_duration = "50ms"/;`,
	}
	tr.Initialize()
	return tr
}

func ConsumerMisbehaviourTestConfig() TestConfig {
	tc := TestConfig{
		name: string(ConsumerMisbehaviourTestCfg),
		containerConfig: ContainerConfig{
			ContainerName: "interchain-security-container",
			InstanceName:  "interchain-security-instance",
			CcvVersion:    "1",
			Now:           time.Now(),
		},
		validatorConfigs: map[ValidatorID]ValidatorConfig{
			ValidatorID("alice"): {
				Mnemonic:                 "pave immune ethics wrap gain ceiling always holiday employ earth tumble real ice engage false unable carbon equal fresh sick tattoo nature pupil nuclear",
				DelAddress:               "cosmos19pe9pg5dv9k5fzgzmsrgnw9rl9asf7ddwhu7lm",
				DelAddressOnConsumer:     "consumer19pe9pg5dv9k5fzgzmsrgnw9rl9asf7ddtz33vu",
				ValoperAddress:           "cosmosvaloper19pe9pg5dv9k5fzgzmsrgnw9rl9asf7ddtrgtng",
				ValoperAddressOnConsumer: "consumervaloper19pe9pg5dv9k5fzgzmsrgnw9rl9asf7ddy6jwzg",
				ValconsAddress:           "cosmosvalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xw4mceq",
				ValconsAddressOnConsumer: "consumervalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xpvpagq",
				PrivValidatorKey:         `{"address":"06C0F3E47CC5C748269088DC2F36411D3AAA27C6","pub_key":{"type":"tendermint/PubKeyEd25519","value":"RrclQz9bIhkIy/gfL485g3PYMeiIku4qeo495787X10="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"uX+ZpDMg89a6gtqs/+MQpCTSqlkZ0nJQJOhLlCJvwvdGtyVDP1siGQjL+B8vjzmDc9gx6IiS7ip6jj3nvztfXQ=="}}`,
				NodeKey:                  `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"fjw4/DAhyRPnwKgXns5SV7QfswRSXMWJpHS7TyULDmJ8ofUc5poQP8dgr8bZRbCV5RV8cPqDq3FPdqwpmUbmdA=="}}`,
				IpSuffix:                 "4",

				// consumer chain assigned key
				ConsumerMnemonic:                 "exile install vapor thing little toss immune notable lounge december final easy strike title end program interest quote cloth forget forward job october twenty",
				ConsumerDelAddress:               "consumer1eeeggku6dzk3mv7wph3zq035rhtd890sh9rl32",
				ConsumerDelAddressOnProvider:     "cosmos1eeeggku6dzk3mv7wph3zq035rhtd890sjswszd",
				ConsumerValoperAddress:           "consumervaloper1eeeggku6dzk3mv7wph3zq035rhtd890scaqql7",
				ConsumerValoperAddressOnProvider: "cosmosvaloper1eeeggku6dzk3mv7wph3zq035rhtd890shy69w7",
				ConsumerValconsAddress:           "consumervalcons1muys5jyqk4xd27e208nym85kn0t4zjcfk9q5ce",
				ConsumerValconsAddressOnProvider: "cosmosvalcons1muys5jyqk4xd27e208nym85kn0t4zjcfeu63fe",
				ConsumerValPubKey:                `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"ujY14AgopV907IYgPAk/5x8c9267S4fQf89nyeCPTes="}`,
				ConsumerPrivValidatorKey:         `{"address":"DF090A4880B54CD57B2A79E64D9E969BD7514B09","pub_key":{"type":"tendermint/PubKeyEd25519","value":"ujY14AgopV907IYgPAk/5x8c9267S4fQf89nyeCPTes="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"TRJgf7lkTjs/sj43pyweEOanyV7H7fhnVivOi0A4yjW6NjXgCCilX3TshiA8CT/nHxz3brtLh9B/z2fJ4I9N6w=="}}`,
				ConsumerNodeKey:                  `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"F966RL9pi20aXRzEBe4D0xRQJtZt696Xxz44XUON52cFc83FMn1WXJbP6arvA2JPyn2LA3DLKCFHSgALrCGXGA=="}}`,
				UseConsumerKey:                   true,
			},
			ValidatorID("bob"): {
				Mnemonic:                 "glass trip produce surprise diamond spin excess gaze wash drum human solve dress minor artefact canoe hard ivory orange dinner hybrid moral potato jewel",
				DelAddress:               "cosmos1dkas8mu4kyhl5jrh4nzvm65qz588hy9qcz08la",
				DelAddressOnConsumer:     "consumer1dkas8mu4kyhl5jrh4nzvm65qz588hy9qahzgv6",
				ValoperAddress:           "cosmosvaloper1dkas8mu4kyhl5jrh4nzvm65qz588hy9qakmjnw",
				ValoperAddressOnConsumer: "consumervaloper1dkas8mu4kyhl5jrh4nzvm65qz588hy9qj0phzw",
				ValconsAddress:           "cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39",
				ValconsAddressOnConsumer: "consumervalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klhuqtq9",
				PrivValidatorKey:         `{"address":"99BD3A72EF12CD024E7584B3AC900AE3743C6ADF","pub_key":{"type":"tendermint/PubKeyEd25519","value":"mAN6RXYxSM4MNGSIriYiS7pHuwAcOHDQAy9/wnlSzOI="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"QePcwfWtOavNK7pBJrtoLMzarHKn6iBWfWPFeyV+IdmYA3pFdjFIzgw0ZIiuJiJLuke7ABw4cNADL3/CeVLM4g=="}}`,
				NodeKey:                  `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"TQ4vHcO/vKdzGtWpelkX53WdMQd4kTsWGFrdcatdXFvWyO215Rewn5IRP0FszPLWr2DqPzmuH8WvxYGk5aeOXw=="}}`,
				IpSuffix:                 "5",

				// consumer chain assigned key
				ConsumerMnemonic:                 "grunt list hour endless observe better spoil penalty lab duck only layer vague fantasy satoshi record demise topple space shaft solar practice donor sphere",
				ConsumerDelAddress:               "consumer1q90l6j6lzzgt460ehjj56azknlt5yrd44y2uke",
				ConsumerDelAddressOnProvider:     "cosmos1q90l6j6lzzgt460ehjj56azknlt5yrd4s38n97",
				ConsumerValoperAddress:           "consumervaloper1q90l6j6lzzgt460ehjj56azknlt5yrd46ufrcd",
				ConsumerValoperAddressOnProvider: "cosmosvaloper1q90l6j6lzzgt460ehjj56azknlt5yrd449nxfd",
				ConsumerValconsAddress:           "consumervalcons1uuec3cjxajv5te08p220usrjhkfhg9wyref26m",
				ConsumerValconsAddressOnProvider: "cosmosvalcons1uuec3cjxajv5te08p220usrjhkfhg9wyvqn0tm",
				ConsumerValPubKey:                `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"QlG+iYe6AyYpvY1z9RNJKCVlH14Q/qSz4EjGdGCru3o="}`,
				ConsumerPrivValidatorKey:         `{"address":"E73388E246EC9945E5E70A94FE4072BD937415C4","pub_key":{"type":"tendermint/PubKeyEd25519","value":"QlG+iYe6AyYpvY1z9RNJKCVlH14Q/qSz4EjGdGCru3o="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"OFR4w+FC6EMw5fAGTrHVexyPrjzQ7QfqgZOMgVf0izlCUb6Jh7oDJim9jXP1E0koJWUfXhD+pLPgSMZ0YKu7eg=="}}`,
				ConsumerNodeKey:                  `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"uhPCqnL2KE8m/8OFNLQ5bN3CJr6mds+xfBi0E4umT/s2uWiJhet+vbYx88DHSdof3gGFNTIzAIxSppscBKX96w=="}}`,
				UseConsumerKey:                   false,
			},
		},
		chainConfigs: map[ChainID]ChainConfig{
			ChainID("provi"): {
				ChainId:        ChainID("provi"),
				AccountPrefix:  ProviderAccountPrefix,
				BinaryName:     "interchain-security-pd",
				IpPrefix:       "7.7.7",
				VotingWaitTime: 20,
				GenesisChanges: ".app_state.gov.params.voting_period = \"20s\" | " +
					// Custom slashing parameters for testing validator downtime functionality
					// See https://docs.cosmos.network/main/modules/slashing/04_begin_block.html#uptime-tracking
					".app_state.slashing.params.signed_blocks_window = \"10\" | " +
					".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
					".app_state.slashing.params.downtime_jail_duration = \"60s\" | " +
					".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\" | " +
					".app_state.provider.params.slash_meter_replenish_fraction = \"1.0\" | " + // This disables slash packet throttling
					".app_state.provider.params.slash_meter_replenish_period = \"3s\" | " +
					".app_state.provider.params.blocks_per_epoch = 3",
			},
			ChainID("consu"): {
				ChainId:        ChainID("consu"),
				AccountPrefix:  ConsumerAccountPrefix,
				BinaryName:     "interchain-security-cd",
				IpPrefix:       "7.7.8",
				VotingWaitTime: 20,
				GenesisChanges: ".app_state.gov.params.voting_period = \"20s\" | " +
					".app_state.slashing.params.signed_blocks_window = \"20\" | " +
					".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
					".app_state.slashing.params.downtime_jail_duration = \"60s\" | " +
					".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\"",
			},
		},
		tendermintConfigOverride: `s/timeout_commit = "5s"/timeout_commit = "1s"/;` +
			`s/peer_gossip_sleep_duration = "100ms"/peer_gossip_sleep_duration = "50ms"/;` +
			// Required to start consumer chain by running a single big validator
			`s/block_sync = true/block_sync = false/;`,
	}
	tc.Initialize()
	return tc
}

func (s *TestConfig) SetCometMockConfig(useCometmock bool) {
	s.useCometmock = useCometmock
}

func (s *TestConfig) SetRelayerConfig(useRly bool) {
	s.useGorelayer = useRly
}

// validateStringLiterals enforces that configs follow the constraints
// necessary to execute the tests
//
// Note: Network interfaces (name of virtual ethernet interfaces for ip link)
// within the container will be named as "$CHAIN_ID-$VAL_ID-out" etc.
// where this name is constrained to 15 bytes or less. Therefore each string literal
// used as a validatorID or chainID needs to be 5 char or less.
func (s *TestConfig) validateStringLiterals() {
	for valID, valConfig := range s.validatorConfigs {
		if len(valID) > 5 {
			panic("validator id string literal must be 5 char or less")
		}

		ipSuffix, err := strconv.Atoi(valConfig.IpSuffix)
		if err != nil {
			panic(fmt.Sprintf("ip suffix must be an int: %v\n", err))
		}

		if ipSuffix == 253 {
			panic("ip suffix 253 is reserved for query node")
		}

		if ipSuffix == 252 {
			panic("ip suffix 252 is reserved for double signing node")
		}

		if ipSuffix < 1 || 251 < ipSuffix {
			panic("ip suffix out of range, need to change config")
		}
	}

	for chainID, chainConfig := range s.chainConfigs {
		if len(chainID) > 5 {
			panic("chain id string literal must be 5 char or less")
		}

		if chainID != chainConfig.ChainId {
			panic("chain config is mapped to a chain id that is different than what's stored in the config")
		}
	}
}

// getValidatorConfigFromVersion returns validator configuration based on provider/consumer version used.
func getValidatorConfigFromVersion(providerVersion, consumerVersion string) map[ValidatorID]ValidatorConfig {
	var validatorCfg map[ValidatorID]ValidatorConfig
	switch providerVersion {
	case "v2.0.0", "v2.1.0", "v2.2.0", "v2.3.0", "v2.4.0",
		"v3.0.0", "v3.1.0", "v3.2.0", "v3.3.0", "v3.3.2-lsm":
		fmt.Println("Using old validator configs: ", providerVersion)

		validatorCfg = map[ValidatorID]ValidatorConfig{
			ValidatorID("alice"): {
				Mnemonic:         "pave immune ethics wrap gain ceiling always holiday employ earth tumble real ice engage false unable carbon equal fresh sick tattoo nature pupil nuclear",
				DelAddress:       "cosmos19pe9pg5dv9k5fzgzmsrgnw9rl9asf7ddwhu7lm",
				ValoperAddress:   "cosmosvaloper19pe9pg5dv9k5fzgzmsrgnw9rl9asf7ddtrgtng",
				ValconsAddress:   "cosmosvalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xw4mceq",
				PrivValidatorKey: `{"address":"06C0F3E47CC5C748269088DC2F36411D3AAA27C6","pub_key":{"type":"tendermint/PubKeyEd25519","value":"RrclQz9bIhkIy/gfL485g3PYMeiIku4qeo495787X10="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"uX+ZpDMg89a6gtqs/+MQpCTSqlkZ0nJQJOhLlCJvwvdGtyVDP1siGQjL+B8vjzmDc9gx6IiS7ip6jj3nvztfXQ=="}}`,
				NodeKey:          `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"fjw4/DAhyRPnwKgXns5SV7QfswRSXMWJpHS7TyULDmJ8ofUc5poQP8dgr8bZRbCV5RV8cPqDq3FPdqwpmUbmdA=="}}`,
				IpSuffix:         "4",

				// consumer chain assigned key
				ConsumerMnemonic:         "exile install vapor thing little toss immune notable lounge december final easy strike title end program interest quote cloth forget forward job october twenty",
				ConsumerDelAddress:       "cosmos1eeeggku6dzk3mv7wph3zq035rhtd890sjswszd",
				ConsumerValoperAddress:   "cosmosvaloper1eeeggku6dzk3mv7wph3zq035rhtd890shy69w7",
				ConsumerValconsAddress:   "cosmosvalcons1muys5jyqk4xd27e208nym85kn0t4zjcfeu63fe",
				ConsumerValPubKey:        `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"ujY14AgopV907IYgPAk/5x8c9267S4fQf89nyeCPTes="}`,
				ConsumerPrivValidatorKey: `{"address":"DF090A4880B54CD57B2A79E64D9E969BD7514B09","pub_key":{"type":"tendermint/PubKeyEd25519","value":"ujY14AgopV907IYgPAk/5x8c9267S4fQf89nyeCPTes="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"TRJgf7lkTjs/sj43pyweEOanyV7H7fhnVivOi0A4yjW6NjXgCCilX3TshiA8CT/nHxz3brtLh9B/z2fJ4I9N6w=="}}`,
				ConsumerNodeKey:          `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"F966RL9pi20aXRzEBe4D0xRQJtZt696Xxz44XUON52cFc83FMn1WXJbP6arvA2JPyn2LA3DLKCFHSgALrCGXGA=="}}`,
				UseConsumerKey:           false,

				ConsumerValconsAddressOnProvider: "cosmosvalcons1muys5jyqk4xd27e208nym85kn0t4zjcfeu63fe",
			},
			ValidatorID("bob"): {
				Mnemonic:         "glass trip produce surprise diamond spin excess gaze wash drum human solve dress minor artefact canoe hard ivory orange dinner hybrid moral potato jewel",
				DelAddress:       "cosmos1dkas8mu4kyhl5jrh4nzvm65qz588hy9qcz08la",
				ValoperAddress:   "cosmosvaloper1dkas8mu4kyhl5jrh4nzvm65qz588hy9qakmjnw",
				ValconsAddress:   "cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39",
				PrivValidatorKey: `{"address":"99BD3A72EF12CD024E7584B3AC900AE3743C6ADF","pub_key":{"type":"tendermint/PubKeyEd25519","value":"mAN6RXYxSM4MNGSIriYiS7pHuwAcOHDQAy9/wnlSzOI="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"QePcwfWtOavNK7pBJrtoLMzarHKn6iBWfWPFeyV+IdmYA3pFdjFIzgw0ZIiuJiJLuke7ABw4cNADL3/CeVLM4g=="}}`,
				NodeKey:          `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"TQ4vHcO/vKdzGtWpelkX53WdMQd4kTsWGFrdcatdXFvWyO215Rewn5IRP0FszPLWr2DqPzmuH8WvxYGk5aeOXw=="}}`,
				IpSuffix:         "5",

				// consumer chain assigned key
				ConsumerMnemonic:         "grunt list hour endless observe better spoil penalty lab duck only layer vague fantasy satoshi record demise topple space shaft solar practice donor sphere",
				ConsumerDelAddress:       "cosmos1q90l6j6lzzgt460ehjj56azknlt5yrd4s38n97",
				ConsumerValoperAddress:   "cosmosvaloper1q90l6j6lzzgt460ehjj56azknlt5yrd449nxfd",
				ConsumerValconsAddress:   "cosmosvalcons1uuec3cjxajv5te08p220usrjhkfhg9wyvqn0tm",
				ConsumerValPubKey:        `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"QlG+iYe6AyYpvY1z9RNJKCVlH14Q/qSz4EjGdGCru3o="}`,
				ConsumerPrivValidatorKey: `{"address":"E73388E246EC9945E5E70A94FE4072BD937415C4","pub_key":{"type":"tendermint/PubKeyEd25519","value":"QlG+iYe6AyYpvY1z9RNJKCVlH14Q/qSz4EjGdGCru3o="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"OFR4w+FC6EMw5fAGTrHVexyPrjzQ7QfqgZOMgVf0izlCUb6Jh7oDJim9jXP1E0koJWUfXhD+pLPgSMZ0YKu7eg=="}}`,
				ConsumerNodeKey:          `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"uhPCqnL2KE8m/8OFNLQ5bN3CJr6mds+xfBi0E4umT/s2uWiJhet+vbYx88DHSdof3gGFNTIzAIxSppscBKX96w=="}}`,
				UseConsumerKey:           false,

				ConsumerValconsAddressOnProvider: "cosmosvalcons1uuec3cjxajv5te08p220usrjhkfhg9wyvqn0tm",
			},
			ValidatorID("carol"): {
				Mnemonic:         "sight similar better jar bitter laptop solve fashion father jelly scissors chest uniform play unhappy convince silly clump another conduct behave reunion marble animal",
				DelAddress:       "cosmos19hz4m226ztankqramvt4a7t0shejv4dc79gp9u",
				ValoperAddress:   "cosmosvaloper19hz4m226ztankqramvt4a7t0shejv4dcm3u5f0",
				ValconsAddress:   "cosmosvalcons1ezyrq65s3gshhx5585w6mpusq3xsj3ayzf4uv6",
				PrivValidatorKey: `{"address":"C888306A908A217B9A943D1DAD8790044D0947A4","pub_key":{"type":"tendermint/PubKeyEd25519","value":"IHo4QEikWZfIKmM0X+N+BjKttz8HOzGs2npyjiba3Xk="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"z08bmSB91uFVpVmR3t2ewd/bDjZ/AzwQpe5rKjWiPG0gejhASKRZl8gqYzRf434GMq23Pwc7MazaenKOJtrdeQ=="}}`,
				NodeKey:          `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"WLTcHEjbwB24Wp3z5oBSYTvtGQonz/7IQabOFw85BN0UkkyY5HDf38o8oHlFxVI26f+DFVeICuLbe9aXKGnUeg=="}}`,
				IpSuffix:         "6",

				// consumer chain assigned key
				ConsumerMnemonic:         "clip choose cake west range gun slam cry village receive juice galaxy lend ritual range provide ritual can since verify breeze vacant play dragon",
				ConsumerDelAddress:       "cosmos1sx6j9g2rh324a342a5f0rnx7me34r9nwgf0mc7",
				ConsumerValoperAddress:   "cosmosvaloper1sx6j9g2rh324a342a5f0rnx7me34r9nwdamw5d",
				ConsumerValconsAddress:   "cosmosvalcons1kswr5sq599365kcjmhgufevfps9njf43e4lwdk",
				ConsumerValPubKey:        `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"Ui5Gf1+mtWUdH8u3xlmzdKID+F3PK0sfXZ73GZ6q6is="}`,
				ConsumerPrivValidatorKey: `{"address":"B41C3A40142963AA5B12DDD1C4E5890C0B3926B1","pub_key":{"type":"tendermint/PubKeyEd25519","value":"Ui5Gf1+mtWUdH8u3xlmzdKID+F3PK0sfXZ73GZ6q6is="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"3YaBAZLA+sl/E73lLfbFbG0u6DYm33ayr/0UpCt/vFBSLkZ/X6a1ZR0fy7fGWbN0ogP4Xc8rSx9dnvcZnqrqKw=="}}`,
				ConsumerNodeKey:          `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"rxBzFedtD3pqgfJQblbxGusKOr47oBfr8ba0Iz14gobtDRZQZlSZ/UGP4pSHkVf+4vtkrkO1vRHBYJobuiP+7A=="}}`,
				UseConsumerKey:           true,

				ConsumerValconsAddressOnProvider: "cosmosvalcons1kswr5sq599365kcjmhgufevfps9njf43e4lwdk",
			},
		}
	case "v4.0.0":
		fmt.Println("Using current default validator configs: ", providerVersion)
		validatorCfg = map[ValidatorID]ValidatorConfig{
			ValidatorID("alice"): {
				Mnemonic:                 "pave immune ethics wrap gain ceiling always holiday employ earth tumble real ice engage false unable carbon equal fresh sick tattoo nature pupil nuclear",
				DelAddress:               "cosmos19pe9pg5dv9k5fzgzmsrgnw9rl9asf7ddwhu7lm",
				DelAddressOnConsumer:     "consumer19pe9pg5dv9k5fzgzmsrgnw9rl9asf7ddtz33vu",
				ValoperAddress:           "cosmosvaloper19pe9pg5dv9k5fzgzmsrgnw9rl9asf7ddtrgtng",
				ValoperAddressOnConsumer: "consumervaloper19pe9pg5dv9k5fzgzmsrgnw9rl9asf7ddy6jwzg",
				ValconsAddress:           "cosmosvalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xw4mceq",
				ValconsAddressOnConsumer: "consumervalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xpvpagq",
				PrivValidatorKey:         `{"address":"06C0F3E47CC5C748269088DC2F36411D3AAA27C6","pub_key":{"type":"tendermint/PubKeyEd25519","value":"RrclQz9bIhkIy/gfL485g3PYMeiIku4qeo495787X10="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"uX+ZpDMg89a6gtqs/+MQpCTSqlkZ0nJQJOhLlCJvwvdGtyVDP1siGQjL+B8vjzmDc9gx6IiS7ip6jj3nvztfXQ=="}}`,
				NodeKey:                  `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"fjw4/DAhyRPnwKgXns5SV7QfswRSXMWJpHS7TyULDmJ8ofUc5poQP8dgr8bZRbCV5RV8cPqDq3FPdqwpmUbmdA=="}}`,
				IpSuffix:                 "4",

				// consumer chain assigned key
				ConsumerMnemonic:                 "exile install vapor thing little toss immune notable lounge december final easy strike title end program interest quote cloth forget forward job october twenty",
				ConsumerDelAddress:               "consumer1eeeggku6dzk3mv7wph3zq035rhtd890sh9rl32",
				ConsumerDelAddressOnProvider:     "cosmos1eeeggku6dzk3mv7wph3zq035rhtd890sjswszd",
				ConsumerValoperAddress:           "consumervaloper1eeeggku6dzk3mv7wph3zq035rhtd890scaqql7",
				ConsumerValoperAddressOnProvider: "cosmosvaloper1eeeggku6dzk3mv7wph3zq035rhtd890shy69w7",
				ConsumerValconsAddress:           "consumervalcons1muys5jyqk4xd27e208nym85kn0t4zjcfk9q5ce",
				ConsumerValconsAddressOnProvider: "cosmosvalcons1muys5jyqk4xd27e208nym85kn0t4zjcfeu63fe",
				ConsumerValPubKey:                `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"ujY14AgopV907IYgPAk/5x8c9267S4fQf89nyeCPTes="}`,
				ConsumerPrivValidatorKey:         `{"address":"DF090A4880B54CD57B2A79E64D9E969BD7514B09","pub_key":{"type":"tendermint/PubKeyEd25519","value":"ujY14AgopV907IYgPAk/5x8c9267S4fQf89nyeCPTes="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"TRJgf7lkTjs/sj43pyweEOanyV7H7fhnVivOi0A4yjW6NjXgCCilX3TshiA8CT/nHxz3brtLh9B/z2fJ4I9N6w=="}}`,
				ConsumerNodeKey:                  `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"F966RL9pi20aXRzEBe4D0xRQJtZt696Xxz44XUON52cFc83FMn1WXJbP6arvA2JPyn2LA3DLKCFHSgALrCGXGA=="}}`,
				UseConsumerKey:                   false,
			},
			ValidatorID("bob"): {
				Mnemonic:                 "glass trip produce surprise diamond spin excess gaze wash drum human solve dress minor artefact canoe hard ivory orange dinner hybrid moral potato jewel",
				DelAddress:               "cosmos1dkas8mu4kyhl5jrh4nzvm65qz588hy9qcz08la",
				DelAddressOnConsumer:     "consumer1dkas8mu4kyhl5jrh4nzvm65qz588hy9qahzgv6",
				ValoperAddress:           "cosmosvaloper1dkas8mu4kyhl5jrh4nzvm65qz588hy9qakmjnw",
				ValoperAddressOnConsumer: "consumervaloper1dkas8mu4kyhl5jrh4nzvm65qz588hy9qj0phzw",
				ValconsAddress:           "cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39",
				ValconsAddressOnConsumer: "consumervalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klhuqtq9",
				PrivValidatorKey:         `{"address":"99BD3A72EF12CD024E7584B3AC900AE3743C6ADF","pub_key":{"type":"tendermint/PubKeyEd25519","value":"mAN6RXYxSM4MNGSIriYiS7pHuwAcOHDQAy9/wnlSzOI="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"QePcwfWtOavNK7pBJrtoLMzarHKn6iBWfWPFeyV+IdmYA3pFdjFIzgw0ZIiuJiJLuke7ABw4cNADL3/CeVLM4g=="}}`,
				NodeKey:                  `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"TQ4vHcO/vKdzGtWpelkX53WdMQd4kTsWGFrdcatdXFvWyO215Rewn5IRP0FszPLWr2DqPzmuH8WvxYGk5aeOXw=="}}`,
				IpSuffix:                 "5",

				// consumer chain assigned key
				ConsumerMnemonic:                 "grunt list hour endless observe better spoil penalty lab duck only layer vague fantasy satoshi record demise topple space shaft solar practice donor sphere",
				ConsumerDelAddress:               "consumer1q90l6j6lzzgt460ehjj56azknlt5yrd44y2uke",
				ConsumerDelAddressOnProvider:     "cosmos1q90l6j6lzzgt460ehjj56azknlt5yrd4s38n97",
				ConsumerValoperAddress:           "consumervaloper1q90l6j6lzzgt460ehjj56azknlt5yrd46ufrcd",
				ConsumerValoperAddressOnProvider: "cosmosvaloper1q90l6j6lzzgt460ehjj56azknlt5yrd449nxfd",
				ConsumerValconsAddress:           "consumervalcons1uuec3cjxajv5te08p220usrjhkfhg9wyref26m",
				ConsumerValconsAddressOnProvider: "cosmosvalcons1uuec3cjxajv5te08p220usrjhkfhg9wyvqn0tm",
				ConsumerValPubKey:                `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"QlG+iYe6AyYpvY1z9RNJKCVlH14Q/qSz4EjGdGCru3o="}`,
				ConsumerPrivValidatorKey:         `{"address":"E73388E246EC9945E5E70A94FE4072BD937415C4","pub_key":{"type":"tendermint/PubKeyEd25519","value":"QlG+iYe6AyYpvY1z9RNJKCVlH14Q/qSz4EjGdGCru3o="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"OFR4w+FC6EMw5fAGTrHVexyPrjzQ7QfqgZOMgVf0izlCUb6Jh7oDJim9jXP1E0koJWUfXhD+pLPgSMZ0YKu7eg=="}}`,
				ConsumerNodeKey:                  `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"uhPCqnL2KE8m/8OFNLQ5bN3CJr6mds+xfBi0E4umT/s2uWiJhet+vbYx88DHSdof3gGFNTIzAIxSppscBKX96w=="}}`,
				UseConsumerKey:                   false,
			},
			ValidatorID("carol"): {
				Mnemonic:                 "sight similar better jar bitter laptop solve fashion father jelly scissors chest uniform play unhappy convince silly clump another conduct behave reunion marble animal",
				DelAddress:               "cosmos19hz4m226ztankqramvt4a7t0shejv4dc79gp9u",
				DelAddressOnConsumer:     "consumer19hz4m226ztankqramvt4a7t0shejv4dcms9wkm",
				ValoperAddress:           "cosmosvaloper19hz4m226ztankqramvt4a7t0shejv4dcm3u5f0",
				ValoperAddressOnConsumer: "consumervaloper19hz4m226ztankqramvt4a7t0shejv4dc5gx3c0",
				ValconsAddress:           "cosmosvalcons1ezyrq65s3gshhx5585w6mpusq3xsj3ayzf4uv6",
				ValconsAddressOnConsumer: "consumervalcons1ezyrq65s3gshhx5585w6mpusq3xsj3ayds0ea6",
				PrivValidatorKey:         `{"address":"C888306A908A217B9A943D1DAD8790044D0947A4","pub_key":{"type":"tendermint/PubKeyEd25519","value":"IHo4QEikWZfIKmM0X+N+BjKttz8HOzGs2npyjiba3Xk="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"z08bmSB91uFVpVmR3t2ewd/bDjZ/AzwQpe5rKjWiPG0gejhASKRZl8gqYzRf434GMq23Pwc7MazaenKOJtrdeQ=="}}`,
				NodeKey:                  `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"WLTcHEjbwB24Wp3z5oBSYTvtGQonz/7IQabOFw85BN0UkkyY5HDf38o8oHlFxVI26f+DFVeICuLbe9aXKGnUeg=="}}`,
				IpSuffix:                 "6",

				// consumer chain assigned key
				ConsumerMnemonic:                 "clip choose cake west range gun slam cry village receive juice galaxy lend ritual range provide ritual can since verify breeze vacant play dragon",
				ConsumerDelAddress:               "consumer1sx6j9g2rh324a342a5f0rnx7me34r9nwduz5te",
				ConsumerDelAddressOnProvider:     "cosmos1sx6j9g2rh324a342a5f0rnx7me34r9nwgf0mc7",
				ConsumerValoperAddress:           "consumervaloper1sx6j9g2rh324a342a5f0rnx7me34r9nwzypt9d",
				ConsumerValoperAddressOnProvider: "cosmosvaloper1sx6j9g2rh324a342a5f0rnx7me34r9nwdamw5d",
				ConsumerValconsAddress:           "consumervalcons1kswr5sq599365kcjmhgufevfps9njf43kv9tuk",
				ConsumerValconsAddressOnProvider: "cosmosvalcons1kswr5sq599365kcjmhgufevfps9njf43e4lwdk",
				ConsumerValPubKey:                `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"Ui5Gf1+mtWUdH8u3xlmzdKID+F3PK0sfXZ73GZ6q6is="}`,
				ConsumerPrivValidatorKey:         `{"address":"B41C3A40142963AA5B12DDD1C4E5890C0B3926B1","pub_key":{"type":"tendermint/PubKeyEd25519","value":"Ui5Gf1+mtWUdH8u3xlmzdKID+F3PK0sfXZ73GZ6q6is="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"3YaBAZLA+sl/E73lLfbFbG0u6DYm33ayr/0UpCt/vFBSLkZ/X6a1ZR0fy7fGWbN0ogP4Xc8rSx9dnvcZnqrqKw=="}}`,
				ConsumerNodeKey:                  `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"rxBzFedtD3pqgfJQblbxGusKOr47oBfr8ba0Iz14gobtDRZQZlSZ/UGP4pSHkVf+4vtkrkO1vRHBYJobuiP+7A=="}}`,
				UseConsumerKey:                   true,
			},
		}

	default:
		fmt.Println("Using current default validator configs for provider: ", providerVersion)
		validatorCfg = getDefaultValidators()
	}

	// Augment validator configs with consumer related configurations
	// this is needed due to address prefix changes introduced in ICS v4.0.0
	switch consumerVersion {
	case "v2.0.0", "v2.1.0", "v2.2.0", "v2.3.0", "v2.4.0",
		"v3.0.0", "v3.1.0", "v3.2.0", "v3.3.0":
		fmt.Println("Using old validator configs for consumer: ", consumerVersion)

		// consumer chain assigned key
		cfg := validatorCfg[ValidatorID("alice")]
		cfg.ConsumerMnemonic = "exile install vapor thing little toss immune notable lounge december final easy strike title end program interest quote cloth forget forward job october twenty"
		cfg.ConsumerDelAddress = "cosmos1eeeggku6dzk3mv7wph3zq035rhtd890sjswszd"
		cfg.ConsumerValoperAddress = "cosmosvaloper1eeeggku6dzk3mv7wph3zq035rhtd890shy69w7"
		cfg.ConsumerValconsAddress = "cosmosvalcons1muys5jyqk4xd27e208nym85kn0t4zjcfeu63fe"
		cfg.ConsumerValPubKey = `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"ujY14AgopV907IYgPAk/5x8c9267S4fQf89nyeCPTes="}`
		cfg.ConsumerPrivValidatorKey = `{"address":"DF090A4880B54CD57B2A79E64D9E969BD7514B09","pub_key":{"type":"tendermint/PubKeyEd25519","value":"ujY14AgopV907IYgPAk/5x8c9267S4fQf89nyeCPTes="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"TRJgf7lkTjs/sj43pyweEOanyV7H7fhnVivOi0A4yjW6NjXgCCilX3TshiA8CT/nHxz3brtLh9B/z2fJ4I9N6w=="}}`
		cfg.ConsumerNodeKey = `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"F966RL9pi20aXRzEBe4D0xRQJtZt696Xxz44XUON52cFc83FMn1WXJbP6arvA2JPyn2LA3DLKCFHSgALrCGXGA=="}}`
		cfg.UseConsumerKey = false

		cfg.DelAddressOnConsumer = "cosmos19pe9pg5dv9k5fzgzmsrgnw9rl9asf7ddwhu7lm"
		cfg.ValoperAddressOnConsumer = "cosmosvaloper19pe9pg5dv9k5fzgzmsrgnw9rl9asf7ddtrgtng"
		cfg.ValconsAddressOnConsumer = "cosmosvalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xw4mceq"
		validatorCfg[ValidatorID("alice")] = cfg

		cfg = validatorCfg[ValidatorID("bob")]
		cfg.ConsumerMnemonic = "grunt list hour endless observe better spoil penalty lab duck only layer vague fantasy satoshi record demise topple space shaft solar practice donor sphere"
		cfg.ConsumerDelAddress = "cosmos1q90l6j6lzzgt460ehjj56azknlt5yrd4s38n97"
		cfg.ConsumerValoperAddress = "cosmosvaloper1q90l6j6lzzgt460ehjj56azknlt5yrd449nxfd"
		cfg.ConsumerValconsAddress = "cosmosvalcons1uuec3cjxajv5te08p220usrjhkfhg9wyvqn0tm"
		cfg.ConsumerValPubKey = `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"QlG+iYe6AyYpvY1z9RNJKCVlH14Q/qSz4EjGdGCru3o="}`
		cfg.ConsumerPrivValidatorKey = `{"address":"E73388E246EC9945E5E70A94FE4072BD937415C4","pub_key":{"type":"tendermint/PubKeyEd25519","value":"QlG+iYe6AyYpvY1z9RNJKCVlH14Q/qSz4EjGdGCru3o="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"OFR4w+FC6EMw5fAGTrHVexyPrjzQ7QfqgZOMgVf0izlCUb6Jh7oDJim9jXP1E0koJWUfXhD+pLPgSMZ0YKu7eg=="}}`
		cfg.ConsumerNodeKey = `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"uhPCqnL2KE8m/8OFNLQ5bN3CJr6mds+xfBi0E4umT/s2uWiJhet+vbYx88DHSdof3gGFNTIzAIxSppscBKX96w=="}}`
		cfg.UseConsumerKey = false

		cfg.DelAddressOnConsumer = "cosmos1dkas8mu4kyhl5jrh4nzvm65qz588hy9qcz08la"
		cfg.ValoperAddressOnConsumer = "cosmosvaloper1dkas8mu4kyhl5jrh4nzvm65qz588hy9qakmjnw"
		cfg.ValconsAddressOnConsumer = "cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39"

		validatorCfg[ValidatorID("bob")] = cfg

		cfg = validatorCfg[ValidatorID("carol")]
		cfg.ConsumerMnemonic = "clip choose cake west range gun slam cry village receive juice galaxy lend ritual range provide ritual can since verify breeze vacant play dragon"
		cfg.ConsumerDelAddress = "cosmos1sx6j9g2rh324a342a5f0rnx7me34r9nwgf0mc7"
		cfg.ConsumerValoperAddress = "cosmosvaloper1sx6j9g2rh324a342a5f0rnx7me34r9nwdamw5d"
		cfg.ConsumerValconsAddress = "cosmosvalcons1kswr5sq599365kcjmhgufevfps9njf43e4lwdk"
		cfg.ConsumerValPubKey = `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"Ui5Gf1+mtWUdH8u3xlmzdKID+F3PK0sfXZ73GZ6q6is="}`
		cfg.ConsumerPrivValidatorKey = `{"address":"B41C3A40142963AA5B12DDD1C4E5890C0B3926B1","pub_key":{"type":"tendermint/PubKeyEd25519","value":"Ui5Gf1+mtWUdH8u3xlmzdKID+F3PK0sfXZ73GZ6q6is="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"3YaBAZLA+sl/E73lLfbFbG0u6DYm33ayr/0UpCt/vFBSLkZ/X6a1ZR0fy7fGWbN0ogP4Xc8rSx9dnvcZnqrqKw=="}}`
		cfg.ConsumerNodeKey = `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"rxBzFedtD3pqgfJQblbxGusKOr47oBfr8ba0Iz14gobtDRZQZlSZ/UGP4pSHkVf+4vtkrkO1vRHBYJobuiP+7A=="}}`
		cfg.UseConsumerKey = true
		validatorCfg[ValidatorID("carol")] = cfg

	case "v4.0.0":
		fmt.Println("Using v4.0.0 validator configs: ", consumerVersion)
		cfg := validatorCfg[ValidatorID("alice")]
		cfg.ConsumerMnemonic = "exile install vapor thing little toss immune notable lounge december final easy strike title end program interest quote cloth forget forward job october twenty"
		cfg.ConsumerDelAddress = "consumer1eeeggku6dzk3mv7wph3zq035rhtd890sh9rl32"
		cfg.ConsumerDelAddressOnProvider = "cosmos1eeeggku6dzk3mv7wph3zq035rhtd890sjswszd"
		cfg.ConsumerValoperAddress = "consumervaloper1eeeggku6dzk3mv7wph3zq035rhtd890scaqql7"
		cfg.ConsumerValoperAddressOnProvider = "cosmosvaloper1eeeggku6dzk3mv7wph3zq035rhtd890shy69w7"
		cfg.ConsumerValconsAddress = "consumervalcons1muys5jyqk4xd27e208nym85kn0t4zjcfk9q5ce"
		cfg.ConsumerValconsAddressOnProvider = "cosmosvalcons1muys5jyqk4xd27e208nym85kn0t4zjcfeu63fe"
		cfg.ConsumerValPubKey = `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"ujY14AgopV907IYgPAk/5x8c9267S4fQf89nyeCPTes="}`
		cfg.ConsumerPrivValidatorKey = `{"address":"DF090A4880B54CD57B2A79E64D9E969BD7514B09","pub_key":{"type":"tendermint/PubKeyEd25519","value":"ujY14AgopV907IYgPAk/5x8c9267S4fQf89nyeCPTes="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"TRJgf7lkTjs/sj43pyweEOanyV7H7fhnVivOi0A4yjW6NjXgCCilX3TshiA8CT/nHxz3brtLh9B/z2fJ4I9N6w=="}}`
		cfg.ConsumerNodeKey = `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"F966RL9pi20aXRzEBe4D0xRQJtZt696Xxz44XUON52cFc83FMn1WXJbP6arvA2JPyn2LA3DLKCFHSgALrCGXGA=="}}`
		cfg.UseConsumerKey = false

		cfg.DelAddressOnConsumer = "consumer19pe9pg5dv9k5fzgzmsrgnw9rl9asf7ddtz33vu"
		cfg.ValoperAddressOnConsumer = "consumervaloper19pe9pg5dv9k5fzgzmsrgnw9rl9asf7ddy6jwzg"
		cfg.ValconsAddressOnConsumer = "consumervalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xpvpagq"
		validatorCfg[ValidatorID("alice")] = cfg

		cfg = validatorCfg[ValidatorID("bob")]
		cfg.ConsumerMnemonic = "grunt list hour endless observe better spoil penalty lab duck only layer vague fantasy satoshi record demise topple space shaft solar practicedonor sphere"
		cfg.ConsumerDelAddress = "consumer1q90l6j6lzzgt460ehjj56azknlt5yrd44y2uke"
		cfg.ConsumerDelAddressOnProvider = "cosmos1q90l6j6lzzgt460ehjj56azknlt5yrd4s38n97"
		cfg.ConsumerValoperAddress = "consumervaloper1q90l6j6lzzgt460ehjj56azknlt5yrd46ufrcd"
		cfg.ConsumerValoperAddressOnProvider = "cosmosvaloper1q90l6j6lzzgt460ehjj56azknlt5yrd449nxfd"
		cfg.ConsumerValconsAddress = "consumervalcons1uuec3cjxajv5te08p220usrjhkfhg9wyref26m"
		cfg.ConsumerValconsAddressOnProvider = "cosmosvalcons1uuec3cjxajv5te08p220usrjhkfhg9wyvqn0tm"
		cfg.ConsumerValPubKey = `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"QlG+iYe6AyYpvY1z9RNJKCVlH14QqSz4EjGdGCru3o="}`
		cfg.ConsumerPrivValidatorKey = `{"address":"E73388E246EC9945E5E70A94FE4072BD937415C4","pub_key":{"type":"tendermint/PubKeyEd25519","value":"QlG+iYe6AyYpvY1z9RNJKCVlH14Q/qSz4EjGdGCru3o="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"OFR4w+FC6EMw5fAGTrHVexyPrjzQ7QfqgZOMgVf0izlCUb6Jh7oDJim9jXP1E0koJWUfXhDpLPgSMZ0YKu7eg=="}}`
		cfg.ConsumerNodeKey = `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"uhPCqnL2KE8m/8OFNLQ5bN3CJr6mds+xfBi0E4umT/s2uWiJhetvbYx88DHSdof3gGFNTIzAIxSppscBKX96w=="}}`
		cfg.UseConsumerKey = false

		cfg.DelAddressOnConsumer = "consumer1dkas8mu4kyhl5jrh4nzvm65qz588hy9qahzgv6"
		cfg.ValoperAddressOnConsumer = "consumervaloper1dkas8mu4kyhl5jrh4nzvm65qz588hy9qj0phzw"
		cfg.ValconsAddressOnConsumer = "consumervalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klhuqtq9"

		validatorCfg[ValidatorID("bob")] = cfg

		cfg = validatorCfg[ValidatorID("carol")]
		cfg.ConsumerMnemonic = "clip choose cake west range gun slam cry village receive juice galaxy lend ritual range provide ritual can since verify breeze vacant play dragon"
		cfg.ConsumerDelAddress = "consumer1sx6j9g2rh324a342a5f0rnx7me34r9nwduz5te"
		cfg.ConsumerDelAddressOnProvider = "cosmos1sx6j9g2rh324a342a5f0rnx7me34r9nwgf0mc7"
		cfg.ConsumerValoperAddress = "consumervaloper1sx6j9g2rh324a342a5f0rnx7me34r9nwzypt9d"
		cfg.ConsumerValoperAddressOnProvider = "cosmosvaloper1sx6j9g2rh324a342a5f0rnx7me34r9nwdamw5d"
		cfg.ConsumerValconsAddress = "consumervalcons1kswr5sq599365kcjmhgufevfps9njf43kv9tuk"
		cfg.ConsumerValconsAddressOnProvider = "cosmosvalcons1kswr5sq599365kcjmhgufevfps9njf43e4lwdk"
		cfg.ConsumerValPubKey = `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"Ui5Gf1+mtWUdH8u3xlmzdKID+F3PK0sfXZ73GZ6q6is="}`
		cfg.ConsumerPrivValidatorKey = `{"address":"B41C3A40142963AA5B12DDD1C4E5890C0B3926B1","pub_key":{"type":"tendermint/PubKeyEd25519","value":"Ui5Gf1+mtWUdH8u3xlmzdKID+F3PK0sfXZ73GZ6q6is="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"3YaBAZLA+sl/E73lLfbFbG0u6DYm33ayr/0UpCt/vFBSLkZ/X6a1ZR0fy7fGWbN0ogP4Xc8rSx9dnvcZnqrqKw=="}}`
		cfg.ConsumerNodeKey = `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"rxBzFedtD3pqgfJQblbxGusKOr47oBfr8ba0Iz14gobtDRZQZlSZ/UGP4pSHkVf+4vtkrkO1vRHBYJobuiP+7A=="}}`
		cfg.UseConsumerKey = true

		cfg.DelAddressOnConsumer = "consumer19hz4m226ztankqramvt4a7t0shejv4dcms9wkm"
		cfg.ValoperAddressOnConsumer = "consumervaloper19hz4m226ztankqramvt4a7t0shejv4dc5gx3c0"
		cfg.ValconsAddressOnConsumer = "consumervalcons1ezyrq65s3gshhx5585w6mpusq3xsj3ayds0ea6"

		validatorCfg[ValidatorID("carol")] = cfg

	default:
		fmt.Println("Using current default validator configs for consumer: ", consumerVersion)
		defaultCfg := getDefaultValidators()
		for _, valId := range []ValidatorID{ValidatorID("alice"), ValidatorID("bob"), ValidatorID("carol")} {
			cfg := validatorCfg[valId]
			cfg.ConsumerMnemonic = defaultCfg[valId].ConsumerMnemonic
			cfg.ConsumerDelAddress = defaultCfg[valId].ConsumerDelAddress
			cfg.ConsumerDelAddressOnProvider = defaultCfg[valId].ConsumerDelAddressOnProvider
			cfg.ConsumerValoperAddress = defaultCfg[valId].ConsumerValoperAddress
			cfg.ConsumerValoperAddressOnProvider = defaultCfg[valId].ConsumerValconsAddressOnProvider
			cfg.ConsumerValconsAddress = defaultCfg[valId].ConsumerValconsAddress
			cfg.ConsumerValconsAddressOnProvider = defaultCfg[valId].ConsumerValconsAddressOnProvider
			cfg.ConsumerValPubKey = defaultCfg[valId].ConsumerValPubKey
			cfg.ConsumerPrivValidatorKey = defaultCfg[valId].ConsumerPrivValidatorKey
			cfg.ConsumerNodeKey = defaultCfg[valId].ConsumerNodeKey
			cfg.UseConsumerKey = defaultCfg[valId].UseConsumerKey

			cfg.DelAddressOnConsumer = defaultCfg[valId].DelAddressOnConsumer
			cfg.ValoperAddressOnConsumer = defaultCfg[valId].ValoperAddressOnConsumer
			cfg.ValconsAddressOnConsumer = defaultCfg[valId].ValconsAddressOnConsumer

			validatorCfg[valId] = cfg
		}
	}
	return validatorCfg
}

// GetHermesConfig returns a configuration string for a given hermes version
//
// Currently templates for Hermes v1.6.0 and v1.4 are supported.
// If provided version is before v1.6.0 then a configuration based on template for v1.4.x is returned
// otherwise the returned configuration is based on template v1.4.
func GetHermesConfig(hermesVersion, queryNodeIP string, chainCfg ChainConfig, isConsumer bool) string {
	ChainId := chainCfg.ChainId
	keyName := "query"
	rpcAddr := "http://" + queryNodeIP + ":26658"
	grpcAddr := "tcp://" + queryNodeIP + ":9091"
	wsAddr := "ws://" + queryNodeIP + ":26658/websocket"

	hermesConfig := ""
	if semver.Compare(hermesVersion, "1.6.0") < 0 {
		fmt.Println("Using hermes config template", "1.4")
		template := hermesTemplates["v1.4"]
		hermesConfig = fmt.Sprintf(template,
			chainCfg.AccountPrefix,
			grpcAddr,
			ChainId,
			keyName,
			rpcAddr,
			wsAddr)
	} else {
		// added event_source (v1.6) + ccv_consumer_chain (v1.5)
		fmt.Println("Using hermes config template", "1.6")
		template := hermesTemplates["v1.6"]
		hermesConfig = fmt.Sprintf(template,
			chainCfg.AccountPrefix,
			grpcAddr,
			ChainId,
			keyName,
			rpcAddr,
			wsAddr,
			isConsumer)
	}
	return hermesConfig
}
