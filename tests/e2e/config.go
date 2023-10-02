package main

import (
	"fmt"
	"strconv"
	"time"
)

// TODO: Determine if user defined type (wrapping a primitive string) is desired in long run
type (
	ChainID     string
	ValidatorID string
)

// Attributes that are unique to a validator. Allows us to map (part of)
// the set of strings defined above to a set of viable validators
type ValidatorConfig struct {
	Mnemonic         string
	DelAddress       string
	ValoperAddress   string
	ValconsAddress   string
	PrivValidatorKey string
	NodeKey          string
	// Must be an integer greater than 0 and less than 253
	IpSuffix string

	// consumer chain key assignment data
	// keys are used on a new node
	ConsumerMnemonic         string
	ConsumerDelAddress       string
	ConsumerValoperAddress   string
	ConsumerValconsAddress   string
	ConsumerValPubKey        string
	ConsumerPrivValidatorKey string
	ConsumerNodeKey          string
	UseConsumerKey           bool // if true the validator node will start with consumer key
}

// Attributes that are unique to a chain. Allows us to map (part of)
// the set of strings defined above to a set of viable chains
type ChainConfig struct {
	ChainId ChainID
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

// TODO: Split out TestConfig and system wide config like localsdkpath
type TestConfig struct {
	// These are the non altered values during a typical test run, where multiple test runs can exist
	// to validate different action sequences and corresponding state checks.
	containerConfig  ContainerConfig
	validatorConfigs map[ValidatorID]ValidatorConfig
	chainConfigs     map[ChainID]ChainConfig
	// override config.toml parameters
	// usually used to override timeout_commit
	// having shorter timeout_commit reduces the test runtime because blocks are produced faster
	// lengthening the timeout_commit increases the test runtime because blocks are produced slower but the test is more reliable
	tendermintConfigOverride string
	localSdkPath             string
	useGaia                  bool
	useCometmock             bool // if false, nodes run CometBFT
	useGorelayer             bool // if false, Hermes is used as the relayer
	gaiaTag                  string
	// chains which are running, i.e. producing blocks, at the moment
	runningChains map[ChainID]bool
	// Used with CometMock. The time by which chains have been advanced. Used to keep chains in sync: when a new chain is started, advance its time by this value to keep chains in sync.
	timeOffset time.Duration

	name string
}

// Initialize initializes the TestConfig instance by setting the runningChains field to an empty map.
func (tr *TestConfig) Initialize() {
	tr.runningChains = make(map[ChainID]bool)
}

func getDefaultValidators() map[ValidatorID]ValidatorConfig {
	return map[ValidatorID]ValidatorConfig{
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
		},
	}
}

func SlashThrottleTestConfig() TestConfig {
	tr := TestConfig{
		name: "slash-throttling",
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
					".app_state.provider.params.slash_meter_replenish_fraction = \"0.10\" | " +
					".app_state.provider.params.slash_meter_replenish_period = \"20s\"",
			},
			ChainID("consu"): {
				ChainId:        ChainID("consu"),
				BinaryName:     "interchain-security-cd",
				IpPrefix:       "7.7.8",
				VotingWaitTime: 20,
				GenesisChanges: ".app_state.gov.params.voting_period = \"20s\" | " +
					".app_state.slashing.params.signed_blocks_window = \"15\" | " +
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

func DefaultTestConfig() TestConfig {
	tr := TestConfig{
		name: "default",
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
			},
			ChainID("consu"): {
				ChainId:        ChainID("consu"),
				BinaryName:     "interchain-security-cd",
				IpPrefix:       "7.7.8",
				VotingWaitTime: 20,
				GenesisChanges: ".app_state.gov.params.voting_period = \"20s\" | " +
					".app_state.slashing.params.signed_blocks_window = \"15\" | " +
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
		".app_state.gov.voting_params.voting_period = \"10s\" | " +
		".app_state.slashing.params.signed_blocks_window = \"10\" | " +
		".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
		".app_state.slashing.params.downtime_jail_duration = \"60s\" | " +
		".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\""

	if allowReward {
		// This allows the consumer chain to send rewards in the stake denom
		consumerGenChanges += " | .app_state.ccvconsumer.params.reward_denoms = [\"stake\"]"
	}

	tr := TestConfig{
		name: "democracy",
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
					".app_state.provider.params.slash_meter_replenish_fraction = \"1.0\"", // This disables slash packet throttling
			},
			ChainID("democ"): {
				ChainId:        ChainID("democ"),
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
		name: "multi-consumer",
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
				BinaryName:     "interchain-security-pd",
				IpPrefix:       "7.7.7",
				VotingWaitTime: 20,
				GenesisChanges: ".app_state.gov.params.voting_period = \"30s\" | " +
					// Custom slashing parameters for testing validator downtime functionality
					// See https://docs.cosmos.network/main/modules/slashing/04_begin_block.html#uptime-tracking
					".app_state.slashing.params.signed_blocks_window = \"10\" | " +
					".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
					".app_state.slashing.params.downtime_jail_duration = \"60s\" | " +
					".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\" | " +
					".app_state.provider.params.slash_meter_replenish_fraction = \"1.0\"", // This disables slash packet throttling
			},
			ChainID("consu"): {
				ChainId:        ChainID("consu"),
				BinaryName:     "interchain-security-cd",
				IpPrefix:       "7.7.8",
				VotingWaitTime: 20,
				GenesisChanges: ".app_state.gov.params.voting_period = \"20s\" | " +
					".app_state.slashing.params.signed_blocks_window = \"10\" | " +
					".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
					".app_state.slashing.params.downtime_jail_duration = \"60s\" | " +
					".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\"",
			},
			ChainID("densu"): {
				ChainId:        ChainID("densu"),
				BinaryName:     "interchain-security-cd",
				IpPrefix:       "7.7.9",
				VotingWaitTime: 20,
				GenesisChanges: ".app_state.gov.params.voting_period = \"20s\" | " +
					".app_state.slashing.params.signed_blocks_window = \"10\" | " +
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
		name: "changeover",
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
			},
			ChainID("sover"): {
				ChainId:        ChainID("sover"),
				BinaryName:     "interchain-security-sd",
				UpgradeBinary:  "interchain-security-cdd",
				IpPrefix:       "7.7.8",
				VotingWaitTime: 20,
				GenesisChanges: ".app_state.gov.params.voting_period = \"20s\" | " +
					".app_state.slashing.params.signed_blocks_window = \"15\" | " +
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

func (s *TestConfig) SetDockerConfig(localSdkPath string, useGaia bool, gaiaTag string) {
	if localSdkPath != "" {
		fmt.Println("USING LOCAL SDK", localSdkPath)
	}
	if useGaia {
		fmt.Println("USING GAIA INSTEAD OF ICS provider app", gaiaTag)
	}

	s.useGaia = useGaia
	s.gaiaTag = gaiaTag
	s.localSdkPath = localSdkPath
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
