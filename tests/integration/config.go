package main

import (
	"fmt"
	"strconv"
	"time"
)

// TODO: Determine if user defined type (wrapping a primitive string) is desired in long run
type chainID string
type validatorID string

// Attributes that are unique to a validator. Allows us to map (part of)
// the set of strings defined above to a set of viable validators
type ValidatorConfig struct {
	mnemonic         string
	delAddress       string
	valoperAddress   string
	valconsAddress   string
	privValidatorKey string
	nodeKey          string
	// Must be an integer greater than 0 and less than 253
	ipSuffix string

	// consumer chain key assignment data
	// keys are used on a new node
	consumerMnemonic         string
	consumerDelAddress       string
	consumerValoperAddress   string
	consumerValconsAddress   string
	consumerValPubKey        string
	consumerPrivValidatorKey string
	consumerNodeKey          string
	useConsumerKey           bool // if true the validator node will start with consumer key
}

// Attributes that are unique to a chain. Allows us to map (part of)
// the set of strings defined above to a set of viable chains
type ChainConfig struct {
	chainId chainID
	// Must be unique per chain
	ipPrefix       string
	votingWaitTime uint
	// Any transformations to apply to the genesis file of all chains instantiated with this chain config, as a jq string.
	// Example: ".app_state.gov.voting_params.voting_period = \"5s\" | .app_state.slashing.params.signed_blocks_window = \"2\" | .app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\""
	genesisChanges string
	binaryName     string
}

type ContainerConfig struct {
	containerName string
	instanceName  string
	ccvVersion    string
	now           time.Time
}

// TODO: Split out TestRun and system wide config like localsdkpath
type TestRun struct {
	// These are the non altered values during a typical test run, where multiple test runs can exist
	// to validate different action sequences and corresponding state checks.
	containerConfig  ContainerConfig
	validatorConfigs map[validatorID]ValidatorConfig
	chainConfigs     map[chainID]ChainConfig
	localSdkPath     string

	name string
}

func getDefaultValidators() map[validatorID]ValidatorConfig {
	return map[validatorID]ValidatorConfig{
		validatorID("alice"): {
			mnemonic:         "pave immune ethics wrap gain ceiling always holiday employ earth tumble real ice engage false unable carbon equal fresh sick tattoo nature pupil nuclear",
			delAddress:       "cosmos19pe9pg5dv9k5fzgzmsrgnw9rl9asf7ddwhu7lm",
			valoperAddress:   "cosmosvaloper19pe9pg5dv9k5fzgzmsrgnw9rl9asf7ddtrgtng",
			valconsAddress:   "cosmosvalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xw4mceq",
			privValidatorKey: `{"address":"06C0F3E47CC5C748269088DC2F36411D3AAA27C6","pub_key":{"type":"tendermint/PubKeyEd25519","value":"RrclQz9bIhkIy/gfL485g3PYMeiIku4qeo495787X10="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"uX+ZpDMg89a6gtqs/+MQpCTSqlkZ0nJQJOhLlCJvwvdGtyVDP1siGQjL+B8vjzmDc9gx6IiS7ip6jj3nvztfXQ=="}}`,
			nodeKey:          `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"fjw4/DAhyRPnwKgXns5SV7QfswRSXMWJpHS7TyULDmJ8ofUc5poQP8dgr8bZRbCV5RV8cPqDq3FPdqwpmUbmdA=="}}`,
			ipSuffix:         "4",

			// consumer chain assigned key
			consumerMnemonic:         "exile install vapor thing little toss immune notable lounge december final easy strike title end program interest quote cloth forget forward job october twenty",
			consumerDelAddress:       "cosmos1eeeggku6dzk3mv7wph3zq035rhtd890sjswszd",
			consumerValoperAddress:   "cosmosvaloper1eeeggku6dzk3mv7wph3zq035rhtd890shy69w7",
			consumerValconsAddress:   "cosmosvalcons1muys5jyqk4xd27e208nym85kn0t4zjcfeu63fe",
			consumerValPubKey:        `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"ujY14AgopV907IYgPAk/5x8c9267S4fQf89nyeCPTes="}`,
			consumerPrivValidatorKey: `{"address":"DF090A4880B54CD57B2A79E64D9E969BD7514B09","pub_key":{"type":"tendermint/PubKeyEd25519","value":"ujY14AgopV907IYgPAk/5x8c9267S4fQf89nyeCPTes="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"TRJgf7lkTjs/sj43pyweEOanyV7H7fhnVivOi0A4yjW6NjXgCCilX3TshiA8CT/nHxz3brtLh9B/z2fJ4I9N6w=="}}`,
			consumerNodeKey:          `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"F966RL9pi20aXRzEBe4D0xRQJtZt696Xxz44XUON52cFc83FMn1WXJbP6arvA2JPyn2LA3DLKCFHSgALrCGXGA=="}}`,
			useConsumerKey:           false,
		},
		validatorID("bob"): {
			mnemonic:         "glass trip produce surprise diamond spin excess gaze wash drum human solve dress minor artefact canoe hard ivory orange dinner hybrid moral potato jewel",
			delAddress:       "cosmos1dkas8mu4kyhl5jrh4nzvm65qz588hy9qcz08la",
			valoperAddress:   "cosmosvaloper1dkas8mu4kyhl5jrh4nzvm65qz588hy9qakmjnw",
			valconsAddress:   "cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39",
			privValidatorKey: `{"address":"99BD3A72EF12CD024E7584B3AC900AE3743C6ADF","pub_key":{"type":"tendermint/PubKeyEd25519","value":"mAN6RXYxSM4MNGSIriYiS7pHuwAcOHDQAy9/wnlSzOI="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"QePcwfWtOavNK7pBJrtoLMzarHKn6iBWfWPFeyV+IdmYA3pFdjFIzgw0ZIiuJiJLuke7ABw4cNADL3/CeVLM4g=="}}`,
			nodeKey:          `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"TQ4vHcO/vKdzGtWpelkX53WdMQd4kTsWGFrdcatdXFvWyO215Rewn5IRP0FszPLWr2DqPzmuH8WvxYGk5aeOXw=="}}`,
			ipSuffix:         "5",

			// consumer chain assigned key
			consumerMnemonic:         "grunt list hour endless observe better spoil penalty lab duck only layer vague fantasy satoshi record demise topple space shaft solar practice donor sphere",
			consumerDelAddress:       "cosmos1q90l6j6lzzgt460ehjj56azknlt5yrd4s38n97",
			consumerValoperAddress:   "cosmosvaloper1q90l6j6lzzgt460ehjj56azknlt5yrd449nxfd",
			consumerValconsAddress:   "cosmosvalcons1uuec3cjxajv5te08p220usrjhkfhg9wyvqn0tm",
			consumerValPubKey:        `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"QlG+iYe6AyYpvY1z9RNJKCVlH14Q/qSz4EjGdGCru3o="}`,
			consumerPrivValidatorKey: `{"address":"E73388E246EC9945E5E70A94FE4072BD937415C4","pub_key":{"type":"tendermint/PubKeyEd25519","value":"QlG+iYe6AyYpvY1z9RNJKCVlH14Q/qSz4EjGdGCru3o="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"OFR4w+FC6EMw5fAGTrHVexyPrjzQ7QfqgZOMgVf0izlCUb6Jh7oDJim9jXP1E0koJWUfXhD+pLPgSMZ0YKu7eg=="}}`,
			consumerNodeKey:          `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"uhPCqnL2KE8m/8OFNLQ5bN3CJr6mds+xfBi0E4umT/s2uWiJhet+vbYx88DHSdof3gGFNTIzAIxSppscBKX96w=="}}`,
			useConsumerKey:           false,
		},
		validatorID("carol"): {
			mnemonic:         "sight similar better jar bitter laptop solve fashion father jelly scissors chest uniform play unhappy convince silly clump another conduct behave reunion marble animal",
			delAddress:       "cosmos19hz4m226ztankqramvt4a7t0shejv4dc79gp9u",
			valoperAddress:   "cosmosvaloper19hz4m226ztankqramvt4a7t0shejv4dcm3u5f0",
			valconsAddress:   "cosmosvalcons1ezyrq65s3gshhx5585w6mpusq3xsj3ayzf4uv6",
			privValidatorKey: `{"address":"C888306A908A217B9A943D1DAD8790044D0947A4","pub_key":{"type":"tendermint/PubKeyEd25519","value":"IHo4QEikWZfIKmM0X+N+BjKttz8HOzGs2npyjiba3Xk="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"z08bmSB91uFVpVmR3t2ewd/bDjZ/AzwQpe5rKjWiPG0gejhASKRZl8gqYzRf434GMq23Pwc7MazaenKOJtrdeQ=="}}`,
			nodeKey:          `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"WLTcHEjbwB24Wp3z5oBSYTvtGQonz/7IQabOFw85BN0UkkyY5HDf38o8oHlFxVI26f+DFVeICuLbe9aXKGnUeg=="}}`,
			ipSuffix:         "6",

			// consumer chain assigned key
			consumerMnemonic:         "clip choose cake west range gun slam cry village receive juice galaxy lend ritual range provide ritual can since verify breeze vacant play dragon",
			consumerDelAddress:       "cosmos1sx6j9g2rh324a342a5f0rnx7me34r9nwgf0mc7",
			consumerValoperAddress:   "cosmosvaloper1sx6j9g2rh324a342a5f0rnx7me34r9nwdamw5d",
			consumerValconsAddress:   "cosmosvalcons1kswr5sq599365kcjmhgufevfps9njf43e4lwdk",
			consumerValPubKey:        `{"@type":"/cosmos.crypto.ed25519.PubKey","key":"Ui5Gf1+mtWUdH8u3xlmzdKID+F3PK0sfXZ73GZ6q6is="}`,
			consumerPrivValidatorKey: `{"address":"B41C3A40142963AA5B12DDD1C4E5890C0B3926B1","pub_key":{"type":"tendermint/PubKeyEd25519","value":"Ui5Gf1+mtWUdH8u3xlmzdKID+F3PK0sfXZ73GZ6q6is="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"3YaBAZLA+sl/E73lLfbFbG0u6DYm33ayr/0UpCt/vFBSLkZ/X6a1ZR0fy7fGWbN0ogP4Xc8rSx9dnvcZnqrqKw=="}}`,
			consumerNodeKey:          `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"rxBzFedtD3pqgfJQblbxGusKOr47oBfr8ba0Iz14gobtDRZQZlSZ/UGP4pSHkVf+4vtkrkO1vRHBYJobuiP+7A=="}}`,
			useConsumerKey:           true,
		},
	}
}

func KeyAssignmentTestRun() TestRun {
	return TestRun{
		name: "key-assignment",
		containerConfig: ContainerConfig{
			containerName: "interchain-security-keys-container",
			instanceName:  "interchain-security-keys-instance",
			ccvVersion:    "1",
			now:           time.Now(),
		},
		validatorConfigs: getDefaultValidators(),
		chainConfigs: map[chainID]ChainConfig{
			chainID("provi"): {
				chainId:        chainID("provi"),
				binaryName:     "interchain-security-pd",
				ipPrefix:       "7.7.7",
				votingWaitTime: 20,
				genesisChanges: ".app_state.gov.voting_params.voting_period = \"20s\" | " +
					// Custom slashing parameters for testing validator downtime functionality
					// See https://docs.cosmos.network/main/modules/slashing/04_begin_block.html#uptime-tracking
					".app_state.slashing.params.signed_blocks_window = \"2\" | " +
					".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
					".app_state.slashing.params.downtime_jail_duration = \"2s\" | " +
					".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\" | " +
					".app_state.provider.params.slash_meter_replenish_fraction = \"1.0\"", // This disables slash packet throttling
			},
			chainID("consu"): {
				chainId:        chainID("consu"),
				binaryName:     "interchain-security-cd",
				ipPrefix:       "7.7.8",
				votingWaitTime: 20,
				genesisChanges: ".app_state.gov.voting_params.voting_period = \"20s\" | " +
					".app_state.slashing.params.signed_blocks_window = \"200\" | " +
					".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
					".app_state.slashing.params.downtime_jail_duration = \"2s\" | " +
					".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\"",
			},
		},
	}
}

func DefaultTestRun() TestRun {
	return TestRun{
		name: "default",
		containerConfig: ContainerConfig{
			containerName: "interchain-security-container",
			instanceName:  "interchain-security-instance",
			ccvVersion:    "1",
			now:           time.Now(),
		},
		validatorConfigs: getDefaultValidators(),
		chainConfigs: map[chainID]ChainConfig{
			chainID("provi"): {
				chainId:        chainID("provi"),
				binaryName:     "interchain-security-pd",
				ipPrefix:       "7.7.7",
				votingWaitTime: 20,
				genesisChanges: ".app_state.gov.voting_params.voting_period = \"20s\" | " +
					// Custom slashing parameters for testing validator downtime functionality
					// See https://docs.cosmos.network/main/modules/slashing/04_begin_block.html#uptime-tracking
					".app_state.slashing.params.signed_blocks_window = \"2\" | " +
					".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
					".app_state.slashing.params.downtime_jail_duration = \"2s\" | " +
					".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\" | " +
					".app_state.provider.params.slash_meter_replenish_fraction = \"0.33\" | " +
					".app_state.provider.params.slash_meter_replenish_period = \"10s\"",
			},
			chainID("consu"): {
				chainId:        chainID("consu"),
				binaryName:     "interchain-security-cd",
				ipPrefix:       "7.7.8",
				votingWaitTime: 20,
				genesisChanges: ".app_state.gov.voting_params.voting_period = \"20s\" | " +
					".app_state.slashing.params.signed_blocks_window = \"15\" | " +
					".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
					".app_state.slashing.params.downtime_jail_duration = \"2s\" | " +
					".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\"",
			},
		},
	}
}

func DemocracyTestRun() TestRun {
	return TestRun{
		name: "democracy",
		containerConfig: ContainerConfig{
			containerName: "interchain-security-democ-container",
			instanceName:  "interchain-security-democ-instance",
			ccvVersion:    "1",
			now:           time.Now(),
		},
		validatorConfigs: getDefaultValidators(),
		chainConfigs: map[chainID]ChainConfig{
			chainID("provi"): {
				chainId:        chainID("provi"),
				binaryName:     "interchain-security-pd",
				ipPrefix:       "7.7.7",
				votingWaitTime: 20,
				genesisChanges: ".app_state.gov.voting_params.voting_period = \"20s\" | " +
					// Custom slashing parameters for testing validator downtime functionality
					// See https://docs.cosmos.network/main/modules/slashing/04_begin_block.html#uptime-tracking
					".app_state.slashing.params.signed_blocks_window = \"2\" | " +
					".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
					".app_state.slashing.params.downtime_jail_duration = \"2s\" | " +
					".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\" | " +
					".app_state.provider.params.slash_meter_replenish_fraction = \"1.0\"", // This disables slash packet throttling
			},
			chainID("democ"): {
				chainId:        chainID("democ"),
				binaryName:     "interchain-security-cdd",
				ipPrefix:       "7.7.9",
				votingWaitTime: 20,
				genesisChanges: ".app_state.ccvconsumer.params.blocks_per_distribution_transmission = \"20\" | " +
					".app_state.gov.voting_params.voting_period = \"10s\" | " +
					".app_state.slashing.params.signed_blocks_window = \"2\" | " +
					".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
					".app_state.slashing.params.downtime_jail_duration = \"2s\" | " +
					".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\"",
			},
		},
	}
}

func MultiConsumerTestRun() TestRun {
	return TestRun{
		name: "multi-consumer",
		containerConfig: ContainerConfig{
			containerName: "interchain-security-multic-container",
			instanceName:  "interchain-security-multic-instance",
			ccvVersion:    "1",
			now:           time.Now(),
		},
		validatorConfigs: getDefaultValidators(),
		chainConfigs: map[chainID]ChainConfig{
			chainID("provi"): {
				chainId:        chainID("provi"),
				binaryName:     "interchain-security-pd",
				ipPrefix:       "7.7.7",
				votingWaitTime: 20,
				genesisChanges: ".app_state.gov.voting_params.voting_period = \"20s\" | " +
					// Custom slashing parameters for testing validator downtime functionality
					// See https://docs.cosmos.network/main/modules/slashing/04_begin_block.html#uptime-tracking
					".app_state.slashing.params.signed_blocks_window = \"2\" | " +
					".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
					".app_state.slashing.params.downtime_jail_duration = \"2s\" | " +
					".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\" | " +
					".app_state.provider.params.slash_meter_replenish_fraction = \"1.0\"", // This disables slash packet throttling
			},
			chainID("consu"): {
				chainId:        chainID("consu"),
				binaryName:     "interchain-security-cd",
				ipPrefix:       "7.7.8",
				votingWaitTime: 20,
				genesisChanges: ".app_state.gov.voting_params.voting_period = \"20s\" | " +
					".app_state.slashing.params.signed_blocks_window = \"2\" | " +
					".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
					".app_state.slashing.params.downtime_jail_duration = \"2s\" | " +
					".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\"",
			},
			chainID("densu"): {
				chainId:        chainID("densu"),
				binaryName:     "interchain-security-cd",
				ipPrefix:       "7.7.9",
				votingWaitTime: 20,
				genesisChanges: ".app_state.gov.voting_params.voting_period = \"20s\" | " +
					".app_state.slashing.params.signed_blocks_window = \"2\" | " +
					".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
					".app_state.slashing.params.downtime_jail_duration = \"2s\" | " +
					".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\"",
			},
		},
	}
}

func (s *TestRun) SetLocalSDKPath(path string) {
	if path != "" {
		fmt.Println("USING LOCAL SDK", path)
	}
	s.localSdkPath = path
}

// ValidateStringLiterals enforces that configs follow the constraints
// necessary to to execute the tests
//
// Note: Network interfaces (name of virtual ethernet interfaces for ip link)
// within the container will be named as "$CHAIN_ID-$VAL_ID-out" etc.
// where this name is constrained to 15 bytes or less. Therefore each string literal
// used as a validatorID or chainID needs to be 5 char or less.
func (s *TestRun) ValidateStringLiterals() {
	for valID, valConfig := range s.validatorConfigs {

		if len(valID) > 5 {
			panic("validator id string literal must be 5 char or less")
		}

		ipSuffix, err := strconv.Atoi(valConfig.ipSuffix)
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

		if chainID != chainConfig.chainId {
			panic("chain config is mapped to a chain id that is different than what's stored in the config")
		}
	}
}
