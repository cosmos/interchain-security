package main

import (
	"flag"
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
	// Must be an integer greater than 0 and less than 254
	ipSuffix string
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
}

func DefaultTestRun() TestRun {
	return TestRun{
		containerConfig: ContainerConfig{
			containerName: "interchain-security-container",
			instanceName:  "interchain-security-instance",
			ccvVersion:    "1",
			now:           time.Now(),
		},
		validatorConfigs: map[validatorID]ValidatorConfig{
			validatorID("alice"): {
				mnemonic:         "pave immune ethics wrap gain ceiling always holiday employ earth tumble real ice engage false unable carbon equal fresh sick tattoo nature pupil nuclear",
				delAddress:       "cosmos19pe9pg5dv9k5fzgzmsrgnw9rl9asf7ddwhu7lm",
				valoperAddress:   "cosmosvaloper19pe9pg5dv9k5fzgzmsrgnw9rl9asf7ddtrgtng",
				valconsAddress:   "cosmosvalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xw4mceq",
				privValidatorKey: `{"address":"06C0F3E47CC5C748269088DC2F36411D3AAA27C6","pub_key":{"type":"tendermint/PubKeyEd25519","value":"RrclQz9bIhkIy/gfL485g3PYMeiIku4qeo495787X10="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"uX+ZpDMg89a6gtqs/+MQpCTSqlkZ0nJQJOhLlCJvwvdGtyVDP1siGQjL+B8vjzmDc9gx6IiS7ip6jj3nvztfXQ=="}}`,
				nodeKey:          `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"fjw4/DAhyRPnwKgXns5SV7QfswRSXMWJpHS7TyULDmJ8ofUc5poQP8dgr8bZRbCV5RV8cPqDq3FPdqwpmUbmdA=="}}`,
				ipSuffix:         "4",
			},
			validatorID("bob"): {
				mnemonic:         "glass trip produce surprise diamond spin excess gaze wash drum human solve dress minor artefact canoe hard ivory orange dinner hybrid moral potato jewel",
				delAddress:       "cosmos1dkas8mu4kyhl5jrh4nzvm65qz588hy9qcz08la",
				valoperAddress:   "cosmosvaloper1dkas8mu4kyhl5jrh4nzvm65qz588hy9qakmjnw",
				valconsAddress:   "cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39",
				privValidatorKey: `{"address":"99BD3A72EF12CD024E7584B3AC900AE3743C6ADF","pub_key":{"type":"tendermint/PubKeyEd25519","value":"mAN6RXYxSM4MNGSIriYiS7pHuwAcOHDQAy9/wnlSzOI="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"QePcwfWtOavNK7pBJrtoLMzarHKn6iBWfWPFeyV+IdmYA3pFdjFIzgw0ZIiuJiJLuke7ABw4cNADL3/CeVLM4g=="}}`,
				nodeKey:          `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"TQ4vHcO/vKdzGtWpelkX53WdMQd4kTsWGFrdcatdXFvWyO215Rewn5IRP0FszPLWr2DqPzmuH8WvxYGk5aeOXw=="}}`,
				ipSuffix:         "5",
			},
			validatorID("carol"): {
				mnemonic:         "sight similar better jar bitter laptop solve fashion father jelly scissors chest uniform play unhappy convince silly clump another conduct behave reunion marble animal",
				delAddress:       "cosmos19hz4m226ztankqramvt4a7t0shejv4dc79gp9u",
				valoperAddress:   "cosmosvaloper19hz4m226ztankqramvt4a7t0shejv4dcm3u5f0",
				valconsAddress:   "cosmosvalcons1ezyrq65s3gshhx5585w6mpusq3xsj3ayzf4uv6",
				privValidatorKey: `{"address":"C888306A908A217B9A943D1DAD8790044D0947A4","pub_key":{"type":"tendermint/PubKeyEd25519","value":"IHo4QEikWZfIKmM0X+N+BjKttz8HOzGs2npyjiba3Xk="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"z08bmSB91uFVpVmR3t2ewd/bDjZ/AzwQpe5rKjWiPG0gejhASKRZl8gqYzRf434GMq23Pwc7MazaenKOJtrdeQ=="}}`,
				nodeKey:          `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"WLTcHEjbwB24Wp3z5oBSYTvtGQonz/7IQabOFw85BN0UkkyY5HDf38o8oHlFxVI26f+DFVeICuLbe9aXKGnUeg=="}}`,
				ipSuffix:         "6",
			},
		},
		chainConfigs: map[chainID]ChainConfig{
			chainID("provi"): {
				chainId:        chainID("provi"),
				binaryName:     "interchain-security-pd",
				ipPrefix:       "7.7.7",
				votingWaitTime: 5,
				genesisChanges: ".app_state.gov.voting_params.voting_period = \"5s\" | " +
					// Custom slashing parameters for testing validator downtime functionality
					// See https://docs.cosmos.network/main/modules/slashing/04_begin_block.html#uptime-tracking
					".app_state.slashing.params.signed_blocks_window = \"2\" | " +
					".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
					".app_state.slashing.params.downtime_jail_duration = \"2s\" | " +
					".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\"",
			},
			chainID("consu"): {
				chainId:        chainID("consu"),
				binaryName:     "interchain-security-cd",
				ipPrefix:       "7.7.8",
				votingWaitTime: 10,
				genesisChanges: ".app_state.gov.voting_params.voting_period = \"10s\" | " +
					".app_state.slashing.params.signed_blocks_window = \"2\" | " +
					".app_state.slashing.params.min_signed_per_window = \"0.500000000000000000\" | " +
					".app_state.slashing.params.downtime_jail_duration = \"2s\" | " +
					".app_state.slashing.params.slash_fraction_downtime = \"0.010000000000000000\"",
			},
		},
	}
}

func (s *TestRun) ParseCLIFlags() {
	localSdkPath := flag.String("local-sdk-path", "",
		"path of a local sdk version to build and reference in integration tests")
	flag.Parse()
	s.localSdkPath = *localSdkPath
	fmt.Println(s.localSdkPath)
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

		if ipSuffix < 1 || ipSuffix > 253 {
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
