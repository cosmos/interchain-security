package main

import (
	"flag"
	"fmt"
	"time"
)

// Attributes that are unique to a validator. Allows us to map (part of) the set of uints to
// a set of viable validators
type ValidatorConfig struct {
	mnemonic         string
	delAddress       string
	valoperAddress   string
	valconsAddress   string
	privValidatorKey string
	nodeKey          string
}

// Attributes that are unique to a chain. Allows us to map (part of) the set of uints to
// a set of viable chains
type ChainConfig struct {
	chainId        string
	ipPrefix       string
	votingWaitTime uint
	genesisChanges string
	binaryName     string
}

type ContainerConfig struct {
	containerName string
	instanceName  string
	ccvVersion    string
	now           time.Time
}

// These values will not be altered during a typical test run
// They are probably not part of the model
type System struct {
	containerConfig  ContainerConfig
	validatorConfigs []ValidatorConfig
	chainConfigs     []ChainConfig
	localSdkPath     string
}

func DefaultSystemConfig() System {
	return System{
		containerConfig: ContainerConfig{
			containerName: "interchain-security-container",
			instanceName:  "interchain-security-instance",
			ccvVersion:    "1",
			now:           time.Now(),
		},
		validatorConfigs: []ValidatorConfig{
			{
				mnemonic:         "pave immune ethics wrap gain ceiling always holiday employ earth tumble real ice engage false unable carbon equal fresh sick tattoo nature pupil nuclear",
				delAddress:       "cosmos19pe9pg5dv9k5fzgzmsrgnw9rl9asf7ddwhu7lm",
				valoperAddress:   "cosmosvaloper19pe9pg5dv9k5fzgzmsrgnw9rl9asf7ddtrgtng",
				valconsAddress:   "cosmosvalcons1qmq08eruchr5sf5s3rwz7djpr5a25f7xw4mceq",
				privValidatorKey: `{"address":"06C0F3E47CC5C748269088DC2F36411D3AAA27C6","pub_key":{"type":"tendermint/PubKeyEd25519","value":"RrclQz9bIhkIy/gfL485g3PYMeiIku4qeo495787X10="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"uX+ZpDMg89a6gtqs/+MQpCTSqlkZ0nJQJOhLlCJvwvdGtyVDP1siGQjL+B8vjzmDc9gx6IiS7ip6jj3nvztfXQ=="}}`,
				nodeKey:          `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"fjw4/DAhyRPnwKgXns5SV7QfswRSXMWJpHS7TyULDmJ8ofUc5poQP8dgr8bZRbCV5RV8cPqDq3FPdqwpmUbmdA=="}}`,
			},
			{
				mnemonic:         "glass trip produce surprise diamond spin excess gaze wash drum human solve dress minor artefact canoe hard ivory orange dinner hybrid moral potato jewel",
				delAddress:       "cosmos1dkas8mu4kyhl5jrh4nzvm65qz588hy9qcz08la",
				valoperAddress:   "cosmosvaloper1dkas8mu4kyhl5jrh4nzvm65qz588hy9qakmjnw",
				valconsAddress:   "cosmosvalcons1nx7n5uh0ztxsynn4sje6eyq2ud6rc6klc96w39",
				privValidatorKey: `{"address":"99BD3A72EF12CD024E7584B3AC900AE3743C6ADF","pub_key":{"type":"tendermint/PubKeyEd25519","value":"mAN6RXYxSM4MNGSIriYiS7pHuwAcOHDQAy9/wnlSzOI="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"QePcwfWtOavNK7pBJrtoLMzarHKn6iBWfWPFeyV+IdmYA3pFdjFIzgw0ZIiuJiJLuke7ABw4cNADL3/CeVLM4g=="}}`,
				nodeKey:          `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"TQ4vHcO/vKdzGtWpelkX53WdMQd4kTsWGFrdcatdXFvWyO215Rewn5IRP0FszPLWr2DqPzmuH8WvxYGk5aeOXw=="}}`,
			},
			{
				mnemonic:         "sight similar better jar bitter laptop solve fashion father jelly scissors chest uniform play unhappy convince silly clump another conduct behave reunion marble animal",
				delAddress:       "cosmos19hz4m226ztankqramvt4a7t0shejv4dc79gp9u",
				valoperAddress:   "cosmosvaloper19hz4m226ztankqramvt4a7t0shejv4dcm3u5f0",
				valconsAddress:   "cosmosvalcons1ezyrq65s3gshhx5585w6mpusq3xsj3ayzf4uv6",
				privValidatorKey: `{"address":"C888306A908A217B9A943D1DAD8790044D0947A4","pub_key":{"type":"tendermint/PubKeyEd25519","value":"IHo4QEikWZfIKmM0X+N+BjKttz8HOzGs2npyjiba3Xk="},"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"z08bmSB91uFVpVmR3t2ewd/bDjZ/AzwQpe5rKjWiPG0gejhASKRZl8gqYzRf434GMq23Pwc7MazaenKOJtrdeQ=="}}`,
				nodeKey:          `{"priv_key":{"type":"tendermint/PrivKeyEd25519","value":"WLTcHEjbwB24Wp3z5oBSYTvtGQonz/7IQabOFw85BN0UkkyY5HDf38o8oHlFxVI26f+DFVeICuLbe9aXKGnUeg=="}}`,
			},
		},
		chainConfigs: []ChainConfig{
			{
				chainId:        "provider",
				binaryName:     "interchain-security-pd",
				ipPrefix:       "7.7.7",
				votingWaitTime: 5,
				genesisChanges: ".app_state.gov.voting_params.voting_period = \"5s\"",
			},
			{
				chainId:        "consumer",
				binaryName:     "interchain-security-cd",
				ipPrefix:       "7.7.8",
				votingWaitTime: 10,
				genesisChanges: ".app_state.gov.voting_params.voting_period = \"10s\"",
			},
		},
	}
}

func (s *System) ParseCLIFlags() {
	localSdkPath := flag.String("local-sdk-path", "",
		"path of a local sdk version to build and reference in integration tests")
	flag.Parse()
	s.localSdkPath = *localSdkPath
	fmt.Println(s.localSdkPath)
}
