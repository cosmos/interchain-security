package e2e

import (
	"fmt"
	"log"
	"strconv"
	"time"

	"golang.org/x/mod/semver"
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

type TestConfig struct {
	// These are the non altered values during a typical test run, where multiple test runs can exist
	// to validate different action sequences and corresponding state checks.
	ContainerConfig  ContainerConfig
	ValidatorConfigs map[ValidatorID]ValidatorConfig
	ChainConfigs     map[ChainID]ChainConfig
	ConsumerChains   map[ConsumerID]ChainConfig
	ProviderVersion  string
	ConsumerVersion  string
	// override config.toml parameters
	// usually used to override timeout_commit
	// having shorter timeout_commit reduces the test runtime because blocks are produced faster
	// lengthening the timeout_commit increases the test runtime because blocks are produced slower but the test is more reliable
	TendermintConfigOverride string
	UseCometmock             bool // if false, nodes run CometBFT
	UseGorelayer             bool // if false, Hermes is used as the relayer
	// chains which are running, i.e. producing blocks, at the moment
	RunningChains map[ChainID]bool
	// Used with CometMock. The time by which chains have been advanced. Used to keep chains in sync: when a new chain is started, advance its time by this value to keep chains in sync.
	TimeOffset       time.Duration
	TransformGenesis bool
	Name             string
}

// Initialize initializes the TestConfig instance by setting the runningChains field to an empty map.
func (tr *TestConfig) Initialize() {
	tr.RunningChains = make(map[ChainID]bool)
}

func (s *TestConfig) SetCometMockConfig(useCometmock bool) {
	s.UseCometmock = useCometmock
}

func (s *TestConfig) SetRelayerConfig(useRly bool) {
	s.UseGorelayer = useRly
}

// ValidateStringLiterals enforces that configs follow the constraints
// necessary to execute the tests
//
// Note: Network interfaces (name of virtual ethernet interfaces for ip link)
// within the container will be named as "$CHAIN_ID-$VAL_ID-out" etc.
// where this name is constrained to 15 bytes or less. Therefore each string literal
// used as a validatorID or chainID needs to be 5 char or less.
func (s *TestConfig) ValidateStringLiterals() {
	for valID, valConfig := range s.ValidatorConfigs {
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

	for chainID, chainConfig := range s.ChainConfigs {
		if len(chainID) > 5 {
			panic(fmt.Sprintf("chain id string literal must be 5 char or less: %s", chainID))
		}

		if chainID != chainConfig.ChainId {
			log.Println("chain config is mapped to a chain id that is different than what's stored in the config")
		}
	}
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
