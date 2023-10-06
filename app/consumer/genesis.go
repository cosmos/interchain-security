package app

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"sort"
	"strings"

	"github.com/spf13/cobra"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/version"

	consumerTypes "github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
	"github.com/cosmos/interchain-security/v3/x/ccv/types"
)

// The genesis state of the blockchain is represented here as a map of raw json
// messages key'd by a identifier string.
// The identifier is used to determine which module genesis information belongs
// to so it may be appropriately routed during init chain.
// Within this application default genesis information is retrieved from
// the ModuleBasicManager which populates json from each BasicModule
// object provided to it during init.
type GenesisState map[string]json.RawMessage

type (
	// Transformation callback for a consumer genesis 'section' exported from a
	// specific version of a provider
	TransformationCallback func([]byte, client.Context) (json.RawMessage, error)

	// TransformationMap defines the mapping from a version to a transformation callback
	TransformationMap map[string]TransformationCallback
)

// Migration of consumer genesis content as it is exported from a provider version v2
// (ICS provider module version) to a format readable by current consumer implementation.
func migrateFromV2(jsonRaw []byte, ctx client.Context) (json.RawMessage, error) {
	// v2 uses deprecated fields of GenesisState type
	oldConsumerGenesis := consumerTypes.GenesisState{}
	err := ctx.Codec.UnmarshalJSON(jsonRaw, &oldConsumerGenesis)
	if err != nil {
		return nil, fmt.Errorf("reading consumer genesis data failed: %s", err)
	}

	// some sanity checks for v2 transformation
	if len(oldConsumerGenesis.Provider.InitialValSet) > 0 {
		return nil, fmt.Errorf("invalid source version. Unexpected element 'provider.initial_val_set'")
	}

	if oldConsumerGenesis.Provider.ClientState != nil {
		return nil, fmt.Errorf("invalid source version. Unexpected element 'provider.client_state'")
	}

	if oldConsumerGenesis.Provider.ConsensusState != nil {
		return nil, fmt.Errorf("invalid source version. Unexpected element 'provider.consensus_state'")
	}

	// Version 2 of provider genesis data fills up deprecated fields
	// ProviderClientState, ConsensusState and InitialValSet
	newGenesis := types.ConsumerGenesisState{
		Params: oldConsumerGenesis.Params,
		Provider: types.ProviderInfo{
			ClientState:    oldConsumerGenesis.ProviderClientState,
			ConsensusState: oldConsumerGenesis.ProviderConsensusState,
			InitialValSet:  oldConsumerGenesis.InitialValSet,
		},
	}

	newJson, err := ctx.Codec.MarshalJSON(&newGenesis)
	if err != nil {
		return nil, fmt.Errorf("failed marshalling data to new type: %s", err)
	}
	return newJson, nil
}

// Mapping of provider module version to related transformation function
var transformationMap = TransformationMap{
	"v2": migrateFromV2,
}

// Transform a consumer genesis json file exported from a given ccv provider version
// to a consumer genesis json format supported by current ccv consumer version.
// Result will be written to defined output.
func TransformConsumerGenesis(cmd *cobra.Command, args []string, transformationMap TransformationMap) error {
	sourceVersion := args[0]
	sourceFile := args[1]

	jsonRaw, err := os.ReadFile(filepath.Clean(sourceFile))
	if err != nil {
		return err
	}

	transform, exists := transformationMap[sourceVersion]
	if !exists {
		return fmt.Errorf("error transforming consumer genesis content: Unsupported versions %s", sourceVersion)
	}

	clientCtx := client.GetClientContextFromCmd(cmd)
	newConsumerGenesis, err := transform(jsonRaw, clientCtx)
	if err != nil {
		return err
	}

	bz, err := newConsumerGenesis.MarshalJSON()
	if err != nil {
		return fmt.Errorf("failed exporting new consumer genesis to JSON: %s", err)
	}

	sortedBz, err := sdk.SortJSON(bz)
	if err != nil {
		return fmt.Errorf("failed sorting transformed consumer genesis JSON: %s", err)
	}

	cmd.Println(string(sortedBz))
	return nil
}

// List of provider versions supported by consumer genesis transformations
func getSupportedTransformationVersions() []string {
	var keys []string
	for k := range transformationMap {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	return keys
}

// NewDefaultGenesisState generates the default state for the application.
func NewDefaultGenesisState(cdc codec.JSONCodec) GenesisState {
	return ModuleBasics.DefaultGenesis(cdc)
}

// GetConsumerGenesisTransformCmd transforms Consumer Genesis JSON content exported from a specific
// provider version to a JSON format supported by this consumer version.
// Note: Provider module version can be received by querying 'module_versions' on the 'upgrade' module.
func GetConsumerGenesisTransformCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "transform [source-version] [genesis-file]",
		Short: "Transform CCV consumer genesis from a specified provider version",
		Long: fmt.Sprintf(`Transform the consumer genesis file from a specified provider version to a version supported by this consumer. Result is printed to STDOUT.
Supported provider versions: %s

Example:
$ %s transform v2 /path/to/consumer_genesis.json `, strings.Join(getSupportedTransformationVersions(), ", "), version.AppName),
		Args: cobra.ExactArgs(2),
		RunE: func(cmd *cobra.Command, args []string) error {
			return TransformConsumerGenesis(cmd, args, transformationMap)
		},
	}

	return cmd
}
