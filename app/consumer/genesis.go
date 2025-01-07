package app

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"strings"

	"github.com/spf13/cobra"
	"golang.org/x/exp/maps"

	"github.com/cosmos/cosmos-sdk/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/version"
)

// The genesis state of the blockchain is represented here as a map of raw json
// messages key'd by a identifier string.
// The identifier is used to determine which module genesis information belongs
// to so it may be appropriately routed during init chain.
// Within this application default genesis information is retrieved from
// the ModuleBasicManager which populates json from each BasicModule
// object provided to it during init.
type GenesisState map[string]json.RawMessage

// Map of supported versions for consumer genesis transformation
type IcsVersion string

const (
	v4_x_x IcsVersion = "<v4.5.x" // all v4 versions < v4.5.0
	v4_5_x IcsVersion = "v4.5.x"
	v5_x_x IcsVersion = "v5.x"    // all v5 version
	v6_x_x IcsVersion = "<v6.4.x" // all v6 versions < v6.4.0
)

var TransformationVersions map[string]IcsVersion = map[string]IcsVersion{
	"<v4.5.x": v4_x_x,
	"v4.5.x":  v4_5_x,
	"v5.x":    v5_x_x,
	"<v6.4.x": v6_x_x,
}

// Remove a parameter from a JSON object
func removeParameterFromParams(params json.RawMessage, param string) (json.RawMessage, error) {
	paramsMap := map[string]json.RawMessage{}
	if err := json.Unmarshal(params, &paramsMap); err != nil {
		return nil, fmt.Errorf("unmarshalling 'params' failed: %v", err)
	}
	_, exists := paramsMap[param]
	if exists {
		delete(paramsMap, param)
	}
	return json.Marshal(paramsMap)
}

// Transformation of consumer genesis content as it is exported by provider version >= v6.2.x
// to a format supported by consumer chains version with either SDK v0.47 and ICS < v4.5.0 or SDK v0.50 and ICS < v6.2.0
// This transformation removes the 'consumer_id' parameter from the 'params' field introduced in ICS v6.2.x
func removeConsumerID(genState map[string]json.RawMessage) (map[string]json.RawMessage, error) {
	// Remove 'consumer_id' from 'params'
	params, err := removeParameterFromParams(genState["params"], "consumer_id")
	if err != nil {
		return nil, err
	}

	genState["params"] = params

	return genState, nil
}

func removeFieldsFromGenesisState(genState map[string]json.RawMessage, keysToRemove []string) (map[string]json.RawMessage, error) {
	for _, key := range keysToRemove {
		delete(genState, key) // Remove the key from the map if it exists
	}
	return genState, nil
}

// transformGenesis transforms ccv consumer genesis data to the specified target version
// Returns the transformed data or an error in case the transformation failed or the format is not supported by current implementation
func transformGenesis(targetVersion IcsVersion, jsonRaw []byte) (json.RawMessage, error) {
	var err error
	// Unmarshal genesis state from raw msg
	genState := map[string]json.RawMessage{}
	if err := json.Unmarshal(jsonRaw, &genState); err != nil {
		return nil, fmt.Errorf("unmarshalling 'GenesisState' failed: %v", err)
	}

	switch targetVersion {
	case v4_x_x, v5_x_x:
		genState, err = removeConsumerID(genState)
		if err != nil {
			break
		}
		genState, err = removeFieldsFromGenesisState(genState, []string{"connection_id"})
	case v4_5_x, v6_x_x:
		genState, err = removeFieldsFromGenesisState(genState, []string{"connection_id"})
	default:
		err = fmt.Errorf("unsupported target version '%s'. Run %s --help",
			targetVersion, version.AppName)
	}

	if err != nil {
		return nil, fmt.Errorf("transformation failed: %v", err)
	}

	// Marshal genesis state to raw msg
	newConsumerGenesis, err := json.Marshal(genState)
	if err != nil {
		return nil, fmt.Errorf("marshalling transformation result failed: %v", err)
	}

	return newConsumerGenesis, err
}

// Transform a consumer genesis json file exported from a given ccv provider version
// to a consumer genesis json format supported by current ccv consumer version
// This allows user to patch consumer genesis of
//   - v4.x, v5.x, v6.1.x from exports of provider >= v6.2.x
//
// Result will be written to defined output.
func TransformConsumerGenesis(cmd *cobra.Command, args []string) error {
	sourceFile := args[0]
	jsonRaw, err := os.ReadFile(filepath.Clean(sourceFile))
	if err != nil {
		return err
	}

	version, err := cmd.Flags().GetString("to")
	if err != nil {
		return fmt.Errorf("error getting targetVersion %v", err)
	}
	targetVersion, exists := TransformationVersions[version]
	if !exists {
		return fmt.Errorf("unsupported target version '%s'", version)
	}

	// try to transform data to target format
	newConsumerGenesis, err := transformGenesis(targetVersion, jsonRaw)
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

// NewDefaultGenesisState generates the default state for the application.
func NewDefaultGenesisState(cdc codec.JSONCodec) GenesisState {
	return ModuleBasics.DefaultGenesis(cdc)
}

// GetConsumerGenesisTransformCmd transforms Consumer Genesis JSON content exported from a
// provider version v1,v2 or v3 to a JSON format supported by this consumer version.
func GetConsumerGenesisTransformCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "transform [-to version] genesis-file",
		Short: "Transform consumer module genesis data exported to a specific target format",
		Long: strings.TrimSpace(
			fmt.Sprintf(`
Transform the consumer genesis data exported from a provider version >= v6.3.x to a specified consumer target version.
The result is printed to STDOUT.

Note: Content to be transformed is not the consumer genesis file itself but the exported content from provider chain which is used to patch the consumer genesis file!

Example:
$ %s transform /path/to/ccv_consumer_genesis.json
$ %s --to v5.x transform /path/to/ccv_consumer_genesis.json
`, version.AppName, version.AppName),
		),
		Args: cobra.RangeArgs(1, 2),
		RunE: TransformConsumerGenesis,
	}
	cmd.Flags().String("to", string(v5_x_x),
		fmt.Sprintf("target version for consumer genesis. Supported versions %s",
			maps.Keys(TransformationVersions)))
	return cmd
}
