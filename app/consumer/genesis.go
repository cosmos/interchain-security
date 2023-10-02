package app

import (
	"encoding/json"
	"fmt"
	"os"

	cmtjson "github.com/cometbft/cometbft/libs/json"
	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/codec"
	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/version"
	consumerTypes "github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
	"github.com/cosmos/interchain-security/v3/x/ccv/types"
	"github.com/spf13/cobra"
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

func migrateFromV2(jsonRaw []byte, ctx client.Context) (json.RawMessage, error) {
	oldConsumerGenesis := consumerTypes.GenesisState{}
	oldConsumerGenesis.Validate()
	err := cmtjson.Unmarshal(jsonRaw, &oldConsumerGenesis)
	if err != nil {
		return nil, err
	}

	newGenesis := types.ConsumerGenesisState{
		Params: oldConsumerGenesis.Params,
		Provider: types.ProviderInfo{
			ClientState:    oldConsumerGenesis.ProviderClientState,
			ConsensusState: oldConsumerGenesis.ConsensusState,
			InitialValSet:  oldConsumerGenesis.InitialValSet,
		},
	}

	newJson := ctx.Codec.MustMarshalJSON(&newGenesis)
	return newJson, nil
}

var transformationMap = TransformationMap{
	"v2": migrateFromV2,
}

// Transform a consumer genesis json file exported from a given ccv provider version
// to a consumer genesis json format supported by current ccv consumer version.
// Result will be writen to defined output.
func TransformConsumerGenesis(cmd *cobra.Command, args []string, transformationMap TransformationMap) error {
	sourceVersion := args[0]
	sourceFile := args[1]

	jsonRaw, err := os.ReadFile(sourceFile)
	if err != nil {
		return err
	}

	// TODO: content validation would be good
	transform, exists := transformationMap[sourceVersion]
	if !exists {
		return fmt.Errorf("error transforming consumer genesis content: Unsupported versions %s", sourceVersion)
	}

	clientCtx := client.GetClientContextFromCmd(cmd)
	newConsumerGenesis, err := transform(jsonRaw, clientCtx)
	if err != nil {
		return err
	}

	bz, err := cmtjson.Marshal(newConsumerGenesis)
	if err != nil {
		return err
	}

	sortedBz, err := sdk.SortJSON(bz)
	if err != nil {
		return err
	}

	cmd.Println(string(sortedBz))
	return nil
}

// NewDefaultGenesisState generates the default state for the application.
func NewDefaultGenesisState(cdc codec.JSONCodec) GenesisState {
	return ModuleBasics.DefaultGenesis(cdc)
}

func GetConsumerGenesisTransformCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "transform [source-version] [genesis-file]",
		Short: "Transform consumer genesis section from a specified provider version",
		Long: fmt.Sprintf(`Transform the consumer genesis into the target version and print to STDOUT.

Example:
$ %s transform v2.0.0 /path/to/consumer_genesis.json `, version.AppName),
		Args: cobra.ExactArgs(2),
		RunE: func(cmd *cobra.Command, args []string) error {
			//return ModuleBasics.ValidateGenesis(cmd, args, migrationMap)
			return TransformConsumerGenesis(cmd, args, transformationMap)
		},
	}

	return cmd
}
