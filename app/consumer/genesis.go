package app

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
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

// Migration of consumer genesis content as it is exported from a provider version v1,2,3
// to a format readable by current consumer implementation.
func transform(jsonRaw []byte, ctx client.Context) (json.RawMessage, error) {
	// v1,2,3 uses deprecated fields of GenesisState type
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
		NewChain: oldConsumerGenesis.NewChain,
	}

	newJson, err := ctx.Codec.MarshalJSON(&newGenesis)
	if err != nil {
		return nil, fmt.Errorf("failed marshalling data to new type: %s", err)
	}
	return newJson, nil
}

// Transform a consumer genesis json file exported from a given ccv provider version
// to a consumer genesis json format supported by current ccv consumer version.
// Result will be written to defined output.
func TransformConsumerGenesis(cmd *cobra.Command, args []string) error {
	sourceFile := args[0]

	jsonRaw, err := os.ReadFile(filepath.Clean(sourceFile))
	if err != nil {
		return err
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

// NewDefaultGenesisState generates the default state for the application.
func NewDefaultGenesisState(cdc codec.JSONCodec) GenesisState {
	return ModuleBasics.DefaultGenesis(cdc)
}

// GetConsumerGenesisTransformCmd transforms Consumer Genesis JSON content exported from a
// provider version v1,v2 or v3 to a JSON format supported by this consumer version.
func GetConsumerGenesisTransformCmd() *cobra.Command {
	cmd := &cobra.Command{
		Use:   "transform [genesis-file]",
		Short: "Transform CCV consumer genesis from an older provider version not supporting current format",
		Long: strings.TrimSpace(
			fmt.Sprintf(`Transform the consumer genesis file from a provider version v1,v2 or v3 to a version supported by this consumer. Result is printed to STDOUT.

Example:
$ %s transform /path/to/ccv_consumer_genesis.json`, version.AppName),
		),
		Args: cobra.ExactArgs(1),
		RunE: TransformConsumerGenesis,
	}

	return cmd
}
