package app_test

import (
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"reflect"
	"testing"

	"github.com/spf13/cobra"
	"github.com/stretchr/testify/require"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/x/auth/types"

	app "github.com/cosmos/interchain-security/v6/app/consumer"
	ccvtypes "github.com/cosmos/interchain-security/v6/x/ccv/types"
)

const (
	Provider_v6_3_x = "v6.3.x"
	Provider_v6_4_x = "v6.4.x"
	Consumer_v6_x_x = "<v6.4.x" // all v6 versions < v6.4.0
	Consumer_v5_x_x = "v5.x"    // all v5 version
	Consumer_v4_5_x = "v4.5.x"
	Consumer_v4_x_x = "<v4.5.x" // all v4 versions < v4.5.0
)

// Testdata mapping consumer genesis exports to a provider module version as
// used by transformation function for consumer genesis content.
var consumerGenesisStates map[string]string = map[string]string{
	"v6.3.x": `
	{
	  "params": {
	    "enabled": true,
	    "blocks_per_distribution_transmission": "1000",
	    "distribution_transmission_channel": "",
	    "provider_fee_pool_addr_str": "",
	    "ccv_timeout_period": "2419200s",
	    "transfer_timeout_period": "3600s",
	    "consumer_redistribution_fraction": "0.75",
	    "historical_entries": "10000",
	    "unbonding_period": "1209600s",
	    "soft_opt_out_threshold": "0",
	    "reward_denoms": [],
	    "provider_reward_denoms": [],
	    "retry_delay_period": "3600s",
	    "consumer_id": "1"
	  },
	  "provider": {
	    "client_state": {
	      "chain_id": "provi",
	      "trust_level": {
	        "numerator": "1",
	        "denominator": "3"
	      },
	      "trusting_period": "1197504s",
	      "unbonding_period": "1814400s",
	      "max_clock_drift": "10s",
	      "frozen_height": {
	        "revision_number": "0",
	        "revision_height": "0"
	      },
	      "latest_height": {
	        "revision_number": "0",
	        "revision_height": "24"
	      },
	      "proof_specs": [
	        {
	          "leaf_spec": {
	            "hash": "SHA256",
	            "prehash_key": "NO_HASH",
	            "prehash_value": "SHA256",
	            "length": "VAR_PROTO",
	            "prefix": "AA=="
	          },
	          "inner_spec": {
	            "child_order": [
	              0,
	              1
	            ],
	            "child_size": 33,
	            "min_prefix_length": 4,
	            "max_prefix_length": 12,
	            "empty_child": null,
	            "hash": "SHA256"
	          },
	          "max_depth": 0,
	          "min_depth": 0,
	          "prehash_key_before_comparison": false
	        },
	        {
	          "leaf_spec": {
	            "hash": "SHA256",
	            "prehash_key": "NO_HASH",
	            "prehash_value": "SHA256",
	            "length": "VAR_PROTO",
	            "prefix": "AA=="
	          },
	          "inner_spec": {
	            "child_order": [
	              0,
	              1
	            ],
	            "child_size": 32,
	            "min_prefix_length": 1,
	            "max_prefix_length": 1,
	            "empty_child": null,
	            "hash": "SHA256"
	          },
	          "max_depth": 0,
	          "min_depth": 0,
	          "prehash_key_before_comparison": false
	        }
	      ],
	      "upgrade_path": [
	        "upgrade",
	        "upgradedIBCState"
	      ],
	      "allow_update_after_expiry": false,
	      "allow_update_after_misbehaviour": false
	    },
	    "consensus_state": {
	      "timestamp": "2024-10-17T07:47:33.124389629Z",
	      "root": {
	        "hash": "cgIJagBEc/5lDkWS12NG5i7SSZ5hNFlDrlparFaWytc="
	      },
	      "next_validators_hash": "632730A03DEF630F77B61DF4092629007AE020B789713158FABCB104962FA54F"
	    },
	    "initial_val_set": [
	      {
	        "pub_key": {
	          "ed25519": "RrclQz9bIhkIy/gfL485g3PYMeiIku4qeo495787X10="
	        },
	        "power": "500"
	      },
	      {
	        "pub_key": {
	          "ed25519": "Ui5Gf1+mtWUdH8u3xlmzdKID+F3PK0sfXZ73GZ6q6is="
	        },
	        "power": "500"
	      },
	      {
	        "pub_key": {
	          "ed25519": "mAN6RXYxSM4MNGSIriYiS7pHuwAcOHDQAy9/wnlSzOI="
	        },
	        "power": "500"
	      }
	    ]
	  },
	  "new_chain": true
	}
	`,
	"v6.4.x": `
	{
	  "params": {
	    "enabled": true,
	    "blocks_per_distribution_transmission": "1000",
	    "distribution_transmission_channel": "",
	    "provider_fee_pool_addr_str": "",
	    "ccv_timeout_period": "2419200s",
	    "transfer_timeout_period": "3600s",
	    "consumer_redistribution_fraction": "0.75",
	    "historical_entries": "10000",
	    "unbonding_period": "1209600s",
	    "soft_opt_out_threshold": "0",
	    "reward_denoms": [],
	    "provider_reward_denoms": [],
	    "retry_delay_period": "3600s",
	    "consumer_id": "1"
	  },
	  "provider": {
	    "client_state": {
	      "chain_id": "provi",
	      "trust_level": {
	        "numerator": "1",
	        "denominator": "3"
	      },
	      "trusting_period": "1197504s",
	      "unbonding_period": "1814400s",
	      "max_clock_drift": "10s",
	      "frozen_height": {
	        "revision_number": "0",
	        "revision_height": "0"
	      },
	      "latest_height": {
	        "revision_number": "0",
	        "revision_height": "24"
	      },
	      "proof_specs": [
	        {
	          "leaf_spec": {
	            "hash": "SHA256",
	            "prehash_key": "NO_HASH",
	            "prehash_value": "SHA256",
	            "length": "VAR_PROTO",
	            "prefix": "AA=="
	          },
	          "inner_spec": {
	            "child_order": [
	              0,
	              1
	            ],
	            "child_size": 33,
	            "min_prefix_length": 4,
	            "max_prefix_length": 12,
	            "empty_child": null,
	            "hash": "SHA256"
	          },
	          "max_depth": 0,
	          "min_depth": 0,
	          "prehash_key_before_comparison": false
	        },
	        {
	          "leaf_spec": {
	            "hash": "SHA256",
	            "prehash_key": "NO_HASH",
	            "prehash_value": "SHA256",
	            "length": "VAR_PROTO",
	            "prefix": "AA=="
	          },
	          "inner_spec": {
	            "child_order": [
	              0,
	              1
	            ],
	            "child_size": 32,
	            "min_prefix_length": 1,
	            "max_prefix_length": 1,
	            "empty_child": null,
	            "hash": "SHA256"
	          },
	          "max_depth": 0,
	          "min_depth": 0,
	          "prehash_key_before_comparison": false
	        }
	      ],
	      "upgrade_path": [
	        "upgrade",
	        "upgradedIBCState"
	      ],
	      "allow_update_after_expiry": false,
	      "allow_update_after_misbehaviour": false
	    },
	    "consensus_state": {
	      "timestamp": "2024-10-17T07:47:33.124389629Z",
	      "root": {
	        "hash": "cgIJagBEc/5lDkWS12NG5i7SSZ5hNFlDrlparFaWytc="
	      },
	      "next_validators_hash": "632730A03DEF630F77B61DF4092629007AE020B789713158FABCB104962FA54F"
	    },
	    "initial_val_set": [
	      {
	        "pub_key": {
	          "ed25519": "RrclQz9bIhkIy/gfL485g3PYMeiIku4qeo495787X10="
	        },
	        "power": "500"
	      },
	      {
	        "pub_key": {
	          "ed25519": "Ui5Gf1+mtWUdH8u3xlmzdKID+F3PK0sfXZ73GZ6q6is="
	        },
	        "power": "500"
	      },
	      {
	        "pub_key": {
	          "ed25519": "mAN6RXYxSM4MNGSIriYiS7pHuwAcOHDQAy9/wnlSzOI="
	        },
	        "power": "500"
	      }
	    ]
	  },
	  "new_chain": true,
	  "preCCV": true,
	  "connection_id": "connection-0"
	}
	`,
}

// creates ccv consumer genesis data content for a given version
// as it was exported from a provider
func createConsumerDataGenesisFile(t *testing.T, version string) string {
	t.Helper()
	filePath := filepath.Join(t.TempDir(), fmt.Sprintf("ConsumerGenesis_%s.json", version))
	err := os.WriteFile(
		filePath,
		[]byte(consumerGenesisStates[version]),
		fs.FileMode(0o644))
	require.NoError(t, err, "Error creating source genesis data for version %s", version)
	return filePath
}

func getClientCtx() client.Context {
	encodingConfig := app.MakeTestEncodingConfig()
	return client.Context{}.
		WithCodec(encodingConfig.Codec).
		WithInterfaceRegistry(encodingConfig.InterfaceRegistry).
		WithTxConfig(encodingConfig.TxConfig).
		WithLegacyAmino(encodingConfig.Amino).
		WithInput(os.Stdin).
		WithAccountRetriever(types.AccountRetriever{})
}

// getGenesisTransformCmd sets up client context and returns
// genesis transformation command (UUT)
func getGenesisTransformCmd() (*cobra.Command, error) {
	cmd := app.GetConsumerGenesisTransformCmd()
	clientCtx := getClientCtx()
	ctx := context.WithValue(context.Background(), client.ClientContextKey, &clientCtx)
	cmd.SetContext(ctx)
	err := client.SetCmdClientContext(cmd, clientCtx)
	return cmd, err
}

// transformConsumerGenesis transform json content in a given file and return
// the consumer genesis transformation result or an error
// - filePath    file with consumer genesis content in json format
// - version     ICS version to which the data should be transformed to
func transformConsumerGenesis(filePath string, version *string) ([]byte, error) {
	cmd, err := getGenesisTransformCmd()
	if err != nil {
		return nil, fmt.Errorf("Error setting up transformation command: %s", err)
	}

	args := []string{}
	if version != nil {
		args = append(args, fmt.Sprintf("--to=%s", *version))
	}
	args = append(args, filePath)

	cmd.SetArgs(args)

	result := new(bytes.Buffer)
	cmd.SetOutput(result)
	_, err = cmd.ExecuteC()
	if err != nil {
		return nil, fmt.Errorf("Error running transformation command: %v", err)
	}
	return result.Bytes(), nil
}

// Check transformation of provider v6.3.x implementation to consumer v5.x
func TestConsumerGenesisTransformationV63xToV5x(t *testing.T) {
	CheckGenesisTransform(t, Provider_v6_3_x, Consumer_v5_x_x)
}

// Check transformation of provider v6.3.x implementation to consumer <v4.5.x
func TestConsumerGenesisTransformationV63xToV4x(t *testing.T) {
	CheckGenesisTransform(t, Provider_v6_3_x, Consumer_v4_x_x)
}

// Check transformation of provider v6.4.x implementation to consumer v4.x.x
func TestConsumerGenesisTransformationV64xToV4xx(t *testing.T) {
	CheckGenesisTransform(t, Provider_v6_4_x, Consumer_v4_x_x)
}

// Check transformation of provider v6.4.x implementation to consumer v5.x.x
func TestConsumerGenesisTransformationV64xToV5xx(t *testing.T) {
	CheckGenesisTransform(t, Provider_v6_4_x, Consumer_v5_x_x)
}

// Check transformation of provider v6.4.x implementation to consumer v4.5.x
func TestConsumerGenesisTransformationV64xToV45x(t *testing.T) {
	CheckGenesisTransform(t, Provider_v6_4_x, Consumer_v4_5_x)
}

// Check transformation of provider v6.4.x implementation to consumer v6.x.x
func TestConsumerGenesisTransformationV64xToV6xx(t *testing.T) {
	CheckGenesisTransform(t, Provider_v6_4_x, Consumer_v6_x_x)
}

// CheckGenesisTransform checks that the transformation of consumer genesis data
// from a given source version to a target version is successful
func CheckGenesisTransform(t *testing.T, sourceVersion string, targetVersion string) {
	filePath := createConsumerDataGenesisFile(t, sourceVersion)
	defer os.Remove(filePath)

	var srcGenesis ccvtypes.ConsumerGenesisState
	ctx := getClientCtx()
	err := ctx.Codec.UnmarshalJSON([]byte(consumerGenesisStates[sourceVersion]), &srcGenesis)
	require.NoError(t, err)

	result, err := transformConsumerGenesis(filePath, &targetVersion)
	require.NoError(t, err)

	resultGenesis := ccvtypes.ConsumerGenesisState{}
	err = ctx.Codec.UnmarshalJSON(result, &resultGenesis)
	require.NoError(t, err)

	resultRaw := map[string]json.RawMessage{}
	err = json.Unmarshal(result, &resultRaw)
	require.NoError(t, err)

	// Check that resultRaw has no subelement consumer_id
	paramsRaw, found := resultRaw["params"]
	require.True(t, found, "params field not found in result genesis")

	params := map[string]json.RawMessage{}
	err = json.Unmarshal(paramsRaw, &params)
	require.NoError(t, err)

	_, consumerIdFound := params["consumer_id"]
	require.Equal(t, shouldContainConsumerId(targetVersion), consumerIdFound)

	// Check for no connection_id
	_, found = resultRaw["connection_id"]
	require.Equal(t, shouldContainConnectionId(targetVersion), found)

	// Iterate over all fields of ConsumerParams and check:
	// - that they match between source and result genesis
	// - that ConsumerId is empty in the result genesis
	srcParams := reflect.ValueOf(srcGenesis.Params)
	resultParams := reflect.ValueOf(resultGenesis.Params)
	srcType := srcParams.Type()
	for i := 0; i < srcParams.NumField(); i++ {
		fieldName := srcType.Field(i).Name
		srcField := srcParams.Field(i).Interface()
		// srcType and resultType are the same so we can use index 'i' to get the field from resultParams
		resultField := resultParams.Field(i).Interface()
		if fieldName == "ConsumerId" && !shouldContainConsumerId(targetVersion) {
			// ConsumerId is not present in v5.x => expect empty string when unmarshalled to v6
			require.EqualValues(t, "", resultField, "Field %s does not match", fieldName)
		} else if fieldName == "ConnectionId" && !shouldContainConnectionId(targetVersion) {
			// ConnectionId is not present in <v6.4.x => expect empty string when unmarshalled it
			require.EqualValues(t, "", resultField, "Field %s does not match", fieldName)
		} else {
			require.EqualValues(t, srcField, resultField, "Field %s does not match", fieldName)
		}
	}

	// Iterate over all fields of ConsumerGenesisState and check
	// - that they match between source and result genesis
	// - that ConsumerId is empty in the result genesis
	srcParams = reflect.ValueOf(srcGenesis)
	resultParams = reflect.ValueOf(resultGenesis)
	srcType = srcParams.Type()
	require.Equal(t, srcParams.Type(), resultParams.Type(), "Different types of source and result genesis")
	for i := 0; i < srcParams.NumField(); i++ {
		fieldName := srcType.Field(i).Name
		// Skip Params field as it was checked above
		if fieldName == "Params" || fieldName == "ConnectionId" {
			continue
		}
		srcField := srcParams.Field(i).Interface()
		// srcType and resultType are the same so we can use index 'i' to get the field from resultParams
		resultField := resultParams.Field(i).Interface()
		require.EqualValues(t, srcField, resultField, "Field %s does not match", fieldName)
	}
}

func shouldContainConsumerId(version string) bool {
	switch version {
	case Consumer_v6_x_x, Consumer_v4_5_x:
		return true
	case Consumer_v5_x_x, Consumer_v4_x_x:
		return false
	}

	return false
}

func shouldContainConnectionId(version string) bool {
	switch version {
	case Consumer_v4_x_x, Consumer_v4_5_x, Consumer_v5_x_x, Consumer_v6_x_x:
		return false
		// future greater versions will contain this fields and should return true
	}

	return false
}
