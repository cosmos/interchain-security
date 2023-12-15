package app_test

import (
	"bytes"
	"context"
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"testing"
	"time"

	"github.com/spf13/cobra"
	"github.com/stretchr/testify/require"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/cosmos-sdk/x/auth/types"

	app "github.com/cosmos/interchain-security/v3/app/consumer"
	consumerTypes "github.com/cosmos/interchain-security/v3/x/ccv/consumer/types"
	ccvtypes "github.com/cosmos/interchain-security/v3/x/ccv/types"
)

// Testdata mapping consumer genesis exports to a provider module version as
// used by transformation function for consumer genesis content.
var consumerGenesisStates map[string]string = map[string]string{
	"v2.x": `
	{
		"params": {
		  "enabled": true,
		  "blocks_per_distribution_transmission": "1500",
		  "distribution_transmission_channel": "",
		  "provider_fee_pool_addr_str": "",
		  "ccv_timeout_period": "2419200s",
		  "transfer_timeout_period": "3600s",
		  "consumer_redistribution_fraction": "0.75",
		  "historical_entries": "10000",
		  "unbonding_period": "1728000s",
		  "soft_opt_out_threshold": "",
		  "reward_denoms": [],
		  "provider_reward_denoms": []
		},
		"provider_client_id": "",
		"provider_channel_id": "",
		"new_chain": true,
		"provider_client_state": {
		  "chain_id": "cosmoshub-4",
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
			"revision_number": "4",
			"revision_height": "15211521"
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
			  "min_depth": 0
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
			  "min_depth": 0
			}
		  ],
		  "upgrade_path": [
			"upgrade",
			"upgradedIBCState"
		  ],
		  "allow_update_after_expiry": true,
		  "allow_update_after_misbehaviour": true
		},
		"provider_consensus_state": {
		  "timestamp": "2023-05-08T11:00:01.563901871Z",
		  "root": {
			"hash": "qKVnVSXlsjDHC8ekKcy/0zSjzr3YekCurld9R4W07EI="
		  },
		  "next_validators_hash": "E08978F493101A3C5D459FB3087B8CFBA9E82D7A1FE1441E7D77E11AC0586BAC"
		},
		"maturing_packets": [],
		"initial_val_set": [
		  {
			"pub_key": {
			  "ed25519": "cOQZvh/h9ZioSeUMZB/1Vy1Xo5x2sjrVjlE/qHnYifM="
			},
			"power": "2345194"
		  },
		  {
			"pub_key": {
			  "ed25519": "vGSKfbQyKApvBhinpOOA0XQAdjxceihYNwtGskfZGyQ="
			},
			"power": "463811"
		  }
		],
		"height_to_valset_update_id": [],
		"outstanding_downtime_slashing": [],
		"pending_consumer_packets": {
		  "list": []
		},
		"last_transmission_block_height": {
		  "height": "0"
		},
		"preCCV": false
	  }

	`,
	"v3.3.x": `
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
		  "soft_opt_out_threshold": "0.05",
		  "reward_denoms": [],
		  "provider_reward_denoms": []
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
			  "revision_height": "20"
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
			"timestamp": "2023-12-15T09:25:46.098392003Z",
			"root": {
			  "hash": "0aoNOwWy67aQKs2r+FcDf2RxIq2UJtBb3g9ZWn0Gkas="
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
	"v4.x": `
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
		  "soft_opt_out_threshold": "0.05",
		  "reward_denoms": [],
		  "provider_reward_denoms": [],
		  "retry_delay_period": "3600s"
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
			  "revision_height": "20"
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
			"timestamp": "2023-12-15T09:57:02.687079137Z",
			"root": {
			  "hash": "EH9YbrWC3Qojy8ycl5GhOdVEC1ifPIGUUItL70bTkHo="
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
}

// creates ccv consumer genesis data content for a given version
// as it was exported from a provider
func createConsumerDataGenesisFile(t *testing.T, version string) string {
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
		return nil, fmt.Errorf("Error runnning transformation command: %v", err)
	}
	return result.Bytes(), nil
}

// Check transformation of a version 2 ConsumerGenesis export to
// consumer genesis json format used by current consumer implementation.
func TestConsumerGenesisTransformationFromV2ToCurrent(t *testing.T) {
	version := "v2.x"
	ctx := getClientCtx()

	srcGenesis := consumerTypes.GenesisState{}
	err := ctx.Codec.UnmarshalJSON([]byte(consumerGenesisStates[version]), &srcGenesis)
	require.NoError(t, err, "Error parsing old version of ccv genesis content for consumer")

	filePath := createConsumerDataGenesisFile(t, version)
	defer os.Remove(filePath)
	resultGenesis := consumerTypes.GenesisState{}
	result, err := transformConsumerGenesis(filePath, nil)
	require.NoError(t, err)
	err = ctx.Codec.UnmarshalJSON(result, &resultGenesis)
	require.NoError(t, err)

	// Some basic sanity checks on the content.
	require.NotNil(t, resultGenesis.Provider.ClientState)
	require.Equal(t, "cosmoshub-4", resultGenesis.Provider.ClientState.ChainId)

	require.Empty(t, resultGenesis.InitialValSet)
	require.NotEmpty(t, resultGenesis.Provider.InitialValSet)
	require.Equal(t, resultGenesis.Params.RetryDelayPeriod, ccvtypes.DefaultRetryDelayPeriod)

	// Check params: retry_delay_period prevents direct comparison
	require.EqualValues(t, srcGenesis.Params.Enabled, resultGenesis.Params.Enabled)
	require.EqualValues(t, srcGenesis.Params.BlocksPerDistributionTransmission, resultGenesis.Params.BlocksPerDistributionTransmission)
	require.EqualValues(t, srcGenesis.Params.DistributionTransmissionChannel, resultGenesis.Params.DistributionTransmissionChannel)
	require.EqualValues(t, srcGenesis.Params.ProviderFeePoolAddrStr, resultGenesis.Params.ProviderFeePoolAddrStr)
	require.EqualValues(t, srcGenesis.Params.CcvTimeoutPeriod, resultGenesis.Params.CcvTimeoutPeriod)
	require.EqualValues(t, srcGenesis.Params.TransferTimeoutPeriod, resultGenesis.Params.TransferTimeoutPeriod)
	require.EqualValues(t, srcGenesis.Params.ConsumerRedistributionFraction, resultGenesis.Params.ConsumerRedistributionFraction)
	require.EqualValues(t, srcGenesis.Params.HistoricalEntries, resultGenesis.Params.HistoricalEntries)
	require.EqualValues(t, srcGenesis.Params.UnbondingPeriod, resultGenesis.Params.UnbondingPeriod)
	require.EqualValues(t, srcGenesis.Params.SoftOptOutThreshold, resultGenesis.Params.SoftOptOutThreshold)
	require.EqualValues(t, srcGenesis.Params.RewardDenoms, resultGenesis.Params.RewardDenoms)
	require.EqualValues(t, srcGenesis.Params.ProviderRewardDenoms, resultGenesis.Params.ProviderRewardDenoms)

	require.Equal(t, srcGenesis.ProviderClientState, resultGenesis.Provider.ClientState)
	require.Nil(t, resultGenesis.ProviderClientState)

	require.Equal(t, srcGenesis.Provider.ConsensusState, resultGenesis.ProviderConsensusState)
	require.Nil(t, resultGenesis.ProviderConsensusState)

	require.Equal(t, srcGenesis.NewChain, resultGenesis.NewChain)
	require.Equal(t, "", resultGenesis.ProviderClientId)
	require.Equal(t, "", resultGenesis.ProviderChannelId)
	require.Equal(t, srcGenesis.InitialValSet, resultGenesis.Provider.InitialValSet)
	require.Empty(t, resultGenesis.InitialValSet)

}

// Check transformation of provider v3.3.x implementation to consumer V2
func TestConsumerGenesisTransformationV330ToV2(t *testing.T) {
	version := "v3.3.x"
	filePath := createConsumerDataGenesisFile(t, version)
	defer os.Remove(filePath)

	var srcGenesis consumerTypes.GenesisState
	ctx := getClientCtx()
	err := ctx.Codec.UnmarshalJSON([]byte(consumerGenesisStates[version]), &srcGenesis)
	require.NoError(t, err)

	targetVersion := "v2.x"
	result, err := transformConsumerGenesis(filePath, &targetVersion)
	require.NoError(t, err)

	resultGenesis := consumerTypes.GenesisState{}
	err = ctx.Codec.UnmarshalJSON(result, &resultGenesis)
	require.NoError(t, err)

	require.Equal(t, srcGenesis.Params, resultGenesis.Params)
	require.Equal(t, srcGenesis.Provider.ClientState, resultGenesis.ProviderClientState)
	require.Equal(t, srcGenesis.Provider.ConsensusState, resultGenesis.ProviderConsensusState)
	require.Equal(t, srcGenesis.NewChain, resultGenesis.NewChain)
	require.Equal(t, "", resultGenesis.ProviderClientId)
	require.Equal(t, "", resultGenesis.ProviderChannelId)

}

// Check transformation of provider v3.3.x implementation to current consumer version
func TestConsumerGenesisTransformationV330ToCurrent(t *testing.T) {
	version := "v3.3.x"
	filePath := createConsumerDataGenesisFile(t, version)
	defer os.Remove(filePath)

	var srcGenesis consumerTypes.GenesisState
	ctx := getClientCtx()
	err := ctx.Codec.UnmarshalJSON([]byte(consumerGenesisStates[version]), &srcGenesis)
	require.NoError(t, err)

	result, err := transformConsumerGenesis(filePath, nil)
	require.NoError(t, err)

	resultGenesis := consumerTypes.GenesisState{}
	err = ctx.Codec.UnmarshalJSON(result, &resultGenesis)
	require.NoError(t, err)

	require.Equal(t, srcGenesis.Params.Enabled, resultGenesis.Params.Enabled)
	require.Equal(t, srcGenesis.Params.BlocksPerDistributionTransmission, resultGenesis.Params.BlocksPerDistributionTransmission)
	require.Equal(t, srcGenesis.Params.DistributionTransmissionChannel, resultGenesis.Params.DistributionTransmissionChannel)
	require.Equal(t, srcGenesis.Params.ProviderFeePoolAddrStr, resultGenesis.Params.ProviderFeePoolAddrStr)
	require.Equal(t, srcGenesis.Params.CcvTimeoutPeriod, resultGenesis.Params.CcvTimeoutPeriod)
	require.Equal(t, srcGenesis.Params.TransferTimeoutPeriod, resultGenesis.Params.TransferTimeoutPeriod)
	require.Equal(t, srcGenesis.Params.ConsumerRedistributionFraction, resultGenesis.Params.ConsumerRedistributionFraction)
	require.Equal(t, srcGenesis.Params.HistoricalEntries, resultGenesis.Params.HistoricalEntries)
	require.Equal(t, srcGenesis.Params.UnbondingPeriod, resultGenesis.Params.UnbondingPeriod)
	require.Equal(t, srcGenesis.Params.SoftOptOutThreshold, resultGenesis.Params.SoftOptOutThreshold)
	require.Equal(t, srcGenesis.Params.RewardDenoms, resultGenesis.Params.RewardDenoms)
	require.Equal(t, srcGenesis.Params.ProviderRewardDenoms, resultGenesis.Params.ProviderRewardDenoms)

	require.Equal(t, resultGenesis.Params.RetryDelayPeriod, ccvtypes.DefaultRetryDelayPeriod)

	require.Equal(t, srcGenesis.Provider.ClientState, resultGenesis.Provider.ClientState)
	require.Nil(t, resultGenesis.ProviderClientState)
	require.Nil(t, resultGenesis.ProviderConsensusState)

	require.Equal(t, srcGenesis.Provider.ConsensusState, resultGenesis.Provider.ConsensusState)
	require.Equal(t, srcGenesis.NewChain, resultGenesis.NewChain)
	require.Equal(t, "", resultGenesis.ProviderClientId)
	require.Equal(t, "", resultGenesis.ProviderChannelId)
}

// Check transformation of provider v4.x implementation to consumer V2
func TestConsumerGenesisTransformationV4ToV2(t *testing.T) {
	version := "v4.x"
	filePath := createConsumerDataGenesisFile(t, version)
	defer os.Remove(filePath)

	var srcGenesis consumerTypes.GenesisState
	ctx := getClientCtx()
	err := ctx.Codec.UnmarshalJSON([]byte(consumerGenesisStates[version]), &srcGenesis)
	require.NoError(t, err)

	targetVersion := "v2.x"
	result, err := transformConsumerGenesis(filePath, &targetVersion)
	require.NoError(t, err)

	resultGenesis := consumerTypes.GenesisState{}
	err = ctx.Codec.UnmarshalJSON(result, &resultGenesis)
	require.NoError(t, err)

	// Check params: retry_delay_period prevents direct comparison
	require.EqualValues(t, srcGenesis.Params.Enabled, resultGenesis.Params.Enabled)
	require.EqualValues(t, srcGenesis.Params.BlocksPerDistributionTransmission, resultGenesis.Params.BlocksPerDistributionTransmission)
	require.EqualValues(t, srcGenesis.Params.DistributionTransmissionChannel, resultGenesis.Params.DistributionTransmissionChannel)
	require.EqualValues(t, srcGenesis.Params.ProviderFeePoolAddrStr, resultGenesis.Params.ProviderFeePoolAddrStr)
	require.EqualValues(t, srcGenesis.Params.CcvTimeoutPeriod, resultGenesis.Params.CcvTimeoutPeriod)
	require.EqualValues(t, srcGenesis.Params.TransferTimeoutPeriod, resultGenesis.Params.TransferTimeoutPeriod)
	require.EqualValues(t, srcGenesis.Params.ConsumerRedistributionFraction, resultGenesis.Params.ConsumerRedistributionFraction)
	require.EqualValues(t, srcGenesis.Params.HistoricalEntries, resultGenesis.Params.HistoricalEntries)
	require.EqualValues(t, srcGenesis.Params.UnbondingPeriod, resultGenesis.Params.UnbondingPeriod)
	require.EqualValues(t, srcGenesis.Params.SoftOptOutThreshold, resultGenesis.Params.SoftOptOutThreshold)
	require.EqualValues(t, srcGenesis.Params.RewardDenoms, resultGenesis.Params.RewardDenoms)
	require.EqualValues(t, srcGenesis.Params.ProviderRewardDenoms, resultGenesis.Params.ProviderRewardDenoms)
	require.Equal(t, resultGenesis.Params.RetryDelayPeriod, time.Duration(0))

	require.Equal(t, srcGenesis.Provider.ClientState, resultGenesis.ProviderClientState)
	require.Nil(t, resultGenesis.Provider.ClientState)
	require.Equal(t, srcGenesis.Provider.ConsensusState, resultGenesis.ProviderConsensusState)
	require.Nil(t, resultGenesis.Provider.ConsensusState)
	require.Equal(t, "", resultGenesis.ProviderClientId)
	require.Equal(t, "", resultGenesis.ProviderChannelId)

	require.Equal(t, 0, len(resultGenesis.Provider.InitialValSet))
	require.Equal(t, srcGenesis.Provider.InitialValSet, resultGenesis.InitialValSet)
	require.Empty(t, resultGenesis.Provider.InitialValSet)

	require.Equal(t, srcGenesis.NewChain, resultGenesis.NewChain)
}

// Check transformation of provider v3.3.x implementation to consumer V2
func TestConsumerGenesisTransformationV4ToV33(t *testing.T) {
	version := "v4.x"
	filePath := createConsumerDataGenesisFile(t, version)
	defer os.Remove(filePath)

	var srcGenesis ccvtypes.ConsumerGenesisState
	ctx := getClientCtx()
	err := ctx.Codec.UnmarshalJSON([]byte(consumerGenesisStates[version]), &srcGenesis)
	require.NoError(t, err)

	targetVersion := "v3.3.x"
	result, err := transformConsumerGenesis(filePath, &targetVersion)
	require.NoError(t, err)
	resultGenesis := consumerTypes.GenesisState{} //Only difference to v33 is no RetryDelayPeriod
	err = ctx.Codec.UnmarshalJSON(result, &resultGenesis)
	require.NoError(t, err)

	// Check params: retry_delay_period prevents direct comparison
	require.EqualValues(t, srcGenesis.Params.Enabled, resultGenesis.Params.Enabled)
	require.EqualValues(t, srcGenesis.Params.BlocksPerDistributionTransmission, resultGenesis.Params.BlocksPerDistributionTransmission)
	require.EqualValues(t, srcGenesis.Params.DistributionTransmissionChannel, resultGenesis.Params.DistributionTransmissionChannel)
	require.EqualValues(t, srcGenesis.Params.ProviderFeePoolAddrStr, resultGenesis.Params.ProviderFeePoolAddrStr)
	require.EqualValues(t, srcGenesis.Params.CcvTimeoutPeriod, resultGenesis.Params.CcvTimeoutPeriod)
	require.EqualValues(t, srcGenesis.Params.TransferTimeoutPeriod, resultGenesis.Params.TransferTimeoutPeriod)
	require.EqualValues(t, srcGenesis.Params.ConsumerRedistributionFraction, resultGenesis.Params.ConsumerRedistributionFraction)
	require.EqualValues(t, srcGenesis.Params.HistoricalEntries, resultGenesis.Params.HistoricalEntries)
	require.EqualValues(t, srcGenesis.Params.UnbondingPeriod, resultGenesis.Params.UnbondingPeriod)
	require.EqualValues(t, srcGenesis.Params.SoftOptOutThreshold, resultGenesis.Params.SoftOptOutThreshold)
	require.EqualValues(t, srcGenesis.Params.RewardDenoms, resultGenesis.Params.RewardDenoms)
	require.EqualValues(t, srcGenesis.Params.ProviderRewardDenoms, resultGenesis.Params.ProviderRewardDenoms)

	require.Equal(t, srcGenesis.Provider.ClientState, resultGenesis.Provider.ClientState)
	require.Nil(t, resultGenesis.ProviderClientState)

	require.Equal(t, srcGenesis.Provider.ConsensusState, resultGenesis.Provider.ConsensusState)
	require.Nil(t, resultGenesis.ProviderConsensusState)

	require.Equal(t, srcGenesis.NewChain, resultGenesis.NewChain)
	require.Equal(t, "", resultGenesis.ProviderClientId)
	require.Equal(t, "", resultGenesis.ProviderChannelId)
	require.Equal(t, srcGenesis.Provider.InitialValSet, resultGenesis.Provider.InitialValSet)
	require.Empty(t, resultGenesis.InitialValSet)
}
