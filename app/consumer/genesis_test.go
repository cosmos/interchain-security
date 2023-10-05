package app_test

import (
	"bytes"
	"context"
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
)

// Testdata mapping consumer genesis exports to a provider module version as
// used by transformation function for consumer genesis content.
var consumerGenesisStates map[string]string = map[string]string{
	"v2": `
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

// Setup client context
func getGenesisTransformCmd() (*cobra.Command, error) {
	cmd := app.GetConsumerGenesisTransformCmd()
	clientCtx := getClientCtx()
	ctx := context.WithValue(context.Background(), client.ClientContextKey, &clientCtx)
	cmd.SetContext(ctx)
	err := client.SetCmdClientContext(cmd, clientCtx)
	return cmd, err
}

// Check transformation of a version 2 ConsumerGenesis export to
// consumer genesis json format used by current consumer implementation.
func TestConsumerGenesisTransformationV2(t *testing.T) {
	version := "v2"
	filePath := filepath.Join(t.TempDir(), "oldConsumerGenesis.json")

	err := os.WriteFile(
		filePath,
		[]byte(consumerGenesisStates[version]),
		fs.FileMode(0o644))
	require.NoError(t, err)
	defer os.Remove(filePath)

	cmd, err := getGenesisTransformCmd()
	require.NoError(t, err, "Error setting up transformation command: %s", err)
	cmd.SetArgs([]string{version, filePath})

	output := new(bytes.Buffer)
	cmd.SetOutput(output)
	require.NoError(t, err)
	_, err = cmd.ExecuteC()
	require.NoError(t, err)

	consumerGenesis := consumerTypes.GenesisState{}

	bz := output.Bytes()
	ctx := client.GetClientContextFromCmd(cmd)
	err = ctx.Codec.UnmarshalJSON(bz, &consumerGenesis)
	require.NoError(t, err, "Error unmarshalling transformed genesis state :%s", err)

	// Some basic sanity checks on the content.
	require.Nil(t, consumerGenesis.ProviderClientState)
	require.NotNil(t, consumerGenesis.Provider.ClientState)
	require.Equal(t, "cosmoshub-4", consumerGenesis.Provider.ClientState.ChainId)

	require.Nil(t, consumerGenesis.ProviderConsensusState)
	require.NotNil(t, consumerGenesis.Provider.ConsensusState)
	require.Equal(t, time.Date(2023, time.May, 8, 11, 0, 1, 563901871, time.UTC),
		consumerGenesis.Provider.ConsensusState.Timestamp)

	require.Empty(t, consumerGenesis.InitialValSet)
	require.NotEmpty(t, consumerGenesis.Provider.InitialValSet)
}
