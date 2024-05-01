package types_test

import (
	fmt "fmt"
	"testing"
	"time"

	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	ibctmtypes "github.com/cosmos/ibc-go/v7/modules/light-clients/07-tendermint"
	"github.com/golang/protobuf/proto" //nolint:staticcheck // see: https://github.com/cosmos/interchain-security/issues/236
	"github.com/stretchr/testify/require"

	"github.com/cosmos/cosmos-sdk/codec"
	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	govv1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1"
	govv1beta1 "github.com/cosmos/cosmos-sdk/x/gov/types/v1beta1"

	"github.com/cosmos/interchain-security/v5/x/ccv/provider/types"
)

func TestConsumerAdditionProposalValidateBasic(t *testing.T) {
	initialHeight := clienttypes.NewHeight(2, 3)

	testCases := []struct {
		name     string
		proposal govv1beta1.Content
		expPass  bool
	}{
		{
			"success",
			types.NewConsumerAdditionProposal("title", "description", "chainID", initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Now(),
				"0.75",
				10,
				"",
				10000,
				100000000000,
				100000000000,
				100000000000,
				0,
				0,
				0,
				nil,
				nil,
			),
			true,
		},
		{
			"success with 0.0 fraction",
			types.NewConsumerAdditionProposal("title", "description", "chainID", initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Now(),
				"0.0", // fraction can be 0.0 but not empty
				10,
				"",
				10000,
				100000000000,
				100000000000,
				100000000000,
				0,
				0,
				0,
				nil,
				nil,
			),
			true,
		},
		{
			"fails validate abstract - empty title",
			types.NewConsumerAdditionProposal(" ", "description", "chainID", initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Now(),
				"0.75",
				10,
				"",
				10000,
				100000000000,
				100000000000,
				100000000000,
				0,
				0,
				0,
				nil,
				nil,
			),
			false,
		},
		{
			"chainID is empty",
			types.NewConsumerAdditionProposal("title", "description", " ", initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Now(),
				"0.75",
				10,
				"",
				10000,
				100000000000,
				100000000000,
				100000000000,
				0,
				0,
				0,
				nil,
				nil,
			),
			false,
		},
		{
			"initial height is zero",
			&types.ConsumerAdditionProposal{
				Title:                             "title",
				Description:                       "description",
				ChainId:                           "chainID",
				InitialHeight:                     clienttypes.Height{},
				GenesisHash:                       []byte("gen_hash"),
				BinaryHash:                        []byte("bin_hash"),
				SpawnTime:                         time.Now(),
				BlocksPerDistributionTransmission: 10,
				CcvTimeoutPeriod:                  100000000000,
				TransferTimeoutPeriod:             100000000000,
				ConsumerRedistributionFraction:    "0.75",
				DistributionTransmissionChannel:   "",
				HistoricalEntries:                 10000,
				UnbondingPeriod:                   100000000000,
			},
			false,
		},
		{
			"genesis hash is empty",
			types.NewConsumerAdditionProposal("title", "description", "chainID", initialHeight, []byte(""), []byte("bin_hash"), time.Now(),
				"0.75",
				10,
				"",
				10000,
				100000000000,
				100000000000,
				100000000000,
				0,
				0,
				0,
				nil,
				nil,
			),
			false,
		},
		{
			"binary hash is empty",
			types.NewConsumerAdditionProposal("title", "description", "chainID", initialHeight, []byte("gen_hash"), []byte(""), time.Now(),
				"0.75",
				10,
				"",
				10000,
				100000000000,
				100000000000,
				100000000000,
				0,
				0,
				0,
				nil,
				nil),
			false,
		},
		{
			"spawn time is zero",
			types.NewConsumerAdditionProposal("title", "description", "chainID", initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Time{},
				"0.75",
				10,
				"",
				10000,
				100000000000,
				100000000000,
				100000000000,
				0,
				0,
				0,
				nil,
				nil,
			),
			false,
		},
		{
			"consumer redistribution fraction is invalid",
			types.NewConsumerAdditionProposal("title", "description", "chainID", initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Now(),
				"", // fraction can be 0.0 but not empty
				10,
				"",
				10000,
				100000000000,
				100000000000,
				100000000000,
				0,
				0,
				0,
				nil,
				nil,
			),
			false,
		},
		{
			"blocks per distribution transmission is invalid",
			types.NewConsumerAdditionProposal("title", "description", "chainID", initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Now(),
				"0.75",
				0,
				"",
				100000000000,
				10000,
				100000000000,
				100000000000,
				0,
				0,
				0,
				nil,
				nil,
			),
			false,
		},
		{
			"distribution transmission channel is invalid",
			types.NewConsumerAdditionProposal("title", "description", "chainID", initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Now(),
				"0.75",
				10,
				"badchannel/",
				10000,
				100000000000,
				100000000000,
				100000000000,
				0,
				0,
				0,
				nil,
				nil,
			),
			false,
		},
		{
			"historical entries is invalid",
			types.NewConsumerAdditionProposal("title", "description", "chainID", initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Now(),
				"0.75",
				10,
				"",
				-2,
				100000000000,
				100000000000,
				100000000000,
				0,
				0,
				0,
				nil,
				nil,
			),
			false,
		},
		{
			"ccv timeout period is invalid",
			types.NewConsumerAdditionProposal("title", "description", "chainID", initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Now(),
				"0.75",
				10,
				"",
				10000,
				0,
				100000000000,
				100000000000,
				0,
				0,
				0,
				nil,
				nil,
			),
			false,
		},
		{
			"transfer timeout period is invalid",
			types.NewConsumerAdditionProposal("title", "description", "chainID", initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Now(),
				"0.75",
				10,
				"",
				10000,
				100000000000,
				0,
				100000000000,
				0,
				0,
				0,
				nil,
				nil,
			),
			false,
		},
		{
			"unbonding period is invalid",
			types.NewConsumerAdditionProposal("title", "description", "chainID", initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Now(),
				"0.75",
				10,
				"",
				10000,
				100000000000,
				100000000000,
				0,
				0,
				0,
				0,
				nil,
				nil,
			),
			false,
		},
	}

	for _, tc := range testCases {

		err := tc.proposal.ValidateBasic()
		if tc.expPass {
			require.NoError(t, err, "valid case: %s should not return error. got %w", tc.name, err)
		} else {
			require.Error(t, err, "invalid case: '%s' must return error but got none", tc.name)
		}
	}
}

func TestMarshalConsumerAdditionProposal(t *testing.T) {
	content := types.NewConsumerAdditionProposal("title", "description", "chainID", clienttypes.NewHeight(0, 1), []byte("gen_hash"), []byte("bin_hash"), time.Now().UTC(),
		"0.75",
		10,
		"",
		10000,
		100000000000,
		100000000000,
		100000000000,
		0,
		0,
		0,
		nil,
		nil)

	cccp, ok := content.(*types.ConsumerAdditionProposal)
	require.True(t, ok)

	// create codec
	ir := codectypes.NewInterfaceRegistry()
	types.RegisterInterfaces(ir)
	govv1.RegisterInterfaces(ir)
	clienttypes.RegisterInterfaces(ir)
	ibctmtypes.RegisterInterfaces(ir)
	cdc := codec.NewProtoCodec(ir)

	// marshal proposal
	bz, err := cdc.MarshalJSON(cccp)
	require.NoError(t, err)

	// unmarshal proposal
	newCccp := &types.ConsumerAdditionProposal{}
	err = cdc.UnmarshalJSON(bz, newCccp)
	require.NoError(t, err)

	require.True(t, proto.Equal(cccp, newCccp), "unmarshalled proposal does not equal original proposal")
}

func TestConsumerAdditionProposalString(t *testing.T) {
	initialHeight := clienttypes.NewHeight(2, 3)
	spawnTime := time.Now()
	proposal := types.NewConsumerAdditionProposal(
		"title",
		"description",
		"chainID",
		initialHeight,
		[]byte("gen_hash"),
		[]byte("bin_hash"),
		spawnTime,
		"0.75",
		10001,
		"",
		500000,
		100000000000,
		10000000000,
		100000000000,
		0,
		0,
		0,
		[]string{},
		[]string{})

	expect := fmt.Sprintf(`CreateConsumerChain Proposal
	Title: title
	Description: description
	ChainID: chainID
	InitialHeight: %s
	GenesisHash: %s
	BinaryHash: %s
	SpawnTime: %s
	ConsumerRedistributionFraction: %s
	BlocksPerDistributionTransmission: %d
	DistributionTransmissionChannel: %s
	HistoricalEntries: %d
	CcvTimeoutPeriod: %d
	TransferTimeoutPeriod: %d
	UnbondingPeriod: %d`, initialHeight, []byte("gen_hash"), []byte("bin_hash"), spawnTime,
		"0.75",
		10001,
		"",
		500000,
		100000000000,
		10000000000,
		100000000000)

	require.Equal(t, expect, proposal.String(), "string method for ConsumerAdditionProposal returned unexpected string")
}

func TestChangeRewardDenomsProposalValidateBasic(t *testing.T) {
	tcs := []struct {
		name        string
		proposal    govv1beta1.Content
		expectError bool
		expectPanic bool
	}{
		{
			name: "invalid change reward denoms proposal, none to add or remove",
			proposal: types.NewChangeRewardDenomsProposal(
				"title", "description", []string{}, []string{}),
			expectError: true,
		},
		{
			name: "invalid change reward denoms proposal, same denom in both sets",
			proposal: types.NewChangeRewardDenomsProposal(
				"title", "description", []string{"denom1"}, []string{"denom1"}),
			expectError: true,
		},
		{
			name: "valid change reward denoms proposal",
			proposal: types.NewChangeRewardDenomsProposal(
				"title", "description", []string{"denom1"}, []string{"denom2"}),
			expectError: false,
		},
		{
			name: "invalid prop, invalid denom, will panic",
			proposal: types.NewChangeRewardDenomsProposal(
				"title", "description", []string{"!@blah"}, []string{"denom2"}),
			expectPanic: true,
		},
	}

	for _, tc := range tcs {
		t.Run(tc.name, func(t *testing.T) {
			if tc.expectPanic {
				require.Panics(t, func() { tc.proposal.ValidateBasic() })
				return
			}
			err := tc.proposal.ValidateBasic()
			if tc.expectError {
				require.Error(t, err)
				return
			}
			require.NoError(t, err)
		})
	}
}
