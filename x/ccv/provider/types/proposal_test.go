package types_test

import (
	fmt "fmt"
	"testing"
	"time"

	"github.com/golang/protobuf/proto"
	"github.com/stretchr/testify/require"

	"github.com/cosmos/cosmos-sdk/codec"
	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
)

func TestValidateBasic(t *testing.T) {
	var (
		proposal govtypes.Content
		err      error
	)
	initialHeight := clienttypes.NewHeight(2, 3)

	testCases := []struct {
		name     string
		malleate func()
		expPass  bool
	}{
		{
			"success", func() {
				proposal, err = types.NewCreateConsumerChainProposal("title", "description", "chainID", initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Now())
				require.NoError(t, err)
			}, true,
		},
		{
			"fails validate abstract - empty title", func() {
				proposal, err = types.NewCreateConsumerChainProposal(" ", "description", "chainID", initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Now())
				require.NoError(t, err)
			}, false,
		},
		{
			"chainID is empty", func() {
				proposal, err = types.NewCreateConsumerChainProposal("title", "description", " ", initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Now())
				require.NoError(t, err)
			}, false,
		},
		{
			"initial height is zero", func() {
				proposal = &types.CreateConsumerChainProposal{
					Title:         "title",
					Description:   "description",
					ChainId:       "chainID",
					InitialHeight: clienttypes.Height{},
					GenesisHash:   []byte("gen_hash"),
					BinaryHash:    []byte("bin_hash"),
					SpawnTime:     time.Now(),
				}
			}, false,
		},
		{
			"genesis hash is empty", func() {
				proposal, err = types.NewCreateConsumerChainProposal("title", "description", "chainID", initialHeight, []byte(""), []byte("bin_hash"), time.Now())
				require.NoError(t, err)
			}, false,
		},
		{
			"binary hash is empty", func() {
				proposal, err = types.NewCreateConsumerChainProposal("title", "description", "chainID", initialHeight, []byte("gen_hash"), []byte(""), time.Now())
				require.NoError(t, err)
			}, false,
		},
		{
			"time is zero", func() {
				proposal, err = types.NewCreateConsumerChainProposal("title", "description", "chainID", initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Time{})
				require.NoError(t, err)
			}, false,
		},
	}

	for _, tc := range testCases {
		tc.malleate()

		err := proposal.ValidateBasic()
		if tc.expPass {
			require.NoError(t, err, "valid case: %s should not return error. got %w", tc.name, err)
		} else {
			require.Error(t, err, "invalid case: %s must return error but got none")
		}
	}
}

func TestMarshalCreateConsumerChainProposal(t *testing.T) {
	content, err := types.NewCreateConsumerChainProposal("title", "description", "chainID", clienttypes.NewHeight(0, 1), []byte("gen_hash"), []byte("bin_hash"), time.Now().UTC())
	require.NoError(t, err)

	cccp, ok := content.(*types.CreateConsumerChainProposal)
	require.True(t, ok)

	// create codec
	ir := codectypes.NewInterfaceRegistry()
	types.RegisterInterfaces(ir)
	govtypes.RegisterInterfaces(ir)
	clienttypes.RegisterInterfaces(ir)
	ibctmtypes.RegisterInterfaces(ir)
	cdc := codec.NewProtoCodec(ir)

	// marshal proposal
	bz, err := cdc.MarshalJSON(cccp)
	require.NoError(t, err)

	// unmarshal proposal
	newCccp := &types.CreateConsumerChainProposal{}
	err = cdc.UnmarshalJSON(bz, newCccp)
	require.NoError(t, err)

	require.True(t, proto.Equal(cccp, newCccp), "unmarshalled proposal does not equal original proposal")
}

func TestCreateConsumerChainProposalString(t *testing.T) {
	initialHeight := clienttypes.NewHeight(2, 3)
	spawnTime := time.Now()
	proposal, err := types.NewCreateConsumerChainProposal("title", "description", "chainID", initialHeight, []byte("gen_hash"), []byte("bin_hash"), spawnTime)
	require.NoError(t, err)

	expect := fmt.Sprintf(`CreateConsumerChain Proposal
	Title: title
	Description: description
	ChainID: chainID
	InitialHeight: %s
	GenesisHash: %s
	BinaryHash: %s
	SpawnTime: %s`, initialHeight, []byte("gen_hash"), []byte("bin_hash"), spawnTime)

	require.Equal(t, expect, proposal.String(), "string method for CreateConsumerChainProposal returned unexpected string")
}
