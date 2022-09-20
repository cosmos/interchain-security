package types_test

import (
	fmt "fmt"
	"testing"
	"time"

	"github.com/golang/protobuf/proto" //nolint - see: https://github.com/cosmos/interchain-security/issues/236
	"github.com/stretchr/testify/require"

	"github.com/cosmos/cosmos-sdk/codec"
	codectypes "github.com/cosmos/cosmos-sdk/codec/types"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"

	clienttypes "github.com/cosmos/ibc-go/v3/modules/core/02-client/types"
	ibctmtypes "github.com/cosmos/ibc-go/v3/modules/light-clients/07-tendermint/types"
	"github.com/cosmos/interchain-security/x/ccv/provider/types"
)

func TestValidateBasic(t *testing.T) {
	initialHeight := clienttypes.NewHeight(2, 3)

	testCases := []struct {
		name     string
		proposal govtypes.Content
		expPass  bool
	}{
		{
			"success",
			types.NewConsumerAdditionProposal("title", "description", "chainID", initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Now()),
			true,
		},
		{
			"fails validate abstract - empty title",
			types.NewConsumerAdditionProposal(" ", "description", "chainID", initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Now()),
			false,
		},
		{
			"chainID is empty",
			types.NewConsumerAdditionProposal("title", "description", " ", initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Now()),
			false,
		},
		{
			"initial height is zero",
			&types.ConsumerAdditionProposal{
				Title:         "title",
				Description:   "description",
				ChainId:       "chainID",
				InitialHeight: clienttypes.Height{},
				GenesisHash:   []byte("gen_hash"),
				BinaryHash:    []byte("bin_hash"),
				SpawnTime:     time.Now(),
			},
			false,
		},
		{
			"genesis hash is empty",
			types.NewConsumerAdditionProposal("title", "description", "chainID", initialHeight, []byte(""), []byte("bin_hash"), time.Now()),
			false,
		},
		{
			"binary hash is empty",
			types.NewConsumerAdditionProposal("title", "description", "chainID", initialHeight, []byte("gen_hash"), []byte(""), time.Now()),
			false,
		},
		{
			"time is zero",
			types.NewConsumerAdditionProposal("title", "description", "chainID", initialHeight, []byte("gen_hash"), []byte("bin_hash"), time.Time{}),
			false,
		},
	}

	for _, tc := range testCases {

		err := tc.proposal.ValidateBasic()
		if tc.expPass {
			require.NoError(t, err, "valid case: %s should not return error. got %w", tc.name, err)
		} else {
			require.Error(t, err, "invalid case: %s must return error but got none")
		}
	}
}

func TestMarshalConsumerAdditionProposal(t *testing.T) {
	content := types.NewConsumerAdditionProposal("title", "description", "chainID", clienttypes.NewHeight(0, 1), []byte("gen_hash"), []byte("bin_hash"), time.Now().UTC())

	cccp, ok := content.(*types.ConsumerAdditionProposal)
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
	newCccp := &types.ConsumerAdditionProposal{}
	err = cdc.UnmarshalJSON(bz, newCccp)
	require.NoError(t, err)

	require.True(t, proto.Equal(cccp, newCccp), "unmarshalled proposal does not equal original proposal")
}

func TestConsumerAdditionProposalString(t *testing.T) {
	initialHeight := clienttypes.NewHeight(2, 3)
	spawnTime := time.Now()
	proposal := types.NewConsumerAdditionProposal("title", "description", "chainID", initialHeight, []byte("gen_hash"), []byte("bin_hash"), spawnTime)

	expect := fmt.Sprintf(`CreateConsumerChain Proposal
	Title: title
	Description: description
	ChainID: chainID
	InitialHeight: %s
	GenesisHash: %s
	BinaryHash: %s
	SpawnTime: %s`, initialHeight, []byte("gen_hash"), []byte("bin_hash"), spawnTime)

	require.Equal(t, expect, proposal.String(), "string method for ConsumerAdditionProposal returned unexpected string")
}
