package client_test

import (
	"testing"
	"time"

	"github.com/cosmos/cosmos-sdk/client"
	"github.com/cosmos/interchain-security/testutil"
	providerClient "github.com/cosmos/interchain-security/x/ccv/provider/client"
	"github.com/stretchr/testify/mock"
	"github.com/stretchr/testify/require"
	cmtproto "github.com/tendermint/tendermint/proto/tendermint/types"
	coretypes "github.com/tendermint/tendermint/rpc/core/types"
)

func ConsumerAdditionProposalCLIDriver(providerUnbondingTime, consumerUnbondingTime time.Duration) error {
	mockClient := new(testutil.MockCometBFTRPCClient)

	resConsensParams := coretypes.ResultConsensusParams{
		BlockHeight: 5,
		ConsensusParams: cmtproto.ConsensusParams{
			Evidence: cmtproto.EvidenceParams{
				MaxAgeDuration: providerUnbondingTime,
			},
		},
	}
	mockClient.On("ConsensusParams", mock.Anything, mock.Anything).Return(&resConsensParams, nil)
	clientCtx := client.Context{}.WithClient(mockClient)

	return providerClient.CheckPropUnbondingPeriod(clientCtx, consumerUnbondingTime)
}

func TestConsumerAdditionProposalSuite(t *testing.T) {
	testCases := []struct {
		name              string
		providerUnbonding time.Duration
		consumerUnbonding time.Duration
		errorExpected     bool
	}{
		{
			name:              "provider unbonding longer",
			providerUnbonding: time.Hour * 5,
			consumerUnbonding: time.Hour * 4,
			errorExpected:     false,
		},
		{
			name:              "consumer unbonding longer",
			providerUnbonding: time.Hour * 5,
			consumerUnbonding: time.Hour * 6,
			errorExpected:     true,
		},
		{
			name:              "unbondings equal",
			providerUnbonding: time.Hour * 5,
			consumerUnbonding: time.Hour * 5,
			errorExpected:     true,
		},
	}

	for _, tc := range testCases {
		res := ConsumerAdditionProposalCLIDriver(tc.providerUnbonding, tc.consumerUnbonding)
		if tc.errorExpected {
			require.Error(t, res)
		} else {
			require.NoError(t, res)
		}
	}
}
