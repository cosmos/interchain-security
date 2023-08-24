package crypto

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	abci "github.com/tendermint/tendermint/abci/types"
	"github.com/tendermint/tendermint/crypto/tmhash"
	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

// utility function duplicated from CometBFT
// see https://github.com/cometbft/cometbft/blob/main/evidence/verify_test.go#L554
func MakeBlockID(hash []byte, partSetSize uint32, partSetHash []byte) tmtypes.BlockID {
	var (
		h   = make([]byte, tmhash.Size)
		psH = make([]byte, tmhash.Size)
	)
	copy(h, hash)
	copy(psH, partSetHash)
	return tmtypes.BlockID{
		Hash: h,
		PartSetHeader: tmtypes.PartSetHeader{
			Total: partSetSize,
			Hash:  psH,
		},
	}
}

func MakeAndSignVote(
	blockID tmtypes.BlockID,
	blockHeight int64,
	blockTime time.Time,
	valSet *tmtypes.ValidatorSet,
	signer tmtypes.PrivValidator,
	chainID string,
) *tmtypes.Vote {
	vote, err := tmtypes.MakeVote(
		blockHeight,
		blockID,
		valSet,
		signer,
		chainID,
		blockTime,
	)
	if err != nil {
		panic(err)
	}

	v := vote.ToProto()
	err = signer.SignVote(chainID, v)
	if err != nil {
		panic(err)
	}

	vote.Signature = v.Signature
	return vote
}

func SetDefaultConsensusEvidenceParams(ctx sdk.Context) sdk.Context {
	return ctx.WithConsensusParams(
		&abci.ConsensusParams{
			Evidence: &tmproto.EvidenceParams{
				MaxAgeNumBlocks: 302400,
				MaxAgeDuration:  504 * time.Hour, // 3 weeks is the max duration
				MaxBytes:        10000,
			},
		},
	)
}
