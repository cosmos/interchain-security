package crypto

import (
	"time"

	"github.com/cometbft/cometbft/crypto/tmhash"
	tmtypes "github.com/cometbft/cometbft/types"
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
