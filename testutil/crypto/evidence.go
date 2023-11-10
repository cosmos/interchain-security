package crypto

import (
	"fmt"
	"time"

	ibctmtypes "github.com/cosmos/ibc-go/v4/modules/light-clients/07-tendermint/types"
	"github.com/tendermint/tendermint/crypto/tmhash"
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

// MakeAndSignVoteWithForgedValAddress makes and signs a vote using two different keys:
// one to derive the validator address in the vote and a second to sign it.
func MakeAndSignVoteWithForgedValAddress(
	blockID tmtypes.BlockID,
	blockHeight int64,
	blockTime time.Time,
	valSet *tmtypes.ValidatorSet,
	signer tmtypes.PrivValidator,
	valAddressSigner tmtypes.PrivValidator,
	chainID string,
) *tmtypes.Vote {
	// create the vote using a different key than the signing key
	vote, err := tmtypes.MakeVote(
		blockHeight,
		blockID,
		valSet,
		valAddressSigner,
		chainID,
		blockTime,
	)
	if err != nil {
		panic(err)
	}

	// sign vote using the given private key
	v := vote.ToProto()
	err = signer.SignVote(chainID, v)
	if err != nil {
		panic(err)
	}

	vote.Signature = v.Signature
	return vote
}

// UpdateHeaderCommitWithNilVotes updates the given light client header
// by changing the commit BlockIDFlag of the given validators to nil
//
// Note that this method is solely used for testing purpose
func UpdateHeaderCommitWithNilVotes(header *ibctmtypes.Header, validators []*tmtypes.Validator) {
	if len(validators) > len(header.ValidatorSet.Validators) {
		panic(fmt.Sprintf("cannot change more than %d validators votes: got %d",
			len(header.ValidatorSet.Validators), len(header.ValidatorSet.Validators)))
	}

	commit, err := tmtypes.CommitFromProto(header.Commit)
	if err != nil {
		panic(err)
	}

	valset, err := tmtypes.ValidatorSetFromProto(header.ValidatorSet)
	if err != nil {
		panic(err)
	}

	for _, v := range validators {
		// get validator index in valset
		idx, _ := valset.GetByAddress(v.Address)
		s := commit.Signatures[idx]
		// change BlockIDFlag to nil
		s.BlockIDFlag = tmtypes.BlockIDFlagNil
		// reassign the signature value
		commit.Signatures[idx] = s
	}

	// overwrite the commit the back in the header
	header.SignedHeader.Commit = commit.ToProto()
}
