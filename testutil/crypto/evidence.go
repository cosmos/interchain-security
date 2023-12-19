package crypto

import (
	"time"

	ibctmtypes "github.com/cosmos/ibc-go/87/modules/light-clients/07-tendermint"

	"github.com/cometbft/cometbft/crypto/tmhash"
	"github.com/cometbft/cometbft/libs/bytes"
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

// CorruptCommitSigsInHeader corrupts the header by changing the value
// of the commit signature for given validator address.
// Note that this method is solely used for testing purposes
func CorruptCommitSigsInHeader(header *ibctmtypes.Header, valAddress bytes.HexBytes) {
	commit, err := tmtypes.CommitFromProto(header.Commit)
	if err != nil {
		panic(err)
	}

	for idx, sig := range commit.Signatures {
		if sig.ValidatorAddress.String() == valAddress.String() {
			sig.Signature = []byte("randomsig")
			commit.Signatures[idx] = sig
		}
	}
	// update the commit in client the header
	header.SignedHeader.Commit = commit.ToProto()
}

// CorruptValidatorPubkeyInHeader corrupts the header by changing the validator pubkey
// of the given validator address in the validator set.
// Note that this method is solely used for testing purposes
func CorruptValidatorPubkeyInHeader(header *ibctmtypes.Header, valAddress bytes.HexBytes) {
	valset, err := tmtypes.ValidatorSetFromProto(header.ValidatorSet)
	if err != nil {
		panic(err)
	}

	for _, v := range valset.Validators {
		if v.Address.String() == valAddress.String() {
			v.PubKey = tmtypes.NewMockPV().PrivKey.PubKey()
		}
	}

	vs, err := valset.ToProto()
	if err != nil {
		panic(err)
	}
	header.ValidatorSet = vs
}
