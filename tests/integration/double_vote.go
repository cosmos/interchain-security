package integration

import (
	"github.com/tendermint/tendermint/crypto/tmhash"
	tmtypes "github.com/tendermint/tendermint/types"
)

func (s *CCVTestSuite) TestHandleConsumerDoubleVoting() {
	s.SetupCCVChannel(s.path)
	// required to have the consumer client revision height greater than 0
	s.SendEmptyVSCPacket()

	// create signing info for all validators
	for _, v := range s.providerChain.Vals.Validators {
		s.setDefaultValSigningInfo(*v)
	}

	valSet, err := tmtypes.ValidatorSetFromProto(s.consumerChain.LastHeader.ValidatorSet)
	s.Require().NoError(err)

	val := valSet.Validators[0]
	signer := s.consumerChain.Signers[val.Address.String()]

	blockID1 := makeBlockID([]byte("blockhash"), 1000, []byte("partshash"))
	blockID2 := makeBlockID([]byte("blockhash2"), 1000, []byte("partshash"))

	vote1, err := tmtypes.MakeVote(
		s.consumerCtx().BlockHeight(),
		blockID1,
		valSet,
		signer,
		s.consumerChain.ChainID,
		s.consumerCtx().BlockTime(),
	)

	s.Require().NoError(err)

	v1 := vote1.ToProto()
	err = signer.SignVote(s.consumerChain.ChainID, v1)
	s.Require().NoError(err)

	badVote, err := tmtypes.MakeVote(
		s.consumerCtx().BlockHeight(),
		blockID2,
		valSet,
		signer,
		s.consumerChain.ChainID,
		s.consumerCtx().BlockTime(),
	)

	s.Require().NoError(err)

	bv := badVote.ToProto()
	err = signer.SignVote(s.consumerChain.ChainID, bv)
	s.Require().NoError(err)

	evidence := &tmtypes.DuplicateVoteEvidence{
		VoteA:            vote1,
		VoteB:            badVote,
		ValidatorPower:   val.ProposerPriority,
		TotalVotingPower: val.ProposerPriority,
		Timestamp:        s.consumerCtx().BlockTime(),
	}

	err = s.providerApp.GetProviderKeeper().HandleConsumerDoubleVoting(s.providerCtx(), evidence, s.consumerChain.LastHeader)
	s.Require().NoError(err)

}

func makeBlockID(hash []byte, partSetSize uint32, partSetHash []byte) tmtypes.BlockID {
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
