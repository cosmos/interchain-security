package e2e

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/cosmos-sdk/x/staking/teststaking"
	ibctmtypes "github.com/cosmos/ibc-go/v4/modules/light-clients/07-tendermint/types"
	"github.com/tendermint/tendermint/crypto/tmhash"
	tmproto "github.com/tendermint/tendermint/proto/tendermint/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

func (s *CCVTestSuite) TestHandleConsumerDoubleVoting() {

	s.SetupCCVChannel(s.path)
	// required to have the consumer client revision height greater than 0
	s.SendEmptyVSCPacket()

	// use the last consumer chain header to mock double votes
	consumerLastHeader := s.consumerChain.LastHeader

	// chainID := s.consumerChain.ChainID
	// blockHeight := s.consumerChain.LastHeader.TrustedHeight
	// blockHeight := s.consumerChain.LastHeader.Header.Time

	valset := s.consumerChain.Vals
	valIndex := int32(0)
	// doc
	chainID := s.consumerChain.ChainID
	_, val := valset.GetByIndex(valIndex)
	blockID := makeBlockID([]byte("blockhash"), 1000, []byte("partshash"))
	blockID2 := makeBlockID([]byte("blockhash2"), 1000, []byte("partshash"))

	// create two votes using the cons
	vote := s.makeVote(*val, chainID, valIndex, consumerLastHeader.Header.Height, 2, 1, blockID, consumerLastHeader.Header.Time)
	badVote := s.makeVote(*val, chainID, valIndex, consumerLastHeader.Header.Height, 2, 1, blockID2, consumerLastHeader.Header.Time)

	// create signing info for all the provider chain's validators
	// Note that converting a validator consensus address from consumer to provider
	// is more accurate but more verbose too.
	consuAddr := sdk.ConsAddress(val.Address.Bytes())
	provAddr := s.providerApp.GetProviderKeeper().GetProviderAddrFromConsumerAddr(s.providerCtx(), chainID, consuAddr)
	provVal, ok := s.providerApp.GetE2eStakingKeeper().GetValidatorByConsAddr(s.providerCtx(), provAddr)
	s.Require().True(ok)

	tmVal, err := teststaking.ToTmValidator(provVal, sdk.DefaultPowerReduction)
	s.Require().NoError(err)
	s.setDefaultValSigningInfo(*tmVal)

	testCases := []struct {
		name     string
		header   *ibctmtypes.Header
		evidence *tmproto.DuplicateVoteEvidence
		epxPass  bool
	}{
		{
			"infraction header cannot be nil",
			nil,
			&tmproto.DuplicateVoteEvidence{
				VoteA:            vote.ToProto(),
				VoteB:            badVote.ToProto(),
				ValidatorPower:   val.VotingPower,
				TotalVotingPower: valset.TotalVotingPower(),
			},
			false,
		},
		{
			"invalid infraction header - empty validator set",
			&ibctmtypes.Header{TrustedValidators: &tmproto.ValidatorSet{}},
			&tmproto.DuplicateVoteEvidence{
				VoteA:            vote.ToProto(),
				VoteB:            badVote.ToProto(),
				ValidatorPower:   val.VotingPower,
				TotalVotingPower: valset.TotalVotingPower(),
			},
			false,
		},
		{
			"evidence cannot be nil",
			consumerLastHeader,
			nil,
			false,
		},
		{
			"duplicated evidence voting powers aren't equal to infraction header validator set voting powers",
			&ibctmtypes.Header{TrustedValidators: &tmproto.ValidatorSet{}},
			&tmproto.DuplicateVoteEvidence{
				VoteA:            vote.ToProto(),
				VoteB:            badVote.ToProto(),
				TotalVotingPower: int64(9999),
				ValidatorPower:   int64(9999),
			},
			false,
		},
		{
			"infraction header trusted validators shouldn't be empty",
			consumerLastHeader,
			&tmproto.DuplicateVoteEvidence{
				VoteA:            vote.ToProto(),
				VoteB:            badVote.ToProto(),
				ValidatorPower:   val.VotingPower,
				TotalVotingPower: valset.TotalVotingPower(),
			},
			true,
		},
	}

	for _, tc := range testCases {
		s.Run(tc.name, func() {
			err := s.providerApp.GetProviderKeeper().HandleConsumerDoubleVoting(s.providerCtx(), tc.evidence, tc.header)
			if !tc.epxPass {
				s.Require().Error(err)
			} else {
				val, ok := s.providerApp.GetE2eStakingKeeper().GetValidatorByConsAddr(s.providerCtx(), provAddr)
				s.Require().NoError(err)
				s.Require().True(ok)
				s.Require().True(val.Jailed)
				s.Require().True(s.providerApp.GetE2eSlashingKeeper().IsTombstoned(s.providerCtx(), provAddr))
			}
		})
	}
}

func (s *CCVTestSuite) makeVote(val tmtypes.Validator, chainID string, valIndex int32, height int64, round int32, step int, blockID tmtypes.BlockID, time time.Time) *tmtypes.Vote {
	privVal, ok := s.providerChain.Signers[val.Address.String()]
	s.Require().True(ok)

	pubKey, err := privVal.GetPubKey()
	s.Require().NoError(err)
	v := &tmtypes.Vote{
		ValidatorAddress: pubKey.Address(),
		ValidatorIndex:   valIndex,
		Height:           height,
		Round:            round,
		Type:             tmproto.SignedMsgType(step),
		BlockID:          blockID,
		Timestamp:        time,
	}

	vpb := v.ToProto()
	err = privVal.SignVote(chainID, vpb)
	s.Require().NoError(err)

	v.Signature = vpb.Signature
	return v
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
