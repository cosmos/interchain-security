package integration

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/v2/x/ccv/provider/types"

	ibctmtypes "github.com/cosmos/ibc-go/v4/modules/light-clients/07-tendermint/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

// TestHandleConsumerMisbehaviour tests that handling a valid misbehaviour,
// with conflicting headers forming an equivocation, results in the jailing and tombstoning of the validators
func (s *CCVTestSuite) TestHandleConsumerMisbehaviour() {
	s.SetupCCVChannel(s.path)
	// required to have the consumer client revision height greater than 0
	s.SendEmptyVSCPacket()

	for _, v := range s.providerChain.Vals.Validators {
		s.setDefaultValSigningInfo(*v)
	}

	altTime := s.providerCtx().BlockTime().Add(time.Minute)

	clientHeight := s.consumerChain.LastHeader.TrustedHeight
	clientTMValset := tmtypes.NewValidatorSet(s.consumerChain.Vals.Validators)
	clientSigners := s.consumerChain.Signers

	misb := &ibctmtypes.Misbehaviour{
		ClientId: s.path.EndpointA.ClientID,
		Header1: s.consumerChain.CreateTMClientHeader(
			s.consumerChain.ChainID,
			int64(clientHeight.RevisionHeight+1),
			clientHeight,
			altTime,
			clientTMValset,
			clientTMValset,
			clientTMValset,
			clientSigners,
		),
		// create a different header by changing the header timestamp only
		// in order to create an equivocation, i.e. both headers have the same deterministic states
		Header2: s.consumerChain.CreateTMClientHeader(
			s.consumerChain.ChainID,
			int64(clientHeight.RevisionHeight+1),
			clientHeight,
			altTime.Add(10*time.Second),
			clientTMValset,
			clientTMValset,
			clientTMValset,
			clientSigners,
		),
	}

	err := s.providerApp.GetProviderKeeper().HandleConsumerMisbehaviour(s.providerCtx(), *misb)
	s.NoError(err)

	// verify that validators are jailed and tombstoned
	for _, v := range clientTMValset.Validators {
		consuAddr := sdk.ConsAddress(v.Address.Bytes())
		provAddr := s.providerApp.GetProviderKeeper().GetProviderAddrFromConsumerAddr(s.providerCtx(), s.consumerChain.ChainID, types.NewConsumerConsAddress(consuAddr))
		val, ok := s.providerApp.GetTestStakingKeeper().GetValidatorByConsAddr(s.providerCtx(), provAddr.Address)
		s.Require().True(ok)
		s.Require().True(val.Jailed)
		s.Require().True(s.providerApp.GetTestSlashingKeeper().IsTombstoned(s.providerCtx(), provAddr.Address))
	}
}

func (s *CCVTestSuite) TestGetByzantineValidators() {
	s.SetupCCVChannel(s.path)
	// required to have the consumer client revision height greater than 0
	s.SendEmptyVSCPacket()

	altTime := s.providerCtx().BlockTime().Add(time.Minute)

	clientHeight := s.consumerChain.LastHeader.TrustedHeight
	clientTMValset := tmtypes.NewValidatorSet(s.consumerChain.Vals.Validators)
	clientSigners := s.consumerChain.Signers

	// Create a validator set subset
	altValset := tmtypes.NewValidatorSet(s.consumerChain.Vals.Validators[0:3])
	altSigners := make(map[string]tmtypes.PrivValidator, 1)
	altSigners[clientTMValset.Validators[0].Address.String()] = clientSigners[clientTMValset.Validators[0].Address.String()]
	altSigners[clientTMValset.Validators[1].Address.String()] = clientSigners[clientTMValset.Validators[1].Address.String()]
	altSigners[clientTMValset.Validators[2].Address.String()] = clientSigners[clientTMValset.Validators[2].Address.String()]

	// TODO: figure out how to test an amnesia cases for "amnesia" attack
	testCases := []struct {
		name                   string
		misbehaviour           *ibctmtypes.Misbehaviour
		expByzantineValidators []*tmtypes.Validator
		expPass                bool
	}{
		{
			"invalid misbehaviour - Header1 is empty",
			&ibctmtypes.Misbehaviour{
				Header1: &ibctmtypes.Header{},
				Header2: s.consumerChain.CreateTMClientHeader(
					s.consumerChain.ChainID,
					int64(clientHeight.RevisionHeight+1),
					clientHeight,
					altTime,
					altValset,
					altValset,
					clientTMValset,
					altSigners,
				),
			},
			nil,
			false,
		},
		{
			"invalid headers - Header2 is empty",
			&ibctmtypes.Misbehaviour{
				Header1: s.consumerChain.CreateTMClientHeader(
					s.consumerChain.ChainID,
					int64(clientHeight.RevisionHeight+1),
					clientHeight,
					altTime,
					clientTMValset,
					clientTMValset,
					clientTMValset,
					clientSigners,
				),
				Header2: &ibctmtypes.Header{},
			},
			nil,
			false,
		},
		{
			"invalid light client attack - lunatic attack",
			&ibctmtypes.Misbehaviour{
				ClientId: s.path.EndpointA.ClientID,
				Header1: s.consumerChain.CreateTMClientHeader(
					s.consumerChain.ChainID,
					int64(clientHeight.RevisionHeight+1),
					clientHeight,
					altTime,
					clientTMValset,
					clientTMValset,
					clientTMValset,
					clientSigners,
				),
				Header2: s.consumerChain.CreateTMClientHeader(
					s.consumerChain.ChainID,
					int64(clientHeight.RevisionHeight+1),
					clientHeight,
					altTime,
					altValset,
					altValset,
					clientTMValset,
					altSigners,
				),
			},
			// Expect to get only the validators
			// who signed both headers are returned
			altValset.Validators,
			true,
		},
		{
			"valid light client attack - equivocation",
			&ibctmtypes.Misbehaviour{
				ClientId: s.path.EndpointA.ClientID,
				Header1: s.consumerChain.CreateTMClientHeader(
					s.consumerChain.ChainID,
					int64(clientHeight.RevisionHeight+1),
					clientHeight,
					altTime,
					clientTMValset,
					clientTMValset,
					clientTMValset,
					clientSigners,
				),
				Header2: s.consumerChain.CreateTMClientHeader(
					s.consumerChain.ChainID,
					int64(clientHeight.RevisionHeight+1),
					clientHeight,
					altTime.Add(time.Minute),
					clientTMValset,
					clientTMValset,
					clientTMValset,
					clientSigners,
				),
			},
			// Expect to get the entire valset since
			// all validators double-signed
			clientTMValset.Validators,
			true,
		},
	}

	for _, tc := range testCases {
		s.Run(tc.name, func() {
			byzantineValidators, err := s.providerApp.GetProviderKeeper().GetByzantineValidators(
				s.providerCtx(),
				*tc.misbehaviour,
			)
			if tc.expPass {
				s.NoError(err)
				// For both lunatic and equivocation attack all the validators
				// who signed the bad header (Header2) should be in returned in the evidence
				h2Valset := tc.misbehaviour.Header2.ValidatorSet

				s.Equal(len(h2Valset.Validators), len(byzantineValidators))

				vs, err := tmtypes.ValidatorSetFromProto(tc.misbehaviour.Header2.ValidatorSet)
				s.NoError(err)

				for _, v := range tc.expByzantineValidators {
					idx, _ := vs.GetByAddress(v.Address)
					s.True(idx >= 0)
				}

			} else {
				s.Error(err)
			}
		})
	}
}
