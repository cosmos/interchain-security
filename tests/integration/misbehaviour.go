package integration

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	stakingtypes "github.com/cosmos/cosmos-sdk/x/staking/types"
	"github.com/cosmos/ibc-go/v4/modules/core/exported"
	"github.com/cosmos/interchain-security/v2/x/ccv/provider"
	"github.com/cosmos/interchain-security/v2/x/ccv/provider/types"

	ibcsolotypes "github.com/cosmos/ibc-go/v4/modules/light-clients/06-solomachine/types"
	ibctmtypes "github.com/cosmos/ibc-go/v4/modules/light-clients/07-tendermint/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

// TestHandleConsumerMisbehaviour verifies first that ICS misbehaviour is handled
// only if its conlflicting headers are valid. Then, it checks
// that validators who signed the incorrect header are jailed and tombstoned.
func (s *CCVTestSuite) TestHandleConsumerMisbehaviour() {
	s.SetupCCVChannel(s.path)
	// required to have the consumer client revision height greater than 0
	s.SendEmptyVSCPacket()

	// create signing info for all validators
	for _, v := range s.providerChain.Vals.Validators {
		s.setDefaultValSigningInfo(*v)
	}

	// create a new header timestamp
	headerTs := s.providerCtx().BlockTime().Add(time.Minute)

	// get trusted validators and height
	clientHeight := s.consumerChain.LastHeader.TrustedHeight
	clientTMValset := tmtypes.NewValidatorSet(s.consumerChain.Vals.Validators)
	clientSigners := s.consumerChain.Signers

	// create an alternative validator set using more than 1/3 of the trusted validator set
	altValset := tmtypes.NewValidatorSet(s.consumerChain.Vals.Validators[0:2])
	altSigners := make(map[string]tmtypes.PrivValidator, 1)
	altSigners[clientTMValset.Validators[0].Address.String()] = clientSigners[clientTMValset.Validators[0].Address.String()]
	altSigners[clientTMValset.Validators[1].Address.String()] = clientSigners[clientTMValset.Validators[1].Address.String()]
	testCases := []struct {
		name         string
		misbehaviour exported.Misbehaviour
		expPass      bool
	}{
		{
			"invalid misbehaviour client type - shouldn't pass",
			&ibcsolotypes.Misbehaviour{},
			false,
		},
		{
			"invalid misbehaviour with empty header1 - shouldn't pass",
			&ibctmtypes.Misbehaviour{
				Header1: &ibctmtypes.Header{},
				Header2: s.consumerChain.CreateTMClientHeader(
					s.consumerChain.ChainID,
					int64(clientHeight.RevisionHeight+1),
					clientHeight,
					headerTs,
					altValset,
					altValset,
					clientTMValset,
					altSigners,
				),
			},
			false,
		},
		{
			"valid misbehaviour - should pass",
			&ibctmtypes.Misbehaviour{
				ClientId: s.path.EndpointA.ClientID,
				Header1: s.consumerChain.CreateTMClientHeader(
					s.consumerChain.ChainID,
					int64(clientHeight.RevisionHeight+1),
					clientHeight,
					headerTs,
					clientTMValset,
					clientTMValset,
					clientTMValset,
					clientSigners,
				),
				// the resulting Header2 will have a different BlockID
				// than Header1 since doesn't share the same valset and signers
				Header2: s.consumerChain.CreateTMClientHeader(
					s.consumerChain.ChainID,
					int64(clientHeight.RevisionHeight+1),
					clientHeight,
					headerTs,
					altValset,
					altValset,
					clientTMValset,
					altSigners,
				),
			},
			true,
		},
	}

	for _, tc := range testCases {
		s.Run(tc.name, func() {
			err := s.providerApp.GetProviderKeeper().HandleConsumerMisbehaviour(s.providerCtx(), tc.misbehaviour)
			// get clienstate
			cs, ok := s.providerApp.GetIBCKeeper().ClientKeeper.GetClientState(s.providerCtx(), s.path.EndpointB.ClientID)
			s.Require().True(ok)

			if tc.expPass {
				s.NoError(err)
				// Check that only the validators of the alternate validator set
				// , i.e. altValset, are jailed and tombstoned on the provider
				for _, consuVal := range clientTMValset.Validators {
					provVal := s.getProviderValFromConsumerVal(*consuVal)
					provConsAddr, err := provVal.GetConsAddr()
					s.Require().NoError(err)
					if _, ok := altSigners[consuVal.Address.String()]; ok {
						s.Require().True(provVal.Jailed)
						s.Require().True(s.providerApp.GetTestSlashingKeeper().IsTombstoned(s.providerCtx(), provConsAddr))

					} else {
						s.Require().False(provVal.Jailed)
						s.Require().False(s.providerApp.GetTestSlashingKeeper().IsTombstoned(s.providerCtx(), provConsAddr))
						s.Require().NotZero(cs.(*ibctmtypes.ClientState).FrozenHeight)

					}
				}
				// verify that the client was frozen
				s.Require().NotZero(cs.(*ibctmtypes.ClientState).FrozenHeight)
			} else {
				// Check that no validators are jailed or tombstoned on the provider
				for _, consuVal := range clientTMValset.Validators {
					s.Error(err)
					provVal := s.getProviderValFromConsumerVal(*consuVal)
					s.Require().False(provVal.Jailed)
					provConsAddr, err := provVal.GetConsAddr()
					s.Require().NoError(err)
					s.Require().False(s.providerApp.GetTestSlashingKeeper().IsTombstoned(s.providerCtx(), provConsAddr))
				}
				// verify that the client wasn't frozen
				s.Require().Zero(cs.(*ibctmtypes.ClientState).FrozenHeight)
			}
		})
	}
}

func (s *CCVTestSuite) TestConstructLightClientEvidence() {
	s.SetupCCVChannel(s.path)
	// required to have the consumer client revision height greater than 0
	s.SendEmptyVSCPacket()

	altTime := s.providerCtx().BlockTime().Add(time.Minute)

	clientHeight := s.consumerChain.LastHeader.TrustedHeight
	clientTMValset := tmtypes.NewValidatorSet(s.consumerChain.Vals.Validators)
	clientSigners := s.consumerChain.Signers

	altValset := tmtypes.NewValidatorSet(s.consumerChain.Vals.Validators[0:3])
	altSigners := make(map[string]tmtypes.PrivValidator, 1)
	altSigners[clientTMValset.Validators[0].Address.String()] = clientSigners[clientTMValset.Validators[0].Address.String()]
	altSigners[clientTMValset.Validators[1].Address.String()] = clientSigners[clientTMValset.Validators[1].Address.String()]
	altSigners[clientTMValset.Validators[2].Address.String()] = clientSigners[clientTMValset.Validators[2].Address.String()]

	testCases := []struct {
		name         string
		misbehaviour *ibctmtypes.Misbehaviour
		expPass      bool
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
			false,
		},
		{
			"invalid misbehaviour - Header2 is empty",
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
			false,
		},
		{
			"invalid misbehaviour - ClientId is empty",
			&ibctmtypes.Misbehaviour{
				ClientId: "unknown-client-id",
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
			false,
		},
		{
			"light client attack - lunatic attack",
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
			true,
		},
		{
			"light client attack - equivocation",
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
			true,
		},
	}

	for _, tc := range testCases {
		s.Run(tc.name, func() {
			ev, err := s.providerApp.GetProviderKeeper().ConstructLightClientEvidence(
				s.providerCtx(),
				*tc.misbehaviour,
			)
			if tc.expPass {
				s.NoError(err)
				// For both lunatic and equivocation attack all the validators
				// who signed the bad header (Header2) should be in returned in the evidence
				h2Valset := tc.misbehaviour.Header2.ValidatorSet

				s.Equal(len(h2Valset.Validators), len(ev.ByzantineValidators))

				vs, err := tmtypes.ValidatorSetFromProto(tc.misbehaviour.Header2.ValidatorSet)
				s.NoError(err)

				for _, v := range ev.ByzantineValidators {
					idx, _ := vs.GetByAddress(v.Address)
					s.True(idx >= 0)
				}

			} else {
				s.Error(err)
			}
		})
	}
}

// TestMsgSubmitConsumerClientHandler tests that the provider
// handler can parse MsgSubmitConsumerMisbehaviour
// TODO: move this to x/provider/handler_test.go
func (s *CCVTestSuite) TestMsgSubmitConsumerMisbehaviourHandler() {
	s.SetupCCVChannel(s.path)
	// required to have the consumer client revision height greater than 0
	s.SendEmptyVSCPacket()

	// create signing info for all validators
	for _, v := range s.providerChain.Vals.Validators {
		s.setDefaultValSigningInfo(*v)
	}

	// create a new header timestamp
	headerTs := s.providerCtx().BlockTime().Add(time.Minute)

	// get trusted validators and height
	clientHeight := s.consumerChain.LastHeader.TrustedHeight
	clientTMValset := tmtypes.NewValidatorSet(s.consumerChain.Vals.Validators)
	clientSigners := s.consumerChain.Signers

	altValset := tmtypes.NewValidatorSet(s.consumerChain.Vals.Validators[0:2])
	altSigners := make(map[string]tmtypes.PrivValidator, 1)
	altSigners[clientTMValset.Validators[0].Address.String()] = clientSigners[clientTMValset.Validators[0].Address.String()]
	altSigners[clientTMValset.Validators[1].Address.String()] = clientSigners[clientTMValset.Validators[1].Address.String()]

	testCases := []struct {
		name         string
		misbehaviour *ibctmtypes.Misbehaviour
		expPass      bool
	}{
		{
			"invalid MsgSubmitMisbehaviour shouldn't pass",
			&ibctmtypes.Misbehaviour{},
			false,
		},
		{

			"valid MsgSubmitMisbehaviour should pass",
			&ibctmtypes.Misbehaviour{
				ClientId: s.path.EndpointA.ClientID,
				Header1: s.consumerChain.CreateTMClientHeader(
					s.consumerChain.ChainID,
					int64(clientHeight.RevisionHeight+1),
					clientHeight,
					headerTs,
					clientTMValset,
					clientTMValset,
					clientTMValset,
					clientSigners,
				),
				// the resulting Header2 will have a different BlockID
				// than Header1 since doesn't share the same valset and signers
				Header2: s.consumerChain.CreateTMClientHeader(
					s.consumerChain.ChainID,
					int64(clientHeight.RevisionHeight+1),
					clientHeight,
					headerTs,
					altValset,
					altValset,
					clientTMValset,
					altSigners,
				),
			},
			true,
		},
	}

	for _, tc := range testCases {
		s.Run(tc.name, func() {
			// build the msg using the misbehaviour data
			msg, err := types.NewMsgSubmitConsumerMisbehaviour(s.providerChain.SenderAccount.GetAddress(), tc.misbehaviour)
			s.Require().NoError(err)

			k := s.providerApp.GetProviderKeeper()

			// Try to handle the message
			_, err = provider.NewHandler(&k)(s.providerCtx(), msg)
			if tc.expPass {
				s.Require().NoError(err)
			} else {
				s.Require().Error(err)
			}
		})
	}
}

func (s *CCVTestSuite) getProviderValFromConsumerVal(valAddr tmtypes.Validator) stakingtypes.Validator {
	consuAddr := types.NewConsumerConsAddress(sdk.ConsAddress(valAddr.Address.Bytes()))
	provAddr := s.providerApp.GetProviderKeeper().GetProviderAddrFromConsumerAddr(s.providerCtx(), s.consumerChain.ChainID, consuAddr)
	val, ok := s.providerApp.GetTestStakingKeeper().GetValidatorByConsAddr(s.providerCtx(), provAddr.Address)
	s.Require().True(ok)
	return val
}
