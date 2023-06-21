package integration

import (
	"fmt"
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	"github.com/cosmos/interchain-security/v2/x/ccv/provider/types"

	ibctmtypes "github.com/cosmos/ibc-go/v4/modules/light-clients/07-tendermint/types"
	tmtypes "github.com/tendermint/tendermint/types"
)

const (
	trustingPeriod time.Duration = time.Hour * 24 * 7 * 2
	ubdPeriod      time.Duration = time.Hour * 24 * 7 * 3
	maxClockDrift  time.Duration = time.Second * 10
)

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

	altValset := tmtypes.NewValidatorSet(s.consumerChain.Vals.Validators[0:2])
	altSigners := make(map[string]tmtypes.PrivValidator, 1)
	altSigners[clientTMValset.Validators[0].Address.String()] = clientSigners[clientTMValset.Validators[0].Address.String()]
	altSigners[clientTMValset.Validators[1].Address.String()] = clientSigners[clientTMValset.Validators[1].Address.String()]

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
	}

	err := s.providerApp.GetProviderKeeper().HandleConsumerMisbehaviour(s.providerCtx(), *misb)
	s.NoError(err)

	for _, v := range altValset.Validators {
		consuAddr := sdk.ConsAddress(v.Address.Bytes())
		provAddr := s.providerApp.GetProviderKeeper().GetProviderAddrFromConsumerAddr(s.providerCtx(), s.consumerChain.ChainID, types.ConsumerConsAddress{consuAddr})
		val, ok := s.providerApp.GetTestStakingKeeper().GetValidatorByConsAddr(s.providerCtx(), provAddr.Address)
		s.Require().True(ok)
		s.Require().True(val.Jailed)
		s.Require().True(s.providerApp.GetTestSlashingKeeper().IsTombstoned(s.providerCtx(), provAddr.Address))
	}

}

func (s *CCVTestSuite) TestConstructLigthClientEvidence() {

	// test cases
	// misbehaviour nil
	// misbheaviour header 1 nil
	// misbehaviour header 2 nil

	// misbehaviour no common height

	s.SetupCCVChannel(s.path)
	// required to have the consumer client revision height greater than 0
	s.SendEmptyVSCPacket()

	altTime := s.providerCtx().BlockTime().Add(time.Minute)

	clientHeight := s.consumerChain.LastHeader.TrustedHeight
	clientTMValset := tmtypes.NewValidatorSet(s.consumerChain.Vals.Validators)
	clientSigners := s.consumerChain.Signers

	altValset := tmtypes.NewValidatorSet(s.consumerChain.Vals.Validators[0:2])
	altSigners := make(map[string]tmtypes.PrivValidator, 1)
	altSigners[clientTMValset.Validators[0].Address.String()] = clientSigners[clientTMValset.Validators[0].Address.String()]
	altSigners[clientTMValset.Validators[1].Address.String()] = clientSigners[clientTMValset.Validators[1].Address.String()]

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
	}

	_ = misb

	// emptyHeader := &ibctmtypes.Header{}

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
				)},
			false,
		}, {
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
		}, {
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
		}, {
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
					altTime,
					clientTMValset,
					clientTMValset,
					clientTMValset,
					clientSigners,
				),
			},
			true,
		},
	}

	// check how it's tested on CometBFTNewExtensionOptionsDecorator

	for _, tc := range testCases {
		s.Run(tc.name, func() {
			ev, err := s.providerApp.GetProviderKeeper().ConstructLigthClientEvidence(
				s.providerCtx(),
				*tc.misbehaviour,
			)
			if tc.expPass {
				s.NoError(err)
				s.Require().Equal(len(altValset.Validators), len(ev.ByzantineValidators))
				fmt.Println("headers 2 validators")

				for _, v := range tc.misbehaviour.Header2.ValidatorSet.Validators {
					fmt.Println(v.String())
				}
				fmt.Println("byzantine validators")
				for _, v := range ev.ByzantineValidators {
					fmt.Println(v.String())
				}
				// TODO: check that the byzantine validators == altValset.Validators
			} else {
				s.Error(err)
			}
		})
	}

}
