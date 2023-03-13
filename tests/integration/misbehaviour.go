package integration

import (
	"time"

	ibcclientypes "github.com/cosmos/ibc-go/v4/modules/core/02-client/types"
	commitmenttypes "github.com/cosmos/ibc-go/v4/modules/core/23-commitment/types"
	ibctmtypes "github.com/cosmos/ibc-go/v4/modules/light-clients/07-tendermint/types"
	ibctestingmock "github.com/cosmos/ibc-go/v4/testing/mock"
	tmtypes "github.com/tendermint/tendermint/types"
)

const (
	trustingPeriod time.Duration = time.Hour * 24 * 7 * 2
	ubdPeriod      time.Duration = time.Hour * 24 * 7 * 3
	maxClockDrift  time.Duration = time.Second * 10
)

// mostly based on TestCheckMisbehaviourAndUpdateState in ibc-go/modules/core/02-client/keeper/client_test.go
func (s *CCVTestSuite) TestCheckConsumerMisbehaviour() {

	s.SetupCCVChannel(s.path)
	// required to have the consumer client revision height greater than 0
	s.SendEmptyVSCPacket()

	consumerConsState, _ := s.providerChain.GetConsensusState(s.path.EndpointA.ClientID, s.consumerChain.LastHeader.TrustedHeight)

	clientHeight := s.consumerChain.LastHeader.TrustedHeight
	clientTMValset := tmtypes.NewValidatorSet(s.consumerChain.Vals.Validators)
	clientSigners := s.consumerChain.Signers

	altPrivVal := ibctestingmock.NewPV()
	altPubKey, err := altPrivVal.GetPubKey()
	s.Require().NoError(err)
	altVal := tmtypes.NewValidator(altPubKey, 4)

	altValset := tmtypes.NewValidatorSet([]*tmtypes.Validator{altVal})
	altSigners := make(map[string]tmtypes.PrivValidator, 1)
	altSigners[altValset.Validators[0].Address.String()] = altPrivVal

	altTime := s.providerCtx().BlockTime().Add(time.Minute)
	heightPlus5 := ibcclientypes.NewHeight(0, clientHeight.RevisionHeight+5)

	heightPlus3 := ibcclientypes.NewHeight(0, clientHeight.RevisionHeight+3)

	testCases := []struct {
		name         string
		misbehaviour func() *ibctmtypes.Misbehaviour
		malleate     func()
		expPass      bool
	}{
		{
			"misbehaviour height is at same height as trusted height",
			func() *ibctmtypes.Misbehaviour {
				return &ibctmtypes.Misbehaviour{
					ClientId: s.path.EndpointA.ClientID,
					Header1: s.consumerChain.CreateTMClientHeader(
						s.consumerChain.ChainID,
						int64(clientHeight.RevisionHeight),
						clientHeight,
						altTime,
						clientTMValset,
						clientTMValset,
						clientTMValset,
						clientSigners,
					),
					Header2: s.consumerChain.CreateTMClientHeader(
						s.consumerChain.ChainID,
						int64(clientHeight.RevisionHeight),
						clientHeight,
						s.providerCtx().BlockTime(),
						clientTMValset,
						clientTMValset,
						clientTMValset,
						clientSigners,
					),
				}
			},
			func() {},
			false,
		}, {
			"invalid chain ID",
			func() *ibctmtypes.Misbehaviour {

				mb := &ibctmtypes.Misbehaviour{
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
				}

				mb.Header1.Header.ChainID = "wrongchainid"
				return mb

			},
			func() {},
			false,
		},
		{
			"invalid client ID",
			func() *ibctmtypes.Misbehaviour {

				mb := &ibctmtypes.Misbehaviour{
					ClientId: "wrongclientid",
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
				}

				return mb

			},
			func() {},
			false,
		}, {
			"trusting period misbehavior should pass",
			func() *ibctmtypes.Misbehaviour {
				return &ibctmtypes.Misbehaviour{
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
						s.providerCtx().BlockTime(),
						clientTMValset,
						clientTMValset,
						clientTMValset,
						clientSigners,
					),
				}
			},
			func() {},
			true,
		},
		{
			"time misbehavior should pass",
			func() *ibctmtypes.Misbehaviour {
				return &ibctmtypes.Misbehaviour{
					ClientId: s.path.EndpointA.ClientID,
					Header1: s.consumerChain.CreateTMClientHeader(
						s.consumerChain.ChainID,
						int64(clientHeight.RevisionHeight+5),
						clientHeight,
						s.providerCtx().BlockTime(),
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
				}
			},
			func() {},
			true,
		},
		{
			"both later height should pass",
			func() *ibctmtypes.Misbehaviour {
				return &ibctmtypes.Misbehaviour{
					ClientId: s.path.EndpointA.ClientID,
					Header1: s.consumerChain.CreateTMClientHeader(
						s.consumerChain.ChainID,
						int64(heightPlus5.RevisionHeight+1),
						clientHeight,
						s.providerCtx().BlockTime(),
						clientTMValset,
						clientTMValset,
						clientTMValset,
						clientSigners,
					),
					Header2: s.consumerChain.CreateTMClientHeader(
						s.consumerChain.ChainID,
						int64(heightPlus5.RevisionHeight+1),
						heightPlus3,
						altTime,
						clientTMValset,
						clientTMValset,
						clientTMValset,
						clientSigners,
					),
				}
			},
			func() {

				consumerConsState.(*ibctmtypes.ConsensusState).NextValidatorsHash = clientTMValset.Hash()
				clientState := ibctmtypes.NewClientState(s.consumerChain.ChainID, ibctmtypes.DefaultTrustLevel, trustingPeriod, ubdPeriod, maxClockDrift, clientHeight, commitmenttypes.GetSDKSpecs(), []string{"upgrade", "upgradedIBCState"}, false, false)

				// store trusted consensus state for Header2
				intermediateConsState := &ibctmtypes.ConsensusState{
					Timestamp:          altTime,
					NextValidatorsHash: clientTMValset.Hash(),
				}

				s.providerApp.GetIBCKeeper().ClientKeeper.SetClientConsensusState(s.providerCtx(), s.path.EndpointA.ClientID, heightPlus3, intermediateConsState)

				clientState.LatestHeight = heightPlus3
				s.providerApp.GetIBCKeeper().ClientKeeper.SetClientState(s.providerCtx(), s.path.EndpointA.ClientID, clientState)
			},
			true,
		},
		{
			"trusted ConsensusState1 not found",
			func() *ibctmtypes.Misbehaviour {
				return &ibctmtypes.Misbehaviour{
					ClientId: s.path.EndpointA.ClientID,
					Header1: s.consumerChain.CreateTMClientHeader(
						s.consumerChain.ChainID,
						int64(clientHeight.RevisionHeight),
						heightPlus3,
						altTime,
						clientTMValset,
						clientTMValset,
						clientTMValset,
						clientSigners,
					),
					Header2: s.consumerChain.CreateTMClientHeader(
						s.consumerChain.ChainID,
						int64(clientHeight.RevisionHeight),
						clientHeight,
						s.providerCtx().BlockTime(),
						clientTMValset,
						clientTMValset,
						clientTMValset,
						clientSigners,
					),
				}
			},
			func() {},
			false,
		},
		{
			"trusted ConsensusState2 not found",
			func() *ibctmtypes.Misbehaviour {
				return &ibctmtypes.Misbehaviour{
					ClientId: s.path.EndpointA.ClientID,
					Header1: s.consumerChain.CreateTMClientHeader(
						s.consumerChain.ChainID,
						int64(clientHeight.RevisionHeight),
						clientHeight,
						altTime,
						clientTMValset,
						clientTMValset,
						clientTMValset,
						clientSigners,
					),
					Header2: s.consumerChain.CreateTMClientHeader(
						s.consumerChain.ChainID,
						int64(clientHeight.RevisionHeight),
						heightPlus3,
						s.providerCtx().BlockTime(),
						clientTMValset,
						clientTMValset,
						clientTMValset,
						clientSigners,
					),
				}
			},
			func() {},
			false,
		},
		{
			"client state not found",
			func() *ibctmtypes.Misbehaviour {
				return &ibctmtypes.Misbehaviour{}
			},
			func() {},
			false,
		}, {
			"client already is not active - client is frozen",
			func() *ibctmtypes.Misbehaviour {
				return &ibctmtypes.Misbehaviour{}
			},
			func() {
				consumerConsState.(*ibctmtypes.ConsensusState).NextValidatorsHash = clientTMValset.Hash()
				clientState := ibctmtypes.NewClientState(s.consumerChain.ChainID, ibctmtypes.DefaultTrustLevel, trustingPeriod, ubdPeriod, maxClockDrift, clientHeight, commitmenttypes.GetSDKSpecs(), []string{"upgrade", "upgradedIBCState"}, false, false)

				clientState.FrozenHeight = ibcclientypes.NewHeight(0, 1)
				s.providerApp.GetIBCKeeper().ClientKeeper.SetClientState(s.providerCtx(), s.path.EndpointA.ClientID, clientState)
			},
			false,
		},
		{
			"misbehaviour check failed",
			func() *ibctmtypes.Misbehaviour {
				return &ibctmtypes.Misbehaviour{
					ClientId: s.path.EndpointA.ClientID,
					Header1: s.consumerChain.CreateTMClientHeader(
						s.consumerChain.ChainID,
						int64(clientHeight.RevisionHeight+1),
						clientHeight,
						s.providerCtx().BlockTime(),
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
			},
			func() {},
			false,
		},
	}

	for i, tc := range testCases {

		s.Run(tc.name, func() {
			// run each test against fresh client states
			cCtx, _ := s.providerCtx().CacheContext()

			tc.malleate()

			err = s.providerApp.GetProviderKeeper().CheckConsumerMisbehaviour(
				cCtx,
				*tc.misbehaviour(),
			)

			// Misbehaviour passed
			if tc.expPass {
				s.NoError(err, "valid test case %s failed with error %s", tc.name, err)
				clientState, found := s.providerApp.GetIBCKeeper().ClientKeeper.GetClientState(cCtx, tc.misbehaviour().ClientId)
				s.Require().True(found, "valid test case %d failed: %s", i, tc.name)
				s.Require().True(!clientState.(*ibctmtypes.ClientState).FrozenHeight.IsZero(), "valid test case %d failed: %s", i, tc.name)

			} else {
				// Misbehaviour rejected
				s.Require().Error(err, "invalid test case %d passed: %s", i, tc.name)
			}
		})
	}
}
