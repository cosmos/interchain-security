package e2e

import (
	"time"

	sdk "github.com/cosmos/cosmos-sdk/types"
	evidencetypes "github.com/cosmos/cosmos-sdk/x/evidence/types"
	govtypes "github.com/cosmos/cosmos-sdk/x/gov/types"
	providertypes "github.com/cosmos/interchain-security/x/ccv/provider/types"
)

func (s *CCVTestSuite) TestPauseUnbondingOnEquivocationProposal() {
	tests := []struct {
		name                string
		setup               func() govtypes.Content
		expectedWithoutProp unbondingsOnHold
		expectedDuringProp  unbondingsOnHold
	}{
		{
			// Assert a text proposal doesn't pause any existing unbondings
			name: "text proposal and unbonding delegation",
			setup: func() govtypes.Content {
				var (
					bondAmt = sdk.NewInt(10000000)
					delAddr = s.providerChain.SenderAccount.GetAddress()
				)
				// delegate bondAmt and undelegate it
				delegateAndUndelegate(s, delAddr, bondAmt, 1)

				return govtypes.NewTextProposal("title", "desc")
			},
			expectedWithoutProp: unbondingsOnHold{
				unbondingDelegationRefCount: 1,
			},
			expectedDuringProp: unbondingsOnHold{
				unbondingDelegationRefCount: 1,
			},
		},
		{
			// Assert an equivocation proposal pauses nothing if there's no existing
			// unbondings.
			name: "equivocation proposal and no unbonding",
			setup: func() govtypes.Content {
				var (
					val, _      = s.getValByIdx(0)
					consAddr, _ = val.GetConsAddr()
				)
				return providertypes.NewEquivocationProposal("title", "desc",
					[]*evidencetypes.Equivocation{{
						Height:           1,
						Power:            1,
						Time:             time.Now(),
						ConsensusAddress: consAddr.String(),
					}},
				)
			},
			expectedWithoutProp: unbondingsOnHold{},
			expectedDuringProp:  unbondingsOnHold{},
		},
		{
			// Assert an equivocation proposal pauses unbonding delegations
			name: "equivocation proposal and unbonding delegation",
			setup: func() govtypes.Content {
				// create an unbonding entry of type UnbondingDelegation
				var (
					bondAmt     = sdk.NewInt(10000000)
					delAddr     = s.providerChain.SenderAccount.GetAddress()
					val, _      = s.getValByIdx(0)
					consAddr, _ = val.GetConsAddr()
				)
				// delegate bondAmt and undelegate it
				delegateAndUndelegate(s, delAddr, bondAmt, 1)

				return providertypes.NewEquivocationProposal("title", "desc",
					[]*evidencetypes.Equivocation{{
						Height:           1,
						Power:            1,
						Time:             time.Now(),
						ConsensusAddress: consAddr.String(),
					}},
				)
			},
			expectedWithoutProp: unbondingsOnHold{
				unbondingDelegationRefCount: 1,
			},
			expectedDuringProp: unbondingsOnHold{
				unbondingDelegationRefCount: 2,
			},
		},
		{
			// Assert an equivocation proposal pauses redelegations
			name: "equivocation proposal and redelegate",
			setup: func() govtypes.Content {
				// create an unbonding entry of type UnbondingDelegation
				var (
					bondAmt         = sdk.NewInt(10000000)
					delAddr         = s.providerChain.SenderAccount.GetAddress()
					val, valSrcAddr = s.getValByIdx(0)
					_, valDstAddr   = s.getValByIdx(1)
					consAddr, _     = val.GetConsAddr()
				)
				// delegate bondAmt and redelegate it
				delegateAndRedelegate(s, delAddr, valSrcAddr, valDstAddr, bondAmt)

				return providertypes.NewEquivocationProposal("title", "desc",
					[]*evidencetypes.Equivocation{{
						Height:           1,
						Power:            1,
						Time:             time.Now(),
						ConsensusAddress: consAddr.String(),
					}},
				)
			},
			expectedWithoutProp: unbondingsOnHold{
				redelegationRefCount: 1,
			},
			expectedDuringProp: unbondingsOnHold{
				redelegationRefCount: 2,
			},
		},
		{
			// Assert an equivocation proposal pauses validator unbonding
			name: "equivocation proposal and validator unbonding",
			setup: func() govtypes.Content {
				var (
					delAddr      = s.providerChain.SenderAccount.GetAddress()
					val, valAddr = s.getValByIdx(0)
					consAddr, _  = val.GetConsAddr()
				)
				// unbond validator by undelegate all his delegation (test setup only
				// delegates from delAddr, there's no validator self delegation)
				undelegate(s, delAddr, valAddr, sdk.NewDec(1))

				return providertypes.NewEquivocationProposal("title", "desc",
					[]*evidencetypes.Equivocation{{
						Height:           1,
						Power:            1,
						Time:             time.Now(),
						ConsensusAddress: consAddr.String(),
					}},
				)
			},
			expectedWithoutProp: unbondingsOnHold{
				unbondingDelegationRefCount: 1,
				validatorUnbondingRefCount:  1,
			},
			expectedDuringProp: unbondingsOnHold{
				unbondingDelegationRefCount: 2,
				validatorUnbondingRefCount:  2,
			},
		},
	}
	submitProp := func(s *CCVTestSuite, content govtypes.Content) uint64 {
		proposal, err := s.providerApp.GetE2eGovKeeper().SubmitProposal(s.providerCtx(), content)
		s.Require().NoError(err)
		return proposal.ProposalId
	}
	addDepositProp := func(s *CCVTestSuite, proposalID uint64, depositAmt sdk.Coins) {
		depositorAddr := s.providerChain.SenderAccount.GetAddress()
		_, err := s.providerApp.GetE2eGovKeeper().AddDeposit(
			s.providerCtx(), proposalID, depositorAddr, depositAmt,
		)
		s.Require().NoError(err)
	}
	for i, tt := range tests {
		s.Run(tt.name, func() {
			if i+1 < len(tests) {
				// reset suite to reset provider client
				defer s.SetupTest()
			}

			//-----------------------------------------
			// Setup

			var (
				govContent    = tt.setup()
				val, valAddr  = s.getValByIdx(0)
				consAddr, _   = val.GetConsAddr()
				govKeeper     = s.providerApp.GetE2eGovKeeper()
				dustAmt       = sdk.NewCoins(sdk.NewCoin(sdk.DefaultBondDenom, sdk.NewInt(1)))
				minDepositAmt = govKeeper.GetDepositParams(s.providerCtx()).MinDeposit
			)
			// Equivocation proposal requires validator signing info and a slash log
			s.setDefaultValSigningInfo(*s.providerChain.Vals.Validators[0])
			s.providerApp.GetProviderKeeper().SetSlashLog(s.providerCtx(),
				providertypes.NewProviderConsAddress(consAddr))
			// Reduce voting period
			votingParams := govKeeper.GetVotingParams(s.providerCtx())
			votingParams.VotingPeriod = 3 * time.Second
			govKeeper.SetVotingParams(s.providerCtx(), votingParams)
			// Reduce deposit period
			depositParams := govKeeper.GetDepositParams(s.providerCtx())
			depositParams.MaxDepositPeriod = 3 * time.Second
			govKeeper.SetDepositParams(s.providerCtx(), depositParams)
			// must move one block forward because unbonding validators are detected
			// during EndBlock.
			s.providerChain.NextBlock()
			checkStakingUnbondingOnHoldRefCount(s, valAddr, tt.expectedWithoutProp)

			//-----------------------------------------
			// #1 Create a proposal, activate it and wait for voting period

			proposalID := submitProp(s, govContent)
			checkStakingUnbondingOnHoldRefCount(s, valAddr, tt.expectedWithoutProp)
			// assert that until voting period starts, there's no pause triggered
			addDepositProp(s, proposalID, dustAmt)
			checkStakingUnbondingOnHoldRefCount(s, valAddr, tt.expectedWithoutProp)
			// activate prop
			addDepositProp(s, proposalID, minDepositAmt)
			checkStakingUnbondingOnHoldRefCount(s, valAddr, tt.expectedDuringProp)
			// assert that an additionnal deposit done after the activation doesn't
			// trigger additionnal pauses
			addDepositProp(s, proposalID, dustAmt)
			checkStakingUnbondingOnHoldRefCount(s, valAddr, tt.expectedDuringProp)
			// ends the voting period
			incrementTime(s, votingParams.VotingPeriod)
			checkStakingUnbondingOnHoldRefCount(s, valAddr, tt.expectedWithoutProp)
			s.Assert().False(
				s.providerApp.GetProviderKeeper().HasEquivocationProposal(s.providerCtx(), proposalID),
				"proposalID should be removed from store after voting period",
			)

			//-----------------------------------------
			// #2 Create an other proposal but let it expire (not enough deposit)

			proposalID = submitProp(s, govContent)
			checkStakingUnbondingOnHoldRefCount(s, valAddr, tt.expectedWithoutProp)
			incrementTime(s, depositParams.MaxDepositPeriod)
			checkStakingUnbondingOnHoldRefCount(s, valAddr, tt.expectedWithoutProp)
			s.Assert().False(
				s.providerApp.GetProviderKeeper().HasEquivocationProposal(s.providerCtx(), proposalID),
				"proposalID shouldn't be registered if proposal didn't reach the voting period",
			)
		})
	}
}
