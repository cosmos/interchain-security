package main

import (
	"testing"

	clienttypes "github.com/cosmos/ibc-go/v7/modules/core/02-client/types"
	"pgregory.net/rapid"
)

func TestChainStateMarshalling(t *testing.T) {
	rapid.Check(t, func(t *rapid.T) {
		chainState := GetChainStateGen().Draw(t, "ChainState")
		err := MarshalAndUnmarshalChainState(chainState)
		if err != nil {
			t.Fatalf("error marshalling and unmarshalling chain state: %v", err)
		}
	})
}

func GetStateGen() *rapid.Generator[State] {
	return rapid.Custom(func(t *rapid.T) State {
		return rapid.MapOf(GetChainIDGen(), GetChainStateGen()).Draw(t, "State")
	})
}

func GetChainStateGen() *rapid.Generator[ChainState] {
	return rapid.Custom(
		func(t *rapid.T) ChainState {
			valBalances := GetValBalancesGen().Draw(t, "ValBalances")
			proposals := GetProposalsGen().Draw(t, "Proposals")
			valPowers := GetValPowersGen().Draw(t, "ValPowers")
			representativePowers := GetRepresentativePowersGen().Draw(t, "RepresentativePowers")
			params := GetParamsGen().Draw(t, "Params")
			rewards := GetRewardsGen().Draw(t, "Rewards")
			consumerChains := GetConsumerChainsGen().Draw(t, "ConsumerChains")
			assignedKeys := GetAssignedKeysGen().Draw(t, "AssignedKeys")
			providerKeys := GetProviderKeysGen().Draw(t, "ProviderKeys")
			consumerChainQueueSizes := GetConsumerChainQueueSizesGen().Draw(t, "ConsumerChainQueueSizes")
			globalSlashQueueSize := rapid.Uint().Draw(t, "GlobalSlashQueueSize")

			return ChainState{
				ValBalances:             &valBalances,
				Proposals:               &proposals,
				ValPowers:               &valPowers,
				RepresentativePowers:    &representativePowers,
				Params:                  &params,
				Rewards:                 &rewards,
				ConsumerChains:          &consumerChains,
				AssignedKeys:            &assignedKeys,
				ProviderKeys:            &providerKeys,
				ConsumerChainQueueSizes: &consumerChainQueueSizes,
				GlobalSlashQueueSize:    &globalSlashQueueSize,
			}
		})
}

func GetConsumerChainQueueSizesGen() *rapid.Generator[map[ChainID]uint] {
	return rapid.Custom(func(t *rapid.T) map[ChainID]uint {
		return rapid.MapOf(GetChainIDGen(), rapid.Uint()).Draw(t, "ConsumerChainQueueSizes")
	})
}

func GetProviderKeysGen() *rapid.Generator[map[ValidatorID]string] {
	return rapid.Custom(func(t *rapid.T) map[ValidatorID]string {
		return rapid.MapOf(GetValidatorIDGen(), rapid.String()).Draw(t, "ProviderKeys")
	})
}

func GetAssignedKeysGen() *rapid.Generator[map[ValidatorID]string] {
	return rapid.Custom(func(t *rapid.T) map[ValidatorID]string {
		return rapid.MapOf(GetValidatorIDGen(), rapid.String()).Draw(t, "AssignedKeys")
	})
}

func GetChainIDGen() *rapid.Generator[ChainID] {
	return rapid.Custom(func(t *rapid.T) ChainID {
		return ChainID(rapid.String().Draw(t, "ChainID"))
	})
}

func GetConsumerChainsGen() *rapid.Generator[map[ChainID]bool] {
	return rapid.Custom(func(t *rapid.T) map[ChainID]bool {
		return rapid.MapOf(GetChainIDGen(), rapid.Bool()).Draw(t, "ConsumerChains")
	})
}

func GetRewardsGen() *rapid.Generator[Rewards] {
	return rapid.Custom(func(t *rapid.T) Rewards {
		return Rewards{
			IsIncrementalReward: rapid.Bool().Draw(t, "IsIncrementalReward"),
			IsNativeDenom:       rapid.Bool().Draw(t, "IsNativeDenom"),
			IsRewarded:          rapid.MapOf(GetValidatorIDGen(), rapid.Bool()).Draw(t, "IsRewarded"),
		}
	})
}

func GetParamsGen() *rapid.Generator[[]Param] {
	return rapid.Custom(func(t *rapid.T) []Param {
		return rapid.SliceOf(GetParamGen()).Draw(t, "Params")
	})
}

func GetParamGen() *rapid.Generator[Param] {
	return rapid.Custom(func(t *rapid.T) Param {
		return Param{
			Key:   rapid.String().Draw(t, "Key"),
			Value: rapid.String().Draw(t, "Value"),
		}
	})
}

func GetRepresentativePowersGen() *rapid.Generator[map[ValidatorID]uint] {
	return rapid.Custom(func(t *rapid.T) map[ValidatorID]uint {
		return rapid.MapOf(
			GetValidatorIDGen(),
			rapid.Uint(),
		).Draw(t, "RepresentativePowers")
	})
}

func GetValPowersGen() *rapid.Generator[map[ValidatorID]uint] {
	return rapid.Custom(func(t *rapid.T) map[ValidatorID]uint {
		return rapid.MapOf(
			GetValidatorIDGen(),
			rapid.Uint(),
		).Draw(t, "ValPowers")
	})
}

func GetValBalancesGen() *rapid.Generator[map[ValidatorID]uint] {
	return rapid.Custom(func(t *rapid.T) map[ValidatorID]uint {
		return rapid.MapOf(
			GetValidatorIDGen(),
			rapid.Uint(),
		).Draw(t, "ValBalances")
	})
}

func GetValidatorIDGen() *rapid.Generator[ValidatorID] {
	return rapid.Custom(func(t *rapid.T) ValidatorID {
		return ValidatorID(rapid.String().Draw(t, "ValidatorID"))
	})
}

func GetProposalsGen() *rapid.Generator[map[uint]Proposal] {
	return rapid.Custom(func(t *rapid.T) map[uint]Proposal {
		return rapid.MapOf(
			rapid.Uint(),
			GetProposalGen(),
		).Draw(t, "Proposals")
	})
}

func GetProposalGen() *rapid.Generator[Proposal] {
	return rapid.Custom(func(t *rapid.T) Proposal {
		gen := rapid.OneOf(
			GetConsumerAdditionProposalGen().AsAny(),
			GetConsumerRemovalProposalGen().AsAny(),
			GetEquivocationProposalGen().AsAny(),
			GetTextProposalGen().AsAny(),
			GetParamsProposalGen().AsAny(),
		)
		return gen.Draw(t, "Proposal").(Proposal)
	})
}

func GetConsumerAdditionProposalGen() *rapid.Generator[ConsumerAdditionProposal] {
	return rapid.Custom(func(t *rapid.T) ConsumerAdditionProposal {
		return ConsumerAdditionProposal{
			Deposit:       rapid.Uint().Draw(t, "Deposit"),
			Chain:         GetChainIDGen().Draw(t, "Chain"),
			SpawnTime:     rapid.Int().Draw(t, "SpawnTime"),
			InitialHeight: GetHeightGen().Draw(t, "InitialHeight"),
			Status:        rapid.String().Draw(t, "Status"),
		}
	})
}

func GetConsumerRemovalProposalGen() *rapid.Generator[ConsumerRemovalProposal] {
	return rapid.Custom(func(t *rapid.T) ConsumerRemovalProposal {
		return ConsumerRemovalProposal{
			Deposit:  rapid.Uint().Draw(t, "Deposit"),
			Chain:    GetChainIDGen().Draw(t, "Chain"),
			StopTime: rapid.Int().Draw(t, "StopTime"),
			Status:   rapid.String().Draw(t, "Status"),
		}
	})
}

func GetEquivocationProposalGen() *rapid.Generator[EquivocationProposal] {
	return rapid.Custom(func(t *rapid.T) EquivocationProposal {
		return EquivocationProposal{
			Power:            rapid.Uint().Draw(t, "Power"),
			Height:           rapid.Uint().Draw(t, "Height"),
			ConsensusAddress: rapid.String().Draw(t, "ConesnsuAddress"),
			Deposit:          rapid.Uint().Draw(t, "Deposit"),
			Status:           rapid.String().Draw(t, "Status"),
		}
	})
}

func GetTextProposalGen() *rapid.Generator[TextProposal] {
	return rapid.Custom(func(t *rapid.T) TextProposal {
		return TextProposal{
			Title:       rapid.String().Draw(t, "Title"),
			Description: rapid.String().Draw(t, "Description"),
			Deposit:     rapid.Uint().Draw(t, "Deposit"),
			Status:      rapid.String().Draw(t, "Status"),
		}
	})
}

func GetParamsProposalGen() *rapid.Generator[ParamsProposal] {
	return rapid.Custom(func(t *rapid.T) ParamsProposal {
		return ParamsProposal{
			Subspace: rapid.String().Draw(t, "Subspace"),
			Key:      rapid.String().Draw(t, "Key"),
			Value:    rapid.String().Draw(t, "Value"),
			Deposit:  rapid.Uint().Draw(t, "Deposit"),
			Status:   rapid.String().Draw(t, "Status"),
		}
	})
}

func GetHeightGen() *rapid.Generator[clienttypes.Height] {
	return rapid.Custom(func(t *rapid.T) clienttypes.Height {
		return clienttypes.Height{
			RevisionNumber: rapid.Uint64().Draw(t, "RevisionNumber"),
			RevisionHeight: rapid.Uint64().Draw(t, "RevisionHeight"),
		}
	})
}
