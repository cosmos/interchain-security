package main

import (
	"encoding/json"
	"fmt"
	"testing"
	"time"

	"github.com/google/go-cmp/cmp"
	"github.com/stretchr/testify/require"
	"pgregory.net/rapid"
)

// This file contains tests for serialization/deserialization of actions.
// The tests are written using the rapid testing library, which allows us to
// generate arbitrary actions and test that they can be serialized and
// deserialized without error.
// The generators for the various actions are defined in this file, and
// essentially tell rapid how to build these actions.

func TestActionMarshalling(t *testing.T) {
	rapid.Check(t, func(t *rapid.T) {
		action := GetActionGen().Draw(t, "Action")
		err := MarshalAndUnmarshalAction(action)
		if err != nil {
			t.Fatalf("error marshalling and unmarshalling action: %v", err)
		}
	})
}

func MarshalAndUnmarshalAction(action interface{}) error {
	// wraps the action with a step, since it needs custom unmarshalling that is called by the step unmarshaller
	step := Step{
		Action: action,
	}
	jsonobj, err := json.Marshal(step)
	if err != nil {
		return fmt.Errorf("error marshalling action inside step: %v", err)
	}

	var got Step
	err = json.Unmarshal(jsonobj, &got)
	if err != nil {
		return fmt.Errorf("error unmarshalling action inside step: %v", err)
	}

	diff := cmp.Diff(step, got)
	if diff != "" {
		return fmt.Errorf("got (-), want (+): %v", diff)
	}

	return nil
}

// This needs to be adjusted manually when new actions are added and should
// include generators for all actions that are mentioned in main.go/runStep.
func GetActionGen() *rapid.Generator[any] {
	return rapid.OneOf(
		GetStartSovereignChainActionGen().AsAny(),
		GetSubmitLegacyUpgradeProposalActionGen().AsAny(),
		GetWaitUntilBlockActionGen().AsAny(),
		GetChangeoverChainActionGen().AsAny(),
		GetSendTokensActionGen().AsAny(),
		GetStartChainActionGen().AsAny(),
		GetSubmitTextProposalActionGen().AsAny(),
		GetSubmitConsumerAdditionProposalActionGen().AsAny(),
		GetSubmitConsumerRemovalProposalActionGen().AsAny(),
		GetSubmitParamChangeProposalActionGen().AsAny(),
		GetVoteGovProposalActionGen().AsAny(),
		GetStartConsumerChainActionGen().AsAny(),
		GetAddChainToRelayerActionGen().AsAny(),
		GetAddIbcConnectionActionGen().AsAny(),
		GetAddIbcChannelActionGen().AsAny(),
		GetStartRelayerActionGen().AsAny(),
		GetTransferChannelCompleteActionGen().AsAny(),
		GetRelayPacketsActionGen().AsAny(),
		GetRelayRewardPacketsToProviderActionGen().AsAny(),
		GetDelegateTokensActionGen().AsAny(),
		GetUnbondTokensActionGen().AsAny(),
		GetReDelegateTokensActionGen().AsAny(),
		GetDowntimeSlashActionGen().AsAny(),
		GetUnjailValidatorActionGen().AsAny(),
		GetRegisterRepresentativeActionGen().AsAny(),
		GetDoublesignSlashActionGen().AsAny(),
		GetAssignConsumerPubKeyActionGen().AsAny(),
		GetCreateIbcClientsActionGen().AsAny(),
		GetSlashMeterReplenishmentAction().AsAny(),
		GetWaitTimeAction().AsAny(),
		CreateCancelUnbondTokensActionGen().AsAny(),
		CreateLightClientEquivocationAttackActionGen().AsAny(),
		CreateLightClientAmnesiaAttackActionGen().AsAny(),
		CreateLightClientLunaticAttackActionGen().AsAny(),
		GetStartConsumerEvidenceDetectorActionGen().AsAny(),
		GetForkConsumerChainActionGen().AsAny(),
		GetUpdateLightClientActionGen().AsAny(),
	)
}

func CreateSubmitChangeRewardDenomsProposalActionGen() *rapid.Generator[SubmitChangeRewardDenomsProposalAction] {
	return rapid.Custom(func(t *rapid.T) SubmitChangeRewardDenomsProposalAction {
		return SubmitChangeRewardDenomsProposalAction{
			From:    GetValidatorIDGen().Draw(t, "From"),
			Deposit: rapid.Uint().Draw(t, "Deposit"),
			Denom:   rapid.String().Draw(t, "Denom"),
		}
	})
}

func CreateLightClientEquivocationAttackActionGen() *rapid.Generator[LightClientEquivocationAttackAction] {
	return rapid.Custom(func(t *rapid.T) LightClientEquivocationAttackAction {
		return LightClientEquivocationAttackAction{
			Validator: GetValidatorIDGen().Draw(t, "Validator"),
			Chain:     GetChainIDGen().Draw(t, "Chain"),
		}
	})
}

func CreateLightClientAmnesiaAttackActionGen() *rapid.Generator[LightClientAmnesiaAttackAction] {
	return rapid.Custom(func(t *rapid.T) LightClientAmnesiaAttackAction {
		return LightClientAmnesiaAttackAction{
			Validator: GetValidatorIDGen().Draw(t, "Validator"),
			Chain:     GetChainIDGen().Draw(t, "Chain"),
		}
	})
}

func CreateLightClientLunaticAttackActionGen() *rapid.Generator[LightClientLunaticAttackAction] {
	return rapid.Custom(func(t *rapid.T) LightClientLunaticAttackAction {
		return LightClientLunaticAttackAction{
			Validator: GetValidatorIDGen().Draw(t, "Validator"),
			Chain:     GetChainIDGen().Draw(t, "Chain"),
		}
	})
}

func CreateCancelUnbondTokensActionGen() *rapid.Generator[CancelUnbondTokensAction] {
	return rapid.Custom(func(t *rapid.T) CancelUnbondTokensAction {
		return CancelUnbondTokensAction{
			Chain:     GetChainIDGen().Draw(t, "Chain"),
			Amount:    rapid.Uint().Draw(t, "Amount"),
			Delegator: GetValidatorIDGen().Draw(t, "Delegator"),
			Validator: GetValidatorIDGen().Draw(t, "Validator"),
		}
	})
}

func GetCreateIbcClientsActionGen() *rapid.Generator[CreateIbcClientsAction] {
	return rapid.Custom(func(t *rapid.T) CreateIbcClientsAction {
		return CreateIbcClientsAction{
			ChainA: GetChainIDGen().Draw(t, "ChainA"),
			ChainB: GetChainIDGen().Draw(t, "ChainB"),
		}
	})
}

func GetStartSovereignChainActionGen() *rapid.Generator[StartSovereignChainAction] {
	return rapid.Custom(func(t *rapid.T) StartSovereignChainAction {
		return StartSovereignChainAction{
			Chain:          GetChainIDGen().Draw(t, "Chain"),
			Validators:     GetStartChainValidatorsGen().Draw(t, "Validators"),
			GenesisChanges: rapid.String().Draw(t, "GenesisChanges"),
		}
	})
}

func GetSubmitLegacyUpgradeProposalActionGen() *rapid.Generator[LegacyUpgradeProposalAction] {
	return rapid.Custom(func(t *rapid.T) LegacyUpgradeProposalAction {
		return LegacyUpgradeProposalAction{
			ChainID:       GetChainIDGen().Draw(t, "ChainID"),
			UpgradeTitle:  rapid.String().Draw(t, "UpgradeTitle"),
			Proposer:      GetValidatorIDGen().Draw(t, "Proposer"),
			UpgradeHeight: rapid.Uint64().Draw(t, "UpgradeHeight"),
		}
	})
}

func GetWaitUntilBlockActionGen() *rapid.Generator[WaitUntilBlockAction] {
	return rapid.Custom(func(t *rapid.T) WaitUntilBlockAction {
		return WaitUntilBlockAction{
			Chain: GetChainIDGen().Draw(t, "Chain"),
			Block: rapid.Uint().Draw(t, "Block"),
		}
	})
}

func GetChangeoverChainActionGen() *rapid.Generator[ChangeoverChainAction] {
	return rapid.Custom(func(t *rapid.T) ChangeoverChainAction {
		return ChangeoverChainAction{
			SovereignChain: GetChainIDGen().Draw(t, "SovereignChain"),
			ProviderChain:  GetChainIDGen().Draw(t, "ProviderChain"),
			Validators:     GetStartChainValidatorsGen().Draw(t, "Validators"),
			GenesisChanges: rapid.String().Draw(t, "GenesisChanges"),
		}
	})
}

func GetSendTokensActionGen() *rapid.Generator[SendTokensAction] {
	return rapid.Custom(func(t *rapid.T) SendTokensAction {
		return SendTokensAction{
			Amount: rapid.Uint().Draw(t, "Amount"),
			Chain:  GetChainIDGen().Draw(t, "Chain"),
			From:   GetValidatorIDGen().Draw(t, "From"),
			To:     GetValidatorIDGen().Draw(t, "To"),
		}
	})
}

func GetStartChainActionGen() *rapid.Generator[StartChainAction] {
	return rapid.Custom(func(t *rapid.T) StartChainAction {
		return StartChainAction{
			Chain:          GetChainIDGen().Draw(t, "Chain"),
			Validators:     GetStartChainValidatorsGen().Draw(t, "Validators"),
			GenesisChanges: rapid.String().Draw(t, "GenesisChanges"),
			IsConsumer:     rapid.Bool().Draw(t, "IsConsumer"),
		}
	})
}

func GetStartChainValidatorsGen() *rapid.Generator[[]StartChainValidator] {
	return rapid.Custom(func(t *rapid.T) []StartChainValidator {
		return rapid.SliceOf(GetStartChainValidatorGen()).Draw(t, "StartChainValidators")
	})
}

func GetStartChainValidatorGen() *rapid.Generator[StartChainValidator] {
	return rapid.Custom(func(t *rapid.T) StartChainValidator {
		return StartChainValidator{
			Id:         GetValidatorIDGen().Draw(t, "Id"),
			Allocation: rapid.Uint().Draw(t, "Allocation"),
			Stake:      rapid.Uint().Draw(t, "Stake"),
		}
	})
}

func GetSubmitTextProposalActionGen() *rapid.Generator[SubmitTextProposalAction] {
	return rapid.Custom(func(t *rapid.T) SubmitTextProposalAction {
		return SubmitTextProposalAction{
			Chain:       GetChainIDGen().Draw(t, "Chain"),
			From:        GetValidatorIDGen().Draw(t, "From"),
			Deposit:     rapid.Uint().Draw(t, "Deposit"),
			Title:       rapid.String().Draw(t, "Title"),
			Description: rapid.String().Draw(t, "Description"),
		}
	})
}

func GetSubmitConsumerAdditionProposalActionGen() *rapid.Generator[SubmitConsumerAdditionProposalAction] {
	return rapid.Custom(func(t *rapid.T) SubmitConsumerAdditionProposalAction {
		return SubmitConsumerAdditionProposalAction{
			Chain:         GetChainIDGen().Draw(t, "Chain"),
			From:          GetValidatorIDGen().Draw(t, "From"),
			Deposit:       rapid.Uint().Draw(t, "Deposit"),
			ConsumerChain: GetChainIDGen().Draw(t, "ConsumerChain"),
			SpawnTime:     rapid.Uint().Draw(t, "SpawnTime"),
			InitialHeight: GetHeightGen().Draw(t, "InitialHeight"),
		}
	})
}

func GetSubmitConsumerRemovalProposalActionGen() *rapid.Generator[SubmitConsumerRemovalProposalAction] {
	return rapid.Custom(func(t *rapid.T) SubmitConsumerRemovalProposalAction {
		return SubmitConsumerRemovalProposalAction{
			Chain:          GetChainIDGen().Draw(t, "Chain"),
			From:           GetValidatorIDGen().Draw(t, "From"),
			Deposit:        rapid.Uint().Draw(t, "Deposit"),
			ConsumerChain:  GetChainIDGen().Draw(t, "ConsumerChain"),
			StopTimeOffset: time.Duration(rapid.Int64().Draw(t, "StopTimeOffset")),
		}
	})
}

func GetSubmitParamChangeProposalActionGen() *rapid.Generator[SubmitParamChangeLegacyProposalAction] {
	return rapid.Custom(func(t *rapid.T) SubmitParamChangeLegacyProposalAction {
		return SubmitParamChangeLegacyProposalAction{
			Chain:    GetChainIDGen().Draw(t, "Chain"),
			From:     GetValidatorIDGen().Draw(t, "From"),
			Deposit:  rapid.Uint().Draw(t, "Deposit"),
			Subspace: rapid.String().Draw(t, "Subspace"),
			Key:      rapid.String().Draw(t, "Key"),
			Value:    rapid.String().Draw(t, "Value"), // could make this more generic in the future, since Value takes interfaces
		}
	})
}

func TestMarshalAndUnmarshalTime(t *testing.T) {
	rapid.Check(t, func(t *rapid.T) {
		time1 := GetTimeGen().Draw(t, "time")
		data, err := time1.MarshalJSON()
		require.NoError(t, err)
		var time2 time.Time
		err = time2.UnmarshalJSON(data)
		require.NoError(t, err)
		require.True(t, time1.Equal(time2))
	})
}

func GetTimeGen() *rapid.Generator[time.Time] {
	return rapid.Custom(func(t *rapid.T) time.Time {
		return time.Unix(rapid.Int64Range(-5.9959e+10, 1.5779e+11).Draw(t, "unix time"), 0).UTC()
	})
}

func GetVoteGovProposalActionGen() *rapid.Generator[VoteGovProposalAction] {
	return rapid.Custom(func(t *rapid.T) VoteGovProposalAction {
		return VoteGovProposalAction{
			Chain:      GetChainIDGen().Draw(t, "Chain"),
			From:       rapid.SliceOf(GetValidatorIDGen()).Draw(t, "From"),
			Vote:       rapid.SliceOf(rapid.String()).Draw(t, "Vote"),
			PropNumber: rapid.Uint().Draw(t, "PropNumber"),
		}
	})
}

func GetStartConsumerChainActionGen() *rapid.Generator[StartConsumerChainAction] {
	return rapid.Custom(func(t *rapid.T) StartConsumerChainAction {
		return StartConsumerChainAction{
			ConsumerChain:  GetChainIDGen().Draw(t, "ConsumerChain"),
			ProviderChain:  GetChainIDGen().Draw(t, "ProviderChain"),
			Validators:     GetStartChainValidatorsGen().Draw(t, "Validators"),
			GenesisChanges: rapid.String().Draw(t, "GenesisChanges"),
		}
	})
}

func GetAddChainToRelayerActionGen() *rapid.Generator[AddChainToRelayerAction] {
	return rapid.Custom(func(t *rapid.T) AddChainToRelayerAction {
		return AddChainToRelayerAction{
			Chain:     GetChainIDGen().Draw(t, "Chain"),
			Validator: GetValidatorIDGen().Draw(t, "Validator"),
		}
	})
}

func GetAddIbcConnectionActionGen() *rapid.Generator[AddIbcConnectionAction] {
	return rapid.Custom(func(t *rapid.T) AddIbcConnectionAction {
		return AddIbcConnectionAction{
			ChainA:  GetChainIDGen().Draw(t, "ChainA"),
			ChainB:  GetChainIDGen().Draw(t, "ChainB"),
			ClientA: rapid.Uint().Draw(t, "ClientA"),
			ClientB: rapid.Uint().Draw(t, "ClientB"),
		}
	})
}

func GetAddIbcChannelActionGen() *rapid.Generator[AddIbcChannelAction] {
	return rapid.Custom(func(t *rapid.T) AddIbcChannelAction {
		return AddIbcChannelAction{
			ChainA:      GetChainIDGen().Draw(t, "ChainA"),
			ChainB:      GetChainIDGen().Draw(t, "ChainB"),
			ConnectionA: rapid.Uint().Draw(t, "ConnectionA"),
			PortA:       rapid.String().Draw(t, "PortA"),
			PortB:       rapid.String().Draw(t, "PortB"),
			Order:       rapid.String().Draw(t, "Order"),
		}
	})
}

func GetStartRelayerActionGen() *rapid.Generator[StartRelayerAction] {
	return rapid.Just(StartRelayerAction{})
}

func GetTransferChannelCompleteActionGen() *rapid.Generator[TransferChannelCompleteAction] {
	return rapid.Custom(func(t *rapid.T) TransferChannelCompleteAction {
		return TransferChannelCompleteAction{
			ChainA:      GetChainIDGen().Draw(t, "ChainA"),
			ChainB:      GetChainIDGen().Draw(t, "ChainB"),
			ConnectionA: rapid.Uint().Draw(t, "ConnectionA"),
			PortA:       rapid.String().Draw(t, "PortA"),
			PortB:       rapid.String().Draw(t, "PortB"),
			Order:       rapid.String().Draw(t, "Order"),
			ChannelA:    rapid.Uint().Draw(t, "ChannelA"),
			ChannelB:    rapid.Uint().Draw(t, "ChannelB"),
		}
	})
}

func GetRelayPacketsActionGen() *rapid.Generator[RelayPacketsAction] {
	return rapid.Custom(func(t *rapid.T) RelayPacketsAction {
		return RelayPacketsAction{
			ChainA:  GetChainIDGen().Draw(t, "Chain"),
			ChainB:  GetChainIDGen().Draw(t, "Chain"),
			Port:    rapid.String().Draw(t, "Port"),
			Channel: rapid.Uint().Draw(t, "Channel"),
		}
	})
}

func GetRelayRewardPacketsToProviderActionGen() *rapid.Generator[RelayRewardPacketsToProviderAction] {
	return rapid.Custom(func(t *rapid.T) RelayRewardPacketsToProviderAction {
		return RelayRewardPacketsToProviderAction{
			ConsumerChain: GetChainIDGen().Draw(t, "ConsumerChain"),
			ProviderChain: GetChainIDGen().Draw(t, "ProviderChain"),
			Port:          rapid.String().Draw(t, "Port"),
			Channel:       rapid.Uint().Draw(t, "Channel"),
		}
	})
}

func GetDelegateTokensActionGen() *rapid.Generator[DelegateTokensAction] {
	return rapid.Custom(func(t *rapid.T) DelegateTokensAction {
		return DelegateTokensAction{
			Chain:  GetChainIDGen().Draw(t, "Chain"),
			Amount: rapid.Uint().Draw(t, "Amount"),
			From:   GetValidatorIDGen().Draw(t, "From"),
			To:     GetValidatorIDGen().Draw(t, "To"),
		}
	})
}

func GetUnbondTokensActionGen() *rapid.Generator[UnbondTokensAction] {
	return rapid.Custom(func(t *rapid.T) UnbondTokensAction {
		return UnbondTokensAction{
			Chain:      GetChainIDGen().Draw(t, "Chain"),
			Amount:     rapid.Uint().Draw(t, "Amount"),
			Sender:     GetValidatorIDGen().Draw(t, "Sender"),
			UnbondFrom: GetValidatorIDGen().Draw(t, "UnbondFrom"),
		}
	})
}

func GetReDelegateTokensActionGen() *rapid.Generator[ReDelegateTokensAction] {
	return rapid.Custom(func(t *rapid.T) ReDelegateTokensAction {
		return ReDelegateTokensAction{
			Chain:    GetChainIDGen().Draw(t, "Chain"),
			Amount:   rapid.Uint().Draw(t, "Amount"),
			Src:      GetValidatorIDGen().Draw(t, "Src"),
			Dst:      GetValidatorIDGen().Draw(t, "Dst"),
			TxSender: GetValidatorIDGen().Draw(t, "TxSender"),
		}
	})
}

func GetDowntimeSlashActionGen() *rapid.Generator[DowntimeSlashAction] {
	return rapid.Custom(func(t *rapid.T) DowntimeSlashAction {
		return DowntimeSlashAction{
			Chain:     GetChainIDGen().Draw(t, "Chain"),
			Validator: GetValidatorIDGen().Draw(t, "Validator"),
		}
	})
}

func GetUnjailValidatorActionGen() *rapid.Generator[UnjailValidatorAction] {
	return rapid.Custom(func(t *rapid.T) UnjailValidatorAction {
		return UnjailValidatorAction{
			Validator: GetValidatorIDGen().Draw(t, "Validator"),
			Provider:  GetChainIDGen().Draw(t, "Provider"),
		}
	})
}

func GetRegisterRepresentativeActionGen() *rapid.Generator[RegisterRepresentativeAction] {
	return rapid.Custom(func(t *rapid.T) RegisterRepresentativeAction {
		return RegisterRepresentativeAction{
			Chain:           GetChainIDGen().Draw(t, "Chain"),
			Representatives: rapid.SliceOf(GetValidatorIDGen()).Draw(t, "Representatives"),
			Stakes:          rapid.SliceOf(rapid.Uint()).Draw(t, "Stakes"),
		}
	})
}

func GetDoublesignSlashActionGen() *rapid.Generator[DoublesignSlashAction] {
	return rapid.Custom(func(t *rapid.T) DoublesignSlashAction {
		return DoublesignSlashAction{
			Chain:     GetChainIDGen().Draw(t, "Chain"),
			Validator: GetValidatorIDGen().Draw(t, "Validator"),
		}
	})
}

func GetAssignConsumerPubKeyActionGen() *rapid.Generator[AssignConsumerPubKeyAction] {
	return rapid.Custom(func(t *rapid.T) AssignConsumerPubKeyAction {
		return AssignConsumerPubKeyAction{
			Chain:           GetChainIDGen().Draw(t, "Chain"),
			Validator:       GetValidatorIDGen().Draw(t, "Validator"),
			ConsumerPubkey:  rapid.String().Draw(t, "ConsumerPubkey"),
			ReconfigureNode: rapid.Bool().Draw(t, "ReconfigureNode"),
			ExpectError:     rapid.Bool().Draw(t, "ExpectError"),
		}
	})
}

func GetSlashMeterReplenishmentAction() *rapid.Generator[SlashMeterReplenishmentAction] {
	return rapid.Custom(func(t *rapid.T) SlashMeterReplenishmentAction {
		return SlashMeterReplenishmentAction{
			TargetValue: rapid.Int64().Draw(t, "TargetValue"),
			Timeout:     time.Duration(rapid.Int().Draw(t, "Timeout")) * time.Millisecond,
		}
	})
}

func GetWaitTimeAction() *rapid.Generator[WaitTimeAction] {
	return rapid.Custom(func(t *rapid.T) WaitTimeAction {
		return WaitTimeAction{
			WaitTime: time.Duration(rapid.Int().Draw(t, "Timeout")) * time.Millisecond,
		}
	})
}

func GetForkConsumerChainActionGen() *rapid.Generator[ForkConsumerChainAction] {
	return rapid.Custom(func(t *rapid.T) ForkConsumerChainAction {
		return ForkConsumerChainAction{
			ConsumerChain: GetChainIDGen().Draw(t, "ConsumerChain"),
			ProviderChain: GetChainIDGen().Draw(t, "ProviderChain"),
			Validator:     GetValidatorIDGen().Draw(t, "Validator"),
			RelayerConfig: rapid.String().Draw(t, "RelayerConfig"),
		}
	})
}

func GetStartConsumerEvidenceDetectorActionGen() *rapid.Generator[StartConsumerEvidenceDetectorAction] {
	return rapid.Custom(func(t *rapid.T) StartConsumerEvidenceDetectorAction {
		return StartConsumerEvidenceDetectorAction{
			Chain: GetChainIDGen().Draw(t, "Chain"),
		}
	})
}

func GetUpdateLightClientActionGen() *rapid.Generator[UpdateLightClientAction] {
	return rapid.Custom(func(t *rapid.T) UpdateLightClientAction {
		return UpdateLightClientAction{
			Chain:         GetChainIDGen().Draw(t, "Chain"),
			HostChain:     GetChainIDGen().Draw(t, "HostChain"),
			RelayerConfig: rapid.String().Draw(t, "RelayerConfig"),
			ClientID:      rapid.String().Draw(t, "ClientID"),
		}
	})
}
