package main

import (
	"testing"
	"time"

	"github.com/stretchr/testify/require"
	"pgregory.net/rapid"
)

func GetActionGen() *rapid.Generator[any] {
	return rapid.OneOf(
		GetSendTokensActionGen().AsAny(),
		GetStartChainActionGen().AsAny(),
		GetSubmitTextProposalActionGen().AsAny(),
		GetSubmitConsumerAdditionProposalActionGen().AsAny(),
		GetSubmitConsumerRemovalProposalActionGen().AsAny(),
		GetSubmitParamChangeProposalActionGen().AsAny(),
		GetSubmitEquivocationProposalActionGen().AsAny(),
		GetVoteGovProposalActionGen().AsAny(),
		GetStartConsumerChainActionGen().AsAny(),
		GetAddChainToRelayerActionGen().AsAny(),
		GetAddIbcConnectionActionGen().AsAny(),
		GetAddIbcChannelActionGen().AsAny(),
		GetStartHermesActionGen().AsAny(),
		GetTransferChannelCompleteActionGen().AsAny(),
		GetRelayPacketsActionGen().AsAny(),
		GetRelayRewardPacketsToProviderActionGen().AsAny(),
		GetDelegateTokensActionGen().AsAny(),
		GetUnbondTokensActionGen().AsAny(),
		GetRedelegateTokensActionGen().AsAny(),
		GetDowntimeSlashActionGen().AsAny(),
		GetUnjailValidatorActionGen().AsAny(),
		GetRegisterRepresentativeActionGen().AsAny(),
		GetDoublesignSlashActionGen().AsAny(),
		GetAssignConsumerPubKeyActionGen().AsAny(),
		GetSlashThrottleDequeueGen().AsAny(),
	)
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
			SkipGentx:      rapid.Bool().Draw(t, "SkipGentx"),
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

func GetSubmitTextProposalActionGen() *rapid.Generator[submitTextProposalAction] {
	return rapid.Custom(func(t *rapid.T) submitTextProposalAction {
		return submitTextProposalAction{
			Chain:       GetChainIDGen().Draw(t, "Chain"),
			From:        GetValidatorIDGen().Draw(t, "From"),
			Deposit:     rapid.Uint().Draw(t, "Deposit"),
			PropType:    rapid.String().Draw(t, "PropType"),
			Title:       rapid.String().Draw(t, "Title"),
			Description: rapid.String().Draw(t, "Description"),
		}
	})
}

func GetSubmitConsumerAdditionProposalActionGen() *rapid.Generator[submitConsumerAdditionProposalAction] {
	return rapid.Custom(func(t *rapid.T) submitConsumerAdditionProposalAction {
		return submitConsumerAdditionProposalAction{
			Chain:         GetChainIDGen().Draw(t, "Chain"),
			From:          GetValidatorIDGen().Draw(t, "From"),
			Deposit:       rapid.Uint().Draw(t, "Deposit"),
			ConsumerChain: GetChainIDGen().Draw(t, "ConsumerChain"),
			SpawnTime:     rapid.Uint().Draw(t, "SpawnTime"),
			InitialHeight: GetHeightGen().Draw(t, "InitialHeight"),
		}
	})
}

func GetSubmitConsumerRemovalProposalActionGen() *rapid.Generator[submitConsumerRemovalProposalAction] {
	return rapid.Custom(func(t *rapid.T) submitConsumerRemovalProposalAction {
		return submitConsumerRemovalProposalAction{
			Chain:          GetChainIDGen().Draw(t, "Chain"),
			From:           GetValidatorIDGen().Draw(t, "From"),
			Deposit:        rapid.Uint().Draw(t, "Deposit"),
			ConsumerChain:  GetChainIDGen().Draw(t, "ConsumerChain"),
			StopTimeOffset: time.Duration(rapid.Int64().Draw(t, "StopTimeOffset")),
		}
	})
}

func GetSubmitParamChangeProposalActionGen() *rapid.Generator[submitParamChangeProposalAction] {
	return rapid.Custom(func(t *rapid.T) submitParamChangeProposalAction {
		return submitParamChangeProposalAction{
			Chain:    GetChainIDGen().Draw(t, "Chain"),
			From:     GetValidatorIDGen().Draw(t, "From"),
			Deposit:  rapid.Uint().Draw(t, "Deposit"),
			Subspace: rapid.String().Draw(t, "Subspace"),
			Key:      rapid.String().Draw(t, "Key"),
			Value:    rapid.String().Draw(t, "Value"), // TODO: make this more generic
		}
	})
}

func GetSubmitEquivocationProposalActionGen() *rapid.Generator[submitEquivocationProposalAction] {
	return rapid.Custom(func(t *rapid.T) submitEquivocationProposalAction {
		return submitEquivocationProposalAction{
			Chain:   GetChainIDGen().Draw(t, "Chain"),
			From:    GetValidatorIDGen().Draw(t, "From"),
			Deposit: rapid.Uint().Draw(t, "Deposit"),
			Height:  rapid.Int64().Draw(t, "Height"),
			Time:    GetTimeGen().Draw(t, "Time"),
			Power:   rapid.Int64().Draw(t, "Power"),
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
		require.Equal(t, time1, time2)
	})
}

func GetTimeGen() *rapid.Generator[time.Time] {
	return rapid.Custom(func(t *rapid.T) time.Time {
		return time.Unix(rapid.Int64Range(-1.5779e+11, 1.5779e+11).Draw(t, "Unix"), 0)
	})
}

func GetVoteGovProposalActionGen() *rapid.Generator[voteGovProposalAction] {
	return rapid.Custom(func(t *rapid.T) voteGovProposalAction {
		return voteGovProposalAction{
			Chain:      GetChainIDGen().Draw(t, "Chain"),
			From:       rapid.SliceOf(GetValidatorIDGen()).Draw(t, "From"),
			Vote:       rapid.SliceOf(rapid.String()).Draw(t, "Vote"),
			PropNumber: rapid.Uint().Draw(t, "PropNumber"),
		}
	})
}

func GetStartConsumerChainActionGen() *rapid.Generator[startConsumerChainAction] {
	return rapid.Custom(func(t *rapid.T) startConsumerChainAction {
		return startConsumerChainAction{
			ConsumerChain:  GetChainIDGen().Draw(t, "ConsumerChain"),
			ProviderChain:  GetChainIDGen().Draw(t, "ProviderChain"),
			Validators:     GetStartChainValidatorsGen().Draw(t, "Validators"),
			GenesisChanges: rapid.String().Draw(t, "GenesisChanges"),
		}
	})
}

func GetAddChainToRelayerActionGen() *rapid.Generator[addChainToRelayerAction] {
	return rapid.Custom(func(t *rapid.T) addChainToRelayerAction {
		return addChainToRelayerAction{
			Chain:     GetChainIDGen().Draw(t, "Chain"),
			Validator: GetValidatorIDGen().Draw(t, "Validator"),
		}
	})
}

func GetAddIbcConnectionActionGen() *rapid.Generator[addIbcConnectionAction] {
	return rapid.Custom(func(t *rapid.T) addIbcConnectionAction {
		return addIbcConnectionAction{
			ChainA:  GetChainIDGen().Draw(t, "ChainA"),
			ChainB:  GetChainIDGen().Draw(t, "ChainB"),
			ClientA: rapid.Uint().Draw(t, "ClientA"),
			ClientB: rapid.Uint().Draw(t, "ClientB"),
		}
	})
}

func GetAddIbcChannelActionGen() *rapid.Generator[addIbcChannelAction] {
	return rapid.Custom(func(t *rapid.T) addIbcChannelAction {
		return addIbcChannelAction{
			ChainA:      GetChainIDGen().Draw(t, "ChainA"),
			ChainB:      GetChainIDGen().Draw(t, "ChainB"),
			ConnectionA: rapid.Uint().Draw(t, "ConnectionA"),
			PortA:       rapid.String().Draw(t, "PortA"),
			PortB:       rapid.String().Draw(t, "PortB"),
			Order:       rapid.String().Draw(t, "Order"),
		}
	})
}

func GetStartHermesActionGen() *rapid.Generator[startHermesAction] {
	return rapid.Just(startHermesAction{})
}

func GetTransferChannelCompleteActionGen() *rapid.Generator[transferChannelCompleteAction] {
	return rapid.Custom(func(t *rapid.T) transferChannelCompleteAction {
		return transferChannelCompleteAction{
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

func GetRelayPacketsActionGen() *rapid.Generator[relayPacketsAction] {
	return rapid.Custom(func(t *rapid.T) relayPacketsAction {
		return relayPacketsAction{
			Chain:   GetChainIDGen().Draw(t, "Chain"),
			Port:    rapid.String().Draw(t, "Port"),
			Channel: rapid.Uint().Draw(t, "Channel"),
		}
	})
}

func GetRelayRewardPacketsToProviderActionGen() *rapid.Generator[relayRewardPacketsToProviderAction] {
	return rapid.Custom(func(t *rapid.T) relayRewardPacketsToProviderAction {
		return relayRewardPacketsToProviderAction{
			ConsumerChain: GetChainIDGen().Draw(t, "ConsumerChain"),
			ProviderChain: GetChainIDGen().Draw(t, "ProviderChain"),
			Port:          rapid.String().Draw(t, "Port"),
			Channel:       rapid.Uint().Draw(t, "Channel"),
		}
	})
}

func GetDelegateTokensActionGen() *rapid.Generator[delegateTokensAction] {
	return rapid.Custom(func(t *rapid.T) delegateTokensAction {
		return delegateTokensAction{
			Chain:  GetChainIDGen().Draw(t, "Chain"),
			Amount: rapid.Uint().Draw(t, "Amount"),
			From:   GetValidatorIDGen().Draw(t, "From"),
			To:     GetValidatorIDGen().Draw(t, "To"),
		}
	})
}

func GetUnbondTokensActionGen() *rapid.Generator[unbondTokensAction] {
	return rapid.Custom(func(t *rapid.T) unbondTokensAction {
		return unbondTokensAction{
			Chain:      GetChainIDGen().Draw(t, "Chain"),
			Amount:     rapid.Uint().Draw(t, "Amount"),
			Sender:     GetValidatorIDGen().Draw(t, "Sender"),
			UnbondFrom: GetValidatorIDGen().Draw(t, "UnbondFrom"),
		}
	})
}

func GetRedelegateTokensActionGen() *rapid.Generator[redelegateTokensAction] {
	return rapid.Custom(func(t *rapid.T) redelegateTokensAction {
		return redelegateTokensAction{
			Chain:    GetChainIDGen().Draw(t, "Chain"),
			Amount:   rapid.Uint().Draw(t, "Amount"),
			Src:      GetValidatorIDGen().Draw(t, "Src"),
			Dst:      GetValidatorIDGen().Draw(t, "Dst"),
			TxSender: GetValidatorIDGen().Draw(t, "TxSender"),
		}
	})
}

func GetDowntimeSlashActionGen() *rapid.Generator[downtimeSlashAction] {
	return rapid.Custom(func(t *rapid.T) downtimeSlashAction {
		return downtimeSlashAction{
			Chain:     GetChainIDGen().Draw(t, "Chain"),
			Validator: GetValidatorIDGen().Draw(t, "Validator"),
		}
	})
}

func GetUnjailValidatorActionGen() *rapid.Generator[unjailValidatorAction] {
	return rapid.Custom(func(t *rapid.T) unjailValidatorAction {
		return unjailValidatorAction{
			Validator: GetValidatorIDGen().Draw(t, "Validator"),
			Provider:  GetChainIDGen().Draw(t, "Provider"),
		}
	})
}

func GetRegisterRepresentativeActionGen() *rapid.Generator[registerRepresentativeAction] {
	return rapid.Custom(func(t *rapid.T) registerRepresentativeAction {
		return registerRepresentativeAction{
			Chain:           GetChainIDGen().Draw(t, "Chain"),
			Representatives: rapid.SliceOf(GetValidatorIDGen()).Draw(t, "Representatives"),
			Stakes:          rapid.SliceOf(rapid.Uint()).Draw(t, "Stakes"),
		}
	})
}

func GetDoublesignSlashActionGen() *rapid.Generator[doublesignSlashAction] {
	return rapid.Custom(func(t *rapid.T) doublesignSlashAction {
		return doublesignSlashAction{
			Chain:     GetChainIDGen().Draw(t, "Chain"),
			Validator: GetValidatorIDGen().Draw(t, "Validator"),
		}
	})
}

func GetAssignConsumerPubKeyActionGen() *rapid.Generator[assignConsumerPubKeyAction] {
	return rapid.Custom(func(t *rapid.T) assignConsumerPubKeyAction {
		return assignConsumerPubKeyAction{
			Chain:           GetChainIDGen().Draw(t, "Chain"),
			Validator:       GetValidatorIDGen().Draw(t, "Validator"),
			ConsumerPubkey:  rapid.String().Draw(t, "ConsumerPubkey"),
			ReconfigureNode: rapid.Bool().Draw(t, "ReconfigureNode"),
			ExpectError:     rapid.Bool().Draw(t, "ExpectError"),
		}
	})
}

func GetSlashThrottleDequeueGen() *rapid.Generator[slashThrottleDequeue] {
	return rapid.Custom(func(t *rapid.T) slashThrottleDequeue {
		return slashThrottleDequeue{
			Chain:            GetChainIDGen().Draw(t, "Chain"),
			CurrentQueueSize: rapid.Int().Draw(t, "CurrentQueueSize"),
			NextQueueSize:    rapid.Int().Draw(t, "NextQueueSize"),
			Timeout:          time.Duration(rapid.Int().Draw(t, "Timeout")) * time.Millisecond,
		}
	})
}
