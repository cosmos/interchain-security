package main

import (
	"github.com/informalsystems/itf-go/itf"
)

// This file contains logic to process
// and access parts of the current state of the Quint trace.

func ProviderState(curStateExpr itf.MapExprType) itf.MapExprType {
	return curStateExpr["providerState"].Value.(itf.MapExprType)
}

func ConsumerState(curStateExpr itf.MapExprType, consumer string) itf.MapExprType {
	return curStateExpr["consumerStates"].Value.(itf.MapExprType)[consumer].Value.(itf.MapExprType)
}

func State(curStateExpr itf.MapExprType, chain string) itf.MapExprType {
	if chain == PROVIDER {
		return ProviderState(curStateExpr)
	} else {
		return ConsumerState(curStateExpr, chain)
	}
}

func ChainState(curStateExpr itf.MapExprType, chain string) itf.MapExprType {
	return State(curStateExpr, chain)["chainState"].Value.(itf.MapExprType)
}

func ValidatorSet(curStateExpr itf.MapExprType, chain string) itf.MapExprType {
	return ChainState(curStateExpr, chain)["currentValidatorPowers"].Value.(itf.MapExprType)
}

func HistoricalValidatorSet(curStateExpr itf.MapExprType, chain string, index int) itf.MapExprType {
	history := ChainState(curStateExpr, chain)["votingPowerHistory"].Value.(itf.ListExprType)
	return history[index].Value.(itf.MapExprType)
}

func RunningTime(curStateExpr itf.MapExprType, chain string) int64 {
	return ChainState(curStateExpr, chain)["runningTimestamp"].Value.(int64)
}

// PacketQueue returns the queued packets between sender and receiver.
// Either sender or receiver need to be the provider.
func PacketQueue(curStateExpr itf.MapExprType, sender, receiver string) itf.ListExprType {
	if sender == PROVIDER {
		packetQueue := ProviderState(curStateExpr)["outstandingPacketsToConsumer"].Value.(itf.MapExprType)[receiver]
		if packetQueue.Value == nil {
			return itf.ListExprType{}
		} else {
			return packetQueue.Value.([]itf.Expr)
		}
	} else {
		consumerState := State(curStateExpr, sender)
		return consumerState["outstandingPacketsToProvider"].Value.([]itf.Expr)
	}
}

// RunningConsumers returns a slice containing the names of the consumers
// that are currently running.
func RunningConsumers(curStateExpr itf.MapExprType) []string {
	exprSlice := ProviderState(curStateExpr)["consumerStatus"].Value.(itf.MapExprType)
	runningConsumers := make([]string, 0)
	for consumer, statusExpr := range exprSlice {
		status := statusExpr.Value.(string)
		if status == "running" {
			runningConsumers = append(runningConsumers, consumer)
		}
	}
	return runningConsumers
}

func ConsumerStatus(curStateExpr itf.MapExprType, consumer string) string {
	return ProviderState(curStateExpr)["consumerStatus"].Value.(itf.MapExprType)[consumer].Value.(string)
}

func GetTimeoutForPacket(packetExpr itf.MapExprType) int64 {
	return packetExpr["timeoutTime"].Value.(int64)
}

func GetSendingTimeForPacket(packetExpr itf.MapExprType) int64 {
	return packetExpr["sendingTime"].Value.(int64)
}

func VscSendTimestamps(curStateExpr itf.MapExprType, consumer string) []int64 {
	sentVscPackets := ProviderState(curStateExpr)["sentVscPacketsToConsumer"].Value.(itf.MapExprType)[consumer].Value.(itf.ListExprType)

	res := make([]int64, len(sentVscPackets))
	for i, packetExpr := range sentVscPackets {
		res[i] = GetSendingTimeForPacket(packetExpr.Value.(itf.MapExprType))
	}
	return res
}

func PacketsToAckOnEndBlock(curStateExpr itf.MapExprType) itf.MapExprType {
	return ProviderState(curStateExpr)["acksToSendOnEndBlock"].Value.(itf.MapExprType)
}

func WaitingForAcks(curStateExpr itf.MapExprType, consumer string) itf.ListExprType {
	return ConsumerState(curStateExpr, consumer)["waitingForSlashPacketAck"].Value.(itf.ListExprType)
}

// ProviderJailedValidators returns the names and the jailEndTimes times of the jailed validators
// on the provider. The slices are in the same order, i.e. the i-th element of jailedValidators
// is the name of the i-th jailed validator and the i-th element of jailEndTimes is its jail end time
func ProviderJailedValidators(curStateExpr itf.MapExprType) ([]string, []int64) {
	jailMap := ChainState(curStateExpr, PROVIDER)["jailedUntil"].Value.(itf.MapExprType)
	jailedValidators := make([]string, 0)
	jailEndTimes := make([]int64, 0)
	for val, endTime := range jailMap {
		jailedValidators = append(jailedValidators, val)
		jailEndTimes = append(jailEndTimes, endTime.Value.(int64))
	}
	return jailedValidators, jailEndTimes
}
