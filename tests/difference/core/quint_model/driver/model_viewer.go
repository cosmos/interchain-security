package main

import "github.com/informalsystems/itf-go/itf"

// This file contains logic to process
// and access parts of the current state of the Quint trace.

const Provider = "provider"

func ProviderState(curStateExpr itf.MapExprType) itf.MapExprType {
	return curStateExpr["providerState"].Value.(itf.MapExprType)
}

func ConsumerState(curStateExpr itf.MapExprType, consumer string) itf.MapExprType {
	return curStateExpr["consumerStates"].Value.(itf.MapExprType)[consumer].Value.(itf.MapExprType)
}

func State(curStateExpr itf.MapExprType, chain string) itf.MapExprType {
	if chain == Provider {
		return ProviderState(curStateExpr)
	} else {
		return ConsumerState(curStateExpr, chain)
	}
}

func ChainState(curStateExpr itf.MapExprType, chain string) itf.MapExprType {
	return State(curStateExpr, chain)["chainState"].Value.(itf.MapExprType)
}

func ValidatorSet(curStateExpr itf.MapExprType, chain string) itf.MapExprType {
	return ChainState(curStateExpr, chain)["currentValidatorSet"].Value.(itf.MapExprType)
}

func HistoricalValidatorSet(curStateExpr itf.MapExprType, chain string, index int) itf.MapExprType {
	history := ChainState(curStateExpr, chain)["votingPowerHistory"].Value.(itf.ListExprType)
	return history[index].Value.(itf.MapExprType)
}

func Time(curStateExpr itf.MapExprType, chain string) int64 {
	return ChainState(curStateExpr, chain)["lastTimestamp"].Value.(int64)
}

// PacketQueue returns the queued packets between sender and receiver.
// Either sender or receiver need to be the provider.
func PacketQueue(curStateExpr itf.MapExprType, sender string, receiver string) itf.ListExprType {
	if sender == Provider {
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
