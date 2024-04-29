#!/bin/bash

echo "Generating bounded drift traces with timeouts"
go run ./... -modelPath=../model/ccv_boundeddrift.qnt -step stepBoundedDrift  -invariant CanTimeoutConsumer -traceFolder traces/bound_timeout -numTraces 20 -numSteps 200 -numSamples 200
echo "Generating long bounded drift traces without invariants"
go run ./... -modelPath=../model/ccv_boundeddrift.qnt -step stepBoundedDrift -traceFolder traces/bound_noinv -numTraces 20 -numSteps 300 -numSamples 1
echo "Generating bounded drift traces with maturations"
go run ./... -modelPath=../model/ccv_boundeddrift.qnt -step stepBoundedDrift -invariant CanReceiveMaturations -traceFolder traces/bound_mat -numTraces 20 -numSteps 100 -numSamples 20
echo "Generating synced traces with maturations"
go run ./... -modelPath=../model/ccv_sync.qnt -init initSync -step stepSync -invariant CanReceiveMaturations -traceFolder traces/sync_mat -numTraces 20 -numSteps 300 -numSamples 20
echo "Generating traces with jails"
go run ./... -modelPath=../model/ccv_sync.qnt -init initSync -step stepSync -invariant CanJail -traceFolder traces/sync_jailmany -numTraces 2 -numSteps 100 -numSamples 20
echo "Generating long synced traces without invariants"
go run ./... -modelPath=../model/ccv_sync.qnt -init initSync -step stepSync -traceFolder traces/sync_noinv -numTraces 20 -numSteps 300 -numSamples 1
go run ./... -modelPath=../model/ccv_boundeddrift.qnt --step stepBoundedDriftKeyAssignment --traceFolder traces/bound_key -numTraces 20 -numSteps 100 -numSamples 20