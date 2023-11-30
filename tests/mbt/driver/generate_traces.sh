echo "Generating bounded drift traces with timeouts"
go run ./... -modelPath=../model/ccv_boundeddrift.qnt -step stepBoundedDrift  -invariant CanTimeoutConsumer -traceFolder traces/bound_timeout -numTraces 100 -numSteps 200 -numSamples 200
echo "Generating long bounded drift traces without invariants"
go run ./... -modelPath=../model/ccv_boundeddrift.qnt -step stepBoundedDrift -traceFolder traces/bound_noinv -numTraces 100 -numSteps 500 -numSamples 1
echo "Generating bounded drift traces with maturations"
go run ./... -modelPath=../model/ccv_boundeddrift.qnt -step stepBoundedDrift -invariant CanReceiveMaturations -traceFolder traces/bound_mat -numTraces 100 -numSteps 100 -numSamples 20
echo "Generating synched traces with maturations"
go run ./... -modelPath=../model/ccv_sync.qnt -init initHappy -step stepHappy -invariant CanReceiveMaturations -traceFolder traces/sync_mat -numTraces 100 -numSteps 300 -numSamples 20
echo "Generating long synched traces without invariants"
go run ./... -modelPath=../model/ccv_sync.qnt -init initHappy -step stepHappy -traceFolder traces/sync_noinv -numTraces 100 -numSteps 500 -numSamples 1