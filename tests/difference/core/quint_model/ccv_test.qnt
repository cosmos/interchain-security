// -*- mode: Bluespec; -*-

// contains test logic for the stateless functions in the CCV module
module ccv_test {
    import ccv_types.* from "./ccv"
    import Time.* from "./libraries/Time"
    import extraSpells.* from "./libraries/extraSpells"

    pure val consumerChains = Set("sender", "receiver")
    pure val chains = consumerChains.union(Set(PROVIDER_CHAIN))
    pure val unbondingPeriods = chains.mapBy(chain => 2 * Week)
    pure val ccvTimeouts = chains.mapBy(chain => 3 * Week)
    pure val trustingPeriods = chains.mapBy(chain => 2 * Week - 1 * Hour)

    import ccv(VscTimeout = 5 * Week, CcvTimeout = ccvTimeouts, UnbondingPeriodPerChain = unbondingPeriods, ConsumerChains = consumerChains, TrustingPeriodPerChain=trustingPeriods).* from "./ccv"

    val votingPowerTestInitState = 
            GetEmptyProtocolState.with(
                "providerState", GetEmptyProtocolState.providerState.with(
                    "chainState", GetEmptyProtocolState.providerState.chainState.with(
                        "currentValidatorSet", GetEmptyProtocolState.providerState.chainState.currentValidatorSet.put(
                            "validator", 5
                        )
                    )
                )
            )

    // changing voting power by zero gives an error
    run VotingPowerZeroChangeTest =
    {
        votingPowerChange(
            votingPowerTestInitState,
            "validator",
            0
        ).hasError()
    }

    run VotingPowerOkTest =
    {
        val result = votingPowerChange(
            votingPowerTestInitState,
            "validator",
            5
        )
        not(result.hasError()) and
        result.newState.providerState.chainState.currentValidatorSet.keys().contains("validator") and
        result.newState.providerState.chainState.currentValidatorSet.get("validator") == 10
    }

    // voting power of 0 is allowed and applied as usual
    run VotingPowerZeroTest =
    {
        val finalResult = votingPowerChange(
            votingPowerTestInitState,
            "validator",
            -5
        )
        not(finalResult.hasError()) and
        finalResult.newState.providerState.chainState.currentValidatorSet.get("validator") == 0
    }

    run VotingPowerSetsFlagTest =
    {
        // change voting power
        val tmpResult = votingPowerChange(
            votingPowerTestInitState,
            "validator",
            5
        )
        // but then set it back to the initial value
        val finalResult = votingPowerChange(
            tmpResult.newState,
            "validator",
            -5
        )
        // still should set the flag
        not(finalResult.hasError()) and
        finalResult.newState.providerState.providerValidatorSetChangedInThisBlock
    }


    // make sure that VotingPowerChange ONLY changes the current validator set, not the history
    run VotingPowerChangeDoesNotChangeHistoryTest =
    {
        val result = votingPowerChange(
            votingPowerTestInitState,
            "validator",
            2
        )
        not(result.hasError()) and
        result.newState.providerState.chainState.votingPowerHistory == List()
    }

    // Changing the voting power to positive from zero is not possible,
    // since the validator will be removed from the current validator set
    run VotingPowerChangeFromZeroTest =
    {
        val result = votingPowerChange(
            votingPowerTestInitState,
            "validator",
            -5
        )
        val result2 = votingPowerChange(
            result.newState,
            "validator",
            5
        )
        not(result.hasError()) and
        result.newState.providerState.chainState.currentValidatorSet.get("validator") == 0 and
        result2.hasError()

    }

    // Defines a test state to test the deliverPacketToProvider function against.
    pure val _DeliverPacketToProvider_TestState =
        val currentState = GetEmptyProtocolState
        val sender = "sender"
        val providerState = currentState.providerState
        val consumerState = GetEmptyConsumerState
        // add the consumer to the consumerStates
        val consumerStates = currentState.consumerStates.put(sender, consumerState)
        val providerState2 = providerState.with(
            "consumerStatus", providerState.consumerStatus.put(sender, RUNNING)
        )
        val providerState3 = providerState2.with(
            "outstandingPacketsToConsumer", providerState2.outstandingPacketsToConsumer.put(sender, List({
                id: 0,
                validatorSet: Map(),
                sendingTime: 0,
                timeoutTime: CcvTimeout.get(sender)
            }))
        )
        currentState.with(
            "providerState", providerState3
        ).with(
            "consumerStates", consumerStates
        )

    // add a packet on the consumer
    pure val DeliverPacketToProviderHappyPathTest_testState = _DeliverPacketToProvider_TestState.with(
        "consumerStates", _DeliverPacketToProvider_TestState.consumerStates.put(
            "sender", _DeliverPacketToProvider_TestState.consumerStates.get("sender").with(
                "outstandingPacketsToProvider", List({
                    id: 0,
                    sendingTime: 0,
                    timeoutTime: CcvTimeout.get("sender")
                })
            )
        )
    ).with(
        // put an entry into sentVscPacket on the provider that corresponds to the packet we put on the consumer
        "providerState", _DeliverPacketToProvider_TestState.providerState.with(
            "sentVscPacketsToConsumer", _DeliverPacketToProvider_TestState.providerState.sentVscPacketsToConsumer.put(
                "sender", List({
                    id: 0,
                    validatorSet: _DeliverPacketToProvider_TestState.providerState.chainState.currentValidatorSet,
                    sendingTime: 0,
                    timeoutTime: CcvTimeout.get("sender")
                })
            )
        )
    )

    pure val DeliverPacketToProviderHappyPathTest_resultAndTimeout = deliverPacketToProvider(DeliverPacketToProviderHappyPathTest_testState, "sender")

    // test is split to be easier to pinpoint which assertion failed
    run DidNotTimeOut_DeliverPacketToProviderHappyPathTest =
    {
        val result = DeliverPacketToProviderHappyPathTest_resultAndTimeout._1
        val timeout = DeliverPacketToProviderHappyPathTest_resultAndTimeout._2
        not(result.hasError()) and
        not(timeout)
    }

    run StateModificationOK_DeliverPacketToProviderHappyPathTest =
    {
        val result = DeliverPacketToProviderHappyPathTest_resultAndTimeout._1
        val newProviderState = result.newState.providerState
        val newConsumerState = result.newState.consumerStates.get("sender")
        not(result.hasError()) and
        newProviderState.receivedMaturations.size() == 1 and
        newConsumerState.outstandingPacketsToProvider.length() == 0
    }

    // add a packet on the consumer
    pure val DeliverPacketToProviderTimeoutTest_testState = DeliverPacketToProviderHappyPathTest_testState.with(
            "providerState", DeliverPacketToProviderHappyPathTest_testState.providerState.with(
                "chainState", DeliverPacketToProviderHappyPathTest_testState.providerState.chainState.with(
                    // set the timestamp to be after the timeout
                    "runningTimestamp", CcvTimeout.get("sender") + 1
                )
            )
        )

    pure val DeliverPacketToProviderTimeoutTest_resultAndTimeout = deliverPacketToProvider(DeliverPacketToProviderTimeoutTest_testState, "sender")

    run DidTimeOut_DeliverPacketToProviderTimeoutTest =
    {
        val result = DeliverPacketToProviderTimeoutTest_resultAndTimeout._1
        val timeout = DeliverPacketToProviderTimeoutTest_resultAndTimeout._2
        val newProviderState = result.newState.providerState
        val newConsumerState = result.newState.consumerStates.get("sender")
        not(result.hasError()) and
        timeout
    }

    run StateModificationOK_DeliverPacketToProviderTimeoutTest =
    {
        val result = DeliverPacketToProviderTimeoutTest_resultAndTimeout._1
        val newProviderState = result.newState.providerState
        val newConsumerState = result.newState.consumerStates.get("sender")
        not(result.hasError()) and
        newProviderState.receivedMaturations.size() == 0 and
        newProviderState.consumerStatus.get("sender") == TIMEDOUT
    }

    run ConsumerStatusMapHappyPathTest = 
    {
        val currentConsumerStatusMap = Map(
            "chain1" -> NOT_CONSUMER,
            "chain2" -> RUNNING,
            "chain3" -> STOPPED
        )
        val res = StartStopConsumers(
            currentConsumerStatusMap,
            Set("chain1"),
            Set("chain2"),
            Set()
        )
        res._2 == "" and
        res._1.get("chain1") == RUNNING and
        res._1.get("chain2") == STOPPED and
        res._1.get("chain3") == STOPPED
    }

    run ConsumerStatusMapAlreadyRunningTest =
    {
        val currentConsumerStatusMap = Map(
            "chain1" -> NOT_CONSUMER,
            "chain2" -> RUNNING,
            "chain3" -> STOPPED
        )
        val res = StartStopConsumers(
            currentConsumerStatusMap,
            Set("chain2"),
            Set("chain3"),
            Set()
        )
        res._2 == "cannot start a consumer that is stopped or already a consumer"
    }

    run ConsumerStatusMapAlreadyStoppedTest =
    {
        val currentConsumerStatusMap = Map(
            "chain1" -> NOT_CONSUMER,
            "chain2" -> RUNNING,
            "chain3" -> STOPPED
        )
        val res = StartStopConsumers(
            currentConsumerStatusMap,
            Set("chain1"),
            Set("chain3"),
            Set()
        )
        res._2 == "Cannot stop a consumer that is not running"
    }

    run ChainBothInStartAndStopTest =
    {
        val currentConsumerStatusMap = Map(
            "chain1" -> NOT_CONSUMER,
            "chain2" -> RUNNING,
            "chain3" -> STOPPED
        )
        val res = StartStopConsumers(
            currentConsumerStatusMap,
            Set("chain1"),
            Set("chain1"),
            Set()
        )
        res._2 == "Cannot start and stop a consumer at the same time"
    }
}