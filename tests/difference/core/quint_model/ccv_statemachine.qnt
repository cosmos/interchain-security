module CCVDefaultStateMachine {
    // A basic state machine that utilizes the CCV protocol.
    import CCVTypes.* from "./ccv"
    import Time.* from "./libraries/Time"
    import extraSpells.* from "./libraries/extraSpells"

    pure val consumerChains = Set("consumer1", "consumer2", "consumer3")
    pure val chains = consumerChains.union(Set(PROVIDER_CHAIN))
    pure val unbondingPeriods = chains.mapBy(chain => 2 * Week)
    pure val ccvTimeouts = chains.mapBy(chain => 3 * Week)

    pure val nodes = Set("node1", "node2", "node3", "node4", "node5", "node6", "node7", "node8", "node9", "node10")
    pure val InitialValidatorSet = nodes.mapBy(node => 100)

    import CCV(VscTimeout = 5 * Week, CcvTimeout = ccvTimeouts, UnbondingPeriodPerChain = unbondingPeriods, ConsumerChains = consumerChains).* from "./ccv"


    var currentState: ProtocolState
    
    // bookkeeping
    var trace: List[str]

    // some utility stateful vals to make invariants easier to define
    val providerValidatorHistory = currentState.providerState.chainState.votingPowerHistory
    val runningConsumers = getRunningConsumers(currentState.providerState)
    val unusedConsumers = getUnusedConsumers(currentState.providerState)

    action init: bool = all {
        val providerState = GetEmptyProviderState
        val consumerStates = ConsumerChains.mapBy(chain => GetEmptyConsumerState)
        val providerStateWithConsumers = providerState.with(
            "consumerStatus", 
            ConsumerChains.mapBy(chain => UNUSED)
        ).with(
            "outstandingPacketsToConsumer", 
            ConsumerChains.mapBy(chain => List())
        ).with(
            "sentVSCPackets", 
            ConsumerChains.mapBy(chain => List())
        ).with(
            // set the validator set to be the initial validator set in the history
            "chainState", providerState.chainState.with(
                "votingPowerHistory", List(InitialValidatorSet)
            ).with(
                "currentValidatorSet", InitialValidatorSet
            )
        )
        currentState' = {
            providerState: providerStateWithConsumers,
            consumerStates: consumerStates
        },
        trace' = List("init")
    }

    action VotingPowerChange(validator: Node, newVotingPower: int): bool = 
        val result = votingPowerChange(currentState, validator, newVotingPower)
        all {
            result.hasError == false,
            currentState' = result.newState,
            trace' = trace.append("VotingPowerChange")
        }

    // The receiver receives the next outstanding VSCPacket from the provider.
    // This will time out the consumer if the packet timeout has passed on the receiver.
    action DeliverVSCPacket(receiver: Chain): bool = 
        val resultAndTimeout = deliverPacketToConsumer(currentState, receiver)
        val result = resultAndTimeout._1
        all {
            result.hasError == false,
            currentState' = result.newState,
            trace' = trace.append("DeliverVSCPacket")
        }

    // The provider receives the next outstanding VSCMaturedPacket from the sender.
    // This will time out the consumer if the packet timeout has passed on the provider.
    action DeliverVSCMaturedPacket(sender: Chain): bool =
        val resultAndTimeout = deliverPacketToProvider(currentState, sender)
        val result = resultAndTimeout._1
        all {
            result.hasError == false,
            currentState' = result.newState,
            trace' = trace.append("DeliverVSCMaturedPacket")
        }

    action EndAndBeginBlockForProvider(
        timeAdvancement: Time,
        consumersToStart: Set[Chain],
        consumersToStop: Set[Chain]): bool = 
        val result = endAndBeginBlockForProvider(currentState, timeAdvancement, consumersToStart, consumersToStop)
        all {
            result.hasError == false,
            currentState' = result.newState,
            trace' = trace.append("EndAndBeginBlockForProvider")
        }

    action EndAndBeginBlockForConsumer(
        chain: Chain,
        timeAdvancement: Time): bool = 
        val result = endAndBeginBlockForConsumer(currentState, chain, timeAdvancement)
        all {
            result.hasError == false,
            currentState' = result.newState,
            trace' = trace.append("EndAndBeginBlockForConsumer")
        }

    // a few different values for time advancements.
    // to keep the number of possible steps small, we only have a few different values.
    // Roughly, 1s for very small advances (like between blocks),
    // and then longer values for increasingly severe downtime scenarios.
    // Note that these can still be combined, so in effect we can get all time advancements by any amount of seconds.
    pure val timeAdvancements = Set(1 * Second, 1 * Day, 1 * Week, 4 * Week)

    // step allows the most generic nondeterminism, in particular it becomes relatively likely
    // that over a long enough runtime, all consumers would time out by mismatching their time advancements,
    // and each endblock has a good chance to stop consumers, ...
    // step is thus suited to test also unhappy paths.
    action step = any {
        nondet chain = oneOf(runningConsumers)
        nondet timeAdvancement = oneOf(timeAdvancements)
        EndAndBeginBlockForConsumer(chain, timeAdvancement),

        val consumerStatus = currentState.providerState.consumerStatus
        nondet consumersToStart = oneOf(unusedConsumers.powerset())
        nondet consumersToStop = oneOf(runningConsumers.powerset())
        nondet timeAdvancement = oneOf(timeAdvancements)
        EndAndBeginBlockForProvider(timeAdvancement, consumersToStart, consumersToStop),

        nondet node = oneOf(nodes)
        // very restricted set of voting powers. exact values are not important,
        // and this keeps the state space smaller.
        // 0 for getting a validator out of the validator set, and two non-zero values
        nondet newVotingPower = oneOf(Set(0, 50, 100))
        VotingPowerChange(node, newVotingPower),

        // try to send a packet. we could filter by chains that can actually send,
        // but it's probably not much faster than just trying and failing.
        nondet sender = oneOf(runningConsumers)
        DeliverVSCMaturedPacket(sender),

        // again, we could filter by chains that can actually receive,
        // but it's probably not much faster than just trying and failing.
        nondet recciver = oneOf(runningConsumers)
        DeliverVSCPacket(recciver),
    }

    // ==================
    // INVARIANT CHECKS
    // ==================


    // Every validator set on any consumer chain MUST either be or have been 
    // a validator set on the provider chain.
    val ValidatorSetHasExistedInv =
        runningConsumers.forall(chain =>
            currentState.consumerStates.get(chain).chainState.votingPowerHistory.toSet().forall(
                validatorSet => providerValidatorHistory.toSet().contains(validatorSet)
            )
        )

    // Any update in the power of a validator on the provider
    // MUST be present in a ValidatorSetChangePacket that is sent to all registered consumer chains
    val ValidatorUpdatesArePropagated =
        // when the provider has just entered a validator set into a block...
        if (trace == trace.append("EndAndBeginBlockForProvider")) {
            val providerValSetInCurBlock = providerValidatorHistory.head()
            // ... for each consumer that is running then ...
            runningConsumers.forall(
                // ...the validator set is in a sent packet
                consumer => currentState.providerState.sentVSCPackets.get(consumer).toSet().exists(
                    packet => packet.validatorSet == providerValSetInCurBlock
                )
            )
        } else {
            true
        }

    // Every consumer chain receives the same sequence of 
    // ValidatorSetChangePackets in the same order.
    // NOTE: since not all consumer chains are running all the time,
    // we need a slightly weaker invariant:
    // For consumer chains c1, c2, if both c1 and c2 received a packet p1 sent at t1 and a packet p2 sent at t2,
    // then both have received ALL packets that were sent between t1 and t2.
    val SameVSCPacketsInv =
        runningConsumers.forall(
            consumer1 => runningConsumers.forall(
                consumer2 => {
                    val packets1 = currentState.consumerStates.get(consumer1).receivedVSCPackets
                    val packets2 = currentState.consumerStates.get(consumer2).receivedVSCPackets
                    val commonPackets = packets1.toSet().intersect(packets2.toSet())
                    if (commonPackets.size() == 0) {
                        true // they don't share any packets, so nothing to check
                    } else {
                        val oldestCommonPacket = packets1.head()
                        val newestCommonPacket = packets1[packets1.length() - 1]
                        // get all packets sent between the oldest and newest common packet
                        val packetsBetween1 = packets1.select(
                            packet => packet.sendingTime >= oldestCommonPacket.sendingTime and packet.sendingTime <= newestCommonPacket.sendingTime
                        )
                        val packetsBetween2 = packets2.select(
                            packet => packet.sendingTime >= oldestCommonPacket.sendingTime and packet.sendingTime <= newestCommonPacket.sendingTime
                        )
                        // these should be the same on both chains
                        packetsBetween1 == packetsBetween2
                    }
                }
            )
        )

    // For every ValidatorSetChangePacket received by a consumer chain at 
    // time t, a MaturedVSCPacket is sent back to the provider in the first block 
    // with a timestamp >= t + UnbondingPeriod
    // NOTE: because we remove the maturationTimes entry when we send the packets,
    // it suffices to check that there is never an entry in maturationTimes
    // that is older than the current time minus the unbonding period.
    val MatureOnTimeInv =
        runningConsumers.forall(
            consumer => {
                val maturationTimes = currentState.consumerStates.get(consumer).maturationTimes
                maturationTimes.keys().forall(
                    packet => packet.sendingTime + UnbondingPeriodPerChain.get(consumer) <= currentState.providerState.chainState.lastTimestamp
                )
            }
        )

    // If we send a VSCPacket, this is eventually responded to by all consumers
    // that were running at the time the packet was sent (and are still running).
    // Since we remove sentVSCPackets when we receive responses for them,
    // we just check that if a sentVSCPacket has been sent more than
    // VSCTimeout ago, the consumer must have been dropped.
    // In practice, when this is true, a pending unbonding can mature.
    val EventuallyMatureOnProviderInv =
        runningConsumers.forall(
            consumer => {
                val sentPackets = currentState.providerState.sentVSCPackets.get(consumer).toSet()
                sentPackets.forall(
                    packet =>
                        // consumer still has time to respond
                        currentState.providerState.chainState.lastTimestamp <= packet.sendingTime + VscTimeout or
                        // consumer was dropped
                        currentState.providerState.consumerStatus.get(consumer) == STOPPED or
                        currentState.providerState.consumerStatus.get(consumer) == TIMEDOUT
                )
            }
        )

    // =================
    // SANITY CHECKS
    // =================
    // some invariants that should fail,
    // to check that certain behaviours can be exhibited.
    // The name of the invariants is the name of the behaviour
    // we want to see, and its definition will *negate* that behaviour, so
    // we expect these to fail when checked as invariants.

     // We can run consumers.
     val CanRunConsumer =
        not(ConsumerChains.exists(
            consumer => 
                currentState.providerState.consumerStatus.get(consumer) == RUNNING
        ))

    val CanStopConsumer =
        not(ConsumerChains.exists(
            consumer => 
                currentState.providerState.consumerStatus.get(consumer) == STOPPED
        ))

    val CanTimeoutConsumer =
        not(ConsumerChains.exists(
            consumer => 
                currentState.providerState.consumerStatus.get(consumer) == TIMEDOUT
        ))

    val CanSendVSCPackets =
        not(ConsumerChains.exists(
            consumer => 
                currentState.providerState.outstandingPacketsToConsumer.get(consumer).length() > 0
        ))

    val CanSendVSCMaturedPackets =
        not(ConsumerChains.exists(
            consumer => 
                currentState.consumerStates.get(consumer).outstandingPacketsToProvider.length() > 0
        ))

    // ==================
    // MANUAL TEST CASES
    // ==================
    // Manually written test cases to get confidence in the base operation of the protocol.

    // Test a simple happy path where:
    // * the consumer chain is set to running
    // * a validator set change happens
    // * a block is ended on the provider, i.e. a packet is sent to the consumer
    // * the consumer receives the packet
    // * the chains wait until the unbonding period is over
    // * the consumer sends a VSCMaturedPacket to the provider
    // * the provider receives the VSCMaturedPacket
    run HappyPathTest: bool = { 
        init.then(
            all {
                assert(currentState.providerState.consumerStatus == Map(
                    "consumer1" -> UNUSED,
                    "consumer2" -> UNUSED,
                    "consumer3" -> UNUSED
                )),
                assert(currentState.providerState.outstandingPacketsToConsumer == Map(
                    "consumer1" -> List(),
                    "consumer2" -> List(),
                    "consumer3" -> List()
                )),
                assert(currentState.providerState.sentVSCPackets == Map(
                    "consumer1" -> List(),
                    "consumer2" -> List(),
                    "consumer3" -> List()
                )),
                assert(currentState.consumerStates.keys() == consumerChains),
                assert(currentState.providerState.chainState.votingPowerHistory == List(InitialValidatorSet)),
                assert(currentState.providerState.chainState.currentValidatorSet == InitialValidatorSet),
                assert(currentState.providerState.chainState.lastTimestamp == 0),
                VotingPowerChange("node1", 50)
            })
            .then(
            all {
                // the validator set has changed
                assert(currentState.providerState.chainState.currentValidatorSet == InitialValidatorSet.put("node1", 50)),
                // start consumer1
                EndAndBeginBlockForProvider(1 * Second, Set("consumer1"), Set())
            })
            .then(
                all {
                    // consumer1 was started
                    assert(currentState.providerState.consumerStatus.get("consumer1") == RUNNING),
                    // a packet was sent to consumer1
                    assert(currentState.providerState.outstandingPacketsToConsumer.get("consumer1").length() == 1),
                    // the validator set on the provider was entered into the history
                    assert(currentState.providerState.chainState.votingPowerHistory == List(InitialValidatorSet.put("node1", 50), InitialValidatorSet)),
                    // deliver the packet
                    DeliverVSCPacket("consumer1")
                }
            )
            .then(
                all {
                    // make sure the packet was removed from the provider
                    assert(currentState.providerState.outstandingPacketsToConsumer.get("consumer1").length() == 0),
                    // ensure the maturation time was entered on the consumer
                    assert(currentState.consumerStates.get("consumer1").maturationTimes.keys().size() == 1),
                    // the validator set was put as the current validator set
                    assert(currentState.consumerStates.get("consumer1").chainState.currentValidatorSet == InitialValidatorSet.put("node1", 50)),
                    // advance time on provider until the unbonding period is over
                    EndAndBeginBlockForProvider(UnbondingPeriodPerChain.get("consumer1"), Set(), Set()),
                }
            )
            .then(
                // advance time on consumer until the unbonding period is over
                EndAndBeginBlockForConsumer("consumer1", UnbondingPeriodPerChain.get("consumer1"))
            )
            .then(
                all {
                    // the packet has matured, so it was sent by the consumer
                    assert(currentState.consumerStates.get("consumer1").outstandingPacketsToProvider.length() == 1),
                    // it was removed from the maturationTimes
                    assert(currentState.consumerStates.get("consumer1").maturationTimes.keys().size() == 0),
                    // receive the packet on the provider
                    DeliverVSCMaturedPacket("consumer1")
                }
            )
            .then(
                all {
                    // the packet was received on the provider
                    assert(currentState.providerState.receivedMaturations.size() == 1),
                    // the packet was removed from the consumer
                    assert(currentState.consumerStates.get("consumer1").outstandingPacketsToProvider.length() == 0),
                    currentState' = currentState, // just so this still has an effect
                    trace' = trace.append("HappyPathTest")
                }
            )
        }
}