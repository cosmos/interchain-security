// -*- mode: Bluespec; -*-
module ccv_model {
    // A basic stateful model that utilizes the CCV protocol.
    import ccv_types.* from "./ccv"
    import Time.* from "./libraries/Time"
    import extraSpells.* from "./libraries/extraSpells"

    pure val consumerChainList = List("consumer1", "consumer2", "consumer3")
    pure val consumerChains = consumerChainList.toSet()
    pure val chains = consumerChains.union(Set(PROVIDER_CHAIN))
    pure val defUnbondingPeriod = 2 * Week
    pure val unbondingPeriods = chains.mapBy(chain => defUnbondingPeriod)
    pure val trustingPeriods = chains.mapBy(chain => defUnbondingPeriod - 1 * Hour)
    pure val ccvTimeouts = chains.mapBy(chain => 3 * Week)

    pure val nodes = Set("node1", "node2", "node3", "node4", "node5", "node6", "node7", "node8", "node9", "node10")
    pure val InitialValidatorSet = nodes.mapBy(node => 100)

    import ccv(VscTimeout = 5 * Week, CcvTimeout = ccvTimeouts, UnbondingPeriodPerChain = unbondingPeriods, ConsumerChains = consumerChains, TrustingPeriodPerChain = trustingPeriods).* from "./ccv"

    // TODO: introduce max clock drift to produce traces with bounded drift

    type Parameters = {
        VscTimeout: Time,
        CcvTimeout: Chain -> Time,
        UnbondingPeriodPerChain: Chain -> Time,
        TrustingPeriodPerChain: Chain -> Time, // TODO: integrate trusting period in logic
        ConsumerChains: Set[Chain],
        Nodes: Set[Node],
        InitialValidatorSet: Node -> int,
    }

    var params: Parameters

    var currentState: ProtocolState

    // a type storing the parameters used in actions.
    // this is used in the trace to store
    // the name of the last action, plus the parameters we passed to it.
    // Note: This type holds ALL parameters that are used in ANY action,
    // so not all of these fields are relevant to each action.
    type Action =
        {
            kind: str,
            consumerChain: Chain,
            timeAdvancement: Time,
            consumersToStart: Set[Chain],
            consumersToStop: Set[Chain],
            validator: Node,
            changeAmount: int,
        }
    

    var trace: List[Action]

    // a few different values for time advancements.
    // to keep the number of possible steps small, we only have a few different values.
    // Roughly, 1s for very small advances (like between blocks),
    // and then longer values for increasingly severe downtime scenarios.
    // Note that these can still be combined, so in effect we can get all time advancements by any amount of seconds.
    // These should be smaller than the minimal TrustingPeriodPerChain,
    // otherwise connections will break down.
    pure val timeAdvancements = Set(1 * Second, 1 * Day, 1 * Week - 1 * Hour) // 4 * Week)

    pure def emptyAction =
            {
                kind: "",
                consumerChain: "",
                timeAdvancement: 0 * Second,
                consumersToStart: Set(),
                consumersToStop: Set(),
                validator: "",
                changeAmount: 0,
            }


    // some utility stateful vals to make invariants easier to define
    val providerValidatorHistory = currentState.providerState.chainState.votingPowerHistory
    val runningConsumers = getRunningConsumers(currentState.providerState)
    val nonConsumers = getNonConsumers(currentState.providerState)

    action init: bool = all {
        val providerState = GetEmptyProviderState
        val consumerStates = ConsumerChains.mapBy(chain => GetEmptyConsumerState)
        val providerStateWithConsumers = providerState.with(
            "consumerStatus", 
            ConsumerChains.mapBy(chain => NOT_CONSUMER)
        ).with(
            "outstandingPacketsToConsumer", 
            ConsumerChains.mapBy(chain => List())
        ).with(
            "sentVscPacketsToConsumer", 
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
        trace' = List(emptyAction.with("kind", "init")),
        params' = {
            VscTimeout: VscTimeout,
            CcvTimeout: CcvTimeout,
            UnbondingPeriodPerChain: UnbondingPeriodPerChain,
            ConsumerChains: ConsumerChains,
            Nodes: nodes,
            InitialValidatorSet: InitialValidatorSet,
            TrustingPeriodPerChain: TrustingPeriodPerChain,
        }
    }

    action VotingPowerChange(validator: Node, changeAmount: int): bool = 
        val result = votingPowerChange(currentState, validator, changeAmount)
        all {
            result.hasError() == false,
            currentState' = result.newState,
            trace' = trace.append(emptyAction.with("kind", "VotingPowerChange").with("validator", validator).with("changeAmount", changeAmount)),
            params' = params,
        }

    // The receiver receives the next outstanding VscPacket from the provider.
    // This will time out the consumer if the packet timeout has passed on the receiver.
    action DeliverVscPacket(receiver: Chain): bool = 
        val resultAndTimeout = deliverPacketToConsumer(currentState, receiver)
        val result = resultAndTimeout._1
        all {
            result.hasError() == false,
            currentState' = result.newState,
            trace' = trace.append(emptyAction.with("kind", "DeliverVscPacket").with("consumerChain", receiver)),
            params' = params,
        }

    // The provider receives the next outstanding VscMaturedPacket from the sender.
    // This will time out the consumer if the packet timeout has passed on the provider.
    action DeliverVscMaturedPacket(sender: Chain): bool =
        val resultAndTimeout = deliverPacketToProvider(currentState, sender)
        val result = resultAndTimeout._1
        all {
            result.hasError() == false,
            currentState' = result.newState,
            trace' = trace.append(emptyAction.with("kind", "DeliverVscMaturedPacket").with("consumerChain", sender)),
            params' = params,
        }

    action EndAndBeginBlockForProvider(
        timeAdvancement: Time,
        consumersToStart: Set[Chain],
        consumersToStop: Set[Chain]): bool = 
        val result = endAndBeginBlockForProvider(currentState, timeAdvancement, consumersToStart, consumersToStop)
        all {
            result.hasError() == false,
            currentState' = result.newState,
            trace' = trace.append(emptyAction.with("kind", "EndAndBeginBlockForProvider").with("timeAdvancement", timeAdvancement).with("consumersToStart", consumersToStart).with("consumersToStop", consumersToStop)),
            params' = params,
        }

    action EndAndBeginBlockForConsumer(
        chain: Chain,
        timeAdvancement: Time): bool = 
        val result = endAndBeginBlockForConsumer(currentState, chain, timeAdvancement)
        all {
            result.hasError() == false,
            currentState' = result.newState,
            trace' = trace.append(emptyAction.with("kind", "EndAndBeginBlockForConsumer").with("consumerChain", chain).with("timeAdvancement", timeAdvancement)),
            params' = params,
        }

     // step_common is the core functionality of steps that does not have anything to do with time.
    // Thus, it is part of both step and stepBoundedDrift.
    action step_common = any {
        nondet node = oneOf(nodes)
        // very restricted set of voting powers. exact values are not important,
        // and this keeps the state space smaller.
        nondet newVotingPower = oneOf(Set(-50, 50))
        VotingPowerChange(node, newVotingPower),

        // try to send a packet. we could filter by chains that can actually send,
        // but it's probably not much faster than just trying and failing.
        all {
            runningConsumers.size() > 0, // ensure there is a running consumer, otherwise this action does not make sense
            nondet sender = oneOf(runningConsumers)
            DeliverVscMaturedPacket(sender),
        },

        // again, we could filter by chains that can actually receive,
        // but it's probably not much faster than just trying and failing.
        all {
            runningConsumers.size() > 0, // ensure there is a running consumer, otherwise this action does not make sense
            nondet recciver = oneOf(runningConsumers)
            DeliverVscPacket(recciver),
        },
    }

    // step allows the most generic nondeterminism, in particular it becomes relatively likely
    // that over a long enough runtime, all consumers would time out by mismatching their time advancements,
    // and each endblock has a good chance to stop consumers, ...
    // step is thus suited to test also unhappy paths.
    action step = any {
        all {
            runningConsumers.size() > 0, // ensure there is a running consumer, otherwise this action does not make sense
            nondet chain = oneOf(runningConsumers)
            nondet timeAdvancement = oneOf(timeAdvancements)
            EndAndBeginBlockForConsumer(chain, timeAdvancement),
        },

        val consumerStatus = currentState.providerState.consumerStatus
        nondet consumersToStart = oneOf(nonConsumers.powerset())
        nondet consumersToStop = oneOf(runningConsumers.powerset())
        nondet timeAdvancement = oneOf(timeAdvancements)
        EndAndBeginBlockForProvider(timeAdvancement, consumersToStart, consumersToStop),

        step_common
    }

    // ==================
    // UTILITY FUNCTIONS
    // ==================

    pure def earliest(packets: Set[VscPacket]): VscPacket =
        val latestPossiblePacket: VscPacket = {
            id: 0,
            validatorSet: Map(),
            sendingTime: 9999999999999 * Second,
        }
        packets.fold(
            latestPossiblePacket,
            (res, pack) => if(res.sendingTime < pack.sendingTime) { res } else { pack }
        )

    pure def latest(packets: Set[VscPacket]): VscPacket =
        val earliestPossiblePacket: VscPacket = {
            id: 0,
            validatorSet: Map(),
            sendingTime: -9999999999 * Second,
        }
        packets.fold(
            earliestPossiblePacket,
            (res, pack) => if(res.sendingTime >= pack.sendingTime) { res } else { pack }
        )

    // run maxByTest =
    // all {
    //   assert(maxBy(Set(1, 2, 3), __x => __x) == 3),
    //   assert(maxBy(Set(1, 2, 3), __x => -__x) == 1),
    // }
    run earliestLatestTest = {
    val packet1 = {
            id: 1,
            validatorSet: Map(),
            sendingTime: 1 * Second,
        }

        val packet2 = {
            id: 2,
            validatorSet: Map(),
            sendingTime: 2 * Second,
        }

        val packet3 = {
            id: 3,
            validatorSet: Map(),
            sendingTime: 3 * Second,
        }
        all {
            assert(earliest(Set(packet1, packet2, packet3)) == packet1),
            assert(earliest(Set(packet3, packet2, packet1)) == packet1),
            assert(latest(Set(packet1, packet2, packet3)) == packet3),
            assert(latest(Set(packet3, packet2, packet1)) == packet3),
        }
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
    val ValUpdatePrecondition = trace[trace.length()-1].kind == "EndAndBeginBlockForProvider"
    val ValidatorUpdatesArePropagatedInv = 
        // when the provider has just entered a validator set into a block...
        ValUpdatePrecondition and currentState.providerState.providerValidatorSetChangedInThisBlock
            implies
        val providerValSetInCurBlock = providerValidatorHistory.head()
        // ... for each consumer that is running then ...
        runningConsumers.forall(
            // ...the validator set is in a sent packet
            consumer => currentState.providerState.sentVscPacketsToConsumer.get(consumer).toSet().exists(
                packet => packet.validatorSet == providerValSetInCurBlock
            )
        )

    // Every consumer chain receives the same sequence of 
    // ValidatorSetChangePackets in the same order.
    // NOTE: since not all consumer chains are running all the time,
    // we need a slightly weaker invariant:
    // For consumer chains c1, c2, if both c1 and c2 received a packet p1 sent at t1 and a packet p2 sent at t2,
    // then both have received ALL packets that were sent between t1 and t2.
    val SameVscPacketsInv =
        runningConsumers.forall(
            consumer1 => runningConsumers.forall(
                consumer2 => {
                    val packets1 = currentState.consumerStates.get(consumer1).receivedVscPackets
                    val packets2 = currentState.consumerStates.get(consumer2).receivedVscPackets
                    val commonPackets = packets1.toSet().intersect(packets2.toSet())
                    if (commonPackets.size() == 0) {
                        true // they don't share any packets, so nothing to check
                    } else {
                        val newestCommonPacket = commonPackets.latest()
                        val oldestCommonPacket = commonPackets.earliest()
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
    // time t, a MaturedVscPacket is sent back to the provider when we end the first block 
    // with a timestamp >= t + UnbondingPeriod
    // NOTE: because we remove the maturationTimes entry when we send the packets,
    // it suffices to check that after we end/begin a block, there is never an entry in maturationTimes
    // that has already matured, i.e. where the maturationTime is smaller-or-equal than the
    // timestamp of the block we just ended
    val MaturationPrecondition = trace[trace.length()-1].kind == "EndAndBeginBlockForConsumer"
    val ConsumerWithPotentialMaturations = trace[trace.length()-1].consumerChain
    val lastTimeAdvancement = trace[trace.length()-1].timeAdvancement
    val lastBlockTime = currentState.consumerStates.get(ConsumerWithPotentialMaturations).chainState.lastTimestamp - lastTimeAdvancement
    val MatureOnTimeInv =
        MaturationPrecondition
        implies
        currentState.consumerStates.get(ConsumerWithPotentialMaturations).maturationTimes.toSet().forall(
            pair => 
            val maturationTime = pair._2 
            maturationTime > lastBlockTime
        )


    // If we send a VscPacket, this is eventually responded to by all consumers
    // that were running at the time the packet was sent (and are still running).
    // Since we remove sentVscPacketsToConsumer when we receive responses for them,
    // we just check that if a sentVscPacket has been sent more than
    // VscTimeout ago, the consumer must have been dropped.
    // In practice, when this is true, a pending unbonding can mature.
    val EventuallyMatureOnProviderInv =
        runningConsumers.forall(
            consumer => {
                val sentPackets = currentState.providerState.sentVscPacketsToConsumer.get(consumer).toSet()
                sentPackets.forall(
                    packet =>
                        // consumer still has time to respond
                        not(packet.sendingTime + VscTimeout < currentState.providerState.chainState.lastTimestamp) or
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

    val CanSendVscPackets =
        not(ConsumerChains.exists(
            consumer => 
                currentState.providerState.outstandingPacketsToConsumer.get(consumer).length() > 0
        ))

    val CanReceiveVscPackets =
        not(trace[length(trace)-1].kind == "DeliverVscPacket")

    val CanSendVscMaturedPackets =
        not(ConsumerChains.exists(
            consumer => 
                currentState.consumerStates.get(consumer).outstandingPacketsToProvider.length() > 0
        ))
    
    val CanReceiveMaturations =
        not(ConsumerChains.exists(
            consumer => 
                currentState.providerState.receivedMaturations.size() > 0
        ))

    // ==================
    // MANUAL TEST CASES
    // ==================
    // Manually written test cases to get confidence in the base operation of the protocol.

    /// Test a simple happy path where:
    /// * the consumer chain is set to running
    /// * a validator set change happens
    /// * a block is ended on the provider, i.e. a packet is sent to the consumer
    /// * the consumer receives the packet
    /// * the chains wait until the unbonding period is over
    /// * the consumer sends a VscMaturedPacket to the provider
    /// * the provider receives the VscMaturedPacket
    run HappyPathTest: bool = { 
        init.then(
            all {
                assert(currentState.providerState.consumerStatus == Map(
                    "consumer1" -> NOT_CONSUMER,
                    "consumer2" -> NOT_CONSUMER,
                    "consumer3" -> NOT_CONSUMER
                )),
                assert(currentState.providerState.outstandingPacketsToConsumer == Map(
                    "consumer1" -> List(),
                    "consumer2" -> List(),
                    "consumer3" -> List()
                )),
                assert(currentState.providerState.sentVscPacketsToConsumer == Map(
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
                assert(currentState.providerState.chainState.currentValidatorSet == InitialValidatorSet.put("node1", 150)),
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
                    assert(currentState.providerState.chainState.votingPowerHistory == List(InitialValidatorSet.put("node1", 150), InitialValidatorSet)),
                    // deliver the packet
                    DeliverVscPacket("consumer1")
                }
            )
            .then(
                all {
                    // make sure the packet was removed from the provider
                    assert(currentState.providerState.outstandingPacketsToConsumer.get("consumer1").length() == 0),
                    // ensure the maturation time was entered on the consumer
                    assert(currentState.consumerStates.get("consumer1").maturationTimes.length() == 1),
                    // the validator set was put as the current validator set
                    assert(currentState.consumerStates.get("consumer1").chainState.currentValidatorSet == InitialValidatorSet.put("node1", 150)),
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
                    // the packet has not matured yet - the timestamp for the current block is after the naturation time,
                    // but packets are only sent on EndBlock
                    assert(currentState.consumerStates.get("consumer1").outstandingPacketsToProvider.length() == 0),
                    // the packet is still waiting to mature
                    assert(currentState.consumerStates.get("consumer1").maturationTimes.length() == 1),
                    // end another block, this time after the time has been reached
                    EndAndBeginBlockForConsumer("consumer1", 1 * Second)
                }
            )
            .then(
                all {
                    // the packet now was sent by the consumer
                    assert(currentState.consumerStates.get("consumer1").outstandingPacketsToProvider.length() == 1),
                    // it was removed from the maturationTimes
                    assert(currentState.consumerStates.get("consumer1").maturationTimes.length() == 0),
                    // receive the packet on the provider
                    DeliverVscMaturedPacket("consumer1")
                }
            )
            .then(
                all {
                    // the packet was received on the provider
                    assert(currentState.providerState.receivedMaturations.size() == 1),
                    // the packet was removed from the consumer
                    assert(currentState.consumerStates.get("consumer1").outstandingPacketsToProvider.length() == 0),
                    VotingPowerChange("node1", 50) // just so this still has an effect
                }
            )
        }

    /// a manual test case for the SameVscPacketsInv, since it needs very specific behaviour to even apply.
    run SameVscPacketsManualTest =
        init.then(
            // start all consumers except for consumer3
            EndAndBeginBlockForProvider(1 * Second, Set("consumer1", "consumer2"), Set())
        ).then(
            // change voting power
            VotingPowerChange("node1", 50)
        ).then(
            // send packet to consumer1 and consumer2
            EndAndBeginBlockForProvider(1 * Second, Set(), Set())
        ).then(
            // deliver the packets
            DeliverVscPacket("consumer1")
        ).then(
            // deliver to consumer2
            DeliverVscPacket("consumer2")
        ).then(
            // start consumer3
            EndAndBeginBlockForProvider(1 * Second, Set("consumer3"), Set())
        ).then(
            // do another voting power change
            VotingPowerChange("node2", 50)
        ).then(
            // send packets
            EndAndBeginBlockForProvider(1 * Second, Set(), Set())
        ).then(
            //deliver to consumer1
            DeliverVscPacket("consumer1")
        ).then(
            // deliver to consumer2
            DeliverVscPacket("consumer2")
        ).then(
            // deliver to consumer3
            DeliverVscPacket("consumer3")
        )
        .then(
            // the SameVscPacketInv should hold here
            all {
                assert(SameVscPacketsInv),
                // action does not matter, but needed to have uniform effect
                VotingPowerChange("node1", 50)
            }
        )

    // a manual test for the EventuallyMatureOnProvider invariant
    run VscTimeoutManualTest =
        init
        .then(
            // start all consumer chains
            EndAndBeginBlockForProvider(1 * Second, ConsumerChains, Set())
        )
        .then(
            // change voting power
            VotingPowerChange("node1", 50)
        )
        .then(
            // send packets
            EndAndBeginBlockForProvider(1 * Second, Set(), Set())
        )
        .then(
            // advance time on provider by VscTimeout + 1 Second
            EndAndBeginBlockForProvider(VscTimeout + 1 * Second, Set(), Set())
        )
        .then(
            all {
                // the consumer chains should have timed out
                assert(ConsumerChains.forall(
                    chain => currentState.providerState.consumerStatus.get(chain) == TIMEDOUT
                )),
                VotingPowerChange("node1", 50) // action needs to be there but does not matter what it is
            }
        )
}