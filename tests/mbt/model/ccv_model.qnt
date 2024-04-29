// -*- mode: Bluespec; -*-
module ccv_model {
    // A basic stateful model that utilizes the CCV protocol.
    import ccv_types.* from "./ccv"
    import Time.* from "./libraries/Time"
    import extraSpells.* from "./libraries/extraSpells"
    import ccv_utils.* from "./ccv_utils"

    pure val consumerChainList = List("consumer1", "consumer2", "consumer3")
    pure val consumerChains = consumerChainList.toSet()
    pure val chains = consumerChains.union(Set(PROVIDER_CHAIN))
    pure val defUnbondingPeriod = 2 * Week
    pure val unbondingPeriods = chains.mapBy(chain => defUnbondingPeriod)
    pure val trustingPeriods = chains.mapBy(chain => defUnbondingPeriod - 1 * Hour)
    pure val ccvTimeouts = chains.mapBy(chain => 3 * Week)
    pure val downtimeJailTime = 5 * Day
    
    // taken from the sdk, jail time ends at maximum of a certain datatype
    // see https://github.com/cosmos/cosmos-sdk/blob/03d578b9de5136ffc658f2b0c07434373b07b7da/x/evidence/types/params.go#L11 
    pure val doubleSignJailEndTime = 253402300799
    pure val epochLength = 3

    pure val nodes = Set("node1", "node2", "node3", "node4", "node5", "node6", "node7", "node8", "node9", "node10")
    // possible consumer addresses that nodes can assign their key to
    pure val consumerAddresses = Set("consAddr1", "consAddr2", "consAddr3", "consAddr4", "consAddr5", "consAddr6", "consAddr7", "consAddr8", "consAddr9", "consAddr10")
    pure val InitialValidatorSet = nodes.mapBy(node => 100)

    import ccv(
        VscTimeout = 5 * Week,
        CcvTimeout = ccvTimeouts,
        UnbondingPeriodPerChain = unbondingPeriods,
        ConsumerChains = consumerChains,
        TrustingPeriodPerChain = trustingPeriods,
        DowntimeJailTime = downtimeJailTime,
        DoubleSignJailEndTime = doubleSignJailEndTime,
        DowntimeSlashPercentage = 5,
        DoubleSignSlashPercentage = 10,
        BlocksPerEpoch = epochLength
    ).* from "./ccv"

    type Parameters = {
        VscTimeout: Time,
        CcvTimeout: Chain -> Time,
        UnbondingPeriodPerChain: Chain -> Time,
        TrustingPeriodPerChain: Chain -> Time,
        ConsumerChains: Set[Chain],
        Nodes: Set[Node],
        ConsumerAddresses: Set[ConsumerAddr],
        InitialValidatorSet: Node -> int,
        DowntimeSlashPercentage: int,
        DoubleSignSlashPercentage: int,
        DowntimeJailDuration: Time,
        BlocksPerEpoch: int,
    }

    // The params variable is never actually changed, and
    // just exists so the parameters are entered into the .itf file when we generate traces.
    // This should be removed when/if Quint adds support to put the
    // constant initializations in its output.
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
            consumerAddr: ConsumerAddr,
            vscId: VscId,
            isDowntime: bool,
        }
    

    var trace: List[Action]

    // a few different values for time advancements.
    // to keep the number of possible steps small, we only have a few different values.
    // Roughly, 1s for very small advances (like between blocks),
    // and then longer values for increasingly severe downtime scenarios.
    // Note that these can still be combined, so in effect we can get all time advancements by any amount of seconds.
    // These should be smaller than the minimal TrustingPeriodPerChain,
    // otherwise connections will break down.
    pure val timeAdvancements = Set(1 * Second, 1 * Day, 1 * Week - 1 * Hour)

    pure def emptyAction: Action =
            {
                kind: "",
                consumerChain: "",
                timeAdvancement: 0 * Second,
                consumersToStart: Set(),
                consumersToStop: Set(),
                validator: "",
                changeAmount: 0,
                consumerAddr: "",
                vscId: 0,
                isDowntime: false,
            }


    // some utility stateful vals to make invariants easier to define
    val providerValidatorHistory = currentState.providerState.chainState.votingPowerHistory
    val runningConsumers = getRunningConsumers(currentState.providerState)
    val nonConsumers = getNonConsumers(currentState.providerState)

    val providerCurValSet = currentState.providerState.chainState.currentValidatorPowers

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
                "currentValidatorPowers", InitialValidatorSet
            )
        ).with(
            "keyAssignedValSetHistory", ConsumerChains.mapBy(chain => List(InitialValidatorSet))
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
            ConsumerAddresses: consumerAddresses,
            DowntimeSlashPercentage: DowntimeSlashPercentage,
            DoubleSignSlashPercentage: DoubleSignSlashPercentage,
            DowntimeJailDuration: DowntimeJailTime,
            BlocksPerEpoch: epochLength,
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

    // The provider receives the next outstanding packet from the sender.
    // This will time out the consumer if the packet timeout has passed on the provider.
    action DeliverPacketToProvider(sender: Chain): bool =
        val resultAndTimeout = deliverPacketToProvider(currentState, sender)
        val result = resultAndTimeout._1
        all {
            result.hasError() == false,
            currentState' = result.newState,
            trace' = trace.append(emptyAction.with("kind", "DeliverPacketToProvider").with("consumerChain", sender)),
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


     // stepCommon is the core functionality of steps that does not have anything to do with time.
    action stepCommon = any {
        all {
            nonJailedNodes(currentState.providerState).size() > 0,
            nondet node = oneOf(nonJailedNodes(currentState.providerState))
            // very restricted set of voting powers. exact values are not important,
            // and this keeps the state space smaller.
            nondet newVotingPower = oneOf(Set(-50, 50))
            VotingPowerChange(node, newVotingPower),
        },

        // try to send a packet. we could filter by chains that can actually send,
        // but it's probably not much faster than just trying and failing.
        all {
            runningConsumers.size() > 0, // ensure there is a running consumer, otherwise this action does not make sense
            nondet sender = oneOf(runningConsumers)
            DeliverPacketToProvider(sender),
        },

        // again, we could filter by chains that can actually receive,
        // but it's probably not much faster than just trying and failing.
        all {
            runningConsumers.size() > 0, // ensure there is a running consumer, otherwise this action does not make sense
            nondet receiver = oneOf(runningConsumers)
            DeliverVscPacket(receiver),
        },

        ConsumerInitiatedSlash
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

        stepCommon
    }

    // Runs epochLength many blocks on the provider.
    // The first block will start all consumers in consumersToStart and stop all consumers in consumersToStop,
    // and advance time by timeAdvancement - ((epochLength-1) * Seconds).
    // The rest of the blocks will not start or stop any consumers, and will advance time by 1 second each.
    // As a a `Run`, it is only used in tests, not during simulation or verification.
    run EndProviderEpoch(
        timeAdvancement: Time,
        consumersToStart: Set[Chain],
        consumersToStop: Set[Chain]
    ): bool =
        epochLength.reps(
            i => 
            if (i == 0) {
                EndAndBeginBlockForProvider(timeAdvancement-((epochLength-1)*Second), consumersToStart, consumersToStop)
            } else {
                EndAndBeginBlockForProvider(1 * Second, Set(), Set())
            }
        )

    // ==================
    // UTILITY FUNCTIONS
    // ==================

    pure def removeZeroPowers(valSet: ValidatorSet): ValidatorSet =
        valSet.keys().fold(
            Map(),
            (acc, node) => 
                if (valSet.get(node) == 0) {
                    acc
                } else {
                    acc.put(node, valSet.get(node))
                }
        )

    pure def oldest(packets: Set[VscPacket]): VscPacket =
        val newestPossiblePacket: VscPacket = {
            id: 0,
            validatorSet: Map(),
            sendingTime: 9999999999999 * Second,
            timeoutTime: 9999999999999 * Second,
            downtimeSlashAcks: List(),
        }
        packets.fold(
            newestPossiblePacket,
            (res, pack) => if(res.sendingTime < pack.sendingTime) { res } else { pack }
        )

    pure def newest(packets: Set[VscPacket]): VscPacket =
        val oldestPossiblePacket: VscPacket = {
            id: 0,
            validatorSet: Map(),
            sendingTime: -9999999999 * Second,
            timeoutTime: -9999999999 * Second,
            downtimeSlashAcks: List(),
        }
        packets.fold(
            oldestPossiblePacket,
            (res, pack) => if(res.sendingTime >= pack.sendingTime) { res } else { pack }
        )

    run oldestnewestTest = {
        val packet1 = {
                id: 1,
                validatorSet: Map(),
                sendingTime: 1 * Second,
                timeoutTime: 1 * Second,
                downtimeSlashAcks: List(),
            }

        val packet2 = {
            id: 2,
            validatorSet: Map(),
            sendingTime: 2 * Second,
            timeoutTime: 2 * Second,
            downtimeSlashAcks: List(),
        }

        val packet3 = {
            id: 3,
            validatorSet: Map(),
            sendingTime: 3 * Second,
            timeoutTime: 3 * Second,
            downtimeSlashAcks: List(),
        }
        all {
            assert(oldest(Set(packet1, packet2, packet3)) == packet1),
            assert(oldest(Set(packet3, packet2, packet1)) == packet1),
            assert(newest(Set(packet1, packet2, packet3)) == packet3),
            assert(newest(Set(packet3, packet2, packet1)) == packet3),
        }
    }        

    // ==================
    // INVARIANT CHECKS
    // ==================


    // Every validator set on any consumer chain MUST either be or have been 
    // a validator set on the provider chain.
    val ValidatorSetHasExistedInv =
        runningConsumers.forall(chain => // for all running consumers
            currentState.consumerStates.get(chain).chainState.votingPowerHistory.toSet().forall(
                // go through all its historical and current validator sets
                validatorSet => providerValidatorHistory.toSet().contains(validatorSet)
                // and check that they are also historical or current validator sets on the provider
            )
        )


    val CurrentBlockEndsEpoch = currentState.providerState.chainState.currentBlockHeight % epochLength == 0

    // Any update in the power of a validator on the provider
    // MUST be present in a ValidatorSetChangePacket that is sent to all registered consumer chains
    val ValUpdatePrecondition = trace[trace.length()-1].kind == "EndAndBeginBlockForProvider"
    val ValidatorUpdatesArePropagatedInv = 
        // when the an epoch ends and the provider has just entered a validator set into a block...
        ValUpdatePrecondition and CurrentBlockEndsEpoch
            implies
        val providerValSetInCurBlock = providerValidatorHistory.head()
        // ... for each consumer for which we need to send a vsc packet ...
        currentState.providerState.consumersWithPowerChangesInThisEpoch.forall(
            // ...the validator set is in a sent packet...
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
                        val newestCommonPacket = commonPackets.newest()
                        val oldestCommonPacket = commonPackets.oldest()
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
        // if a consumer ended a block
        MaturationPrecondition
        implies
        // then all matured packets need to have been processed and removed from the packets
        // waiting to mature
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
                val sentPackets = currentState.providerState.sentVscPacketsToConsumer.getOrElse(consumer, List()).toSet()
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

    // for all consumers, waitingForSlashPacketAck is either empty or has a single element
    val WaitingForSlashPacketAckInv = 
        runningConsumers.forall(
            consumer => 
                currentState.consumerStates.get(consumer).waitingForSlashPacketAck.size() <= 1
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
                currentState.providerState.outstandingPacketsToConsumer.getOrElse(consumer, List()).length() > 0
        ))

    val CanReceiveVscPackets =
        not(trace[length(trace)-1].kind == "DeliverVscPacket")

    val CanSendVscMaturedPackets =
        not(ConsumerChains.exists(
            consumer => 
                currentState.consumerStates.get(consumer)
                    .outstandingPacketsToProvider
                    .select(IsVscMaturedPacket).length() > 0
        ))

    val CanSendSlashPacket = 
        not(ConsumerChains.exists(
            consumer => 
                currentState.consumerStates.get(consumer)
                    .outstandingPacketsToProvider
                    .select(IsSlashPacket).length() > 0
        ))

    val CanJail =
        not(
            currentState.providerState.chainState.jailedUntil.keys().size() > 0
        )

    val CanJailMany =
        not(
            currentState.providerState.chainState.jailedUntil.keys().size() > 3
        )
    
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
                assert(currentState.providerState.chainState.currentValidatorPowers == InitialValidatorSet),
                assert(currentState.providerState.chainState.lastTimestamp == -1),
                assert(currentState.providerState.chainState.runningTimestamp == 0),
                VotingPowerChange("node1", 50)
            })
            .then(
            all {
                // the validator set has changed
                assert(currentState.providerState.chainState.currentValidatorPowers == InitialValidatorSet.put("node1", 150)),
                // start consumer1
                EndAndBeginBlockForProvider(1 * Second, Set("consumer1"), Set())
            })
            .then(
                all {
                    // consumer1 was started
                    assert(currentState.providerState.consumerStatus.get("consumer1") == RUNNING),
                    // but no packet was sent to consumer 1
                    assert(currentState.providerState.outstandingPacketsToConsumer.getOrElse("consumer1", List()).length() == 0),
                    // the validator set on the provider was entered into the history
                    assert(currentState.providerState.chainState.votingPowerHistory == List(InitialValidatorSet.put("node1", 150), InitialValidatorSet)),
                    // change voting power on provider again
                    VotingPowerChange("node1", 50).then(
                        // end the epoch
                        EndProviderEpoch(epochLength * Second, Set(), Set())
                    )
                    .then(
                        // deliver packet to consumer1
                        DeliverVscPacket("consumer1")
                    )
                }
            )
            .then(
                all {
                    // make sure the packet was removed from the provider
                    assert(currentState.providerState.outstandingPacketsToConsumer.get("consumer1").length() == 0),
                    // ensure the maturation time was entered on the consumer
                    assert(currentState.consumerStates.get("consumer1").maturationTimes.length() == 1),
                    // the validator set was put as the current validator set
                    assert(currentState.consumerStates.get("consumer1").chainState.currentValidatorPowers == InitialValidatorSet.put("node1", 200)),
                    // advance time on provider and consumer until unbonding period is over - ensure that the consumer and provider
                    // stay in sync relative to each other
                    // We want to make sure the steps we make are shorter the trusting period,
                    // since that would time out clients in reality.
                    4.reps(
                        i => 
                        EndAndBeginBlockForProvider(UnbondingPeriodPerChain.get("consumer1")/4, Set(), Set()).then(
                            EndAndBeginBlockForConsumer("consumer1", UnbondingPeriodPerChain.get("consumer1")/4)
                        )

                    )
                }
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
                    DeliverPacketToProvider("consumer1")
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
            EndProviderEpoch(epochLength * Second, Set(), Set())
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
            EndProviderEpoch(epochLength * Second, Set(), Set())
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
            EndProviderEpoch(epochLength * Second, Set(), Set())
        )
        .then(
            // advance time on provider by VscTimeout + 1 Second
            EndAndBeginBlockForProvider(VscTimeout + 1 * Second, Set(), Set())
        )
        .then(
            // enter the advanced time on chain
            EndAndBeginBlockForProvider(1 * Second, Set(), Set())
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


    // ===== KEY ASSIGNMENT =======
    action stepKeyAssignment = 
        any {
            step,
            nondetKeyAssignment,
        }

    action nondetKeyAssignment = 
        all {
            runningConsumers.size() > 0,
            nonJailedNodes(currentState.providerState).size() > 0,
            nondet node = oneOf(nonJailedNodes(currentState.providerState))
            nondet consumerAddr = oneOf(consumerAddresses)
            nondet consumer = oneOf(runningConsumers)
            KeyAssignment(consumer, node, consumerAddr),
        }

    action KeyAssignment(
        chain: Chain,
        validator: Node,
        consumerAddr: ConsumerAddr
    ): bool =
        val result = assignConsumerKey(currentState, chain, validator, consumerAddr)
        all {
            hasError(result) == false,
            currentState' = result.newState,
            trace' = trace.append(
                {...emptyAction,
                kind: "KeyAssignment",
                consumerChain: chain,
                validator: validator,
                consumerAddr: consumerAddr
                }
            ),
            params' = params,
        }

    // Make the consumer send a slash request for the given node
    // (which must be the nodes address on the consumer)
    // and a given validator set id, which indicates during which
    // time period the infraction occurred.
    action ConsumerInitiatedSlashDet(
        consumer: Chain,
        consumerNode: Node,
        vscId: VscId,
        isDowntime: bool
    ): bool = {
        val result = sendSlashRequest(currentState, consumer, consumerNode, vscId, isDowntime)
        all {
            hasError(result) == false,
            currentState' = result.newState,
            trace' = trace.append(
                {...emptyAction,
                kind: "ConsumerInitiatedSlash",
                consumerChain: consumer,
                validator: consumerNode,
                vscId: vscId,
                isDowntime: isDowntime
                }
            ),
            params' = params,
        }
    }

    // Nondeterministic version of consumer initiated slashing,
    // which first chooses sensible arguments, and then invokes the deterministic version.
    action ConsumerInitiatedSlash(): bool = {
        all {
            runningConsumers.size() > 0,
            // pick a running consumer to slash from
            nondet consumer = oneOf(runningConsumers)
            // we want to be able to slash for past infractions,
            // and we need both the validator address and the
            // vsc id of the packet to send to the provider
            // pick a validator to slash...
            val consumerState = currentState.consumerStates.get(consumer)
            // ...by getting all received vsc packets...
            val rcvdVscPackets = consumerState.receivedVscPackets
            all {
                rcvdVscPackets.length() > 0,
                // ...picking one of the packets...
                nondet packet = oneOf(rcvdVscPackets.toSet())
                val vscId = packet.id
                val valSet = packet.validatorSet.keys()
                // ...and picking one of the validators with non-zero power in the packet
                nondet validator = oneOf(valSet.filter(node => packet.validatorSet.get(node) > 0))
                // finally, choose whether to slash for downtime or double-signing
                nondet isDowntime = oneOf(Set(true, false))
                // then we can invoke the deterministic slash
                ConsumerInitiatedSlashDet(consumer, validator, vscId, isDowntime)
            }
        }
    }

    // invariants for key assignment - some invariants are in addition, some need to be adjusted from the original model

    // Every validator set on any consumer chain MUST either be or have been 
    // a validator set on the provider chain, under the key assignment at the time.
    val providerKeyAssignedValSetHistory = currentState.providerState.keyAssignedValSetHistory

    val ValidatorSetHasExistedKeyAssignmentInv =
        runningConsumers.forall(chain => // for every running consumer
            currentState.consumerStates.get(chain).chainState.votingPowerHistory.toSet().forall(
                // for every validator set the consumer ever had
                validatorSet => providerKeyAssignedValSetHistory.getOrElse(chain, List()).toSet().exists(
                    // that validator set needs to also have existed on the provider
                    provValSet => removeZeroPowers(provValSet) == removeZeroPowers(validatorSet)
                )
            )
        )

    // Any update in the power of a validator on the provider
    // MUST be present in a ValidatorSetChangePacket that is sent to all registered consumer chains,
    // and the key assignment of each validator should be applied in that VSCPacket.
    val ValidatorUpdatesArePropagatedKeyAssignmentInv = 
        // when the provider has just entered a validator set into a block...
        ValUpdatePrecondition and CurrentBlockEndsEpoch
            implies
        val providerValSetInCurBlock = providerValidatorHistory.head()
        // ... for each consumer that is running then ...
        val providerState = currentState.providerState
        currentState.providerState.consumersWithPowerChangesInThisEpoch.forall(
            // ...the validator set under key assignment is in a sent packet...
            consumer => providerState.sentVscPacketsToConsumer.get(consumer).toSet().exists(
                packet => 
                    packet.validatorSet == 
                    applyKeyAssignmentToValSet(providerState, consumer, providerValSetInCurBlock)
            )
        )

    // Every consumer chain receives the same sequence of 
    // ValidatorSetChangePackets in the same order.
    // NOTE: since not all consumer chains are running all the time,
    // we need a slightly weaker invariant:
    // For consumer chains c1, c2, if both c1 and c2 received a packet p1 sent at t1 and a packet p2 sent at t2,
    // then both have received ALL packets that were sent between t1 and t2.
    val SameVscPacketsKeyAssignmentInv =
        runningConsumers.forall(
            consumer1 => runningConsumers.forall(
                consumer2 => {
                    val packets1 = currentState.consumerStates.get(consumer1).receivedVscPackets
                    val packets2 = currentState.consumerStates.get(consumer2).receivedVscPackets
                    val commonPackets = packets1.toSet().intersect(packets2.toSet())
                    if (commonPackets.size() == 0) {
                        true // they don't share any packets, so nothing to check
                    } else {
                        val newestCommonPacket = newest(commonPackets)
                        val oldestCommonPacket = oldest(commonPackets)
                        // get all packets sent between the oldest and newest common packet
                        val packetsBetween1 = packets1.select(
                            packet => packet.sendingTime >= oldestCommonPacket.sendingTime and packet.sendingTime <= newestCommonPacket.sendingTime
                        )
                        val packetsBetween2 = packets2.select(
                            packet => packet.sendingTime >= oldestCommonPacket.sendingTime and packet.sendingTime <= newestCommonPacket.sendingTime
                        )
                        
                        // revert key assignments
                        val packetsBetween1noKeyAssignment = packetsBetween1.foldl(
                            List(),
                            (acc, packet) => 
                            acc.concat(List({...packet,
                                validatorSet: revertKeyAssignment(
                                    currentState.providerState.keyAssignmentsForVSCPackets
                                        .getOrElse(packet.id, Map())
                                        .getOrElse(consumer1, Map()),
                                    packet.validatorSet)
                            }))
                        )

                        val packetsBetween2noKeyAssignment = packetsBetween2.foldl(
                            List(), (acc, packet) => 
                            acc.concat(List({...packet,
                                validatorSet: revertKeyAssignment(
                                    currentState.providerState.keyAssignmentsForVSCPackets
                                        .getOrElse(packet.id, Map())
                                        .getOrElse(consumer2, Map()),
                                    packet.validatorSet)
                            }))
                        )
                        // check that the packets between the common packets are equal
                        // when key assignment is reversed
                        packetsBetween1noKeyAssignment == packetsBetween2noKeyAssignment
                    }
                }
            )
        )


    // Rules for key assignment:
    val KeyAssignmentRulesInv =
        NoProviderReuse and NoDuplicationOnSameConsumer
    
    // validator A cannot assign consumer key K to consumer chain X if there is already a validator B (B!=A) using K on the provider
    val NoProviderReuse = 
        consumerChains.forall(
            consumer =>
            val valConsPk = currentState.providerState.validatorToConsumerAddr.getOrElse(consumer, Map())
            valConsPk.keys().forall(
                node =>
                    val consAddr = valConsPk.get(node)
                    // either the key is the nodes key itself (B == A)
                    consAddr == node or
                    // or the consAddr must not be a validator on the provider
                    not(currentState.providerState.chainState.currentValidatorPowers.keys().contains(consAddr))
            )
        )

    // validator A cannot assign consumer key K to consumer chain X if there is already a validator B using K on X
    val NoDuplicationOnSameConsumer =
        consumerChains.forall(
            consumer => 
            val valConsPk = currentState.providerState.validatorToConsumerAddr.getOrElse(consumer, Map())
            valConsPk.keys().forall(
                node =>
                    val consAddr = valConsPk.get(node)
                    // no other node may use consAddr
                    not(valConsPk.keys().exists(
                        otherNode => otherNode != node and valConsPk.get(otherNode) == consAddr
                    ))
            )
        )

    // sanity checks
    val CanAssignConsumerKey =
        not(consumerChains.exists(
            consumer => 
                currentState.providerState.consumerAddrToValidator.getOrElse(consumer, Map()).keys().size() > 0
        ))

    val CanHaveConsumerAddresses =
        not(consumerChains.exists(
            consumer => 
                currentState.consumerStates.get(consumer).chainState.currentValidatorPowers.keys().exists(
                    addr => addr.in(consumerAddresses)
                )
        ))

    // == tests for key assignment ==
    run KeyAssignmentTest =
        init
        .then(
            // start all consumer chains
            EndAndBeginBlockForProvider(1 * Second, consumerChains, Set())
        )
        .then(
            // node 1 assigns a key on consumer1
            KeyAssignment("consumer1", "node1", "consAddr1")
        )
        .then(
            // end and begin block to make sure the key assignment is processed and the packet is sent
            EndProviderEpoch(epochLength * Second, Set(), Set())
        )
        .then(
            // receive the packet on the consumer
            DeliverVscPacket("consumer1")
        )
        .then(
            // end and begin block to make sure the packet is processed
            EndAndBeginBlockForConsumer("consumer1", 1 * Second)
        )
        .then(
            all {
                // the key should be present in the valset on the consumer, and the node itself should not
                assert(currentState.consumerStates.get("consumer1").chainState.currentValidatorPowers.getOrElse("node1", 0) == 0),
                assert(currentState.consumerStates.get("consumer1").chainState.currentValidatorPowers.get("consAddr1") == 100),
                // try some key assignments that should fail/succeed without committing to state
                val res = assignConsumerKey(currentState, "consumer1", "node1", "consAddr1")
                // fail - key already assigned (even if it is the same node)
                assert(hasError(res)),
                val res2 = assignConsumerKey(currentState, "consumer1", "node2", "consAddr1")
                // fail - key assigned to other node
                assert(hasError(res2)),
                val res3 = assignConsumerKey(currentState, "consumer2", "node2", "consAddr1")
                //  ok - may reuse the key on a different consumer
                assert(not(hasError(res3))),
                val res4 = assignConsumerKey(currentState, "consumer1", "node2", "node1")
                // fail - may not reuse a provider key of a different val
                assert(hasError(res4)),
                val res5 = assignConsumerKey(currentState, "consumer1", "node1", "consAddr2")
                // ok - assigning unused key to node
                assert(not(hasError(res5))),
                val res6 = assignConsumerKey(currentState, "consumer1", "node1", "node1")
                // ok - going back to original key
                assert(not(hasError(res6))),
                // mature the vsc packet on the consumer
                EndAndBeginBlockForConsumer("consumer1", unbondingPeriods.get("consumer1") + 1 * Hour)
            }
        )
        .then(
            // End a block to send the maturation
            EndAndBeginBlockForConsumer("consumer1", 1 * Second)
        )
        .then(
            // deliver the vsc matured packet to the provider
            DeliverPacketToProvider("consumer1")
        )
        .then(
            // the old key should have been pruned
            all {
                // check that pruning has been performed nicely
                assert(currentState.providerState.consumerAddrToValidator.get("consumer1").get("consAddr1") == "node1"),
                assert(currentState.providerState.consumerAddrsToPrune.get("consumer1").getOrElse(0, List()).length() == 0),
                // action does not matter
                VotingPowerChange("node1", 50)
            }
        )

    run KeyAssignmentInvTest =
        init.then(
            KeyAssignment("consumer3", "node3", "consAddr6")
        ).then(
            VotingPowerChange("node1", 50)
        )
        .then(
            EndAndBeginBlockForProvider(1 * Second, Set("consumer1", "consumer2"), Set())
        ).then(
            all {
                ValidatorSetHasExistedKeyAssignmentInv,
                // action doesn't matter
                VotingPowerChange("node1", 50)
            }
        )

    // ======= tests for consumer initiated slashing =======

    run DowntimeSlashTest = 
        init.then(
            // start all consumer chains
            EndAndBeginBlockForProvider(1 * Second, consumerChains, Set())
        ).then(
            // change voting power
            VotingPowerChange("node1", 50)
        ).then(
            // end a block on the provider
            EndProviderEpoch(3 * Second, Set(), Set())
        ).then(
            val vscId = currentState.providerState.sentVscPacketsToConsumer.get("consumer1").head().id
            // deliver the vsc packet to consumer1
            DeliverVscPacket("consumer1").then(
                // end a block on consumer 1
                EndAndBeginBlockForConsumer("consumer1", 1 * Second)
            ).then(
                // slash for downtime on consumer1
                ConsumerInitiatedSlashDet("consumer1", "node1", vscId, true)
            ).then(
                // end a block on the consumer
                EndAndBeginBlockForConsumer("consumer1", 1 * Second)
            )
            .then(
                // deliver the slash request to the provider
                DeliverPacketToProvider("consumer1")
            )
            .then(
                // the provider should have jailed node1
                all {
                    assert(currentState.providerState.chainState.jailedUntil.keys().contains("node1")),
                    // action does not matter
                    VotingPowerChange("node1", 50)
                }
            )
        )

    run SlashValSetInvTest = 
        init
        .then(
            // start consumer 3
            EndAndBeginBlockForProvider(1 * Second, Set("consumer3"), Set())
        )
        .then(
            // change voting power for node 3 by 50
            VotingPowerChange("node3", 50)
        )
        .then(
            // start consumer 2
            EndProviderEpoch(3 * Second, Set("consumer2"), Set())
        )
        .then(
            // deliver a vsc packet to consumer 3
            DeliverVscPacket("consumer3")
        )
        .then(
            // consumer 3 slashes validator 1
            ConsumerInitiatedSlashDet("consumer3", "node3", 0, true )
        )
        .then(
            // end and begin a block for consumer 3
            EndAndBeginBlockForConsumer("consumer3", 1 * Second)
        )
        .then(
            // deliver the slash request to the provider
            DeliverPacketToProvider("consumer3")
        )
        .then(
            // start consumer 1
            EndAndBeginBlockForProvider(1 * Second, Set("consumer1"), Set())
        )
        .then(
            all {
                assert(ValidatorSetHasExistedInv),
                // action does not matter
                VotingPowerChange("node1", 50)
            }
        )
        
    run SlashValSetKeyAssignmentTest =
        init
        .then(
            // start consumer 2
            EndAndBeginBlockForProvider(1 * Second, Set("consumer2"), Set())
        )
        .then(
            // change vp of node 10 by -50
            VotingPowerChange("node10", -50)
        )
        .then(
            // end and begin a block on the provider
            EndProviderEpoch(3 * Second, Set(), Set())
        )
        .then(
            // deliver the vsc packet to consumer 2
            DeliverVscPacket("consumer2")
        )
        .then(
            // consumer 2 slashes validator 9
            ConsumerInitiatedSlashDet("consumer2", "node9", 0, true )
        )
        .then(
            // end and begin a block for consumer 2
            EndAndBeginBlockForConsumer("consumer2", 1 * Second)
        )
        .then(
            // deliver the slash request to the provider
            DeliverPacketToProvider("consumer2")
        )
        .then(
            // end and begin a block on the provider, starting consumer 3
            EndAndBeginBlockForProvider(1 * Second, Set("consumer3"), Set())
        )
        .then(
            // check the ValidatorSetHasExistedKeyAssignmentInv
            all {
                assert(ValidatorSetHasExistedKeyAssignmentInv),
                // action does not matter
                VotingPowerChange("node1", 50)
            }
        )

    run SlashAckTest = 
        init
        .then(
            // start consumer 1
            EndAndBeginBlockForProvider(1 * Second, Set("consumer1"), Set())
        )
        .then(
            // change voting power for node 1 by 50
            VotingPowerChange("node1", 50)
        )
        .then(
            // end and begin a block on the provider
            EndProviderEpoch(3 * Second, Set(), Set())
        )
        .then(
            // deliver the vsc packet to consumer 1
            DeliverVscPacket("consumer1")
        )
        .then(
            // initiate a slash for downtime
            ConsumerInitiatedSlashDet("consumer1", "node1", 0, true)
        )
        .then(
            // end and begin a block for consumer 1 to send the packet
            EndAndBeginBlockForConsumer("consumer1", 1 * Second)
        )
        .then(
            all {
                assert(currentState.consumerStates.get("consumer1").outstandingPacketsToProvider.length() == 1),
                assert(currentState.consumerStates.get("consumer1").waitingForSlashPacketAck.size() == 1),
                // deliver the slash request to the provider
                DeliverPacketToProvider("consumer1")
            }
        )
}