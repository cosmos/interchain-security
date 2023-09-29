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
    var lastAction: str

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
        lastAction' = "init"
    }

    action VotingPowerChange(validator: Node, newVotingPower: int): bool = 
        val result = votingPowerChange(currentState, validator, newVotingPower)
        all {
            result.hasError == false,
            currentState' = result.newState,
            lastAction' = "VotingPowerChange"
        }

    // The receiver receives the next outstanding VSCPacket from the provider.
    // This will time out the consumer if the packet timeout has passed on the receiver.
    action DeliverVSCPacket(receiver: Chain): bool = 
        val resultAndTimeout = deliverPacketToConsumer(currentState, receiver)
        val result = resultAndTimeout._1
        all {
            result.hasError == false,
            currentState' = result.newState,
            lastAction' = "DeliverVSCPacket"
        }

    // The provider receives the next outstanding VSCMaturedPacket from the sender.
    // This will time out the consumer if the packet timeout has passed on the provider.
    action DeliverVSCMaturedPacket(sender: Chain): bool =
        val resultAndTimeout = deliverPacketToProvider(currentState, sender)
        val result = resultAndTimeout._1
        all {
            result.hasError == false,
            currentState' = result.newState,
            lastAction' = "DeliverVSCMaturedPacket"
        }

    action EndAndBeginBlockForProvider(
        timeAdvancement: Time,
        consumersToStart: Set[Chain],
        consumersToStop: Set[Chain]): bool = 
        val result = endAndBeginBlockForProvider(currentState, timeAdvancement, consumersToStart, consumersToStop)
        all {
            result.hasError == false,
            currentState' = result.newState,
            lastAction' = "EndAndBeginBlockForProvider"
        }

    action EndAndBeginBlockForConsumer(
        chain: Chain,
        timeAdvancement: Time): bool = 
        val result = endAndBeginBlockForConsumer(currentState, chain, timeAdvancement)
        all {
            result.hasError == false,
            currentState' = result.newState,
            lastAction' = "EndAndBeginBlockForConsumer"
        }

    // a few different values for time advancements.
    // to keep the number of possible steps small, we only have a few different values.
    // Roughly, 1s for very small advances (like between blocks),
    // and then longer values for increasingly severe downtime scenarios.
    // Note that these can still be combined, so in effect we can get all time advancements by any amount of seconds.
    pure val timeAdvancements = Set(1 * Second, 1 * Day, 1 * Week, 4 * Week)

    action step = any {
        nondet node = oneOf(nodes)
        // very restricted set of voting powers. exact values are not important,
        // and this keeps the state space smaller.
        // 0 for getting a validator out of the validator set, and two non-zero values
        nondet newVotingPower = oneOf(Set(0, 50, 100))
        VotingPowerChange(node, newVotingPower),

        nondet chain = oneOf(consumerChains)
        // a few different values for time advancements.
        // to keep the number of possible steps small, we only have a few different values.
        // Roughly, 1s for very small advances (like between blocks),
        // and then longer values for increasingly severe downtime scenarios.
        // Note that these can still be combined, so in effect we can get all time advancements by any amount of seconds.
        nondet timeAdvancement = oneOf(timeAdvancements)
        EndAndBeginBlockForConsumer(chain, timeAdvancement),

        val consumerStatus = currentState.providerState.consumerStatus
        nondet consumersToStart = oneOf(runningConsumers.powerset())
        nondet consumersToStop = oneOf(unusedConsumers.powerset())
        nondet timeAdvancement = oneOf(timeAdvancements)
        EndAndBeginBlockForProvider(timeAdvancement, consumersToStart, consumersToStop),

        // 
        // try to send a packet. we could filter by chains that can actually send,
        // but it's probably not much faster than just trying and failing.
        nondet sender = oneOf(consumerChains)
        DeliverVSCMaturedPacket(sender),

        // again, we could filter by chains that can actually receive,
        // but it's probably not much faster than just trying and failing.
        nondet recciver = oneOf(consumerChains)
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
        if (lastAction == "EndAndBeginBlockForProvider") {
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
                        // get oldest common packet
                        val oldestCommonPacket = commonPackets.MinBy(packet => packet.sendingTime, packets1.head())
                        false
                    }
                }
            )
        )

        


//     \* Invariants from https://github.com/cosmos/interchain-security/blob/main/docs/quality_assurance.md

// (*
// 6.03 - Every consumer chain receives the same sequence of 
// ValidatorSetChangePackets in the same order.

// Note: consider only prefixes on received packets (ccvChannelsResolved)
// *)
// Inv603 == 
//   \A c1,c2 \in LiveConsumers:
//     \A i \in (DOMAIN ccvChannelsResolved[c1] \intersect DOMAIN ccvChannelsResolved[c2]):
//       ccvChannelsResolved[c1][i] = ccvChannelsResolved[c2][i]

// (*
// 7.01 - For every ValidatorSetChangePacket received by a consumer chain at 
// time t, a MaturedVSCPacket is sent back to the provider in the first block 
// with a timestamp >= t + UnbondingPeriod

// Modification: not necessarily _first_ block with that timestamp, 
// since we don't model height _and_ time. Also, only true for ACTIVE chains.
// *)
// Inv701 ==
//   boundedDrift => MaturedBeforeTimeout

// (*
// 7.02 - If an unbonding operation resulted in a ValidatorSetChangePacket sent
// to all registered consumer chains, then it cannot complete before receiving
// matching MaturedVSCPackets from these consumer chains 
// (unless some of these consumer chains are removed)

// We can define change completion, but we don't model it. Best approximation:
// *)
// Inv702 ==
//   boundedDrift => EventuallyMatureOnProvider

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
                    lastAction' = "HappyPathTest"
                }
            )
        }
}