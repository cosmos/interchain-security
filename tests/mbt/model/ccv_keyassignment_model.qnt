// -*- mode: Bluespec; -*-



// A module for a model with key assignment.
// Adds key assignment as a possible action.
// Also redefines several invariants to include key assignment.
module ccv_keyassignment_model {
    import ccv_model as b from "ccv_model"
    import ccv_types as Ccvt from "ccv"
    import Time.* from "./libraries/Time"
    import extraSpells.* from "./libraries/extraSpells"
    import ccv_keyassignment.* from "ccv_keyassignment"

    action stepKeyAssignment = 
        any {
            b::step,

            all {
                // ensure there is a consumer that either
                // runs right now or can run in the future
                // (otherwise all consumers are stopped, so we don't need to assign any keys)
                b::runningConsumers.size() + b::nonConsumers.size() > 0,
                nondet consumer = oneOf(b::runningConsumers.union(b::nonConsumers))
                nondet node = oneOf(b::nodes)
                nondet address = oneOf(b::consumerAddresses)
                // do a key assignment
                KeyAssignment(consumer, node, address),
            }
        }

    action KeyAssignment(
        chain: Ccvt::Chain,
        validator: Ccvt::Node,
        consumerAddr: Ccvt::ConsumerAddr
    ): bool =
        val result = assignConsumerKey(b::currentState, chain, validator, consumerAddr)
        all {
            Ccvt::hasError(result) == false,
            b::currentState' = result.newState,
            b::trace' = b::trace.append(
                {...b::emptyAction,
                kind: "KeyAssignment",
                consumerChain: chain,
                validator: validator,
                consumerAddr: consumerAddr
                }
            ),
            b::params' = b::params,
        }

    action step_keyassignment =
        any {
            b::step,

        }

    // invariants for key assignment - some invariants are in addition, some need to be adjusted from the original model
    // Every validator set on any consumer chain MUST either be or have been 
    // a validator set on the provider chain.
    val ValidatorSetHasExistedInv =
        b::runningConsumers.forall(chain =>
            b::currentState.consumerStates.get(chain).chainState.votingPowerHistory.toSet().forall(
                validatorSet => b::providerValidatorHistory.toSet().contains(validatorSet)
            )
        )

    // Any update in the power of a validator on the provider
    // MUST be present in a ValidatorSetChangePacket that is sent to all registered consumer chains
    val ValUpdatePrecondition = b::trace[b::trace.length()-1].kind == "EndAndBeginBlockForProvider"
    val ValidatorUpdatesArePropagatedInv = 
        // when the provider has just entered a validator set into a block...
        ValUpdatePrecondition and b::currentState.providerState.providerValidatorSetChangedInThisBlock
            implies
        val providerValSetInCurBlock = b::providerValidatorHistory.head()
        // ... for each consumer that is running then ...
        b::runningConsumers.forall(
            // ...the validator set is in a sent packet...
            consumer => b::currentState.providerState.sentVscPacketsToConsumer.get(consumer).toSet().exists(
                packet => packet.validatorSet == providerValSetInCurBlock
            )
            // or the consumer was just started, which we detect by the consumer having a timestamp of 0
            // and the consumer having the validator set that was just sent in the block
            or 
            (b::currentState.consumerStates.get(consumer).chainState.lastTimestamp == 0 and b::currentState.consumerStates.get(consumer).chainState.currentValidatorSet == providerValSetInCurBlock)
        )

    // Every consumer chain receives the same sequence of 
    // ValidatorSetChangePackets in the same order.
    // NOTE: since not all consumer chains are running all the time,
    // we need a slightly weaker invariant:
    // For consumer chains c1, c2, if both c1 and c2 received a packet p1 sent at t1 and a packet p2 sent at t2,
    // then both have received ALL packets that were sent between t1 and t2.
    val SameVscPacketsInv =
        b::runningConsumers.forall(
            consumer1 => b::runningConsumers.forall(
                consumer2 => {
                    val packets1 = b::currentState.consumerStates.get(consumer1).receivedVscPackets
                    val packets2 = b::currentState.consumerStates.get(consumer2).receivedVscPackets
                    val commonPackets = packets1.toSet().intersect(packets2.toSet())
                    if (commonPackets.size() == 0) {
                        true // they don't share any packets, so nothing to check
                    } else {
                        val newestCommonPacket = b::newest(commonPackets)
                        val oldestCommonPacket = b::oldest(commonPackets)
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


    // Rules for key assignment:
    val KeyAssignmentRulesInv =
        NoProviderReuse and NoDuplicationOnSameConsumer
    
    // validator A cannot assign consumer key K to consumer chain X if there is already a validator B (B!=A) using K on the provider
    val NoProviderReuse = 
        b::consumerChains.forall(
            consumer =>
            val valConsPk = b::currentState.providerState.validatorConsumerPubKey.getOrElse(consumer, Map())
            valConsPk.keys().forall(
                node =>
                    val consAddr = valConsPk.get(node)
                    // either the key is the nodes key itself (B == A)
                    consAddr == node or
                    // or the consAddr must not be a validator on the provider
                    not(b::currentState.providerState.chainState.currentValidatorSet.keys().contains(consAddr))
            )
        )

    // validator A cannot assign consumer key K to consumer chain X if there is already a validator B using K on X
    val NoDuplicationOnSameConsumer =
        b::consumerChains.forall(
            consumer => 
            val valConsPk = b::currentState.providerState.validatorConsumerPubKey.getOrElse(consumer, Map())
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
        not(b::consumerChains.exists(
            consumer => 
                b::currentState.providerState.validatorByConsumerAddr.getOrElse(consumer, Map()).keys().size() > 0
        ))

    val CanHaveConsumerAddresses =
        not(b::consumerChains.exists(
            consumer => 
                b::currentState.consumerStates.get(consumer).chainState.currentValidatorSet.keys().exists(
                    addr => addr.in(b::consumerAddresses)
                )
        ))

    // == tests for key assignment ==
    run KeyAssignmentTest =
        b::init
        .then(
            // start all consumer chains
            b::EndAndBeginBlockForProvider(1 * Second, b::consumerChains, Set())
        )
        .then(
            // node 1 assigns a key on consumer1
            KeyAssignment("consumer1", "node1", "consAddr1")
        )
        .then(
            // end and begin block to make sure the key assignment is processed and the packet is sent
            b::EndAndBeginBlockForProvider(1 * Second, Set(), Set())
        )
        .then(
            // receive the packet on the consumer
            b::DeliverVscPacket("consumer1")
        )
        .then(
            // end and begin block to make sure the packet is processed
            b::EndAndBeginBlockForConsumer("consumer1", 1 * Second)
        )
        .then(
            all {
                // the key should be present in the valset on the consumer, and the node itself should not
                assert(b::currentState.consumerStates.get("consumer1").chainState.currentValidatorSet.get("node1") == 0),
                assert(b::currentState.consumerStates.get("consumer1").chainState.currentValidatorSet.get("consAddr1") == 100),
                // try some key assignments that should fail/succeed without comitting to state
                val res = assignConsumerKey(b::currentState, "consumer1", "node1", "consAddr1")
                // fail - key already assigned (even if it is the same node)
                assert(Ccvt::hasError(res)),
                val res2 = assignConsumerKey(b::currentState, "consumer1", "node2", "consAddr1")
                // fail - key assigned to other node
                assert(Ccvt::hasError(res2)),
                val res3 = assignConsumerKey(b::currentState, "consumer2", "node2", "consAddr1")
                //  ok - may reuse the key on a different consumer
                assert(not(Ccvt::hasError(res3))),
                val res4 = assignConsumerKey(b::currentState, "consumer1", "node2", "node1")
                // fail - may not reuse a provider key of a different val
                assert(Ccvt::hasError(res4)),
                val res5 = assignConsumerKey(b::currentState, "consumer1", "node1", "consAddr2")
                // ok - assigning unused key to node
                assert(not(Ccvt::hasError(res5))),
                val res6 = assignConsumerKey(b::currentState, "consumer1", "node1", "node1")
                // ok - going back to original key
                assert(not(Ccvt::hasError(res6))),
                // mature the vsc packet on the consumer
                b::EndAndBeginBlockForConsumer("consumer1", b::unbondingPeriods.get("consumer1") + 1 * Hour)
            }
        )
        .then(
            // End a block to send the maturation
            b::EndAndBeginBlockForConsumer("consumer1", 1 * Second)
        )
        .then(
            // deliver the vsc matured packet to the provider
            b::DeliverVscMaturedPacket("consumer1")
        )
        .then(
            // the old key should have been pruned
            all {
                // check that pruning has been performed nicely
                assert(b::currentState.providerState.validatorByConsumerAddr.get("consumer1").get("consAddr1") == "node1"),
                assert(b::currentState.providerState.consumerAddrsToPrune.get("consumer1").get(0).length() == 0),
                assert(b::currentState.providerState.keyAssignmentReplacements.getOrElse("consumer1", Map()).keys().size() == 0),
                // action does not matter
                b::VotingPowerChange("node1", 50)
            }
        )


}