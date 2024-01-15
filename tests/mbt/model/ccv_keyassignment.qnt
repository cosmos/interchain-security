// -*- mode: Bluespec; -*-

// A module for a model with key assignment.
// Adds key assignment as a possible action.
// Also redefines several invariants to include key assignment.
module ccv_keyassignment {
    import ccv_model as b from "ccv_model"
    import ccv_types as Ccvt from "ccv"
    import ccv.* from "ccv"
    import Time.* from "./libraries/Time"
    import extraSpells.* from "./libraries/extraSpells"

    action step = 
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

    // == tests for key assignment ==
    
    run KeyAssignmentTest =
        b::init
        .then(
            // start all consumer chains
            b::EndAndBeginBlockForProvider(1 * Second, ConsumerChains, Set())
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
                assert(res.hasError()),
                val res2 = assignConsumerKey(b::currentState, "consumer1", "node2", "consAddr1")
                // fail - key assigned to other node
                assert(res2.hasError()),
                val res3 = assignConsumerKey(b::currentState, "consumer2", "node2", "consAddr1")
                //  ok - may reuse the key on a different consumer
                assert(not(res3.hasError())),
                val res4 = assignConsumerKey(b::currentState, "consumer1", "node2", "node1")
                // fail - may not reuse a provider key of a different val
                assert(res4.hasError()),
                val res5 = assignConsumerKey(b::currentState, "consumer1", "node1", "consAddr2")
                // ok - assigning unused key to node
                assert(not(res5.hasError())),
                val res6 = assignConsumerKey(b::currentState, "consumer1", "node1", "node1")
                // ok - going back to original key
                assert(not(res6.hasError())),
                // mature the vsc packet on the consumer
                EndAndBeginBlockForConsumer("consumer1", UnbondingPeriodPerChain.get("consumer1") + 1 * Hour)
            }
        )
        .then(
            // End a block to send the maturation
            EndAndBeginBlockForConsumer("consumer1", 1 * Second)
        )
        .then(
            // deliver the vsc matured packet to the provider
            DeliverVscMaturedPacket("consumer1")
        )
        .then(
            // the old key should have been pruned
            all {
                // check that pruning has been performed nicely
                assert(currentState.providerState.validatorByConsumerAddr.get("consumer1").get("consAddr1") == "node1"),
                assert(currentState.providerState.consumerAddrsToPrune.get("consumer1").get(0).length() == 0),
                assert(currentState.providerState.keyAssignmentReplacements.getOrElse("consumer1", Map()).keys().size() == 0),
                // action does not matter
                VotingPowerChange("node1", 50)
            }
        )
}