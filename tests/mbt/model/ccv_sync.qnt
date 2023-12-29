module ccv_sync {
    import ccv_model.* from "ccv_model"
    import ccv_types as ccvt from "ccv"
    import ccv from "ccv"
    import Time.* from "./libraries/Time"
    import extraSpells.* from "./libraries/extraSpells"


    // The sync module has its own init and step functions.
    // They ensure that chains do not drift from each other in terms of time,
    // and all chains produce blocks synchronously.
    // To do so, it makes use of
    // "action scheduling", essentially using a variable to
    // determine the next action to be taken.

    // QueuedChainsToEndBlock contains a list of chains which will end their blocks next,
    // together with the time advancement they should advance by.
    // When stepSync selects an action, it checks if there are any chains in this list,
    // and if so, it will only select actions that end blocks on the head of the list.
    // QueuedChainsToEndBlock is thus used to schedule actions.
    var QueuedChainsToEndBlock: List[(ccvt::Chain, Time)]

    // runs init, then ends and begins a block for each chain, while also starting all consumers.
    // necessary because we want the happy path to have all consumer chains started.
    action initSync =
        all {
            init.then(
                EndAndBeginBlockForProvider(1 * Second, consumerChains, Set())
            ),
            QueuedChainsToEndBlock' = consumerChainList.foldl(
                List(),
                (acc, consumer) => acc.append((consumer, 1 * Second))
            ),
        }



    // step will advance time for all chains at the same rate,
    // thus the clock times are always in sync.
    // This is useful to test happy paths.
    action stepSync = any { // choose any of the three "all" blocks
        nondet timeAdvancement = oneOf(timeAdvancements)
        all {
            QueuedChainsToEndBlock.length() == 0, // no queued action needs to be taken
            EndAndBeginBlockForProvider(timeAdvancement, Set(), Set()), // end a block for the provider
            QueuedChainsToEndBlock' = consumerChainList.foldl( // queue all consumers to end a block
                List(),
                (acc, consumer) => acc.append((consumer, timeAdvancement))
            ),
        },

        all {
            QueuedChainsToEndBlock.length() > 0, // there is a consumer that needs to end a block next
            val pair = QueuedChainsToEndBlock.head()
            val chain = pair._1
            val timeAdv = pair._2
            EndAndBeginBlockForConsumer(chain, timeAdv), // end a block for that consumer
            QueuedChainsToEndBlock' = QueuedChainsToEndBlock.tail(), // remove that consumer from the queue
        },

        all { 
            QueuedChainsToEndBlock.length() == 0, // no action is queued
            stepCommon, // do one of the actions that are NOT ending a block, like delivering packets, voting power changes, ...
            QueuedChainsToEndBlock' = QueuedChainsToEndBlock,
        }
    }
}