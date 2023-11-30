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

    // QueuedEndBlocks contains a list of chains which will end their blocks next,
    // together with the time advancement they should advance by.
    // When stepHappy selects an action, it checks if there are any chains in this list,
    // and if so, it will only select actions that end blocks on the head of the list.
    // QueuedEndBlocks is thus used to schedule actions.
    var QueuedEndBlocks: List[(ccvt::Chain, Time)]

    // runs init, then ends and begins a block for each chain, while also starting all consumers.
    // necessary because we want the happy path to have all consumer chains started.
    action initHappy =
        all {
            init.then(
                EndAndBeginBlockForProvider(1 * Second, consumerChains, Set())
            ),
            QueuedEndBlocks' = consumerChainList.foldl(
                List(),
                (acc, consumer) => acc.append((consumer, 1 * Second))
            ),
        }



    // step will advance time for all chains at the same rate,
    // thus the clock times are always in sync.
    // This is useful to test happy paths.
    action stepHappy = any {
        nondet timeAdvancement = oneOf(timeAdvancements)
        all {
            QueuedEndBlocks.length() == 0,
            EndAndBeginBlockForProvider(timeAdvancement, Set(), Set()),
            QueuedEndBlocks' = consumerChainList.foldl(
                List(),
                (acc, consumer) => acc.append((consumer, timeAdvancement))
            ),
        },

        all {
            QueuedEndBlocks.length() > 0,
            val pair = QueuedEndBlocks.head()
            val chain = pair._1
            val timeAdv = pair._2
            EndAndBeginBlockForConsumer(chain, timeAdv),
            QueuedEndBlocks' = QueuedEndBlocks.tail(),
        },

        all {
            QueuedEndBlocks.length() == 0,
            step_common,
            QueuedEndBlocks' = QueuedEndBlocks,
        }
    }
}