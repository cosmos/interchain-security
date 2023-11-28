module ccv_happy {
    import ccv_model.* from "ccv_model"
    import ccv_types as ccvt from "ccv"
    import ccv from "ccv"
    import Time.* from "./libraries/Time"
    import extraSpells.* from "./libraries/extraSpells"


    // The boundeddrift module has its own step function.
    // They ensure that chains do not drift from each other in terms of time
    // more than a given bound.
    // It differs from the sync module in that it does not require
    // the chains to produce blocks at the same time.

    // The maximal drift that this module will allow between chains.
    // In particular, it will ensure that the lastTime of any chain
    // does not differ from the runningTime of any other chain by more than
    // this value.
    pure val maxDrift = defUnbondingPeriod - 2 * Hour

    // Finds the maximal time advancement that can be done for a given chain
    // without violating the maxDrift constraint.
    pure def findMaxTimeAdvancement(advancingChain: ccvt::ChainState, otherChains: Set[ccvt::ChainState]): Time =
        val otherChainsLastTimes = otherChains.map(c => c.lastTimestamp)
        0
        // // start with advancingChain.RunningTime - if this is the minimal element, we can advance by maxDrift anyways
        // val otherChainsMinLastTime = otherChainsLastTimes.fold(advancingChain.runningTimestamp, (acc, t) => if (acc < t) acc else t)
        // val maxTime = advancingChain.runningTimestamp - otherChainsMinLastTime + maxDrift

    // step will advance time for all chains at the same rate,
    // thus the clock times are always in sync.
    // This is useful to test happy paths.
    action stepBoundedDrift = any {
        step_common, // allow actions that do not influence time

        all {
            // advance a block for a consumer
            all {
            runningConsumers.size() > 0, // ensure there is a running consumer, otherwise this action does not make sense
            nondet chain = oneOf(runningConsumers)
            nondet timeAdvancement = oneOf(timeAdvancements)
            EndAndBeginBlockForConsumer(chain, timeAdvancement),
            },

            // advance a block for the provider
            val consumerStatus = currentState.providerState.consumerStatus
            nondet consumersToStart = oneOf(nonConsumers.powerset())
            nondet consumersToStop = oneOf(runningConsumers.powerset())
            nondet timeAdvancement = oneOf(timeAdvancements)
            EndAndBeginBlockForProvider(timeAdvancement, consumersToStart, consumersToStop),
        }
    }
}