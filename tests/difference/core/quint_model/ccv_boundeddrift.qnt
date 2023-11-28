module ccv_happy {
    import ccv_model.* from "ccv_model"
    import ccv_types as Ccvt from "ccv"
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

    pure def findMaxTimeAdvancement(advancingChain: Ccvt::ChainState, otherChains: Set[Ccvt::ChainState], maximalDrift: Time): Time =
        val otherChainsLastTimes = otherChains.map(c => c.lastTimestamp)
        // start with advancingChain.RunningTime - if this is the minimal element, we can advance by maxDrift anyways
        val otherChainsMinLastTime = otherChainsLastTimes.fold(advancingChain.runningTimestamp, (acc, t) => if (acc < t) acc else t)
        val maxTime = advancingChain.runningTimestamp - otherChainsMinLastTime + maximalDrift
        maxTime

    // Given the name of a chain, gets a set with the chain states of all other chains.
    def GetOtherChainStates(advancingChain: Ccvt::Chain): Set[Ccvt::ChainState] =
        val runCons = ccv::getRunningConsumers(currentState.providerState)
        if (advancingChain == Ccvt::PROVIDER_CHAIN) {
            runCons.map(c => currentState.consumerStates.get(c).chainState)
        } else {
            val consumerChainStates = runCons.filter(c => c != advancingChain).map(c => currentState.consumerStates.get(c).chainState)
            consumerChainStates.union(Set(currentState.providerState.chainState))
        }

    def GetChainState(advancingChain: Ccvt::Chain): Ccvt::ChainState =
        if (advancingChain == Ccvt::PROVIDER_CHAIN) {
            currentState.providerState.chainState
        } else {
            currentState.consumerStates.get(advancingChain).chainState
        }

    def GetChainStates(): Set[Ccvt::ChainState] = 
        val runCons = ccv::getRunningConsumers(currentState.providerState)
        val consumerChainStates = runCons.map(c => currentState.consumerStates.get(c).chainState)
        consumerChainStates.union(Set(currentState.providerState.chainState))

    // step will advance time for all chains at the same rate,
    // thus the clock times are always in sync.
    // This is useful to test happy paths.
    action stepBoundedDrift = any {
        step_common, // allow actions that do not influence time

        // advance a block for a consumer
        all {
        runningConsumers.size() > 0, // ensure there is a running consumer, otherwise this action does not make sense
        nondet chain = oneOf(runningConsumers)
        val maxTimeAdvancement = findMaxTimeAdvancement(GetChainState(chain), GetOtherChainStates(chain), maxDrift)
        nondet timeAdvancement = oneOf(timeAdvancements.filter(t => t <= maxTimeAdvancement))
        EndAndBeginBlockForConsumer(chain, timeAdvancement),
        },

        // advance a block for the provider
        val consumerStatus = currentState.providerState.consumerStatus
        nondet consumersToStart = oneOf(nonConsumers.powerset())
        nondet consumersToStop = oneOf(runningConsumers.powerset())
        val maxTimeAdvancement = findMaxTimeAdvancement(GetChainState(Ccvt::PROVIDER_CHAIN), GetOtherChainStates(Ccvt::PROVIDER_CHAIN), maxDrift)
        nondet timeAdvancement = oneOf(timeAdvancements.filter(t => t <= maxTimeAdvancement))
        EndAndBeginBlockForProvider(timeAdvancement, consumersToStart, consumersToStop),
    }

    // INVARIANT
    // The maxDrift between chains is never exceeded.
    // This *should* be ensured by the step function.
    val BoundedDriftInv = 
        GetChainStates.forall(
            chain1 => GetChainStates.forall(
                chain2 => chain1.runningTimestamp - chain2.lastTimestamp <= maxDrift
            )
        )
}