module ccv_boundeddrift {
    import ccv_model.* from "ccv_model"
    import ccv_types as Ccvt from "ccv"
    import ccv_utils.* from "ccv_utils"
    import ccv from "ccv"
    import Time.* from "./libraries/Time"
    import extraSpells.* from "./libraries/extraSpells"
    import ccv_pss_model.* from "ccv_pss_model"


    // The boundeddrift module has its own step function.
    // They ensure that chains do not drift from each other in terms of time
    // more than a given bound.
    // It differs from the sync module in that it does not require
    // the chains to produce blocks at the same time.

    // The maximal drift that this module will allow between chains.
    // In particular, it will ensure that the lastTime of any chain
    // does not differ from the runningTime of any other chain by more than
    // this value.
    // We choose unbondingPeriod - 2 * Hour here, because we want this to be less than the trustingPeriod,
    // which is currently defined as unbondingPeriod - 1 * Hour
    pure val maxDrift = defUnbondingPeriod - 2 * Hour

    // The chance, in percentage points, that we will stop consumer chains, whenever we begin a block on the provider chain.
    pure val consumerStopChance = 2

    pure def findMaxTimeAdvancement(advancingChain: Ccvt::ChainState, otherChains: Set[Ccvt::ChainState], maximalDrift: Time): Time =
        val otherChainsLastTimes = otherChains.map(c => c.lastTimestamp)
        // start with advancingChain.RunningTime - if this is the minimal element, we can advance by maxDrift anyways
        val otherChainsMinLastTime = otherChainsLastTimes.fold(advancingChain.runningTimestamp, (acc, t) => if (acc < t) acc else t)
        val maxTime = otherChainsMinLastTime - advancingChain.runningTimestamp + maximalDrift
        maxTime

    // Given the name of a chain, gets a set with the chain states of all other chains.
    def GetOtherChainStates(advancingChain: Ccvt::Chain): Set[Ccvt::ChainState] =
        val runCons = getRunningConsumers(currentState.providerState)
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

    def GetRunningChainStates(): Set[Ccvt::ChainState] = 
        val runCons = getRunningConsumers(currentState.providerState)
        val consumerChainStates = runCons.map(c => currentState.consumerStates.get(c).chainState)
        consumerChainStates.union(Set(currentState.providerState.chainState))

    // step will advance time for all chains at the same rate,
    // thus the clock times are always in sync.
    // This is useful to test happy paths.
    action stepBoundedDrift = any {
        stepCommon, // allow actions that do not influence time

        // advance a block for a consumer
        stepBoundedDriftConsumer,
        
        // advance a block for the provider
        stepBoundedDriftProvider
    }

    action stepBoundedDriftProvider: bool = {
        stepBoundedDriftProvider_helper(allFullConsumers)
    }

    action stepBoundedDriftProviderPSS: bool = {
        stepBoundedDriftProvider_helper(variousPossibleTopN)
    }

    // As an argument, takes a function that, when invoked, gives a top N value to use for a new consumer chain.
    action stepBoundedDriftProvider_helper(topNOracle: Set[int]): bool = {
        val maxAdv = findMaxTimeAdvancement(GetChainState(Ccvt::PROVIDER_CHAIN), GetOtherChainStates(Ccvt::PROVIDER_CHAIN), maxDrift)
        val possibleAdvancements = timeAdvancements.filter(t => t <= maxAdv)
        all {
            possibleAdvancements.size() > 0, // ensure there is a possible advancement, otherwise this action does not make sense
            // advance a block for the provider
            val consumerStatus = currentState.providerState.consumerStatus
            nondet consumersToStart = oneOf(nonConsumers.powerset())
            nondet topN = oneOf(topNOracle)
            nondet consumerAdditions = consumersToStart.map(c => Ccvt::NewTopNConsumer(c, topN))
            // make it so we stop consumers only with small likelihood:
            nondet stopConsumersRand = oneOf(1.to(100))
            nondet consumersToStop = if (stopConsumersRand <= consumerStopChance) oneOf(runningConsumers.powerset()) else Set()
            nondet timeAdvancement = oneOf(possibleAdvancements)
            EndAndBeginBlockForProvider(timeAdvancement, consumerAdditions, consumersToStop),
        }
    }

    action stepBoundedDriftConsumer = all {
        runningConsumers.size() > 0, // ensure there is a running consumer, otherwise this action does not make sense
            nondet chain = runningConsumers.oneOf()
            val maxAdv = findMaxTimeAdvancement(GetChainState(chain), GetOtherChainStates(chain), maxDrift)
            val possibleAdvancements = timeAdvancements.filter(t => t <= maxAdv)
            all {
                possibleAdvancements.size() > 0, // ensure there is a possible advancement, otherwise this action does not make sense
                nondet timeAdvancement = possibleAdvancements.oneOf()
                EndAndBeginBlockForConsumer(chain, timeAdvancement),
            }
    }

    action stepBoundedDriftKeyAssignment = any {
        stepBoundedDrift,
        nondetKeyAssignment,
    }

    action stepBoundedDriftKeyAndPSS = any {
        stepCommon,
        stepBoundedDriftProviderPSS,
        stepBoundedDriftConsumer,
        nondetKeyAssignment,
        StepOptIn,
        StepOptOut,
        
        // advance a block for the provider
        val maxAdv = findMaxTimeAdvancement(GetChainState(Ccvt::PROVIDER_CHAIN), GetOtherChainStates(Ccvt::PROVIDER_CHAIN), maxDrift)
        val possibleAdvancements = timeAdvancements.filter(t => t <= maxAdv)
        all {
            possibleAdvancements.size() > 0, // ensure there is a possible advancement, otherwise this action does not make sense
            // advance a block for the provider
            val consumerStatus = currentState.providerState.consumerStatus
            nondet consumersToStart = oneOf(nonConsumers.powerset())
            // make it so we stop consumers only with small likelihood:
            nondet stopConsumersRand = oneOf(1.to(100))
            nondet consumersToStop = if (stopConsumersRand <= consumerStopChance) oneOf(runningConsumers.powerset()) else Set()
            nondet timeAdvancement = oneOf(possibleAdvancements)
            EndAndBeginBlockForProvider(timeAdvancement, consumersToStart, consumersToStop),
        }
    }
    
    // INVARIANT
    // The maxDrift between chains is never exceeded.
    // This *should* be ensured by the step function.
    val BoundedDriftInv = 
        GetRunningChainStates.forall(
            chain1 => GetRunningChainStates.forall(
                chain2 => abs(chain1.runningTimestamp - chain2.lastTimestamp) <= maxDrift
            )
        )
}