// This module contains logic for PSS (Partial Set Security).
// PSS is a variant/extension of CCV that 
// allows for only a subset of the validator set
// to secure a consumer chain.
// Not all logic related to PSS is inside this module, as some logic is
// too tightly coupled with the core CCV logic,
// which is instead found in ccv.qnt
module ccv_pss {
    import ccv_types.* from "./ccv"
    import extraSpells.* from "./libraries/extraSpells"
    import ccv_utils.* from "./ccv_utils"

    // Given a base validator set, an N for a top N chain, and a set of validators that have opted in to the chain,
    // returns the validator set that should be sent to the chain.
    // Assumes that the value for N is valid.
    pure def GetPSSValidatorSet(providerState: ProviderState, origValSet: ValidatorSet, consumer: Chain): ValidatorSet = {
        pure val optedInVals = providerState.optedInVals.getOrElse(consumer, Set())
        GetPSSValidatorSet_helper(origValSet, optedInVals)
    }

    pure def GetPSSValidatorSet_helper(origValSet: ValidatorSet, optedInVals: Set[Node]): ValidatorSet = {
        origValSet.mapFilter(v => optedInVals.contains(v))
    }

    // Given a validator set and N, returns the top N% of validators by power.
    pure def GetTopNVals(origValSet: ValidatorSet, N: int): Set[Node] = {
        // == sort validators by power ==
        // define a comparator that compares validators by power
        pure def powerCompare(a: Node, b: Node): Ordering = {
            pure val powA = origValSet.get(a)
            pure val powB = origValSet.get(b)
            intCompare(powB, powA)
        }
        // get a sorted list of validators by power
        pure val sortedVals = origValSet.keys().toSortedList(powerCompare)

        // == compute the threshold of how much power the top N have ==
        pure val totalPower = origValSet.mapValuesSum()
        pure val topNPower = totalPower * N / 100
        
        // == construct the validator set by going through the sorted vals ==
        pure val res = sortedVals.foldl(
            // fold carries two values: current validator set and total power added so far
            (Set(), 0),
            (acc, validator) =>
                pure val curValSet = acc._1
                pure val accPower = acc._2
                pure val validatorPower = origValSet.get(validator)
                if (validatorPower > 0 and accPower < topNPower) {
                    // if we don't have enough power yet, add the validator to the set
                    pure val newAccPower = accPower + validatorPower
                    (curValSet.union(Set(validator)), newAccPower)
                } else {
                    // if we have enough power, don't add them
                    (curValSet, accPower)
                }
        )
        res._1
    }

    // Opts a validator in for a consumer chain the provider.
    // Possible before the consumer chain starts running,
    // and will then be applied when the consumer chain starts running.
    pure def OptIn(currentState: ProtocolState, consumer: Chain, validator: Node): Result = {
        pure val optedInVals = currentState.providerState.optedInVals.get(consumer)
        pure val newOptedInVals = optedInVals.union(Set(validator))
        Ok({
            ...currentState,
            providerState: {
                ...currentState.providerState,
                optedInVals: currentState.providerState.optedInVals.put(consumer, newOptedInVals)
            }
        })
    }

    // Returns true if the given validator is in the top N for the given consumer chain,
    // and false otherwise.
    pure def IsTopN(currentState: ProtocolState, validator: Node, consumer: Chain): bool = {
        val proviValSet = currentState.providerState.chainState.currentValidatorSet
        val N = currentState.providerState.topNByConsumer.get(consumer)

        val topNValSet = GetTopNVals(proviValSet, N)

        topNValSet.contains(validator)
    }

    // Returns true if the given validator has opted in to the given consumer chain,
    pure def IsOptedIn(currentState: ProtocolState, validator: Node, consumer: Chain): bool = {
        currentState.providerState.optedInVals.getOrElse(consumer, Set()).contains(validator)
    }

    // Opts a validator out. Safe to call before the consumer chain even runs.
    // Will not stop the validator set from being forced to validate when in the top N.
    // Validators that are in the top N will not be able to opt out, and
    // an error will be returned.
    // Similarly, if the validator is not opted in, an error will be returned.
    pure def OptOut(currentState: ProtocolState, consumer: Chain, validator: Node): Result = {
        if (currentState.IsTopN(validator, consumer)) {
            Err("Cannot opt out a validator that is in the top N")
        } else if (not(currentState.IsOptedIn(validator, consumer))) {
            Err("Cannot opt out a validator that is not opted in")
        } else {
            pure val optedInVals = currentState.providerState.optedInVals.get(consumer)
            pure val newOptedInVals = optedInVals.exclude(Set(validator))
            Ok({
                ...currentState,
                providerState: {
                    ...currentState.providerState,
                    optedInVals: currentState.providerState.optedInVals.put(consumer, newOptedInVals)
                }
            })
        }
    }

    // Runs the PSS logic that needs to run on endblock.
    // Concretely, this will forcefully opt in all validators that are in the top N
    // for each chain.
    pure def endBlockPSS(providerState: ProviderState): ProviderState = {
        val runningConsumers = providerState.getRunningConsumers()
        runningConsumers.fold(
            providerState,
            (acc, consumer) => endBlockPSS_helper(acc, consumer)
        )
    }

    // Runs the PSS logic for a single consumer.
    // Should only be run for running chains.
    pure def endBlockPSS_helper(providerState: ProviderState, consumer: Chain): ProviderState = {
        val proviValSet = providerState.chainState.currentValidatorSet
        val topNVals = GetTopNVals(proviValSet, providerState.topNByConsumer.get(consumer))
        val prevOptedInVals = providerState.optedInVals.getOrElse(consumer, Set())
        // opt in all the top N validators, i.e. union the top N vals with the previous opted in vals
        val newOptedInVals = providerState.optedInVals.put(consumer, prevOptedInVals.union(topNVals))
        {
            ...providerState,
            optedInVals: newOptedInVals
        }
    }
}