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
    
    // The N in TopN must be:
    // * either 0 (to signify that this is not a top N chain)
    // * or be between 50 and 95 
    pure def ValidTopNValue(N: int): bool = {
        N.in(50.to(95)) or N == 0
    }

    // Given a base validator set, an N for a top N chain, and a set of validators that have opted in to the chain,
    // returns the validator set that should be sent to the chain.
    // Assumes that the value for N is valid.
    pure def GetTopNValidatorSet(providerState: ProviderState, origValSet: ValidatorSet, consumer: Chain): ValidatorSet = {
        pure val N = providerState.topNByConsumer.get(consumer)
        pure val optedInVals = providerState.optedInVals.getOrElse(consumer, Set())
        GetTopNValidatorSet_helper(origValSet, N, optedInVals)
    }

    pure def GetTopNValidatorSet_helper(origValSet: ValidatorSet, N: int, optedInVals: Set[Node]): ValidatorSet = {
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
            (Map(), 0),
            (acc, validator) =>
                pure val curValSet = acc._1
                pure val accPower = acc._2
                if (accPower < topNPower) {
                    // if we don't have enough power yet, add the validator to the set
                    pure val validatorPower = origValSet.get(validator)
                    pure val newAccPower = accPower + validatorPower
                    pure val newCurValSet = curValSet.put(validator, validatorPower)
                    (newCurValSet, newAccPower)
                } else if (optedInVals.contains(validator)) {
                    // if the validator has opted in, add them
                    pure val validatorPower = origValSet.get(validator)
                    pure val newCurValSet = curValSet.put(validator, validatorPower)
                    // acc power is not relevant anymore, because we already have enough power anyways
                    (newCurValSet, accPower)
                } else {
                    // if we have enough power and the validator has not opted in, don't add them
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

    // Opts a validator out. Safe to call before the consumer chain even runs.
    // Will not stop the validator set from being forced to validate when in the top N.
    pure def OptOut(currentState: ProtocolState, consumer: Chain, validator: Node): Result = {
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