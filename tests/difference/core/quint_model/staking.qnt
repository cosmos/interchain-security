module staking {
    import common.* from "./common"

    import slashing_state.* from "./slashing_state"
    import staking_state.* from "./staking_state"
    import basicSpells.* from "./basicSpells"
    import extraSpells.* from "./extraSpells"

    // Constructor for undelegations.
    pure def NewUndelegation(validator: Validator, amount: int, completionTime: Timestamp, currentHeight: int): Undelegation =
        {validator: validator, amount: amount, completionTime: completionTime, creationHeight: currentHeight, onHold: true}

    // Constructor for unbondings.
    pure def NewUnbonding(validator: Validator, completionTime: Timestamp, creationHeight: int): ValidatorUnbonding =
        {validator: validator, completionTime: completionTime, creationHeight: creationHeight, onHold: true}
        

    // Delegates an amount of tokens from the single delegator to the validator
    action Delegate(validator: Validator, amount: int): bool = all {
        delegatorTokens' = delegatorTokens - amount, // unbonded tokens are decreased because we bond tokens
        delegationAmounts' = delegationAmounts.setBy(validator, (oldDelegation => oldDelegation + amount)),
        validatorPower' = validatorPower.setBy(validator, (oldBalance => oldBalance + amount)),
        currentValidatorSet' = currentValidatorSet
    }

    // Undelegates tokens (delegated by the single delegator) from a validator.
    action Undelegate(validator: Validator, undelegationAmount: int): bool = any {
        all {
            // failure case: the undelegation amount is larger than the delegated amount.
            assert(undelegationAmount > delegationAmounts.get(validator)),
            // thus, the undelegation should not proceed.
            delegationAmounts' = delegationAmounts,
            pendingUndelegations' = pendingUndelegations,
            currentValidatorSet' = currentValidatorSet
        },
        all {
            // happy path: the undelegation amount is at most the delegated amount.
            assert(undelegationAmount <= delegationAmounts.get(validator)),
            // reduce the delegated amount immediately
            delegationAmounts' = delegationAmounts.setBy(validator, (oldDelegation => oldDelegation - undelegationAmount)),
            // keep the undelegation in the queue until unbonding is complete
            pendingUndelegations' = 
                pendingUndelegations.add(NewUndelegation(
                        validator, 
                        undelegationAmount,
                        providerState.time + UnbondingSeconds,
                        providerState.height)),
            currentValidatorSet' = currentValidatorSet,
            // TODO: call hooks for undelegate
        }
    }

    action Staking_EndBlock(chain: Chain): bool = all {
        val potentialValidators = 
            validatorPower.keys().filter(validator => validatorPower.get(validator) > 0 and jailed.getOrElse(validator, 0) <= providerState.time)
        val potentialValidatorList = potentialValidators.toList()
        def HasMorePower(this: Validator, other: Validator): bool = validatorPower.get(this) > validatorPower.get(other)
        val sortedValidatorList = potentialValidatorList.listSorted(HasMorePower)
        val newValidators = sortedValidatorList.slice(0, MaxValidators)
        val newValidatorSet = newValidators.toSet()
        all {
        currentValidatorSet' = newValidatorSet,
        validatorStatus' = validatorStatus.keys().union(newValidatorSet).mapBy(validator => 
            GetNewValidatorStatus(newValidatorSet, validator)),
        UpdateUnbondingQueue(currentValidatorSet, newValidatorSet)
        }
    }

    def IsMature(unbonding: ValidatorUnbonding): bool = {
        unbonding.completionTime >= providerState.time and
        unbonding.creationHeight >= providerState.height and
        not(unbonding.onHold)
    }

    // Computes how to update the status of a given validator.
    def GetNewValidatorStatus(newValidatorSet: Set[Validator], validator: Validator): str = 
        if (newValidatorSet.contains(validator)) { 
            // new validator gets bonded
            Bonded 
        } else { 
            if (currentValidatorSet.contains(validator))
            { // validator is in current but not in new validator set
                Unbonding
            } else {
                // validator is not in new nor current validator set, so only change might be the unbonding completes
                if (
                    pendingUnbondings.exists(unbonding =>
                    unbonding.IsMature() and
                    unbonding.validator == validator)) {
                    Unbonded
                } else {
                    validatorStatus.get(validator)
                }
            }
        }

    // Removes all mature unbondings from the queue, and adds new unbondings for validators that are no longer in the validator set.
    action UpdateUnbondingQueue(curValSet: Set[Validator], newValSet: Set[Validator]): bool =
        pendingUnbondings' = pendingUnbondings.filter(unbonding => 
            not(unbonding.IsMature())).union(
                curValSet.exclude(newValSet).map(validator => 
                    NewUnbonding(validator, providerState.time + UnbondingSeconds, providerState.height))
            )
}