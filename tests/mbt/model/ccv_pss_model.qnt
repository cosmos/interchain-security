module ccv_pss_model {
    import ccv_types.* from "./ccv"
    import ccv_model.* from "./ccv_model"
    import ccv_pss.* from "./ccv_pss"
    import extraSpells.* from "./libraries/extraSpells"

    action StepOptIn(): bool = {
        all {
            runningConsumers.size() > 0,
            nondet consumer = oneOf(runningConsumers)
            nondet validator = oneOf(nodes)
            OptIn_Deterministic(consumer, validator)
        }
    }

    action OptIn_Deterministic(consumer: Chain, validator: Node): bool = {
        val res = option(currentState, consumer, validator)
        all {
            currentState' = res.newState,
            trace' = trace.append(
                {
                    ...emptyAction,
                    kind: "option",
                    consumerChain: consumer,
                    validator: validator
                }
            ),
            params' = params,
        }
    }

    action StepOptOut(): bool = {
        all {
            runningConsumers.size() > 0,    
            nondet consumer = oneOf(runningConsumers)
            nondet validator = oneOf(nodes)
            OptOut_Deterministic(consumer, validator)
        }
    }

    action OptOut_Deterministic(consumer: Chain, validator: Node): bool = {
        val res = OptOut(currentState, consumer, validator)
        all {
            // if we expect an error, this should be a noop
            currentState' = if (res.error == "") res.newState else currentState,
            trace' = trace.append(
                {
                    ...emptyAction,
                    kind: "OptOut",
                    consumerChain: consumer,
                    validator: validator,
                    expectedError: res.error
                }
            ),
            params' = params,
        }
    }

    // Different sets of possible values for the topN parameter.
    val allFullConsumers: Set[int] = Set(100)
    val allOptIn: Set[int] = Set(0)
    // only choose a few values for top N here to not make the "edge cases" of 0 and 100 too unlikely
    val variousPossibleTopN: Set[int] = Set(50, 70, 80, 90, 100)

    // INVARIANTS

    // For a consumer chain with a given top N value,
    // the total VP on the consumer is at least N% of the total VP of some historical val set on the provider.
    val AtLeastTopNPower: bool = 
        runningConsumers.forall(consumer => {
            val topN = currentState.providerState.topNByConsumer.get(consumer)
            val totalPowerConsu = currentState.consumerStates.get(consumer).chainState.currentValidatorPowers.mapValuesSum()
            currentState.providerState.chainState.votingPowerHistory.toSet().exists(
                valSet => {
                    val totalPowerProvi = valSet.mapValuesSum()

                    totalPowerConsu >= totalPowerProvi * topN / 100
                }
            )
        })

    // SANITY CHECKS

    val CanOptIn = {
        not(
            trace[length(trace)-1].kind == "option"
            and
            trace[length(trace)-1].expectedError == ""
        )
    }

    val CanOptOut = {
        not(
            trace[length(trace)-1].kind == "OptOut"
            and
            trace[length(trace)-1].expectedError == ""
        )
    }

    val CanFailOptOut = {
        not(
            trace[length(trace)-1].kind == "OptOut"
            and
            trace[length(trace)-1].expectedError != ""
        )
    }

    val CanHaveOptIn = {
        currentState.providerState.topNByConsumer.keys().exists(consumer => {
            currentState.providerState.topNByConsumer.get(consumer) != 100
        })
    }
}