module ccv_pss_model {
    import ccv_types.* from "./ccv"
    import ccv_model.* from "./ccv_model"
    import ccv_pss.* from "./ccv_pss"
    import extraSpells.* from "./libraries/extraSpells"

    action StepOptIn(): bool = {
        nondet consumer = oneOf(runningConsumers)
        nondet validator = oneOf(nodes)
        OptIn_Deterministic(consumer, validator)
    }

    action OptIn_Deterministic(consumer: Chain, validator: Node): bool = {
        val res = OptIn(currentState, consumer, validator)
        all {
            currentState' = res.newState,
            trace' = trace.append(
                {
                    ...emptyAction,
                    kind: "OptIn",
                    consumerChain: consumer,
                    validator: validator,
                    expectedError: res.error
                }
            ),
            params' = params,
        }
    }

    action StepOptOut(): bool = {
        nondet consumer = oneOf(runningConsumers)
        nondet validator = oneOf(nodes)
        OptOut_Deterministic(consumer, validator)
    }

    action OptOut_Deterministic(consumer: Chain, validator: Node): bool = {
        val res = OptOut(currentState, consumer, validator)
        all {
            currentState' = res.newState,
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

    // Functions that, given a random number from 1 to 100,
    // returns a top N value to be set for a new consumer chain to start.
    // Used to decide on the distribution of top N values.
    pure def allFullConsumers(): int = 100

    pure def allOptIn(): int = 0

    // 30% are opt in, rest are random between
    // 50 and 95, with a slight bias towards
    // 95 
    pure def biasLargeTopN(): int =
    nondet x = oneOf(1.to(100))
    if(x <= 30) {
        0
    } else {
        min(95, x+19)
    }
}