// This module contains logic for PSS (Partial Set Security).
// PSS is a variant/extension of CCV that 
// allows for only a subset of the validator set
// to secure a consumer chain.
// Not all logic related to PSS is inside this module, as some logic is
// too tightly coupled with the core CCV logic,
// which is instead found in ccv.qnt
module ccv_pss_test {
    import ccv_types.* from "./ccv"
    import extraSpells.* from "./libraries/extraSpells"
    import ccv_utils.* from "./ccv_utils"
    import ccv_pss.* from "./ccv_pss"
    import ccv.* from "./ccv"

    run TopN1Test = 
        val valSet =
            Map("d" -> 25, "c1" -> 15, "c" -> 15, "b2" -> 10, "b1" -> 10, "b" -> 10, "a2" -> 5, "a1" -> 5, "a" -> 5)
        // total power: 5*3 + 10*3 + 15*2 + 25 = 100
        all
        {
            assert(GetTopNVals(valSet, 0) == Set()),
            assert(GetTopNVals(valSet, 1) == Set("d")),
            assert(GetTopNVals(valSet, 10) == Set("d")),
            assert(GetTopNVals(valSet, 25) == Set("d")),
            // if one validator with a power is included, all validators with that power need to be included
            assert(GetTopNVals(valSet, 26) == Set("d", "c1", "c")),
            assert(GetTopNVals(valSet, 45) == Set("d", "c1", "c")),
            assert(GetTopNVals(valSet, 55) == Set("d", "c1", "c")),
            assert(GetTopNVals(valSet, 56) == Set("d", "c1", "c", "b2", "b1", "b")),
            assert(GetTopNVals(valSet, 85) == Set("d", "c1", "c", "b2", "b1", "b")),
            assert(GetTopNVals(valSet, 86) == valSet.keys()),
            assert(GetTopNVals(valSet, 95) == valSet.keys()),
            assert(GetTopNVals(valSet, 100) == valSet.keys()),
        }    

    val providerState = GetEmptyProviderState().with(
            "chainState", GetEmptyChainState().with(
                "currentValidatorPowers", Map(
                    "a" -> 5,
                    "a1" -> 5,
                    "a2" -> 5,
                    "b" -> 10,
                    "b1" -> 10,
                    "b2" -> 10,
                    "c" -> 15,
                    "c1" -> 15,
                    "d" -> 25
                )
            )
        ).with(
            "consumerStatus", Map(
                "consumer1" -> "running"
            )
        ).with(
            "topNByConsumer", Map(
                "consumer1" -> 80
            )
        )
    run TopN2Test =
        true
}