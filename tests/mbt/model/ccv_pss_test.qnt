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

    run TopNTest = 
        val valSet =
            Map("d" -> 25, "c1" -> 15, "c" -> 15, "b2" -> 10, "b1" -> 10, "b" -> 10, "a2" -> 5, "a1" -> 5, "a" -> 5)
        // total power: 5*3 + 10*3 + 15*2 + 25 = 100
        all
        {
            assert(GetTopNVals(valSet, 0) == Set()),
            assert(GetTopNVals(valSet, 1) == Set("e")),
            assert(GetTopNVals(valSet, 10) == Set("e")),
            assert(GetTopNVals(valSet, 25) == Set("e")),
            // if one validator with a power is included, all validators with that power need to be included
            assert(GetTopNVals(valSet, 26) == Set("e", "c1", "c")),
            assert(GetTopNVals(valSet, 45) == Set("e", "c1", "c")),
            assert(GetTopNVals(valSet, 55) == Set("e", "c1", "c")),
            assert(GetTopNVals(valSet, 56) == Set("e", "c1", "c", "b2", "b1", "b")),
            assert(GetTopNVals(valSet, 85) == Set("e", "c1", "c", "b2", "b1", "b")),
            assert(GetTopNVals(valSet, 86) == Set("e", "c1", "c", "b2", "b1", "b", "a2", "a1", "a")),
            assert(GetTopNVals(valSet, 95) == Set("e", "c1", "c", "b2", "b1", "b", "a2", "a1", "a")),
            assert(GetTopNVals(valSet, 100) == Set("e", "c1", "c", "b2", "b1", "b", "a2", "a1", "a")),
        }
}