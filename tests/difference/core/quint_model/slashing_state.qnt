module slashing_state {
    import common.* from "./common"

    // Stores, for each validator, until when it is jailed.
    // If this is less than the current time, the validator is not jailed.
    var jailed: Validator -> int

    val jailTime: int = 50
}