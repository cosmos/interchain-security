// Staking models the staking module with a single delegator, but multiple validators.
module staking_state {
    import common.* from "./common"


    type Undelegation = {validator: Validator, amount: int, completionTime: Timestamp, creationHeight: int, onHold: bool}

    val Bonded: str = "Bonded"
    val Unbonded: str = "Unbonded"
    val Unbonding: str = "Unbonding"

    // params
    val MaxValidators: int = 100
    val UnbondingSeconds: int = 5200

    // The amount of unbonded tokens of the single delegator.
    var delegatorTokens: int
    // The amount delegated to each validator by the single delegator.
    var delegationAmounts: Validator -> int
    // The total stake of the validator. Includes, but may exceed, the delegationAmount (e.g. validators can have self-delegations).
    var validatorPower: Validator -> int
     // A queue of pending undelegations.
    var pendingUndelegations: Set[Undelegation]
    // A queue of pending validator unbondings.
    var pendingUnbondings: Set[ValidatorUnbonding]
    // The status of the validators, either Bonded, Unbonded, or Unbonding.
    var validatorStatus: Validator -> string

    var currentValidatorSet: Set[Validator]
}