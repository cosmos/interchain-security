module common {
    type Validator = str
    type Chain = str

    pure val Provider = "provider"
    pure val Consumer = "consumer"

    type Timestamp = int

    type ValidatorUpdate = {validator: Validator, newPower: int64}

    // Generic state for a chain.
    type ChainState = {
        height: int,
        time: Timestamp,
    }

    // State for the provider chain.
    val providerState: ChainState = {height: 0, time: 0}

    // State for the consumer chain.
    val consumerState: ChainState = {height: 0, time: 0}

    type ValidatorUnbonding = {validator: Validator, completionTime: Timestamp, creationHeight: int, onHold: bool}
}