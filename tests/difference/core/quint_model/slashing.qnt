module slashing {
    import common.* from "./common"

    import ccv_packets.* from "./ccv_packets"
    import slashing_state.* from "./slashing_state"
    import staking_state.* from "./staking_state"

    // For now, just jails the validator.
    action SlashValidator(validator: Validator): bool = all {
        JailUntil(validator, providerState.time + jailTime)
    }

    action JailUntil(validator: Validator, time: Timestamp): bool = 
        jailed' = jailed.set(validator, time)

    action SlashingNoop(): bool = 
        jailed' = jailed

    action OnRecvSlash(data: SlashPacketData): bool = all {
        // TODO: soft opt out https://github.com/cosmos/interchain-security/blob/main/docs/docs/adrs/adr-009-soft-opt-out.md
        if(validatorStatus.get(data.validator) == Unbonded) {
            // noop, the validator is unbonded so cannot be slashed anymore
            SlashingNoop
        } else {
            // tell the slashing module to slash the validator
            SlashValidator(data.validator)
        }
    }
}