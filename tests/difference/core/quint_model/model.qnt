// -*- mode: Bluespec; -*-
module common {
    type Validator = str
    type Chain = str
    type Packet = int

    type Timestamp = int
    }

// Staking models the staking module with a single delegator, but multiple validators.
module staking {
    import common.*

    type Undelegation = {validator: Validator, amount: int, startTime: Timestamp}

    var delegatorTokens: int
    var delegationAmounts: Validator -> int
    var validatorBalance: Validator -> int
    var undelegationsQueue: List[Undelegation]


    // Delegates an amount of tokens from the single delegator to the validator
    action Delegate(validator: Validator, amount: int): bool = all {
        delegatorTokens' = delegatorTokens + amount,
        delegationAmounts' = delegationAmounts.setBy(validator, (oldDelegation => oldDelegation + amount)),
        validatorBalance' = validatorBalance.setBy(validator, (oldBalance => oldBalance + amount))
    }

    // Undelegates tokens (delegated by the single delegator) from a validator.
    action Undelegate(validator: Validator, amount: int): bool = any {
        all {
            assert(amount > delegationAmounts.get(validator)),
            delegationAmounts' = delegationAmounts
        },
        all {
            assert(amount <= delegationAmounts.get(validator)),
            delegationAmounts' = delegationAmounts.setBy(validator, (oldDelegation => oldDelegation - amount)),
            // TODO: call hooks for undelegate
        }
    }



    }

module ccv_consumer {
    import common.*

    

    action ConsumerInitiatedSlash(validator: Validator, infractionHeight: int, slashType: str): bool = true
        
    }

module main {
    import common.*

    pure val SlashTypes = Set("downtime", "equivocation")

    action UpdateClient(chain: Chain): bool = true
    action DeliverPacket(chain: Chain, packet: Packet): bool = true
    action endAndBeginBlock(chain: Chain): bool = true

    }