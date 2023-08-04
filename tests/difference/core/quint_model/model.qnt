// -*- mode: Bluespec; -*-
module common {
    type Validator = str
    type Chain = str

    pure val Provider = "provider"
    pure val Consumer = "consumer"

    type Timestamp = int

    type ValidatorUpdate = {validator: Validator, newPower: int64}

     val curTime: int = 0
    }

module ccv_packets {
    import common.*
    // contains validator updates
    type VSCPacketData =
    {
        // id of the vsc packet
        id: int,
        // validator updates
        updates: List[ValidatorUpdate],
        // downtime slash requests acknowledgements, 
        // i.e., list of validator addresses
        downtimeSlashAcks: List[string],
    }

    // contains a request to slash a validator
    type SlashPacketData = 
    {
        validator: Validator,
        validatorPower: int,
        // the id of the vsc packet that the consumer last applied
        vscId: int,
        // if it is not downtime, it is equivocation
        isDowntime: bool
    }

    type VSCMaturedPacketData = 
    {
        // the id of the VSC that reached maturity
        id: int
    }
}

module ibc {
    import common.*
    import ccv_packets.*

    // Since Quint does not support sum types yet, this is a workaround
    // to allow a packet to be one of the various types of packets.
    // Assumed invariants on Packet:
    // 1) Exactly 1 of the "is[X]Packet" fields will be true.
    // 2) If the is[X]Packet field is false, the [x]Data field is an empty set.
    // 3) If the is[X]Packet field is true, the [x]Data field is a singleton set.
    type Packet = 
    {isVscPacket: bool, vscPacketData: Set[VSCPacketData],
    isSlashPacket: bool, slashPacketData: Set[SlashPacketData],
    isVSCMaturedPacket: bool, vscMaturedPacketData: Set[VSCMaturedPacketData]
    }

    pure def newVSCPacket(id: int, updates: List[ValidatorUpdate], downtimeSlashAcks: List[string]): Packet =
        {isVscPacket: true, vscPacketData: Set({id: id, updates: updates, downtimeSlashAcks: downtimeSlashAcks}),
        isSlashPacket: false, slashPacketData: Set(),
        isVSCMaturedPacket: false, vscMaturedPacketData: Set()}

    pure def newSlashPacket(validator: Validator, validatorPower: int, vscId: int, isDowntime: bool): Packet =
        {isVscPacket: false, vscPacketData: Set(),
        isSlashPacket: true, slashPacketData: Set({validator: validator, validatorPower: validatorPower, vscId: vscId, isDowntime: isDowntime}),
        isVSCMaturedPacket: false, vscMaturedPacketData: Set()}

    pure def newVSCMaturePacket(id: int): Packet =
        {isVscPacket: false, vscPacketData: Set(),
        isSlashPacket: false, slashPacketData: Set(),
        isVSCMaturedPacket: true, vscMaturedPacketData: Set({id: id})}

    // Queue of outstanding packets from the consumer to the provider.
    var ConsumerToProviderChannel: List[Packet]
    // Queue of outstanding packets from the provider to the consumer.
    var ProviderToConsumerChannel: List[Packet]
    
}

// Staking models the staking module with a single delegator, but multiple validators.
module staking {
    import common.*

    type Undelegation = {validator: Validator, amount: int, startTime: Timestamp}

    // The amount of unbonded tokens of the single delegator.
    var delegatorTokens: int
    // The total stake of the validator. Includes, but may exceed, the delegationAmount (e.g. validators can have self-delegations).
    var delegationAmounts: Validator -> int
    // The total stake of the validator. Includes, but may exceed, the delegationAmount (e.g. validators can have self-delegations).
    var validatorPower: Validator -> int
     // A queue of pending undelegations (i.e. unbondings).
    var undelegationsQueue: List[Undelegation]


    // Constructor for undelegations.
    pure def NewUndelegation(validator: Validator, amount: int, startTime: Timestamp): Undelegation =
        {validator: validator, amount: amount, startTime: startTime}

    // Delegates an amount of tokens from the single delegator to the validator
    action Delegate(validator: Validator, amount: int): bool = all {
        delegatorTokens' = delegatorTokens + amount,
        delegationAmounts' = delegationAmounts.setBy(validator, (oldDelegation => oldDelegation + amount)),
        validatorPower' = validatorPower.setBy(validator, (oldBalance => oldBalance + amount))
    }

    // Undelegates tokens (delegated by the single delegator) from a validator.
    action Undelegate(validator: Validator, undelegationAmount: int): bool = any {
        all {
            // failure case: the undelegation amount is larger than the delegated amount.
            assert(undelegationAmount > delegationAmounts.get(validator)),
            // thus, the undelegation should not proceed.
            delegationAmounts' = delegationAmounts,
            undelegationsQueue' = undelegationsQueue,
        },
        all {
            // happy path: the undelegation amount is at most the delegated amount.
            assert(undelegationAmount <= delegationAmounts.get(validator)),
            // reduce the delegated amount immediately
            delegationAmounts' = delegationAmounts.setBy(validator, (oldDelegation => oldDelegation - undelegationAmount)),
            // keep the undelegation in the queue until unbonding is complete
            undelegationsQueue' = undelegationsQueue.append(NewUndelegation(validator, undelegationAmount, curTime)),
            // TODO: call hooks for undelegate
        }
    }



}


module ccv_consumer {
    import common.*
    import ibc.*
    import ccv_packets.*

    var validatorPower: Validator -> int

    // outstandingDowntime.get(valAddr) = true entails that the consumer chain sent a request to slash for downtime the validator with address valAddr.
    // outstandingDowntime.get(valAddr) is set to false once the consumer chain receives a confirmation that the downtime slash request was received by the provider chain, 
    // The mapping enables the consumer CCV module to avoid sending to the provider chain multiple slashing requests for the same downtime infraction.
    var outstandingDowntime: Validator -> bool

    // A queue of VSCPacketData which was received but not yet applied.
    var receivedVSCs: List[VSCPacketData]

    // A mapping from consumer chain heights to VSC IDs. It enables the mapping from consumer heights to provider heights.
    var HtoVSC: int -> int

    // Sends a slash request packet from the consumer chain to the provider.
    action ConsumerInitiatedSlash(validator: Validator, infractionHeight: int, isDowntime: bool): bool = 
    any {
        all {
            // it is a downtime slash but we already have outstanding downtime for that validator, so do nothing
            isDowntime,
            ConsumerToProviderChannel' = ConsumerToProviderChannel,
        },
        all {
            // we need to put a slash packet
            ConsumerToProviderChannel' = ConsumerToProviderChannel.append(
                newSlashPacket(validator, validatorPower.get(validator), HtoVSC.get(infractionHeight),
            isDowntime))
        }
    }
}

module main {
    import common.*
    import ibc.Packet

    pure val SlashTypes = Set("downtime", "equivocation")

    action UpdateClient(chain: Chain): bool = true
    action DeliverPacket(chain: Chain, packet: Packet): bool = true
    action endAndBeginBlock(chain: Chain): bool = true

}