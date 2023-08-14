// -*- mode: Bluespec; -*-

// Design notes:
// The spec is modular.
// The various modules generally have actions and variables.
// The internal state may be read, but not modified, by other modules.
// In turn, *all* public actions of modules should specify behavior for /all/ variables of the module.
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

module ccv_common {
    import common.* 

    type VscId = int
    type UnbondingId = int
    type UnbondingOperation = 
        {id: int}
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

    // Returns the VSCPacketData of a packet.
    // If the packet is not a VSC packet, this function will give undefined output.
    pure def GetVSCData(packet: Packet): VSCPacketData =
        packet.vscPacketData.chooseSome()

    // Returns the SlashPacketData of a packet.
    // If the packet is not a Slash packet, this function will give undefined output.
    pure def GetSlashData(packet: Packet): SlashPacketData =
        packet.slashPacketData.chooseSome()

    // Returns the VSCMaturedPacketData of a packet.
    // If the packet is not a VSCMatured packet, this function will give undefined output.
    pure def GetVSCMaturedData(packet: Packet): VSCMaturedPacketData =
        packet.vscMaturedPacketData.chooseSome()

    // Queue of outstanding packets from the consumer to the provider.
    var ConsumerToProviderChannel: List[Packet]

    // Queue of uncommitted packets from the consumer to the provider.
    // These packets will be put in the ConsumerToProviderChannel when
    // the consumer ends a block.
    var UncommitedConsumerToProviderChannel: List[Packet]

    // Queue of outstanding packets from the provider to the consumer.
    var ProviderToConsumerChannel: List[Packet]

    // These packets will be put in the ConsumerToProviderChannel when
    // the provider ends a block.
    var UncommitedProviderToConsumerChannel: List[Packet]

    // description taken from the old difftest model:
    // noop. We do not explicitly model the client update process
    // but we must call this function at appropriate times in order
    // to test the SUT using this model. This is because
    // if we allow too much time to elapse between updates, the light
    // clients in the SUT will expire, and the test will fail.
    action UpdateClient(chain: Chain): bool = true

    action QueuePacket(packet: Packet, receiver: Chain): bool =
        any {
            all {
            receiver == Provider,
            UncommitedConsumerToProviderChannel' = UncommitedConsumerToProviderChannel.append(packet),
            UncommitedProviderToConsumerChannel' = UncommitedProviderToConsumerChannel
        },
        all {
            receiver == Consumer,
            UncommitedProviderToConsumerChannel' = UncommitedProviderToConsumerChannel.append(packet),
            UncommitedConsumerToProviderChannel' = UncommitedConsumerToProviderChannel
        }
    }

    // Puts uncomitted packets into their respective
    // channels and clears the uncommitted channels.
    action IBC_EndBlock(chain: Chain): bool = all {
        UncommitedConsumerToProviderChannel' = List(),
        UncommitedProviderToConsumerChannel' = List(),
        ConsumerToProviderChannel' = ConsumerToProviderChannel.concat(UncommitedConsumerToProviderChannel),
        ProviderToConsumerChannel' = ProviderToConsumerChannel.concat(UncommitedProviderToConsumerChannel)
    }
}

module slashing_state {
    import common.*
    // Stores, for each validator, until when it is jailed.
    // If this is less than the current time, the validator is not jailed.
    var jailed: Validator -> int

    val jailTime: int = 50
}

module staking_state {
    import common.*

    type Undelegation = {validator: Validator, amount: int, completionTime: Timestamp, unbondingHeight: height}

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
     // A queue of pending undelegations (i.e. unbondings).
    var undelegationsQueue: List[Undelegation]
    // The status of the validators, either Bonded, Unbonded, or Unbonding.
    var validatorStatus: Validator -> string

    var currentValidatorSet: Set[Validator]
}

module slashing {
    import common.*
    import ccv_packets.*
    import slashing_state.*
    import staking_state.*

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

// Staking models the staking module with a single delegator, but multiple validators.
module staking {
    import common.*
    import slashing_state.*
    import staking_state.*
    import basicSpells.* from "./basicSpells"
    import extraSpells.* from "./extraSpells"

    // Constructor for undelegations.
    pure def NewUndelegation(validator: Validator, amount: int, completionTime: Timestamp, currentHeight: height): Undelegation =
        {validator: validator, amount: amount, completionTime: completionTime, unbondingHeight: currentHeight}

    // Delegates an amount of tokens from the single delegator to the validator
    action Delegate(validator: Validator, amount: int): bool = all {
        delegatorTokens' = delegatorTokens - amount, // unbonded tokens are decreased because we bond tokens
        delegationAmounts' = delegationAmounts.setBy(validator, (oldDelegation => oldDelegation + amount)),
        validatorPower' = validatorPower.setBy(validator, (oldBalance => oldBalance + amount)),
        currentValidatorSet' = currentValidatorSet
    }

    // Undelegates tokens (delegated by the single delegator) from a validator.
    action Undelegate(validator: Validator, undelegationAmount: int): bool = any {
        all {
            // failure case: the undelegation amount is larger than the delegated amount.
            assert(undelegationAmount > delegationAmounts.get(validator)),
            // thus, the undelegation should not proceed.
            delegationAmounts' = delegationAmounts,
            undelegationsQueue' = undelegationsQueue,
            currentValidatorSet' = currentValidatorSet
        },
        all {
            // happy path: the undelegation amount is at most the delegated amount.
            assert(undelegationAmount <= delegationAmounts.get(validator)),
            // reduce the delegated amount immediately
            delegationAmounts' = delegationAmounts.setBy(validator, (oldDelegation => oldDelegation - undelegationAmount)),
            // keep the undelegation in the queue until unbonding is complete
            undelegationsQueue' = 
                undelegationsQueue.append(NewUndelegation(
                        validator, 
                        undelegationAmount,
                        providerState.time + UnbondingSeconds,
                        providerState.height)),
            currentValidatorSet' = currentValidatorSet,
            // TODO: call hooks for undelegate
        }
    }

    action Staking_EndBlock(chain: Chain): bool = all {
        ComputeValUpdates(chain),
        // ApplyMatureUnbondings(chain),
    }

    // Computes how to update the status of a given validator.
    def GetNewValidatorStatus(newValidatorSet: Set[Validator], validator: Validator): str = 
        if (newValidatorSet.contains(validator)) { 
            // new validator gets bonded
            Bonded 
        } else { 
            if (currentValidatorSet.contains(validator))
            { // validator is in current but not in new validator set
                Unbonding
            } else {
                // validator is not in new nor current validator set, so only change might be if unbonding completes
                if (undelegationsQueue.filter(undelegation => all {
                    undelegation.completionTime >= providerState.currentTime,
                    undelegation.completionHeight >= providerState.height,
                })
                )
                validatorStatus.get(validator)
            }
        }

    action ComputeValUpdates(chain: Chain): bool = 
        val potentialValidators = 
            validatorPower.keys().filter(validator => validatorPower.get(validator) > 0 and jailed.getOrElse(validator, 0) <= providerState.time)
        val potentialValidatorList = potentialValidators.toList()
        def HasMorePower(this: Validator, other: Validator): bool = validatorPower.get(this) > validatorPower.get(other)
        val sortedValidatorList = potentialValidatorList.listSorted(HasMorePower)
        val newValidators = sortedValidatorList.slice(0, MaxValidators)
        val newValidatorSet = newValidators.toSet()
        all {
        currentValidatorSet' = newValidatorSet,
        validatorStatus' = validatorStatus.keys().union(newValidatorSet).mapBy(validator => 
            GetNewValidatorStatus(newValidatorSet, validator))
    }
}


module ccv_provider {
    import common.*
    import ibc.*
    import ccv_packets.*
    import ccv_common.*
    import basicSpells.* from "./basicSpells"
    import extraSpells.* from "./extraSpells"
    import slashing.*
    import staking.*

    // Enables accessing, for every unbonding operation,
    // the set of consumer chains that are still unbonding.
    var unbondingOps: UnbondingId -> UnbondingOperation

    // Enables the provider CCV module to match a VSCMaturedPacket{vscId},
    // received from a consumer chain with chainId,
    // with the corresponding unbonding operations.
    var vscToUnbondingOps: VscId -> Set[UnbondingId]

    var matureUnbondingOps: Set[UnbondingId]

    // Matures all unbondings associated with the vscId of the given VSCMaturedPacketData.
    // Remove the unbonding operations from the unbondingOps map.
    // Add the 
    action OnRecvVSCMatured(data: VSCMaturedPacketData): bool = all {
        matureUnbondingOps' = matureUnbondingOps.union(vscToUnbondingOps.get(data.id)),
        unbondingOps'  = unbondingOps.mapRemoveAll(vscToUnbondingOps.get(data.id)),
        vscToUnbondingOps' = vscToUnbondingOps.mapRemove(data.id),
    }

    action CCVProviderNoop: bool = all {
        unbondingOps' = unbondingOps,
        vscToUnbondingOps' = vscToUnbondingOps,
        matureUnbondingOps' = matureUnbondingOps,
    }
}


module ccv_consumer {
    import common.*
    import ibc.*
    import ccv_packets.*
    import staking.*
    import slashing.*
    import staking_state.*

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
            isDowntime == true,
            outstandingDowntime.get(validator) == true,
            ConsumerToProviderChannel' = ConsumerToProviderChannel,
            outstandingDowntime' = outstandingDowntime,
        },
        all {
            // it is not a downtime slash or we don't have outstanding downtime for that validator, so send a downtime slash request
            isDowntime == false or outstandingDowntime.get(validator) == false,
            // we need to put a slash packet
            ConsumerToProviderChannel' = ConsumerToProviderChannel.append(
                newSlashPacket(validator, validatorPower.get(validator), HtoVSC.get(infractionHeight),
            isDowntime)),
            if (isDowntime == true) {
                outstandingDowntime' = outstandingDowntime.setBy(validator, (oldOutstandingDowntime => true))
            } else {
                outstandingDowntime' = outstandingDowntime
            }
        }
    }

    action OnRecvVSC(data: VSCPacketData): bool = all {
        HtoVSC' = HtoVSC.put(consumerState.height + 1, data.id),
        receivedVSCs' = receivedVSCs.append(data),
        outstandingDowntime' = outstandingDowntime,
    }

    action CCVConsumerNoop(): bool = all {
        HtoVSC' = HtoVSC,
        receivedVSCs' = receivedVSCs,
        outstandingDowntime' = outstandingDowntime,
    }
}

// Actions of the main module always touch all the other modules.
module main {
    import common.*
    import ibc.*
    import ccv_consumer.*
    import ccv_provider.*
    import slashing.*

     // Delivers the next pending packet to the given chain.
    action DeliverPacket(receiver: Chain): bool = all {
        receiver == Provider or receiver == Consumer,
        if(receiver == Provider) {
            all {
                ConsumerToProviderChannel' = ConsumerToProviderChannel.tail(),
                ProviderToConsumerChannel' = ProviderToConsumerChannel,
                DeliverPacketToChain(receiver, ConsumerToProviderChannel.head())
            }
        } else { // receiver == Consumer
            all {
                ProviderToConsumerChannel' = ProviderToConsumerChannel.tail(),
                ConsumerToProviderChannel' = ConsumerToProviderChannel,
                DeliverPacketToChain(receiver, ConsumerToProviderChannel.head())
            }
        }
    }

    // Delivers a specific packet to the given chain.
    action DeliverPacketToChain(receiver: Chain, packet: Packet): bool =
        any {
            all {
                packet.isSlashPacket,
                receiver == Provider,
                OnRecvSlash(packet.GetSlashData()),
                CCVProviderNoop,
                CCVConsumerNoop
            },
            all {
                packet.isVscPacket,
                receiver == Consumer,
                OnRecvVSC(packet.GetVSCData()),
                SlashingNoop,
                CCVProviderNoop
            },
            all {
                packet.isVSCMaturedPacket,
                receiver == Provider,
                OnRecvVSCMatured(packet.GetVSCMaturedData()),
                CCVConsumerNoop,
                SlashingNoop
            }
        }

    pure val SlashTypes = Set("downtime", "equivocation")

    action endAndBeginBlock(chain: Chain): bool = true

}