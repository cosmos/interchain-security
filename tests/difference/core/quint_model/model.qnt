// -*- mode: Bluespec; -*-
module ccv_common {
    import common.* from "./common"
 
    type VscId = int
    type UnbondingId = int
}

module ibc {
    import common.* from "./common"

    import ccv_packets.* from "./ccv_packets"


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


module ccv_provider {
    import common.* from "./common"

    import ibc.*
    import ccv_packets.* from "./ccv_packets"
    import ccv_common.*
    import basicSpells.* from "./basicSpells"
    import extraSpells.* from "./extraSpells"
    import slashing.* from "./slashing"
    import staking.* from "./staking"

    // Enables accessing, for every unbonding operation,
    // the set of consumer chains that are still unbonding.
    var unbondingOps: UnbondingId -> ValidatorUnbonding

    // Enables the provider CCV module to match a VSCMaturedPacket{vscId},
    // received from a consumer chain with chainId,
    // with the corresponding unbonding operations.
    var vscToUnbondingOps: VscId -> Set[UnbondingId]

    var matureUnbondingOps: Set[UnbondingId]

    // Matures all unbondings associated with the vscId of the given VSCMaturedPacketData.
    // Remove the unbonding operations from the unbondingOps map.
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
    import common.* from "./common"

    import ibc.*
    import ccv_packets.* from "./ccv_packets"
    import staking.* from "./staking"
    import slashing.* from "./slashing"
    import staking_state.* from "./staking"

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

module main {
    import common.* from "./common"

    import ibc.*
    import ccv_consumer.*
    import ccv_provider.*
    import slashing.* from "./slashing"

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