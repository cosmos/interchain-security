// -*- mode: Bluespec; -*-
// This file contains utility functions for ccv.qnt
// that are not part of the API/core logic of ccv, but still relevant
// for the functional logic of the protocol.
module ccv_utils {
    import ccv_types.* from "./ccv"
    import extraSpells.* from "./libraries/extraSpells"
    import Time.* from "./libraries/Time"


    // Takes the current provider state and validator set and returns 
    // the validator set under the current key assignments for the given consumer, as stored in the provider state.
    pure def applyKeyAssignmentToValSet(
        providerState: ProviderState,
        consumer: Chain,
        valSet: ValidatorSet
    ): ValidatorSet = {
        // map each validator to a tuple of (consumer address, voting power)
        valSet.keys().map(
            (node) => 
            pure val power = valSet.get(node)
            // check if the validator has a key assigned
            pure val validatorToConsumerAddr = providerState.validatorToConsumerAddr.getOrElse(consumer, Map())
            if (validatorToConsumerAddr.keys().contains(node)) {
                // the validator has a key assigned
                pure val consAddr = validatorToConsumerAddr.get(node)
                (consAddr, power)
            } else {
                // the validator has no key assigned
                // use the default key
                (node, power)
            }
        ).fold( // fold the (addr,pow) tuples into a map addr -> pow
            Map(),
            (acc, pair) => acc.put(pair._1, pair._2)
        )
    }

    // Takes a validator set, to which a key assignment has been applied, and reverts it,
    // i.e. returns the original validator set.
    // This also filters out validators that are assigned 0 power.
    pure def revertKeyAssignment(
        keyAssignment: Node -> ConsumerAddr,
        valSetWithAssignment: ValidatorSet
    ): ValidatorSet = {
        // get an assignment from consumer addr to nodes
        pure val reverseAssignment = keyAssignment.keys().map(
            (consAddr) => 
            (keyAssignment.get(consAddr), consAddr)
        ).fold(
            Map(),
            (acc, pair) => acc.put(pair._1, pair._2)
        )

        // for each node in the valset, reverse its key assignment
        valSetWithAssignment.keys().map(
            (addr) => 
            pure val power = valSetWithAssignment.get(addr)
            // if the addr has a key assigned, use that. otherwise, the addr doesn't have a key assigned,
            // and therefore *is* the key that should be used. 
            pure val consAddr = reverseAssignment.getOrElse(addr, addr)
            (consAddr, power)
        ).filter(
            pair => pair._2 > 0
        ).fold(
            Map(),
            (acc, pair) => acc.put(pair._1, pair._2)
        )
    }

    // Appends the key assignment for the given oldConsAddr on the consumer by a validator
    // to be pruned when a VscMaturedPacket for the current runningVscId is received from the consumer.
    pure def AppendConsumerAddrToPrune(currentState: ProtocolState, oldConsAddr: ConsumerAddr, consumer: Chain): ProtocolState = {
        pure val vscId = currentState.providerState.runningVscId
        pure val consumerAddrsToPrune = currentState.providerState.consumerAddrsToPrune.getOrElse(consumer, Map())
        pure val prevConsAddrs = consumerAddrsToPrune.getOrElse(vscId, [])

        pure val newConsAddrsToPrune = consumerAddrsToPrune.put(vscId, prevConsAddrs.append(oldConsAddr))

        currentState.with(
            "providerState", 
            currentState.providerState.with(
                "consumerAddrsToPrune",
                currentState.providerState.consumerAddrsToPrune.put(consumer, newConsAddrsToPrune)
            )
        )
    }

    // Returns the new ConsumerStatusMap according to the consumers to stop
    // and the consumers to time out.
    // If a consumer is both stopped and timed out, it will be timed out.
    // The second return is an error string: If it is not equal to "",
    // it contains an error message, and the first return should be ignored.
    pure def stopConsumers(
        currentConsumerStatusMap: Chain -> str,
        consumersToStop: Set[Chain],
        consumersToTimeout: Set[Chain]): (Chain -> str, str) = {
            val runningConsumers = currentConsumerStatusMap.keys().filter(
                chain => currentConsumerStatusMap.get(chain) == RUNNING
            )
            // all consumers to stop must be running right now, else we have an error
            if (consumersToStop.exclude(runningConsumers).size() > 0) {
                (currentConsumerStatusMap, "Cannot stop a consumer that is not running")
            } else {
                val newConsumerStatusMap = currentConsumerStatusMap.keys().mapBy(
                    (chain) => 
                    if (consumersToTimeout.contains(chain)) {
                        TIMEDOUT
                    } else if (consumersToStop.contains(chain)) {
                        STOPPED
                    } else {
                        currentConsumerStatusMap.get(chain)
                    }
                )
                (newConsumerStatusMap, "")
            }
        }
        
    // Returns the new ConsumerStatusMap according to the consumers to start.
    // The second return is an error string: If it is not equal to "",
    // it contains an error message, and the first return should be ignored.
    pure def startConsumers(
        currentConsumerStatusMap: Chain -> str,
        consumersToStart: Set[Chain]): (Chain -> str, str) = {
            val nonConsumers = currentConsumerStatusMap.keys().filter(
                chain => currentConsumerStatusMap.get(chain) == NOT_CONSUMER
            )
            // all consumers to start must be nonConsumers right now, otherwise we have an error
            if (consumersToStart.exclude(nonConsumers).size() > 0) {
                (currentConsumerStatusMap, "cannot start a consumer that is stopped or already a consumer")
            } else {
                val newConsumerStatusMap = currentConsumerStatusMap.keys().mapBy(
                    (chain) => 
                    if (consumersToStart.contains(chain)) {
                        RUNNING
                    } else {
                        currentConsumerStatusMap.get(chain)
                    }
                )
                (newConsumerStatusMap, "")
            }
        }

    pure def StartStopConsumers(
        currentProviderState: ProviderState,
        consumersToStart: Set[ConsumerAdditionMsg],
        consumersToStop: Set[Chain],
        consumersToTimeout: Set[Chain]
    ): (ProviderState, str) = {
        val consumerAdditions = consumersToStart.map(
                msg => msg.chain
        )
        // check if any consumer is both started and stopped
        if (consumerAdditions.intersect(consumersToStop).size() > 0) {
            (currentProviderState, "Cannot start and stop a consumer at the same time")
        } else {
            val res1 = currentProviderState.consumerStatus.startConsumers(consumerAdditions)
            val newConsumerStatus = res1._1
            val err1 = res1._2
            val res2 = newConsumerStatus.stopConsumers(consumersToStop, consumersToTimeout)
            val err2 = res2._2
            // set the top N values in the provider correctly

            if (err1 != "") {
                (currentProviderState, err1)
            } else if (err2 != "") {
                (currentProviderState, err2)
            } else {
                (currentProviderState
                    .with("consumerStatus", res2._1)
                    .SetTopNValues(consumersToStart), "")
            }
        }
    }


    // Takes the currentValidatorPowers and puts it as the newest set of the voting history,
    // omitting any validators that are jailed.
    pure def enterCurValSetIntoBlock(chainState: ChainState): ChainState = {
        chainState.with(
            "votingPowerHistory", chainState.votingPowerHistory.prepend(
                chainState.currentValidatorPowers.filterJailedVals(
                    chainState.jailedUntil.keys()
                )
            )
        )
    }

    pure def filterJailedVals(
        valSet: ValidatorSet,
        jailedValidators: Set[Node]
    ): ValidatorSet = {
        valSet.mapRemoveAll(jailedValidators)
    }

    // Advances the timestamp in the chainState by timeAdvancement
    pure def advanceTime(chainState: ChainState, timeAdvancement: Time): ChainState = 
    {
        ...chainState,
        lastTimestamp: chainState.runningTimestamp,
        runningTimestamp: chainState.runningTimestamp + timeAdvancement,
    }

    pure def incrementBlockHeight(chainState: ChainState): ChainState = 
    {
        chainState.with(
            "currentBlockHeight", chainState.currentBlockHeight + 1
        )
    }

    // common logic to update the chain state, used by both provider and consumers.
    pure def endAndBeginBlockShared(chainState: ChainState, timeAdvancement: Time): ChainState = {
        chainState.enterCurValSetIntoBlock().advanceTime(timeAdvancement).incrementBlockHeight()
    }

    // returns the providerState with the following modifications:
    // * sends VscPackets to all running consumers, using the provided timestamp as sending time
    // * increments the runningVscId
    // This should only be called when the provider chain is ending a block.
    // If no vsc packets need to be sent, this will be a noop.
    // the ccv timeout should be the ccv timeout for the provider chain.
    pure def sendVscPackets(
        providerState: ProviderState,
        sendingTimestamp: Time,
        ccvTimeout: Time): ProviderState = {
        val newSentPacketsPerConsumer = providerState.getConsumers().mapBy( // compute, for each consumer, a list of new packets to be sent
            (consumer) => 
            // if validator set changed or the key assignments for this chain changed, and the consumer is running, send a packet
            if ((providerState.consumersWithPowerChangesInThisEpoch.contains(consumer) or 
                providerState.consumersWithAddrAssignmentChangesInThisEpoch.contains(consumer))
                and 
                isRunningConsumer(consumer, providerState)) {
                    // send a packet, i.e. use a list with one element (the packet to be sent)
                List({
                        id: providerState.runningVscId,
                        // apply key assignment to the current validator set
                        validatorSet: providerState.applyKeyAssignmentToValSet(
                            consumer, 
                            providerState.chainState.votingPowerHistory.head()
                        ),
                        sendingTime: sendingTimestamp,
                        timeoutTime: sendingTimestamp + ccvTimeout,
                        downtimeSlashAcks: providerState.downtimeSlashRequests.getOrElse(consumer, [])
                })
            } else {
                // no packet to be sent, so empty list
                List()
            }
        )
        val newOutstandingPacketsToConsumer = providerState.getConsumers().mapBy(
                (consumer) => 
                providerState.outstandingPacketsToConsumer.getOrElse(consumer, List()).concat(
                    newSentPacketsPerConsumer.get(consumer).VscPacketListToPacketList()
                )
            )
        val newSentVscPackets = providerState.getConsumers().mapBy(
                    (consumer) => 
                    providerState.sentVscPacketsToConsumer.getOrElse(consumer, List()).concat(
                        newSentPacketsPerConsumer.get(consumer)
                    )
                )
        {
            ...providerState,
            outstandingPacketsToConsumer: newOutstandingPacketsToConsumer,
            sentVscPacketsToConsumer: newSentVscPackets,
            runningVscId: providerState.runningVscId + 1,
            // we ended the block and processed that the valset or key assignments changed,
            // so reset the flags
            consumersWithPowerChangesInThisEpoch: Set(),
            consumersWithAddrAssignmentChangesInThisEpoch: Set(),
            // remember the key assignments that were applied to send the packets
            keyAssignmentsForVSCPackets: providerState.keyAssignmentsForVSCPackets.put(
                providerState.runningVscId,
                providerState.validatorToConsumerAddr
            )
        }
    }

    pure def recvPacketOnConsumer(
        currentState: ProtocolState,
        sender: Chain,
        packet: Packet,
        receiverUnbondingPeriod: Time): Result = {
        if (not(isRunningConsumer(sender, currentState.providerState))) {
            Err("Sender is not currently a consumer - must have 'running' status!")
        } else {
            match packet {
                | Vsc(p) => recvVscPacketOnConsumer(currentState, sender, p, receiverUnbondingPeriod)
                | _ => Err("Do not know how to handle this packet type")
            }
        }
    }

    // receives a given packet (sent by the provider) on the consumer. The arguments are the consumer chain that is receiving the packet, and the packet itself,
    // as well as the unbonding period for the consumer chain.
    // To receive a packet, modify the running validator set (not the one entered into the block yet,
    // but the candidate that would be put into the block if it ended now)
    // and store the maturation time for the packet.
    pure def recvVscPacketOnConsumer(
        currentState: ProtocolState,
        receiver: Chain,
        packet: VscPacket,
        receiverUnbondingPeriod: Time): Result = {
        if(not(isRunningConsumer(receiver, currentState.providerState))) {
            Err("Receiver is not currently a consumer - must have 'running' status!")
        } else {
            // update the running validator set, but not the history yet,
            // as that only happens when the next block is started
            val currentConsumerState: ConsumerState = currentState.consumerStates.get(receiver)
            val newConsumerState: ConsumerState = 
                {
                    ...currentConsumerState,
                    chainState: currentConsumerState.chainState.with(
                        "currentValidatorPowers", packet.validatorSet
                    ),
                    maturationTimes: currentConsumerState.maturationTimes.append(
                        (
                            packet, 
                            currentConsumerState.chainState.runningTimestamp + receiverUnbondingPeriod
                        )
                    ),
                    receivedVscPackets: currentConsumerState.receivedVscPackets.prepend(packet),
                    outstandingDowntime: currentConsumerState.outstandingDowntime.filter(
                        validator => not(packet.downtimeSlashAcks.toSet().contains(validator))
                    )
                }
            val newConsumerStates = currentState.consumerStates.set(receiver, newConsumerState)
            val newState = currentState.with(
                "consumerStates", newConsumerStates
            )
            Ok(newState)
        }
    }

    // removes the oldest outstanding packet from the consumer. on-chain, this would happen when the packet is acknowledged.
    // only the oldest packet can be removed, since we model ordered channels.
    pure def removeOutstandingPacketFromConsumer(currentState: ProtocolState, sender: Chain): ProtocolState = {
        val currentOutstandingPackets = currentState.consumerStates.get(sender).outstandingPacketsToProvider
        val newOutstandingPackets = currentOutstandingPackets.tail()
        val newConsumerState = currentState.consumerStates.get(sender).with(
            "outstandingPacketsToProvider", newOutstandingPackets
        )
        val newConsumerStates = currentState.consumerStates.set(sender, newConsumerState)
        val newState = currentState.with(
            "consumerStates", newConsumerStates
        )
        newState
    }

    // removes the oldest outstanding packet (to the given consumer) from the provider.
    // on-chain, this would happen when the packet is acknowledged.
    // only the oldest packet can be removed, since we model ordered channels.
    pure def removeOutstandingPacketFromProvider(currentState: ProtocolState, receiver: Chain): ProtocolState = {
        val currentOutstandingPackets = currentState.providerState.outstandingPacketsToConsumer.get(receiver)
        val newOutstandingPackets = currentOutstandingPackets.tail()
        val newProviderState = currentState.providerState.with(
            "outstandingPacketsToConsumer", 
            currentState.providerState.outstandingPacketsToConsumer.set(receiver, newOutstandingPackets)
        )
        val newState = currentState.with(
            "providerState", newProviderState
        )
        newState
    }

    // Returns a ProtocolState where the current validator set on the provider is set to 
    // newValidatorSet.
    pure def setProviderValidatorSet(currentState: ProtocolState, newValidatorSet: ValidatorSet): ProtocolState = {
        pure val newChainState = currentState.providerState.chainState.with(
            "currentValidatorPowers", newValidatorSet
        )
        currentState.with(
            "providerState", 
                currentState.providerState.with(
                    "chainState", newChainState
            )
        )
    }

    // Returns true if the given chain is currently a running consumer, false otherwise.
    pure def isRunningConsumer(chain: Chain, providerState: ProviderState): bool = {
        val status = providerState.consumerStatus.get(chain)
        status == RUNNING
    }

    // Returns the set of all consumer chains.
    pure def getConsumers(providerState: ProviderState): Set[Chain] = providerState.consumerStatus.keys()

    // Returns the set of all consumer chains that currently have the status RUNNING.
    pure def getRunningConsumers(providerState: ProviderState): Set[Chain] = {
        providerState.consumerStatus.keys().filter(
            chain => providerState.consumerStatus.get(chain) == RUNNING
        )
    }

    // Returns the set of all consumer chains that currently have the status NOT_CONSUMER.
    pure def getNonConsumers(providerState: ProviderState): Set[Chain] = {
        providerState.consumerStatus.keys().filter(
            chain => providerState.consumerStatus.get(chain) == NOT_CONSUMER
        )
    }

    // Returns whether the consumer has timed out due to the vscTimeout, and an error message.
    // If the second return is not equal to "", the first return should be ignored.
    // If it is equal to "", the first return will be true if the consumer has timed out and should be dropped,
    // or false otherwise.
    pure def TimeoutDueToVscTimeout(currentState: ProtocolState, consumer: Chain, vscTimeout: Time): (bool, str) =
        // check for errors: the consumer is not running
        if (not(isRunningConsumer(consumer, currentState.providerState))) {
            (false, "Consumer is not currently a consumer - must have 'running' status!")
        } else {
            val providerState = currentState.providerState
            val consumerState: ConsumerState = currentState.consumerStates.get(consumer)

            // has a packet been sent on the provider more than vscTimeout ago, but we have not received an answer since then?
            val sentVscPacketsToConsumer = providerState.sentVscPacketsToConsumer.getOrElse(consumer, List())
            if(sentVscPacketsToConsumer.length() > 0) {
                val oldestSentVscPacket = sentVscPacketsToConsumer.head() // if length is 0, this is undefined, but we check for this before we use it
                if(oldestSentVscPacket.sendingTime + vscTimeout < providerState.chainState.runningTimestamp) {
                    (true, "")
                } else {
                    // no timeout yet, it has not been vscTimeout since that packet was sent
                    (false, "")
                }
            } else {
                // no packet has been sent yet, so no timeout
                (false, "")
            }
        }

    // Sets the top N values on the provider chain for the given consumer chains,
    // taken as consumerAdditionMsgs = chains with the top N values.
    // If a chain in the set is already present, the old value will be overwritten.
    pure def SetTopNValues(providerState: ProviderState, consumers: Set[ConsumerAdditionMsg]): ProviderState =
        providerState.with(
            "topNByConsumer",
            consumers.fold(
                providerState.topNByConsumer,
                (acc, consumer) => acc.put(consumer.chain, consumer.topN)
            )
        ) 

    // From a validator set, removes all validators with zero power.
    pure def removeZeroPowers(valSet: ValidatorSet): ValidatorSet =
        valSet.keys().fold(
            Map(),
            (acc, node) => 
                if (valSet.get(node) == 0) {
                    acc
                } else {
                    acc.put(node, valSet.get(node))
                }
        )
    // Transforms a list of VscPackets into a list of the generic
    // "packet" type.
    pure def VscPacketListToPacketList(original: List[VscPacket]): List[Packet] =
        original.listMap(
            elem => Vsc(elem)
        )

    pure def GetPacketTimeout(packet: Packet): Time = {
        match packet {
            | Vsc(p) => p.timeoutTime
            | Slash(p) => p.timeoutTime
            | VscMatured(p) => p.timeoutTime
            | _ => 0
        }
    }

    pure def GetPacketSendingTime(packet: Packet): Time = {
        match packet {
            | Vsc(p) => p.sendingTime
            | Slash(p) => p.sendingTime
            | VscMatured(p) => p.sendingTime
            | _ => 0
        }
    }

    pure def IsVscPacket(packet: Packet): bool = {
        match packet {
            | Vsc(_) => true
            | _ => false
        }
    }

    pure def IsSlashPacket(packet: Packet): bool = {
        match packet {
            | Slash(_) => true
            | _ => false
        }
    }

    pure def IsVscMaturedPacket(packet: Packet): bool = {
        match packet {
            | VscMatured(_) => true
            | _ => false
        }
    }

    // Commits a packet on the consumer, which will then be sent when a block is ended.
    // Internally, prepends the packet to the senders packetsToSendOnEndBlock list.
    pure def commitPacketOnConsumer(senderState: ConsumerState, packet: Packet): ConsumerState = {
        senderState.with(
            "queuedPackets", senderState.queuedPackets.append(packet)
        )
    }

    // Jails a validator until the given time.
    // Note that they are not automatically unjailed afterwards,
    // this must be done by another action. (TODO: currently not implemented)
    pure def jailUntil(
        providerState: ProviderState,
        validator: Node,
        jailEndTime: Time
    ): ProviderState = {
        val newChainState = providerState.chainState.with(
            "jailedUntil", providerState.chainState.jailedUntil.put(validator, jailEndTime)
        )
        providerState.with(
            "chainState", newChainState
        )
    }

    // Slahes a given validator by the given percentage of the given power.
    // The provided power is typically the power of the validator
    // at the time of the infraction for which this slashes.
    // The slash percentage should be a number between 0 and 100.
    // Note that nodes cannot end up with negative power,
    // so if their voting power is smaller than power * slashPercentage / 100,
    // they will be set to 0.
    pure def slash(
        providerState: ProviderState,
        validator: Node,
        power: int,
        slashPercentage: int
    ): ProviderState = {
        val slashAmount = power * slashPercentage / 100
        val newChainState = providerState.chainState.with(
            "currentValidatorPowers",
            providerState.chainState.currentValidatorPowers.keys().mapBy(
                node =>
                val oldPower = providerState.chainState.currentValidatorPowers.get(node) 
                if (node == validator) {
                    max(0, oldPower - slashAmount)
                } else {
                    oldPower
                }
            )
        )
        providerState.with(
            "chainState", newChainState
        )
    }

    // Returns the set of all nodes that are not currently jailed on the provider.
    pure def nonJailedNodes(
        providerState: ProviderState
    ): Set[Node] = {
        providerState.chainState.currentValidatorPowers.keys().filter(
            node => not(providerState.chainState.jailedUntil.keys().contains(node))
        )
    }

    pure def IsEmptyValSet(valSet: ValidatorSet): bool = {
        valSet.keys().filter(
            node => valSet.get(node) > 0
        ).size() == 0
    }

    pure def ProviderBlockTime(currentState: ProtocolState): Time = {
        currentState.providerState.chainState.runningTimestamp
    }


}