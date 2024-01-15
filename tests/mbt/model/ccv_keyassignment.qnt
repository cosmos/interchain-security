// The functional definition of key assignment.
module ccv_keyassignment {
    import ccv_types.* from "ccv"
    import extraSpells.* from "./libraries/extraSpells"

    // Validator providerNode assigns their address for the consumer to be the consumerAddress.
    pure def assignConsumerKey(currentState: ProtocolState, consumer: Chain, providerNode: Node, consumerAddr: ConsumerAddr): Result = {
        // rule 1: validator A cannot assign consumer key K to consumer chain X
        // if there is already a validator B (B!=A) using K on the provider
        pure val provCurValSet = currentState.providerState.chainState.currentValidatorSet
        if (provCurValSet.keys().exists(node => node != providerNode and node == consumerAddr)) {
            Err("validator A cannot assign consumer key K to consumer chain X
            if there is already a validator B (B!=A) using K on the provider")
        } else {
            // rule 2: validator A cannot assign consumer key K to consumer chain X if
            // there is already a validator B using K on X
            pure val valByConsAddr = currentState.providerState.validatorByConsumerAddr.getOrElse(consumer, Map())
            if (valByConsAddr.keys().contains(consumerAddr)) {
                Err("consumer key is already in use on the consumer chain")
            } else {
                // this key can be assigned
                
                // get the old assigned key
                pure val consKeyByVal = currentState.providerState.validatorConsumerPubKey.getOrElse(consumer, Map())
                pure val p = if (consKeyByVal.keys().contains(providerNode)) {
                    // providerNode had previously assigned a consumer key
                    (consKeyByVal.get(providerNode), true)
                } else {
                    (providerNode, false)
                }
                // the consumer address that was previously associated with the node
                pure val oldConsAddr = p._1
                // whether the old address was explicitly assigned, or the default key
                pure val prevAssigned = p._2
                
                // set the old address for pruning, if it was assigned
                pure val tmpState = if (prevAssigned) {
                    AppendConsumerAddrToPrune(currentState, oldConsAddr, consumer)
                } else {
                    currentState
                }

                // check whether the validator has positive power
                pure val provValSet = currentState.providerState.chainState.currentValidatorSet
                pure val provValPower = if (provValSet.keys().contains(providerNode)) provValSet.get(providerNode) else 0
                pure val newKeyAssignmentReplacement = 
                    if (provValPower > 0 and
                        not(currentState.providerState.keyAssignmentReplacements.
                            getOrElse(consumer, Map()).keys().contains(providerNode))) {
                        // the validator has positive power and is not already in the key assignment replacements
                        currentState.providerState.keyAssignmentReplacements.put(
                            consumer,
                            currentState.providerState.keyAssignmentReplacements.getOrElse(consumer, Map()).put(
                                providerNode,
                                (oldConsAddr, provValPower)
                            )
                        )
                    } else {
                        currentState.providerState.keyAssignmentReplacements
                    
                    }
                pure val tmpStateAfterKeyAssignmentReplacement = tmpState.with(
                    "providerState", tmpState.providerState.with(
                        "keyAssignmentReplacements", newKeyAssignmentReplacement
                    )
                )
                
                pure val newValidatorConsumerPubKey = currentState.providerState.validatorConsumerPubKey.getOrElse(consumer, Map()).put(
                    consumer,
                    currentState.providerState.validatorConsumerPubKey.getOrElse(consumer, Map()).put(
                        providerNode,
                        consumerAddr
                    )
                )

                pure val newValidatorByConsumerAddr = currentState.providerState.validatorByConsumerAddr.getOrElse(consumer, Map()).put(
                    consumer,
                    currentState.providerState.validatorByConsumerAddr.getOrElse(consumer, Map()).put(
                        consumerAddr,
                        providerNode
                    )
                )

                pure val newProviderState = tmpStateAfterKeyAssignmentReplacement.providerState.with(
                    "validatorConsumerPubKey", newValidatorConsumerPubKey
                ).with(
                    "validatorByConsumerAddr", newValidatorByConsumerAddr
                )

                Ok(
                    tmpStateAfterKeyAssignmentReplacement.with(
                        "providerState", newProviderState
                    )
                )
            }
        }
    }

    // Appends the key assignment for the given oldConsAddr on the consumer by a validator
    // to be pruned when a VscMaturedPacket for the current runningVscId is received from the consumer.
    pure def AppendConsumerAddrToPrune(currentState: ProtocolState, oldConsAddr: ConsumerAddr, consumer: Chain): ProtocolState = {
        pure val vscId = currentState.providerState.runningVscId
        pure val consumerAddrsToPrune = currentState.providerState.consumerAddrsToPrune.getOrElse(consumer, Map())
        pure val prevConsAddrs = consumerAddrsToPrune.getOrElse(oldConsAddr, Map()).getOrElse(vscId, [])

        pure val newConsAddrsToPrune = consumerAddrsToPrune.put(vscId, prevConsAddrs.append(oldConsAddr))

        currentState.with(
            "providerState", 
            currentState.providerState.with(
                "consumerAddrsToPrune",
                currentState.providerState.consumerAddrsToPrune.put(consumer, newConsAddrsToPrune)
            )
        )
    }
}