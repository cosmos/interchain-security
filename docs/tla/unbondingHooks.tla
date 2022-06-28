--------------------------- MODULE unbondingHooks ---------------------------

EXTENDS Integers, Sequences, FiniteSets

VARIABLES 
    staking_ubdes,
    staking_ubdeIdCounter,
    ccv_ubdes,
    ccv_valsetIdCounter,
    consumer_unbondingValsets

\* UNCHANGED  <<
\*     staking_ubdes,
\*     staking_ubdeIdCounter,
\*     ccv_ubdes,
\*     ccv_valsetIdCounter,
\*     consumer_unbondingValsets
\* >>

\* "constants" (i don't like having to switch back and forth to the cfg file)
ConsumerChains == { 0, 1, 2 }
MaxUbdeIdCounter == 2
MaxValsetIdCounter == 2

Init ==
    /\ staking_ubdes = {}
    /\ staking_ubdeIdCounter = 0
    /\ ccv_ubdes = {}
    /\ ccv_valsetIdCounter = 0
    /\ consumer_unbondingValsets = [ p \in ConsumerChains |-> <<>> ]

\* Typechecking
StakingUbde == [ onHold: BOOLEAN, unbonded: BOOLEAN, ubdeId: 0..2 ]

\* I don't know how to express the type of unbondingConsumerChains more nicely than this
CcvUbde == [ ubdeId: 0..2, valsetUpdateId: 0..2, unbondingConsumerChains: {{}, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} ]

TypeOK ==
    /\ staking_ubdes \subseteq StakingUbde
    /\ ccv_ubdes     \subseteq CcvUbde

\* Invariants
\* - All consumer chains should eventually finish unbonding all valset updates
\* - No ubdes should be left with unbonded = false
\* - No ubde should have unbonded = true before its valset has been unbonded on all consumers
\* - If all acks have been receieved, 

NoUnbondedProviderBeforeConsumer ==
    \E ubde \in { u \in staking_ubdes: u.unbonded }:
        \E c \in ConsumerChains:
            \E v \in consumer_unbondingValsets[c]:
                ~(ubde.ubdeId = v)

Consumer_ReceiveValsetChangePacket(consumer, valsetUpdateId) ==
    \* consumer receives ValsetChangePacket and adds this valsetId to its unbonding valsets
    consumer_unbondingValsets' = [ consumer_unbondingValsets EXCEPT ![consumer] = Append(consumer_unbondingValsets[consumer], valsetUpdateId) ]

Staking_CompleteStoppedUnbonding(ubdeId) ==
    \* find the staking_ubde with this ubdeId. If it is `onHold`, complete unbonding by setting
    \* `unbonded` to true. This represents giving the user's coins back etc.
    staking_ubdes' = { 
        IF ubde.onHold THEN
            [ ubde EXCEPT !.unbonded = TRUE ]
        ELSE
            ubde
    : ubde \in {u \in staking_ubdes: u.ubdeId = ubdeId} }

CCV_BeforeUBDECompleteHook(id) ==
    \* try to find the ccv_ubde with this id. if it exists, return true
    Cardinality({ ubde \in ccv_ubdes: ubde.ubdeId = id }) > 0

CCV_UBDECreatedHook(id) ==
    /\ ccv_ubdes' = ccv_ubdes \union {[ 
            ubdeId |-> id, 
            valsetUpdateId |-> ccv_valsetIdCounter, 
            unbondingConsumerChains |-> ConsumerChains 
        ]}

CCV_ReceiveValsetChangeAck(consumer, unbondedValsetId) ==
    \* each ccv_ubde which has this `unbondedValsetId` as its `valsetId` has `consumer` removed from its 
    \* `unbondingConsumerChains` list
    LET new_ccv_ubdes == {
        IF ubde.valsetUpdateId = unbondedValsetId THEN
            [ ubde EXCEPT !.unbondingConsumerChains = {
                \*  remove `consumer` from the `unbondingConsumerChains` set
                c \in @: ~(c = consumer)
            } ]
        ELSE
            ubde
    : ubde \in ccv_ubdes } IN

    \* call Staking_CompleteStoppedUnbonding for all ubdes with no more `unbondingConsumerChains`
    /\ \E ubde \in { ubde \in new_ccv_ubdes: Cardinality(ubde.unbondingConsumerChains) = 0 }:
        Staking_CompleteStoppedUnbonding(ubde.ubdeId)

    \* save ccv_ubdes which still have `unbondingConsumerChains`
    /\ ccv_ubdes' = { ubde \in new_ccv_ubdes: Cardinality(ubde.unbondingConsumerChains) > 0 }


Consumer_FinishUnbonding(consumer) ==
    \* the longest-lived valset finishes unbonding
    LET unbondedValsetId == Head(consumer_unbondingValsets[consumer]) IN

    \* avoid erroring if there are none
    /\ Len(consumer_unbondingValsets[consumer]) > 0

    \* ValsetChangeAck is sent by consumer and received by provider
    /\ CCV_ReceiveValsetChangeAck(consumer, unbondedValsetId)

    \* The valset is done unbonding, remove from queue
    /\ consumer_unbondingValsets' = Tail(consumer_unbondingValsets[consumer])

    /\ UNCHANGED  <<
            staking_ubdeIdCounter,
            ccv_valsetIdCounter
        >>

Staking_CompleteUnbonding ==
    \* find the staking_ubde which is unbonding next. Call the CCV_BeforeUBDECompleteHook and
    \* if it returns true, set ubde.onHold true. If it returns false, set ubde.unbonded true
    \* to complete unbonding
    /\ staking_ubdes' = {
        IF CCV_BeforeUBDECompleteHook(ubde.ubdeId) THEN
            [ ubde EXCEPT !.onHold = TRUE ]
        ELSE
            [ ubde EXCEPT !.unbonded = TRUE ]
        : ubde \in staking_ubdes }
    /\ UNCHANGED  <<
            staking_ubdeIdCounter,
            ccv_ubdes,
            ccv_valsetIdCounter,
            consumer_unbondingValsets
        >>

Staking_Undelegate ==
    \* Stop from going forever
    /\ staking_ubdeIdCounter < MaxUbdeIdCounter
    \* Create new UBDE with incremented id
    /\ staking_ubdes' = staking_ubdes \union {[
            ubdeId |-> staking_ubdeIdCounter,
            onHold |-> FALSE,
            unbonded |-> FALSE
        ]}
    \* Tell CCV about it
    /\ CCV_UBDECreatedHook(staking_ubdeIdCounter)
    \* Increment id
    /\ staking_ubdeIdCounter' = staking_ubdeIdCounter + 1
    /\ UNCHANGED  <<
            ccv_valsetIdCounter,
            consumer_unbondingValsets
        >>

Staking_SendValsetChangePacket ==
    \* Stop from going forever
    IF ccv_valsetIdCounter < MaxValsetIdCounter THEN
        \* Send packet to all consumer chains
        \E c \in ConsumerChains:
            Consumer_ReceiveValsetChangePacket(c, ccv_valsetIdCounter)
        
        \* increment valset id counter
        /\ ccv_valsetIdCounter' = ccv_valsetIdCounter + 1
        /\ UNCHANGED  <<
                staking_ubdes,
                staking_ubdeIdCounter,
                ccv_ubdes
            >>
    ELSE
        UNCHANGED  <<
            staking_ubdes,
            staking_ubdeIdCounter,
            ccv_ubdes,
            ccv_valsetIdCounter,
            consumer_unbondingValsets
        >>


Next ==
    \/ Staking_Undelegate
    \/ Staking_SendValsetChangePacket
    \/ Staking_CompleteUnbonding
    \/ \E c \in ConsumerChains: Consumer_FinishUnbonding(c)


=============================================================================
