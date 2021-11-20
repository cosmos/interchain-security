--------------------------- MODULE PaymentChannel ---------------------------

EXTENDS Integers, TLC

VARIABLES 
    packets,
    staking_ubdes,
    staking_ubdeIdCounter,
    \* staking_unbondingUbdes,
    staking_nextUnbondingUbde,
    ccv_ubdes,
    ccv_valsetIdCounter,
    consumer_unbondingValsets,

StakingUbde == [ onHold: BOOLEAN, unbonded: BOOLEAN, ubdeId: 0..2 ]

CcvUbde == [ ubdeId: 0..2, valsetUpdateId: 0..2, unbondingConsumers: 0..2 -> BOOLEAN ]

\* ValsetChangePacket == [ ubdeId: 0..2 ]

\* ValsetChangeAck == [ ubdeId: 0..2 ]

\* This is fixed for now, every validator is on every consumer chain *\
ConsumerChains == { 0, 1, 2 }

\* Init ==
\*     /\ packets = {}
\*     /\ staking_ubdes = {}
\*     /\ ccvUbdes = {}
\*     /\ staking_ubdeIdCounter = 0
\*     /\ ccv_valsetIdCounter = 0

UserStartsUnbonding ==
    /\ staking_ubdes' = staking_ubdes \union {[ ubdeId |-> staking_ubdeIdCounter, onHold |-> FALSE, unbonded |-> FALSE ]}
    \* /\ staking_unbondingUbdes' = Append(staking_unbondingUbdes, staking_ubdeIdCounter)
    /\ UbdeCreatedHook(staking_ubdeIdCounter)
    /\ staking_ubdeIdCounter' = staking_ubdeIdCounter + 1

ValsetChangePacketSent ==
    \E c \in ConsumerChains:
        \* consumer receives ValsetChangePacket and adds this valsetId to its unbonding valsets
        /\ consumer_unbondingValsets[c] = Append(consumer_unbondingValsets, ccv_valsetIdCounter)
        \* increment valset id counter
        /\ ccv_valsetIdCounter' = ccv_valsetIdCounter + 1

ValsetChangeAckSent(consumer) ==
    \* the longest-lived valset finishes unbonding
    LET unbondedValsetId == Head(consumer_unbondingValsets) IN
    \* ValsetChangeAck is sent by consumer and received by provider

    \* each ccv_ubde which has this `unbondedValsetId` as its `valsetId` has `consumer` removed from its 
    \* `unbondingConsumers` list
    LET new_ccv_ubdes = {
        IF ubde.valsetId = unbondedValsetId THEN
            [ ubde EXCEPT !.unbondingConsumers = { c \in !.unbondingConsumers: c ~= consumer } ]
        ELSE
            ubde
    : ubde \in ccv_ubdes }

    \* call CompleteStoppedUnbonding for all ubdes with no more `unbondingConsumers`
    \E ubde \in { ubde \in new_ccv_ubdes: Cardinality(ubde.unbondingConsumers) = 0 }:
        CompleteStoppedUnbonding(ubde.ubdeId)

    \* save ccv_ubdes which still have `unbondingConsumers`
    ccv_ubdes' = { ubde \in new_ccv_ubdes: Cardinality(ubde.unbondingConsumers) > 0 }

CompleteStoppedUnbonding(ubdeId) ==
    \* find the staking_ubde with this ubdeId. If it is `onHold`, complete unbonding by setting
    \* `unbonded` to true. This represents giving the user's coins back etc.
    staking_ubdes' = { 
        IF ubde.onHold THEN
            [ ubde EXCEPT !.unbonded = TRUE ]
        ELSE
            ubde
    : ubde \in staking_ubdes }

ProviderUnbondingFinished() ==
    \* find the staking_ubde which is unbonding next. Call the BeforeUBDECompleteHook and
    \* if it returns true, set ubde.onHold true. If it returns false, set ubde.unbonded true
    \* to complete unbonding
    staking_ubdes' = {
        IF BeforeUBDECompleteHook(ubde.ubdeId) THEN
            [ ubde EXCEPT !.onHold = TRUE ]
        ELSE
            [ ubde EXCEPT !.unbonded = TRUE ]
    : ubde \in staking_ubdes }

BeforeUBDECompleteHook(id) ==
    \* try to find the ccv_ubde with this id. if it exists, return true
    Cardinality({ ubde \in ccv_ubdes: ubde.ubdeId = id }) > 0

UbdeCreatedHook(id) ==
    /\ ccvUbdes' = ccvUbdes \union {[ ubdeId |-> id, valsetUpdateId |-> ccv_valsetIdCounter, unbondingConsumerChains |-> ConsumerChains ]}

    