--------------------------- MODULE CCV ---------------------------

EXTENDS Integers, Apalache, Variants, typedefs

CONSTANT 
  \* @type: Set($validator);
  Validators,
  \* @type: $validator -> $power;
  PowerInit, \* assume DOMAIN PowerInit == Validators
  \* @type: Set($chain);
  ConsumerChainsInit, 
  \* @type: Set($chain);
  AllConsumerChains, 
  \* @type: $height;
  MaturityDelay,
  \* @type: $height;
  MaxHeight

CInit == 
  LET Vs == {"1_OF_V", "2_OF_V", "3_OF_V"} IN
  /\ Validators = Vs
  /\ PowerInit = [v \in Vs |-> 10]
  /\ ConsumerChainsInit = {"1_OF_C", "2_OF_C"}
  /\ AllConsumerChains = {"1_OF_C", "2_OF_C", "3_OF_C"}
  /\ MaturityDelay = 2
  /\ MaxHeight = 10


Heights == 0 .. MaxHeight

\* Provider chain ID, assumed to be distinct from all consumer chain IDs
ProviderChain == "provider_OF_C"

Chains == AllConsumerChains \union {ProviderChain}

(* 
Consumer chain variables:
  votingPowerAtHeight - for each trio of (C, H, V), defines the voting
  power of validator V on chain C at height H.
  "removed" validators are modeled as having power 0.
  Due to communication delays, votingPowerAtHeight[c,h,v], for a given 
  consumer chain c, may differ from votingPowerAtHeight[provider, h v], 
  but must be equal to votingPowerAtHeight[provider, hh, v] for some hh < h.

  messages - a history of sent messages. Channels are implicitly encoded
  in the message format.
*)
VARIABLES
  \* @type: $votingPower;
  votingPower,
  \* @type: Set($message);
  messages,
  \* @type: Set($chain);
  activeConsumers,
  \* @type: $chain -> $height;
  heights,
  \* @type: $id;
  nextId



Init == 
  /\ votingPower = [chain \in Chains |-> PowerInit]
  /\ messages = {}
  /\ activeConsumers = ConsumerChainsInit
  /\ heights = [chain \in Chains |-> 0]
  /\ nextId = 0

\* @type: ($message) => Bool;
Send(msg) == messages' = messages \union {msg}

\* @type: ($validator, $height, $power, $id) => $message;
UndelegateInit(v, h, pow, id) == 
  Variant("UndelegateInit", [validator |-> v, height |-> h, powerReduction |-> pow, id |-> id])
\* @type: ($validator, $validator, $height, $power, $id) => $message;
RedelegateInit(src, dest, h, pow, id) == 
  Variant("RedelegateInit", [src |-> src, dest |-> dest, height |-> h, powerDelta |-> pow, id |-> id])
\* @type: ($validator, $height, $id) => $message;
UnbondInit(v, h, id) == 
  Variant("UnbondInit", [validator |-> v, height |-> h, id |-> id])

\* @type: ($chain, $id, $height) => $ack;
Ack(c, id, h) == [chain |-> c, id |-> id, height |-> h]
\* @type: ($chain, $id, $height) => $message;
UndelegateAck(c, id, h) == Variant("UndelegateAck", Ack(c, id, h))
\* @type: ($chain, $id, $height) => $message;
RedelegateAck(c, id, h) == Variant("RedelegateAck", Ack(c, id, h))
\* @type: ($chain, $id, $height) => $message;
UnbondAck(c, id, h) == Variant("UnbondAck", Ack(c, id, h))

AdvanceId == 
  \E n \in Int:
    /\ n > nextId
    /\ nextId' = n

StartUndelegate == 
  \E v \in Validators:
    /\ votingPower[ProviderChain][v] > 0 \* Only active validators can undelegate
    /\ \E reduction \in Int:
      /\ 0 < reduction 
      /\ reduction < votingPower[ProviderChain][v] \* strictly <, otherwise unbond
      /\ votingPower' = [votingPower EXCEPT ![ProviderChain][v] = @ - reduction]
      /\ Send(UndelegateInit(v, heights[ProviderChain], reduction, nextId))
    /\ AdvanceId
    /\ UNCHANGED <<activeConsumers, heights>>

StartRedelegate == 
  \E src, dest \in Validators:
    /\ src /= dest
    /\ votingPower[ProviderChain][src] > 0 \* Only active validators can redelegate
    /\ \E delta \in Int:
      /\ 0 < delta 
      /\ delta < votingPower[ProviderChain][src] \* strictly <, otherwise unbond
      /\ votingPower' = [votingPower EXCEPT 
        ![ProviderChain][src] = @ - delta,
        ![ProviderChain][dest] = @ + delta
        ]
      /\ Send(RedelegateInit(src, dest, heights[ProviderChain], delta, nextId))
    /\ AdvanceId
    /\ UNCHANGED <<activeConsumers, heights>>

StartUnbond == 
  \E v \in Validators:
    /\ votingPower[ProviderChain][v] > 0 \* Only active validators can unbond
    /\ votingPower' = [votingPower EXCEPT ![ProviderChain][v] = 0]
    /\ Send(UnbondInit(v, heights[ProviderChain], nextId))
    /\ \E n \in Int:
      /\ n > nextId
      /\ nextId' = n
    /\ UNCHANGED <<activeConsumers, heights>>

AckUndelegate == 
  \E c \in activeConsumers:
    \E undelegate \in VariantFilter("UndelegateInit",messages):
      /\ \A ack \in VariantFilter("UndelegateAck",messages):
        \/ ack.chain /= c
        \/ ack.id /= undelegate.id
      /\ votingPower' = [votingPower EXCEPT ![c][undelegate.validator] = @ - undelegate.powerReduction]
      \* The voting power decreases immediately, but the ack message contains
      \* the height at which the VSC will mature 
      /\ Send(UndelegateAck(c, undelegate.id, heights[c] + MaturityDelay))
      /\ UNCHANGED <<activeConsumers, heights, nextId>>

AckRedelegate == 
  \E c \in activeConsumers:
    \E redelegate \in VariantFilter("RedelegateInit",messages):
      /\ \A ack \in VariantFilter("RedelegateAck",messages):
        \/ ack.chain /= c
        \/ ack.id /= redelegate.id
      /\ votingPower' = [votingPower EXCEPT 
        ![c][redelegate.src] = @ - redelegate.powerDelta,
        ![c][redelegate.dest] = @ + redelegate.powerDelta
        ]
      \* The voting power decreases immediately, but the ack message contains
      \* the height at which the VSC will mature 
      /\ Send(RedelegateAck(c, redelegate.id, heights[c] + MaturityDelay))
      /\ UNCHANGED <<activeConsumers, heights, nextId>>

AckUnbond == 
  \E c \in activeConsumers:
    \E unbond \in VariantFilter("UnbondInit",messages):
      /\ \A ack \in VariantFilter("UnbondAck",messages):
        \/ ack.chain /= c
        \/ ack.id /= unbond.id
      /\ votingPower' = [votingPower EXCEPT ![c][unbond.validator] = 0]
      \* The voting power decreases immediately, but the ack message contains
      \* the height at which the VSC will mature 
      /\ Send(UnbondAck(c, unbond.id, heights[c] + MaturityDelay))
      /\ UNCHANGED <<activeConsumers, heights, nextId>>


AdvanceHeight ==
  \E c \in Chains:
    \E h \in Int:
      /\ h > heights[c]
      /\ h < MaxHeight
      /\ heights' = [heights EXCEPT ![c] = h]
      /\ UNCHANGED <<activeConsumers, messages, votingPower, nextId>>

UndelegationInProgress == 
  \E undelegate \in VariantFilter("UndelegateInit",messages):
    LET h == undelegate.height
        v == undelegate.validator 
        id == undelegate.id IN 
    \* At least one consumer chain has not sent an ack, OR
    \* the ack has been sent, but the VCS hasn't matured yet
    \/ \E c \in activeConsumers: 
      \A ack \in VariantFilter("UndelegateAck",messages):
        \/ ack.chain /= c
        \/ ack.id /= id
        \/ heights[c] < ack.height \* no maturity
    \* Undelegation period hasn't elapsed 
    \/ heights[ProviderChain] - h < MaturityDelay \* height > h

RedelegationInProgress == 
  \E redelegate \in VariantFilter("RedelegateInit",messages):
    LET h == redelegate.height
        src == redelegate.src 
        dest == redelegate.dest
        id == redelegate.id IN 
    \* At least one consumer chain has not sent an ack, OR
    \* the ack has been sent, but the VCS hasn't matured yet
    \/ \E c \in activeConsumers: 
      \A ack \in VariantFilter("RedelegateAck",messages):
        \/ ack.chain /= c
        \/ ack.id /= id
        \/ heights[c] < ack.height \* no maturity
    \* Redelegation period hasn't elapsed 
    \/ heights[ProviderChain] - h < MaturityDelay \* height > h

UnbondingInProgress == 
  \E unbond \in VariantFilter("UnbondInit",messages):
    LET h == unbond.height
        v == unbond.validator 
        id == unbond.id IN 
    \* At least one consumer chain has not sent an ack, OR
    \* the ack has been sent, but the VCS hasn't matured yet
    \/ \E c \in activeConsumers: 
      \A ack \in VariantFilter("UnbondAck",messages):
        \/ ack.chain /= c
        \/ ack.id /= id
        \/ heights[c] < ack.height \* no maturity
    \* Unbonding period hasn't elapsed 
    \/ heights[ProviderChain] - h < MaturityDelay \* height > h


ActiveVPC ==
  \/ UndelegationInProgress
  \/ RedelegationInProgress
  \/ UnbondingInProgress
  
AgreementOnPower == 
  \A c \in activeConsumers:
    votingPower[c] = votingPower[ProviderChain]

Next == 
  \/ AdvanceHeight
  \/ StartUndelegate
  \/ StartRedelegate
  \/ StartUnbond
  \/ AckUndelegate
  \/ AckRedelegate
  \/ AckUnbond

Inv == 
  ~ActiveVPC => AgreementOnPower


=============================================================================