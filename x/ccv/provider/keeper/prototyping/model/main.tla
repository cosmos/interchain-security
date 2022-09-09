---- MODULE main ----

\* EXTENDS Integers, FiniteSets, Sequences, TLC, Apalache
EXTENDS Integers, FiniteSets, Sequences, TLC

VARIABLES
    \* @type: Str;
    actionKind,
    \* @type: Int;
    nextVSCId,
    \* @type: Int;
    nextConsumerId,
    \* @type: Set(Int);
    initialisingConsumers,
    \* @type: Set(Int); 
    activeConsumers,
    \* Maps consumer -> vscId
    \* @type: Set(<<Int, Int>>);
    awaitedVSCIds

InitConsumer ==
    /\ actionKind' = "InitConsumer"
    /\ UNCHANGED  nextVSCId
    /\ nextConsumerId' = nextConsumerId + 1
    /\ initialisingConsumers' = initialisingConsumers \cup {nextConsumerId}
    /\ UNCHANGED activeConsumers
    /\ UNCHANGED awaitedVSCIds
    
ActivateConsumer == 
    /\ actionKind' = "ActivateConsumer"
    /\ UNCHANGED nextVSCId
    /\ UNCHANGED nextConsumerId
    /\ \E c \in initialisingConsumers:
        /\ initialisingConsumers' = initialisingConsumers \ {c}
        /\ activeConsumers' = activeConsumers \cup {c}
    /\ UNCHANGED awaitedVSCIds

StopConsumer == 
    /\ actionKind' = "StopConsumer"
    /\ UNCHANGED nextVSCId
    /\ UNCHANGED nextConsumerId
    /\  \/ \E c \in initialisingConsumers:
            /\ initialisingConsumers' = initialisingConsumers \ {c}
            /\ UNCHANGED activeConsumers
            /\ UNCHANGED awaitedVSCIds
        \/ \E c \in activeConsumers:
            /\ UNCHANGED initialisingConsumers
            /\ activeConsumers' = activeConsumers \ {c}
            /\ awaitedVSCIds' = {pair \in awaitedVSCIds: pair[1] # c}

(*
After EndBlock the SUT will check that the ref cnts are 0 for every
VSCID that does not appear in awaited, and that ref cnts are positive
for every VSCID that does appear in awaited
*)
EndBlock == 
    /\ actionKind' = "EndBlock"
    /\ nextVSCId' = nextVSCId + 1
    /\ UNCHANGED nextConsumerId
    /\ UNCHANGED initialisingConsumers
    /\ UNCHANGED  activeConsumers
    /\ awaitedVSCIds' = awaitedVSCIds \cup {<<c, nextVSCId>> : c \in activeConsumers}
    
RecvMaturity == 
    /\ actionKind' = "RecvMaturity"
    /\ UNCHANGED nextVSCId
    /\ UNCHANGED nextConsumerId
    /\ UNCHANGED initialisingConsumers
    /\ UNCHANGED activeConsumers
    /\ \E pair \in awaitedVSCIds:
        awaitedVSCIds' = awaitedVSCIds \ {pair} 

Init == 
    /\ actionKind = "Init"
    /\ nextVSCId = 0
    /\ nextConsumerId = 0
    /\ initialisingConsumers = {}
    /\ activeConsumers = {}
    /\ awaitedVSCIds = {}

Next == 
    \/ InitConsumer
    \/ ActivateConsumer 
    \/ StopConsumer
    \/ EndBlock
    \/ RecvMaturity

Inv == \A pair \in awaitedVSCIds : pair[1] \in (initialisingConsumers \cup activeConsumers)

====
