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


Init == 
    /\ actionKind = "Init"
    /\ nextVSCId = 0
    /\ nextConsumerId = 0
    /\ initialisingConsumers = {}
    /\ activeConsumers = {}
    /\ awaitedVSCIds = {}

EndBlock == 

SetKey ==

ReceiveSlash == 

ReceiveMaturity ==

Next == 
    \/ EndBlock
    \/ SetKey
    \/ ReceiveSlash
    \/ ReceiveMaturity

\* When a validator had a positive power on the consumer, it was slashable up until UNBONDING_PERIOD later
Inv == 

====
