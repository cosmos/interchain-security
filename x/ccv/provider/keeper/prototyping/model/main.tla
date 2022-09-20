---- MODULE main ----

EXTENDS Integers, FiniteSets, Sequences, TLC, Apalache
\* EXTENDS Integers, FiniteSets, Sequences, TLC

(*

    @typeAlias: action = { kind : Str };
    @typeAlias: lk = Str;
    @typeAlias: fk = Str;
    @typeAlias: mapping = $lk -> $fk;
    @typeAlias: power = $lk -> Int;

*)

TypeAliases == TRUE

CONSTANTS
    \* @type: Set($lk);
    LKS,
    \* @type: Set($fk);
    FKS,
    \* @type: Set($mapping);
    MAPPINGS,
    \* @type: Set($power);
    POWERS 

VARIABLES
    \* @type: $action;
    Action,
    \* @type: $mapping;
    Mapping,
    \* @type: $power;
    Power,
    \* @type: Int;
    TP,
    \* @type: Int;
    TC,
    \* @type: Int;
    TM


CInit == 
    /\ LKS = {"lk0", "lk1", "lk2"}
    /\ FKS = {"fk0", "fk1", "fk2", "fk3", "fk4", "fk5", "fk6", "fk7", "fk8"}
    /\ MAPPINGS = [LKS -> FKS]
    /\ POWERS = [ LKS -> 0..2 ]

Init == 
    \E m \in MAPPINGS : 
    /\ \A a, b \in DOMAIN m : a = b \/ m[a] # m[b]
    /\ Action = [kind |-> "none"]
    /\ Mapping = m
    /\ Power \in POWERS
    /\ TP = 1
    /\ TC = 0
    /\ TM = 0

EndBlock == 
    \E m \in MAPPINGS, p \in POWERS : 
    /\ \A a, b \in DOMAIN m : a = b \/ m[a] # m[b]
    /\ UNCHANGED Action
    /\ Mapping' = m
    /\ Power' = p
    /\ TP' = TP + 1
    /\ UNCHANGED TC
    /\ UNCHANGED TM

UpdateConsumer == 
    \E t \in (TC+1)..TP :
    /\ UNCHANGED Action
    /\ UNCHANGED Mapping
    /\ UNCHANGED Power
    /\ UNCHANGED TP
    /\ TC' = t
    /\ UNCHANGED TM

ReceiveMaturities == 
    \E t \in (TM+1)..TC :
    /\ UNCHANGED Action
    /\ UNCHANGED Mapping
    /\ UNCHANGED Power
    /\ UNCHANGED TP
    /\ UNCHANGED TC
    /\ TM' = t

Next == 
    \/ EndBlock
    \/ UpdateConsumer
    \/ ReceiveMaturities

Inv == TRUE

====
