---- MODULE keymap ----

EXTENDS Integers, FiniteSets, Sequences, TLC, Apalache

(*

    @typeAlias: lk = Str;
    @typeAlias: fk = Str;
    @typeAlias: mapping = $lk -> $fk;
    @typeAlias: updates = $lk -> Int;

*)

TypeAliases == TRUE

LKS == {"lk0", "lk1", "lk2"}
FKS == {"fk0", "fk1", "fk2", "fk3", "fk4", "fk5", "fk6", "fk7", "fk8"}

VARIABLES
    \* @type: $mapping;
    Mapping,
    \* @type: $updates;
    Updates,
    \* @type: Int;
    TP,
    \* @type: Int;
    TC,
    \* @type: Int;
    TM

Init == 
    \E m \in [LKS -> FKS], ss \in SUBSET LKS: 
    /\ \A a, b \in DOMAIN m : m[a] = m[b] => a = b
    /\ Mapping = m
    /\ Updates \in [ss -> 0..2]
    /\ TP = 1
    /\ TC = 0
    /\ TM = 0

EndBlock == 
    \E m \in [LKS -> FKS], ss \in SUBSET LKS: 
    /\ \A a, b \in DOMAIN m : m[a] = m[b] => a = b
    /\ Mapping' = m
    /\ Updates' \in [ss -> 0..2]
    /\ TP' = TP + 1
    /\ UNCHANGED TC
    /\ UNCHANGED TM

UpdateConsumer == 
    \E t \in (TC+1)..TP :
    /\ UNCHANGED Mapping
    /\ UNCHANGED Updates
    /\ UNCHANGED TP
    /\ TC' = t
    /\ UNCHANGED TM

ReceiveMaturities == 
    \E t \in (TM+1)..TC :
    /\ UNCHANGED Mapping
    /\ UNCHANGED Updates
    /\ UNCHANGED TP
    /\ UNCHANGED TC
    /\ TM' = t

Next == 
    \/ EndBlock
    \/ UpdateConsumer
    \/ ReceiveMaturities

View == <<Mapping, Updates, TP, TC, TM>>

====
