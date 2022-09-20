---- MODULE main ----

EXTENDS Integers, FiniteSets, Sequences, TLC, Apalache

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
    Power

CInit == 
    /\ LKS = {"lk0", "lk1", "lk2"}
    /\ FKS = {"fk0", "fk1", "fk2", "fk3", "fk4", "fk5", "fk6", "fk7", "fk8"}
    /\ MAPPINGS = { f \in [LKS -> FKS] : ~ (\E a, b \in DOMAIN f : f[a] = f[b]) }
    /\ POWERS = [ LKS -> 0..2 ]

Init == 
    /\ Action = [kind |-> "none"]
    /\ Mapping \in MAPPINGS
    /\ Power \in POWERS

EndBlock == 
    \E m \in MAPPINGS, p \in POWERS : 
    /\ UNCHANGED Action
    /\ Mapping' = m 
    /\ Power' = p

Next == 
    \/ EndBlock
    \/ TRUE

Inv == TRUE

====
