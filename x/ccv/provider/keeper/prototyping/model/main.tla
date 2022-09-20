---- MODULE main ----

EXTENDS Integers, FiniteSets, Sequences, TLC, Apalache
\* EXTENDS Integers, FiniteSets, Sequences, TLC

(*

    @typeAlias: ACTION = [ kind : Str ];
    @typeAlias: LK = Str;
    @typeAlias: FK = Str;
    @typeAlias: MAPPING = LK -> FK;
    @typeAlias: POWER = LK -> Int;

*)

VARIABLES
    \* @type: ACTION;
    action,
    \* @type: MAPPING;
    mapping,
    \* @type: POWER;
    power

\* @type: () => Set(LK);
LKS == {"lk0", "lk1", "lk2"}

\* @type: () => Set(FK);
FKS == {"fk0", "fk1", "fk2", "fk3", "fk4", "fk5", "fk6", "fk7", "fk8"}

\* @type: () => Set(MAPPING);
Mappings == { f \in [LKS -> FKS] : ~ (\E a, b \in DOMAIN f : f[a] = f[b]) }

\* @type: () => Set(POWER);
Powers == [ LKS -> 0..2 ]


Init == 
    /\ action = [kind |-> "none"]
    /\ mapping \in Mappings
    /\ power \in Powers

EndBlock == 
    \E m \in Mappings, p \in Powers : 
    /\ UNCHANGED action
    /\ mapping' = m 
    /\ power' = p

Next == 
    \/ EndBlock
    \/ TRUE

Inv == TRUE

====
