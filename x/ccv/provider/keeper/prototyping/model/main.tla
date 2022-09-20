---- MODULE main ----

EXTENDS Integers, FiniteSets, Sequences, TLC, Apalache
\* EXTENDS Integers, FiniteSets, Sequences, TLC

(*

@typeAlias: Action = [ kind : Str, ... ];
@typeAlias: Pair = [ lk : Str, fk : Str ];
@typeAlias: LK = Str;
@typeAlias: FK = Str;
@typeAlias: Mapping = LK -> FK;

*)

LKS = 

Pairs == {
    [ lk : "lk0", fk : "fk0-0" ],
    [ lk : "lk0", fk : "fk0-1" ],
    [ lk : "lk0", fk : "fk0-2" ],
    [ lk : "lk1", fk : "fk1-0" ],
    [ lk : "lk1", fk : "fk1-1" ],
    [ lk : "lk1", fk : "fk1-2" ],
    [ lk : "lk2", fk : "fk2-0" ],
    [ lk : "lk2", fk : "fk2-1" ],
    [ lk : "lk2", fk : "fk2-2" ]
    }

Mappings == { f \in [LKS -> FKS] : ~ (\E a, b \in DOMAIN f : f[a] = f[b]) }
Powers == [ LKS -> 0..2 ]

VARIABLES
    \* @type: Action;
    action,
    \* @type: Mapping;
    mapping,
    \* @type: Str -> Int;
    powers,


Init == 

EndBlock == 
    \E m \in Mappings, p \in Powers : 
    

SetKey ==
    \E p \in Pairs : 

ReceiveSlash == 

ReceiveMaturity ==

Next == 
    \/ EndBlock
    \/ SetKey
    \/ ReceiveSlash
    \/ ReceiveMaturity

Inv == 

(*
It is always possible to slash a local key as long as the 
An FK to LK mapping is always available from the time an update includes the LK until the time the vscid
for 

If a vscid for a given mapping was not matured then the mapping exists
*)

====
