---- MODULE main ----

EXTENDS Integers, FiniteSets, Sequences, TLC, Apalache

(*

    @typeAlias: X = Str;

*)

CONSTANTS
    \* @type: Set(X);
    XS

VARIABLES
    \* @type: Int;
    a

CInit == XS = {"k", "u", "v"}

Init == a = 42

Go == a' = 42

Next == Go

Inv == TRUE

====
