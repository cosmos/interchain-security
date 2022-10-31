---- MODULE keymap_api ----

EXTENDS  Integers, Naturals, FiniteSets, Sequences, TLC

Validators == 0..2

VARIABLES
    valsets,
    mappings,
    consumerIndex,
    consumerIndexMatured

Init ==
    /\ valsets = 
    /\ mappings = 
    /\ consumerIndex = 
    /\ consumerIndexMatured = 

Next ==
    \/ Map(providerKey, consumerKey)
    \/ NewValSet

Inv == 

====