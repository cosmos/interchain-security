---- MODULE keymap_api ----

EXTENDS  Integers, Naturals, FiniteSets, Sequences, TLC

Validators == 0..2

VARIABLES
    consumerIndex,
    consumerIndexMatured,
    mappings,
    valsets

Init ==
    /\ consumerVscid = 1,
    /\ consumerVscidMatured = 0,
    /\ mappings = [],
    /\ valsets = []

Next ==
    \/ Map(providerKey, consumerKey)
    \/ Increase(providerKey, consumerKey)
    \/ Map(providerKey, consumerKey)
       

Inv == 

====