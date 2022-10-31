---- MODULE keymap_api ----

EXTENDS  Integers, Naturals, FiniteSets, Sequences, TLC

Validators == 0..2
ProviderKeys == 0..2
ConsumerKeys == 0..8

VARIABLES
    assignments,
    providerValSets,
    committedProviderVSCID,
    committedConsumerVSCID,
    greatestConsumerVSCIDMatured

Init ==
    \* Store the genesis assignment, and the current assignment
    /\ assignments = [1 |-> [key \in ProviderKeys |-> key],
                      2 |-> [key \in ProviderKeys |-> key]]
    \* One valset has been committed (genesis)
    /\ \E valset \in SUBSET Validators: 
       providerValSets = [1 |-> valset]
    \* Genesis block is committed
    /\ committedProviderVSCID = 1
    \* on consumer too.
    /\ committedConsumerVSCID = 1
    \* Nothing has matured yet.
    /\ greatestConsumerVSCIDMatured = 0

AssignKey == 
    \E providerKey \in ProviderKeys, consumerKey \in ConsumerKeys:
    \* consumerKey is not in use
    /\ ~(k \in DOMAIN assignments : assignments[k][providerKey] = consumerKey)
    \* Do assignment
    /\ assignments' = [assignments EXCEPT ![committedProviderVSCID + 1] = [@ EXCEPT ![providerKey] = consumerKey] ]
    \* The rest...
    /\ UNCHANGED << providerValSets, committedProviderVSCID, committedConsumerVSCID, greatestConsumerVSCIDMatured >>

ProviderEndAndCommitBlock ==
    \E valset \in SUBSET Validators:
    \* Create a new assignment entry
    /\ assignments' = assignments @@ [committedProviderVSCID' |-> assignments[committedProviderVSCID]]
    \* Get a new validator set from changes in voting power
    /\ providerValSets' = providerValSets @@ [committedProviderVSCID' |-> valset]
    \* Increment vscid
    /\ committedProviderVSCID' = committedProviderVSCID + 1
    \* The rest...
    /\ UNCHANGED << committedConsumerVSCID, greatestConsumerVSCIDMatured >>

ConsumerDeliverUpdates == 
    \* Fast forward the consumer
    \E vscid \in (committedConsumerVSCID + 1)..committedProviderVSCID:
    committedConsumerVSCID' = vscid

ProviderDeliverMaturities == 
    \* Fast forward the consumer maturities, and notify provider
    \E vscid \in (greatestConsumerVSCIDMatured + 1)..committedConsumerVSCID:
    greatestConsumerVSCIDMatured' = vscid

Next ==
    \/ AssignKey
    \/ ProviderEndAndCommitBlock
    \/ ConsumerDeliverUpdates
    \/ ProviderDeliverMaturities

ReverseQueries == 
    LET Query(consumerKey) == {providerKey \in ProviderKeys : 
    \E ix \in assignments
    assignments[Len(assignments)][providerKey] = consumerKey}


    \A ix \in (greatestConsumerVSCIDMatured+1)..consumerVSCID:
      \A consumerKey \in {assignments[ix][key] : key \in providerValSets[ix]}:
        


Sanity == LET
    Sanity0 == committedConsumerVSCID <= committedProviderVSCID
    Sanity1 == greatestConsumerVSCIDMatured <= committedConsumerVSCID
    Sanity2 == committedProviderVSCID \in DOMAIN assignments
    Sanity3 == committedProviderVSCID + 1 \in DOMAIN assignments
    Sanity4 == committedProviderVSCID \in DOMAIN providerValSets
    IN
    /\ Sanity0
    /\ Sanity1
    /\ Sanity2
    /\ Sanity3
    /\ Sanity4

====