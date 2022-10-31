---- MODULE keymap_api ----

EXTENDS  Integers, Naturals, FiniteSets, Sequences, TLC

Validators == 0..2
ProviderKeys == 0..2
ConsumerKeys == 0..8

VARIABLES
    \*
    assignments,
    providerValSets,
    consumerIndex,
    consumerIndexMatured

Init ==
    \* One block has been committed (genesis)
    /\ \E valset \in SUBSET Validators: valsets = <<valset>>
    \* Store the genesis assignment, and the current assignment
    /\ assignments = <<[key \in ProviderKeys |-> key], [key \in ProviderKeys |-> key]>>
    /\ consumerIndex = 1
    /\ consumerIndexMatured = 0 \* Nothing has been matured yet

AssignKey == 
    \E providerKey \in ProviderKeys, consumerKey \in ConsumerKeys:
    /\ ~(\E i \in (consumerIndexMatured + 1)..Len(assignments) : assignments[i][providerKey] = consumerKey)
    /\ assignments' = Subseq(assignments, 1, Len(assignments) - 1) \o <<[Tail(assignments) EXCEPT ![providerKey] = consumerKey]>>

ProviderEndAndCommitBlock ==
    \E valset \in SUBSET Validators:
    /\ assignments' = assignments \o <<Tail(assignments)>> \* Extend assignments with a copy of the last committed mapping
    /\ providerValSets' = providerValSets \o <<valset>> \* Obtain a new validator set from changes in voting power

ConsumerDeliverUpdates(index) == 
    \E index \in (consumerIndex + 1)..Len(providerValSets):
    consumerIndex' = index

ProviderDeliverMaturities(index) == 
    \E index \in (consumerIndexMatured + 1)..consumerIndex:
    consumerIndexMatured' = index

Next ==
    \/ /\ AssignKey
       /\ UNCHANGED <<providerValSets, consumerIndex, consumerIndexMatured>>
    \/ /\ ProviderEndAndCommitBlock
       /\ UNCHANGED <<consumerIndex, consumerIndexMatured>>
    \/ /\ ConsumerDeliverUpdates
       /\ UNCHANGED <<assignments,providerValSets,consumerIndexMatured>>
    \/ /\ ProviderDeliverMaturities
       /\ UNCHANGED <<assignments,providerValSets,consumerIndex>>

ReverseQueries == 
    LET Query(consumerKey) == {providerKey \in ProviderKeys : 
    \E ix \in assignments
    assignments[Len(assignments)][providerKey] = consumerKey}


    \A ix \in (consumerIndexMatured+1)..consumerIndex:
      \A consumerKey \in {assignments[ix][key] : key \in providerValSets[ix]}:


        


Sanity == LET
    Sanity0 == consumerIndexMatured <= consumerIndex
    Sanity1 == Len(providerValSets) + 1 = Len(assignments) 
    Sanity2 == consumerIndex <= Len(providerValSets)
    IN
    /\ Sanity0
    /\ Sanity1
    /\ Sanity2

====