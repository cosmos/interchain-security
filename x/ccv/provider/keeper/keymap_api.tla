---- MODULE keymap_api ----

EXTENDS  Integers, Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    STORAGE_CONSTANT,
    ProviderKeys,
    ConsumerKeys

VARIABLES
    assignments,
    providerValSets,
    committedProviderVSCID,
    committedConsumerVSCID,
    maturedConsumerVSCID

(***************************************************************************)
(** State at genesis *******************************************************)
(***************************************************************************)
(***************************************************************************)

Init ==
    \* Store the genesis assignment, and the current assignment
    /\ assignments = [vscid \in 1..2 |-> [key \in ProviderKeys |-> key]]
    \* One valset has been committed (genesis)
    /\ \E valset \in SUBSET ProviderKeys: 
       providerValSets = [vscid \in {1} |-> valset]
    \* Genesis block is committed
    /\ committedProviderVSCID = 1
    \* on consumer too.
    /\ committedConsumerVSCID = 1
    \* Nothing has matured yet.
    /\ maturedConsumerVSCID = 0

(***************************************************************************)
(** Public write operation API *********************************************)
(***************************************************************************)
(***************************************************************************)

AssignKey == 
    \E providerKey \in ProviderKeys, consumerKey \in ConsumerKeys:
    \* consumerKey is not in use
    /\ ~(\E i \in DOMAIN assignments: \E k \in DOMAIN assignments[i] : assignments[i][k] = consumerKey)
    \* Do assignment
    /\ assignments' = [
        assignments EXCEPT ![committedProviderVSCID + 1] = 
        [@ EXCEPT ![providerKey] = consumerKey] ]
    \* The rest...
    /\ UNCHANGED << providerValSets, committedProviderVSCID, committedConsumerVSCID, maturedConsumerVSCID >>

(***************************************************************************)
(** Internal API ***********************************************************)
(***************************************************************************)
(***************************************************************************)

ProviderEndAndCommitBlock ==
    \E valset \in SUBSET ProviderKeys:
    \* Create a new assignment entry
    /\ assignments' = assignments @@ [vscid \in {committedProviderVSCID+2} |-> assignments[committedProviderVSCID]]
    \* Get a new validator set from changes in voting power
    /\ providerValSets' = providerValSets @@ [vscid \in {committedProviderVSCID+1} |-> valset]
    \* Increment vscid
    /\ committedProviderVSCID' = committedProviderVSCID + 1
    \* The rest...
    /\ UNCHANGED << committedConsumerVSCID, maturedConsumerVSCID >>

ConsumerDeliverUpdates == 
    \* Fast forward the consumer
    \E vscid \in (committedConsumerVSCID + 1)..committedProviderVSCID:
    committedConsumerVSCID' = vscid
    \* The rest...
    /\ UNCHANGED <<committedProviderVSCID, assignments, providerValSets, maturedConsumerVSCID >>

ProviderDeliverMaturities == 
    \* Fast forward the consumer maturities, and notify provider
    \E vscid \in (maturedConsumerVSCID + 1)..committedConsumerVSCID:
    /\ maturedConsumerVSCID' = vscid
    /\ assignments' = [i \in {
            j \in DOMAIN assignments : vscid < j \/ committedProviderVSCID <= j
        } |-> assignments[i]]
    \* The rest...
    /\ UNCHANGED <<committedConsumerVSCID, committedProviderVSCID, providerValSets>>

Next ==
    \/ AssignKey
    \/ ProviderEndAndCommitBlock
    \/ ConsumerDeliverUpdates
    \/ ProviderDeliverMaturities

(***************************************************************************)
(** Invariants *************************************************************)
(***************************************************************************)
(***************************************************************************)

(***********************************)
(** Query properties ***************)
(***********************************)
(***********************************)

(*
The current consumer key assigned to a provider key is defined and
queryable.
True by construction, not explicityl modelled.
*)
AssignmentIsDefined == 
    \A k \in ProviderKeys:
    LET ConsumerKey == assignments[committedProviderVSCID + 1][k]
    IN TRUE

(*
The consumer validator set at committedConsumerVSCID
is defined as the provider validator set at committedConsumerVSCID
mapped through the assignment at committedConsumerVSCID.
True by construction, not explicitly modelled.
*)
ConsumerValidatorSetIsDefined == 
    LET
    ConsumerValset == {assignments[committedConsumerVSCID][k] : k \in providerValSets[committedConsumerVSCID]}
    IN TRUE

(*
For any unmatured consumer valset, it is always possible to retrieve a unique provider key
for any consumer key in the set.
*)
UniqueReverseQueryResultIsDefined == 
    \A i \in (maturedConsumerVSCID + 1)..committedConsumerVSCID : 
    LET
    \* The valset known to the consumer
    ConsumerValset == {assignments[i][k] : k \in providerValSets[i]}
    \* All the keys that are assigned to the consumerKey in stored assignments
    Assigned(consumerKey) == {
            providerKey \in ProviderKeys :
            \E j \in DOMAIN assignments : assignments[j][providerKey] = consumerKey
        }
    \* The query for the providerKey is successful and the result is unique.
    IN \A consumerKey \in ConsumerValset : Cardinality(Assigned(consumerKey)) = 1

(*
Storage cost grows linearly with committedProviderVSCID - maturedConsumerVSCID
*)
BoundedStorage ==
    Cardinality(DOMAIN(assignments)) <= STORAGE_CONSTANT * (1 + (committedProviderVSCID - maturedConsumerVSCID))


(*Check that the spec is written correctly.*)
Sanity == LET
    Sanity0 == committedConsumerVSCID <= committedProviderVSCID
    Sanity1 == maturedConsumerVSCID <= committedConsumerVSCID
    Sanity2 == committedProviderVSCID \in DOMAIN assignments
    Sanity3 == committedProviderVSCID + 1 \in DOMAIN assignments
    Sanity4 == committedProviderVSCID \in DOMAIN providerValSets
    IN
    /\ Sanity0
    /\ Sanity1
    /\ Sanity2
    /\ Sanity3
    /\ Sanity4

Invariant == Sanity /\ BoundedStorage /\ UniqueReverseQuery

(***************************************************************************)

====