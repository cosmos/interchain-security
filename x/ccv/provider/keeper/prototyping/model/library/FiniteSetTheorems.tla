------------------------- MODULE FiniteSetTheorems --------------------------
(***************************************************************************)
(* `^{\large \vspace{12pt}                                                 *)
(*  Facts about finite sets and their cardinality.                         *)
(*  Originally contributed by Tom Rodeheffer, MSR.                         *)
(*  \vspace{12pt}}^'                                                       *)
(*  Proofs of these theorems appear in module FiniteSetTheorems_proofs.    *)
(***************************************************************************)

EXTENDS
  FiniteSets,
  Functions,
  WellFoundedInduction


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* A set S is finite iff there exists a natural number n such that there   *)
(* exist a surjection (or a bijection) from 1..n to S.                     *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)

LEMMA FS_NatSurjection ==
  ASSUME NEW S
  PROVE  IsFiniteSet(S) <=> \E n \in Nat : ExistsSurjection(1..n,S)


LEMMA FS_NatBijection ==
  ASSUME NEW S
  PROVE  IsFiniteSet(S) <=> \E n \in Nat : ExistsBijection(1..n,S)


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* If there exists n \in Nat such that a bijection exists from 1..n to S,  *)
(* then Cardinality(S) = n.                                                *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)

LEMMA FS_CountingElements ==
  ASSUME NEW S, NEW n \in Nat, ExistsBijection(1..n,S)
  PROVE  Cardinality(S) = n


(***************************************************************************)
(* Corollary: a surjection from 1..n to S provides a cardinality bound.    *)
(***************************************************************************)
THEOREM FS_SurjCardinalityBound ==
  ASSUME NEW S, NEW n \in Nat, ExistsSurjection(1..n, S)
  PROVE  Cardinality(S) <= n


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* For any finite set S, Cardinality(S) \in Nat. Moreover, there is a      *)
(* bijection from 1 .. Cardinality(S) to S.                                *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FS_CardinalityType ==
  ASSUME NEW S, IsFiniteSet(S)
  PROVE  /\ Cardinality(S) \in Nat
         /\ ExistsBijection(1..Cardinality(S), S)



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* The image of a finite set under a bijection or surjection is finite.    *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FS_Bijection ==
  ASSUME NEW S, NEW T, IsFiniteSet(S), ExistsBijection(S,T)
  PROVE  /\ IsFiniteSet(T)
         /\ Cardinality(T) = Cardinality(S)


THEOREM FS_SameCardinalityBij ==
  ASSUME NEW S, NEW T, IsFiniteSet(S), IsFiniteSet(T),
         Cardinality(S) = Cardinality(T)
  PROVE  ExistsBijection(S,T)


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Any surjection between two finite sets of equal cardinality is          *)
(* an injection.                                                           *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FS_SurjSameCardinalityImpliesInj ==
  ASSUME NEW S, NEW T, IsFiniteSet(S), Cardinality(S) = Cardinality(T),
         NEW f \in Surjection(S,T)
  PROVE  f \in Injection(S,T)


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* The image of a finite set is finite.                                    *)
(*                                                                         *)
(* NB: Note that any function is a surjection on its range by theorem      *)
(* Fun_RangeProperties.                                                    *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FS_Surjection ==
  ASSUME NEW S, NEW T, NEW f \in Surjection(S,T), IsFiniteSet(S)
  PROVE  /\ IsFiniteSet(T)
         /\ Cardinality(T) <= Cardinality(S)
         /\ Cardinality(T) = Cardinality(S) <=> f \in Injection(S,T)


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* The cardinality of a finite set S is 0 iff S is empty.                  *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FS_EmptySet ==
  /\ IsFiniteSet({})
  /\ Cardinality({}) = 0
  /\ \A S : IsFiniteSet(S) => (Cardinality(S) = 0 <=> S = {})



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* If S is finite, so are S \cup {x} and S \ {x}.                          *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FS_AddElement ==
  ASSUME NEW S, NEW x, IsFiniteSet(S)
  PROVE  /\ IsFiniteSet(S \cup {x})
         /\ Cardinality(S \cup {x}) =
            IF x \in S THEN Cardinality(S) ELSE Cardinality(S)+1


THEOREM FS_RemoveElement ==
  ASSUME NEW S, NEW x, IsFiniteSet(S)
  PROVE  /\ IsFiniteSet(S \ {x})
         /\ Cardinality(S \ {x}) =
            IF x \in S THEN Cardinality(S)-1 ELSE Cardinality(S)


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* In particular, a singleton set is finite.                               *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FS_Singleton ==
  /\ \A x : IsFiniteSet({x}) /\ Cardinality({x}) = 1
  /\ \A S : IsFiniteSet(S) => (Cardinality(S) = 1 <=> \E x: S = {x})




(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Any subset of a finite set is finite.                                   *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FS_Subset ==
  ASSUME NEW S, IsFiniteSet(S), NEW T \in SUBSET S
  PROVE  /\ IsFiniteSet(T)
         /\ Cardinality(T) <= Cardinality(S)
         /\ Cardinality(S) = Cardinality(T) => S = T



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* a..b is a finite set for any a,b \in Int.                               *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FS_Interval ==
  ASSUME NEW a \in Int, NEW b \in Int
  PROVE  /\ IsFiniteSet(a..b)
         /\ Cardinality(a..b) = IF a > b THEN 0 ELSE b-a+1


THEOREM FS_BoundedSetOfNaturals ==
  ASSUME NEW S \in SUBSET Nat, NEW n \in Nat,
         \A s \in S : s <= n
  PROVE  /\ IsFiniteSet(S)
         /\ Cardinality(S) \leq n+1


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Induction for finite sets.                                              *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)

THEOREM FS_Induction == 
  ASSUME NEW S, IsFiniteSet(S),
         NEW P(_), P({}),
         ASSUME NEW T, NEW x, IsFiniteSet(T), P(T), x \notin T
         PROVE  P(T \cup {x})
  PROVE  P(S)



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* The finite subsets form a well-founded ordering with respect to strict  *)
(* set inclusion.                                                          *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)

FiniteSubsetsOf(S) == { T \in SUBSET S : IsFiniteSet(T) }
StrictSubsetOrdering(S) == { ss \in (SUBSET S) \X (SUBSET S) : 
                                ss[1] \subseteq ss[2] /\ ss[1] # ss[2] }

LEMMA FS_FiniteSubsetsOfFinite ==
  ASSUME NEW S, IsFiniteSet(S)
  PROVE  FiniteSubsetsOf(S) = SUBSET S


(*****************************************************************************)
(*  The formulation of the following theorem doesn't require S being finite. *)
(*  If S is finite, it implies                                               *)
(*       IsWellFoundedOn(StrictSubsetOrdering(S), SUBSET S)                  *)
(*  using lemma FS_FiniteSubsetsOfFinite.                                    *)
(*****************************************************************************)
THEOREM FS_StrictSubsetOrderingWellFounded ==
  ASSUME NEW S
  PROVE  IsWellFoundedOn(StrictSubsetOrdering(S), FiniteSubsetsOf(S))



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Well-founded induction for finite subsets.                              *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)

THEOREM FS_WFInduction ==
  ASSUME NEW P(_), NEW S, IsFiniteSet(S),
         ASSUME NEW T \in SUBSET S,
                \A U \in (SUBSET T) \ {T} : P(U)
         PROVE  P(T)
  PROVE  P(S)


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* The union of two finite sets is finite.                                 *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FS_Union ==
  ASSUME NEW S, IsFiniteSet(S),
         NEW T, IsFiniteSet(T)
  PROVE  /\ IsFiniteSet(S \cup T)
         /\ Cardinality(S \cup T) =
               Cardinality(S) + Cardinality(T) - Cardinality(S \cap T)



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Corollary: two majorities intersect. More precisely, any two subsets    *)
(* of a finite set U such that the sum of cardinalities of the subsets     *)
(* exceeds that of U must have non-empty intersection.                     *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FS_MajoritiesIntersect == 
  ASSUME NEW U, NEW S, NEW T, IsFiniteSet(U), 
         S \subseteq U, T \subseteq U, 
         Cardinality(S) + Cardinality(T) > Cardinality(U)
  PROVE  S \cap T # {}



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* The intersection of a finite set with an arbitrary set is finite.       *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
  

THEOREM FS_Intersection == 
  ASSUME NEW S, IsFiniteSet(S), NEW T
  PROVE  /\ IsFiniteSet(S \cap T)
         /\ IsFiniteSet(T \cap S)
         /\ Cardinality(S \cap T) <= Cardinality(S)
         /\ Cardinality(T \cap S) <= Cardinality(S)



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* The difference between a finite set and an arbitrary set is finite.     *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FS_Difference == 
  ASSUME NEW S, NEW T, IsFiniteSet(S)
  PROVE /\ IsFiniteSet(S \ T)
        /\ Cardinality(S \ T) = Cardinality(S) - Cardinality(S \cap T)
      


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* The union of a finite number of finite sets is finite.                  *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FS_UNION ==
  ASSUME NEW S, IsFiniteSet(S), \A T \in S : IsFiniteSet(T)
  PROVE  IsFiniteSet(UNION S)



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* The product of two finite sets is finite.                               *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FS_Product ==
  ASSUME NEW S, IsFiniteSet(S),
         NEW T, IsFiniteSet(T)
  PROVE  /\ IsFiniteSet(S \X T)
         /\ Cardinality(S \X T) = Cardinality(S) * Cardinality(T)



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* The powerset of a finite set is finite.                                 *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FS_SUBSET ==
  ASSUME NEW S, IsFiniteSet(S)
  PROVE  /\ IsFiniteSet(SUBSET S)
         /\ Cardinality(SUBSET S) = 2^Cardinality(S)





    
=============================================================================
\* Modification History
\* Last modified Fri Feb 14 19:42:05 GMT-03:00 2014 by merz
\* Last modified Thu Jul 04 15:15:07 CEST 2013 by bhargav
\* Last modified Tue Jun 04 11:44:51 CEST 2013 by bhargav
\* Last modified Fri May 03 12:02:51 PDT 2013 by tomr
\* Created Fri Oct 05 15:04:18 PDT 2012 by tomr