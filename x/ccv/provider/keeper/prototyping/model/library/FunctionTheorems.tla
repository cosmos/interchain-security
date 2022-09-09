------------------------- MODULE FunctionTheorems ---------------------------
(***************************************************************************)
(* `^{\large\vspace{12pt}                                                  *)
(*  Facts about functions.                                                 *)
(*  Originally contributed by Tom Rodeheffer, MSR.                         *)
(*  For the proofs of these theorems, see module FunctionTheorems\_proofs. *)
(*  \vspace{12pt}}^'                                                       *)
(***************************************************************************)

EXTENDS
  Functions,
  Integers

(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Function restriction.                                                   *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_RestrictProperties ==
  ASSUME NEW S, NEW T, NEW f \in [S -> T], NEW A \in SUBSET S
  PROVE  /\ Restrict(f,A) \in [A -> T]
         /\ \A x \in A : Restrict(f,A)[x] = f[x]


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Range of a function.                                                    *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_RangeProperties ==
  ASSUME NEW S, NEW T, NEW f \in [S -> T]
  PROVE  /\ Range(f) \subseteq T
         /\ \A y \in Range(f) : \E x \in S : f[x] = y
         /\ f \in Surjection(S, Range(f))


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Range of a function.                                                    *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_InverseProperties ==
  ASSUME NEW S, NEW T, NEW f \in [S -> T]
  PROVE  /\ (S = {} => T = {}) => Inverse(f,S,T) \in [T -> S]
         /\ \A y \in Range(f) : f[Inverse(f,S,T)[y]] = y


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Introduction rules for injections, surjections, bijections.             *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_IsInj ==
  ASSUME NEW S, NEW T, NEW F \in [S -> T],
         \A a,b \in S : F[a] = F[b] => a = b 
  PROVE  F \in Injection(S,T)


THEOREM Fun_IsSurj ==
  ASSUME NEW S, NEW T, NEW F \in [S -> T],
         \A t \in T : \E s \in S : F[s] = t
  PROVE  F \in Surjection(S,T)


THEOREM Fun_IsBij ==
  ASSUME NEW S, NEW T, NEW F,
         \/ F \in Injection(S,T)
         \/ (F \in [S -> T] /\ \A a,b \in S : F[a] = F[b] => a = b),

         \/ F \in Surjection(S,T)
         \/ (F \in [S -> T] /\ \A t \in T : \E s \in S : F[s] = t)
  PROVE  F \in Bijection(S,T)




(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Properties of injections, surjections, and bijections.                  *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_InjectionProperties ==
  ASSUME NEW S, NEW T, NEW F \in Injection(S,T)
  PROVE  /\ F \in [S -> T]
         /\ \A a,b \in S : F[a] = F[b] => a = b


THEOREM Fun_SurjectionProperties ==
  ASSUME NEW S, NEW T, NEW F \in Surjection(S,T)
  PROVE  /\ F \in [S -> T]
         /\ \A t \in T : \E s \in S : F[s] = t
         /\ Range(F) = T


THEOREM Fun_BijectionProperties ==
  ASSUME NEW S, NEW T, NEW F \in Bijection(S,T)
  PROVE  /\ F \in [S -> T]
         /\ F \in Injection(S,T)
         /\ F \in Surjection(S,T)
         /\ \A a,b \in S : F[a] = F[b] => a = b
         /\ \A t \in T : \E s \in S : F[s] = t



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* A surjection in [S -> T] such that there is no surjection from any      *)
(* subset of S to T is a bijection.                                        *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_SmallestSurjectionIsBijection ==
  ASSUME NEW S, NEW T, NEW f \in Surjection(S,T),
         \A U \in SUBSET S : U # S => Surjection(U,T) = {}
  PROVE  f \in Bijection(S,T)


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Transitivity of injections, surjections, bijections.                    *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_InjTransitive ==
  ASSUME NEW S, NEW T, NEW U,
         NEW F \in Injection(S,T),
         NEW G \in Injection(T,U)
  PROVE  [s \in S |-> G[F[s]]] \in Injection(S,U)


THEOREM Fun_SurjTransitive ==
  ASSUME NEW S, NEW T, NEW U,
         NEW F \in Surjection(S,T),
         NEW G \in Surjection(T,U)
  PROVE  [s \in S |-> G[F[s]]] \in Surjection(S,U)


THEOREM Fun_BijTransitive ==
  ASSUME NEW S, NEW T, NEW U,
         NEW F \in Bijection(S,T),
         NEW G \in Bijection(T,U)
  PROVE  [s \in S |-> G[F[s]]] \in Bijection(S,U)



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* The inverse of a surjection is an injection and vice versa.             *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_SurjInverse ==
  ASSUME NEW S, NEW T, NEW f \in Surjection(S,T)
  PROVE  Inverse(f,S,T) \in Injection(T,S)


THEOREM Fun_InjInverse ==
  ASSUME NEW S, NEW T, NEW f \in Injection(S,T), S = {} => T = {}
  PROVE  Inverse(f,S,T) \in Surjection(T,S)


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Properties of the inverse of a bijection.                               *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_BijInverse ==
  ASSUME NEW S, NEW T, NEW f \in Bijection(S,T)
  PROVE  /\ Inverse(f,S,T) \in Bijection(T,S)
         /\ \A s \in S : Inverse(f,S,T)[f[s]] = s
         /\ Inverse(Inverse(f,S,T), T,S) = f


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* The restriction of a bijection is a bijection.                          *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_BijRestrict ==
  ASSUME NEW S, NEW T, NEW F \in Bijection(S,T),
         NEW R \in SUBSET S
  PROVE  Restrict(F, R) \in Bijection(R, Range(Restrict(F, R)))



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Given F an injection from S to T, then F is a bijection from S to F(S). *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_InjMeansBijImage ==
  ASSUME NEW S, NEW T, NEW F \in Injection(S,T)
  PROVE  F \in Bijection(S, Range(F))




-----------------------------------------------------------------------------
(***************************************************************************)
(* `^{\large \vspace{12pt}                                                 *)
(*  Facts about exists jections.                                           *)
(*  \vspace{12pt}}^'                                                       *)
(***************************************************************************)



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Definitions restated as facts.                                          *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_ExistsInj ==
  \A S,T : ExistsInjection(S,T)  <=>  Injection(S,T) # {}


THEOREM Fun_ExistsSurj ==
  \A S,T : ExistsSurjection(S,T)  <=>  Surjection(S,T) # {}


THEOREM Fun_ExistsBij ==
  \A S,T : ExistsBijection(S,T)  <=>  Bijection(S,T) # {}




(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* There is a surjection from any set S to any non-empty subset T of S.    *)
(* (Note that there cannot be a surjection to {} except if S is empty.)    *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_ExistsSurjSubset ==
  ASSUME NEW S, NEW T \in SUBSET S, T # {}
  PROVE  ExistsSurjection(S,T)




(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* If there is a surjection from S to T, then there is an injection from T *)
(* to S.                                                                   *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_ExistsSurjMeansExistsRevInj ==
  ASSUME NEW S, NEW T, ExistsSurjection(S,T)
  PROVE  ExistsInjection(T,S)



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* ExistsBijection is reflexive, symmetric, and transitive.                *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_ExistsBijReflexive ==
  ASSUME NEW S
  PROVE  ExistsBijection(S,S)


THEOREM Fun_ExistsBijSymmetric ==
  ASSUME NEW S, NEW T, ExistsBijection(S,T)
  PROVE  ExistsBijection(T,S)


THEOREM Fun_ExistsBijTransitive ==
  ASSUME NEW S, NEW T, NEW U, ExistsBijection(S,T), ExistsBijection(T,U)  
  PROVE  ExistsBijection(S,U)



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Existence of injections and surjections is reflexive and transitive.    *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_ExistsInjReflexive ==
  ASSUME NEW S
  PROVE  ExistsInjection(S,S)


THEOREM Fun_ExistsSurjReflexive ==
  ASSUME NEW S
  PROVE  ExistsSurjection(S,S)


THEOREM Fun_ExistsInjTransitive ==
  ASSUME NEW S, NEW T, NEW U,
         ExistsInjection(S,T), ExistsInjection(T,U)
  PROVE  ExistsInjection(S,U)


THEOREM Fun_ExistsSurjTransitive ==
  ASSUME NEW S, NEW T, NEW U,
         ExistsSurjection(S,T), ExistsSurjection(T,U)
  PROVE  ExistsSurjection(S,U)


-----------------------------------------------------------------------------
(***************************************************************************)
(* `^{\large \vspace{12pt}                                                 *)
(* The Cantor-Bernstein-Schroeder theorem.                                 *)
(*  \vspace{12pt}}^'                                                       *)
(***************************************************************************)


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* If there exists an injection from S to T, where T is a subset of S,     *)
(* then there exists a bijection from S to T.                              *)
(*                                                                         *)
(* A lemma for the Cantor-Bernstein-Schroeder theorem.                     *)
(*                                                                         *)
(* This proof is formalized from                                           *)
(* `^\url{http://www.proofwiki.org/wiki/Cantor-Bernstein-Schroeder\_Theorem/Lemma}^' *)
(* retrieved April 29, 2013.                                               *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_CantorBernsteinSchroeder_Lemma ==
  ASSUME NEW S, NEW T, T \subseteq S, ExistsInjection(S,T)
  PROVE  ExistsBijection(S,T)




(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* If an injection exists from S to T and an injection exists from T to S, *)
(* then there is a bijection from S to T.                                  *)
(*                                                                         *)
(* This is the Cantor-Bernstein-Schroeder theorem.                         *)
(*                                                                         *)
(* This proof is formalized from                                           *)
(* `^\url{http://www.proofwiki.org/wiki/Cantor-Bernstein-Schroeder_Theorem/Proof_5}^' *)
(* retrieved April 29, 2013.                                               *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_CantorBernsteinSchroeder ==
  ASSUME NEW S, NEW T,
         ExistsInjection(S,T), ExistsInjection(T,S)
  PROVE  ExistsBijection(S,T)



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Applications of the Cantor-Bernstein-Schroeder Theorem.                 *)
(* If there exists an injection f: A->B and a surjection g: A->B, then     *)
(* there exists a bijection between A and B.                               *)
(* Also, if there are surjections between A and B, then there is a         *)
(* bijection.                                                              *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)

THEOREM Fun_ExistInjAndSurjThenBij == 
  ASSUME NEW S, NEW T,
         ExistsInjection(S,T), ExistsSurjection(S,T)
  PROVE  ExistsBijection(S,T)



THEOREM Fun_ExistSurjAndSurjThenBij == 
  ASSUME NEW S, NEW T,
         ExistsSurjection(S,T), ExistsSurjection(T,S)
  PROVE  ExistsBijection(S,T)




(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Equivalences for ExistsBijection.                                       *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_ExistsBijEquiv ==
  ASSUME NEW S, NEW T
  PROVE  /\ ExistsBijection(S,T) <=> ExistsBijection(T,S)
         /\ ExistsBijection(S,T) <=> ExistsInjection(S,T) /\ ExistsInjection(T,S)
         /\ ExistsBijection(S,T) <=> ExistsInjection(S,T) /\ ExistsSurjection(S,T)
         /\ ExistsBijection(S,T) <=> ExistsInjection(T,S) /\ ExistsSurjection(T,S)
         /\ ExistsBijection(S,T) <=> ExistsSurjection(S,T) /\ ExistsSurjection(T,S)


-----------------------------------------------------------------------------
(***************************************************************************)
(* `^{\large \vspace{12pt}                                                 *)
(*  Facts about functions involving integer intervals.                     *)
(*  \vspace{12pt}}^'                                                       *)
(***************************************************************************)


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* There is a bijection from 1..b-a+1 to a..b for integers a,b with a <= b.*)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_ExistsBijInterval ==
  ASSUME NEW a \in Int, NEW b \in Int, a <= b
  PROVE  ExistsBijection(1 .. b-a+1, a .. b)


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* There is an injection from 1..n to 1..m iff n \leq m.                   *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_NatInjLeq ==
  ASSUME NEW n \in Nat, NEW m \in Nat
  PROVE  ExistsInjection(1..n,1..m) <=> n \leq m




(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* If a surjection from 1..n to S exists (for some n \in Nat) then a       *)
(* bijection from 1..m to S exists (for some m \in Nat) and m \leq n.      *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_NatSurjImpliesNatBij ==
  ASSUME NEW S, NEW n \in Nat, ExistsSurjection(1..n,S)
  PROVE  \E m \in Nat : ExistsBijection(1..m,S) /\ m \leq n


(***************************************************************************)
(* Simple corollary.                                                       *)
(***************************************************************************)
THEOREM Fun_NatSurjEquivNatBij ==
  ASSUME NEW S
  PROVE  (\E n \in Nat : ExistsSurjection(1..n,S))
    <=>  (\E m \in Nat : ExistsBijection(1..m,S))



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* For any set S, given n, m \in Nat such that bijections exist from 1..n  *)
(* to S and from 1..m to S, then it must be the case that n = m.           *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_NatBijSame ==
  ASSUME NEW S,
         NEW n \in Nat, ExistsBijection(1..n,S),
         NEW m \in Nat, ExistsBijection(1..m,S)
  PROVE  n = m



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* S is empty iff there exists a bijection from 1..0 to S.                 *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_NatBijEmpty ==
  ASSUME NEW S
  PROVE  ExistsBijection(1..0,S) <=> S = {}


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* S is a singleton iff there exists a bijection from 1..1 to S.           *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_NatBijSingleton ==
  ASSUME NEW S
  PROVE  ExistsBijection(1..1,S) <=> \E s : S = {s}




(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* If there exists a bijection from 1..m to S (for some m \in Nat), then   *)
(* there exists a bijection from 1..n to T (for some n \in Nat), where T   *)
(* is a subset of S.  Furthermore n \leq m.                                *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_NatBijSubset ==
  ASSUME NEW S, NEW m \in Nat, ExistsBijection(1..m,S),
         NEW T \in SUBSET S
  PROVE  \E n \in Nat : ExistsBijection(1..n,T) /\ n \leq m
  



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* If there exists a bijection from 1..m to S (for some m \in Nat), then   *)
(* there exists a bijection from 1..(m+1) to S \cup {x}, where x \notin S. *)
(*                                                                         *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_NatBijAddElem ==
  ASSUME NEW S, NEW m \in Nat, ExistsBijection(1..m,S),
         NEW x, x \notin S
  PROVE  ExistsBijection(1..(m+1), S \cup {x})



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* If there exists a bijection from 1..m to S (for some m \in Nat), then   *)
(* there exists a bijection from 1..(m-1) to S \ {x}, where x \in S.       *)
(*                                                                         *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_NatBijSubElem ==
  ASSUME NEW S, NEW m \in Nat, ExistsBijection(1..m,S),
         NEW x, x \in S
  PROVE  ExistsBijection(1..(m-1), S \ {x})



=============================================================================
\* Modification History
\* Last modified Thu Feb 13 14:49:08 GMT-03:00 2014 by merz
\* Last modified Tue Jun 11 12:30:05 CEST 2013 by bhargav
\* Last modified Fri May 31 15:27:41 CEST 2013 by bhargav
\* Last modified Fri May 03 12:55:32 PDT 2013 by tomr
\* Created Thu Apr 11 10:36:10 PDT 2013 by tomr
