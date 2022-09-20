---------------------------- MODULE JectionThm ------------------------------
(***************************************************************************)
(* `^{\large\bf \vspace{12pt}                                              *)
(*  Facts about injections, surjections, and bijections.                   *)
(*  \vspace{12pt}}^'                                                       *)
(***************************************************************************)

EXTENDS
  Naturals,
  Jections,
  NaturalsInduction,
  WellFoundedInduction,
  TLAPS,
  Sequences





(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Definitions of injections, surjections, bijections restated as facts.   *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_IsInj ==
  ASSUME NEW S, NEW T, NEW F \in [S -> T],
         \A a,b \in S : F[a] = F[b] => a = b 
  PROVE  F \in Injection(S,T)
BY DEF Injection


THEOREM Fun_IsSurj ==
  ASSUME NEW S, NEW T, NEW F \in [S -> T],
         \A t \in T : \E s \in S : F[s] = t
  PROVE  F \in Surjection(S,T)
BY DEF Surjection


THEOREM Fun_IsBij ==
  ASSUME NEW S, NEW T, NEW F,
         \/ F \in Injection(S,T)
         \/ (F \in [S -> T] /\ \A a,b \in S : F[a] = F[b] => a = b),

         \/ F \in Surjection(S,T)
         \/ (F \in [S -> T] /\ \A t \in T : \E s \in S : F[s] = t)
  PROVE  F \in Bijection(S,T)
BY DEF Bijection, Injection, Surjection




(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Properties of an injection.                                             *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
Fun_InjProp_Qed(S,T,F) ==
/\ F \in [S -> T]
/\ \A a,b \in S : F[a] = F[b] => a = b


THEOREM Fun_InjProp ==
  ASSUME NEW S, NEW T, NEW F \in Injection(S,T)
  PROVE  Fun_InjProp_Qed(S,T,F)
BY DEF Injection, Fun_InjProp_Qed




(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Properties of a surjection.                                             *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
Fun_SurjProp_Qed(S,T,F) ==
/\ F \in [S -> T]
/\ \A t \in T : \E s \in S : F[s] = t


THEOREM Fun_SurjProp ==
  ASSUME NEW S, NEW T, NEW F \in Surjection(S,T)
  PROVE  Fun_SurjProp_Qed(S,T,F)
BY DEF Surjection, Fun_SurjProp_Qed






(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Properties of a bijection.                                              *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
Fun_BijProp_Qed(S,T,F) ==
/\ F \in [S -> T]
/\ F \in Injection(S,T)
/\ F \in Surjection(S,T)
/\ \A a,b \in S : F[a] = F[b] => a = b
/\ \A t \in T : \E s \in S : F[s] = t


THEOREM Fun_BijProp ==
  ASSUME NEW S, NEW T, NEW F \in Bijection(S,T)
  PROVE  Fun_BijProp_Qed(S,T,F)
BY DEF Bijection, Injection, Surjection, Fun_BijProp_Qed



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
<1>1. f \in [S -> T]
  BY Fun_SurjProp DEF Fun_SurjProp_Qed
<1>2. SUFFICES ASSUME f \notin Injection(S,T) PROVE FALSE
  BY Fun_IsBij
<1>3. PICK a,b \in S : a # b /\ f[a] = f[b]
  BY <1>1, <1>2, Fun_IsInj
<1>.  DEFINE U == S \ {b}
<1>4. U \in SUBSET S /\ U # S
  OBVIOUS
<1>.  DEFINE g == [x \in U |-> f[x]]
<1>5. g \in Surjection(U,T)
  <2>1. g \in [U -> T] BY <1>1
  <2>2. ASSUME NEW t \in T PROVE \E u \in U : g[u] = t
    <3>1. CASE t = f[b] BY <1>3, <3>1
    <3>2. CASE t # f[b]
      <4>1. PICK s \in S : f[s] = t
        BY SMT, Fun_SurjProp DEF Fun_SurjProp_Qed  \** Zenon fails ??
      <4>2. s \in U BY <3>2, <4>1
      <4>. QED BY <4>1, <4>2
    <3>3. QED BY <3>1, <3>2
  <2>3. QED BY <2>1, <2>2, Fun_IsSurj
<1>. QED BY <1>4, <1>5



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
BY DEF Injection


THEOREM Fun_SurjTransitive ==
  ASSUME NEW S, NEW T, NEW U,
         NEW F \in Surjection(S,T),
         NEW G \in Surjection(T,U)
  PROVE  [s \in S |-> G[F[s]]] \in Surjection(S,U)
BY DEF Surjection


THEOREM Fun_BijTransitive ==
  ASSUME NEW S, NEW T, NEW U,
         NEW F \in Bijection(S,T),
         NEW G \in Bijection(T,U)
  PROVE  [s \in S |-> G[F[s]]] \in Bijection(S,U)
BY Fun_SurjTransitive, Fun_InjTransitive DEF Bijection



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* The inverse of a surjection is an injection.                            *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_SurjInverse ==
  ASSUME NEW S, NEW T, NEW F \in Surjection(S,T)
  PROVE  JectionInverse(S,T,F) \in Injection(T,S)
BY DEF JectionInverse, Surjection, Injection



(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Properties of the inverse of a bijection.                               *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
Fun_BijInverse_Qed(S,T,F,G) ==
  /\ G \in Bijection(T,S)
  /\ \A s \in S : G[F[s]] = s
  /\ \A t \in T : F[G[t]] = t
  /\ F = JectionInverse(T,S,G)


THEOREM Fun_BijInverse ==
  ASSUME NEW S, NEW T,
         NEW F \in Bijection(S,T),
         NEW G, G = JectionInverse(S,T,F)
  PROVE  Fun_BijInverse_Qed(S,T,F,G)

<1>1. \A a,b \in S : F[a] = F[b] => a = b  BY DEF Bijection, Injection
<1>2. \A t \in T : \E s \in S : F[s] = t   BY DEF Bijection, Surjection
<1>3. F \in [S -> T]  BY DEF Bijection, Injection

<1>4. G = [t \in T |-> CHOOSE s \in S : F[s] = t]  BY DEF JectionInverse
<1>5. G \in [T -> S]  BY <1>2, <1>4

<1>6. \A t \in T : F[G[t]] = t  BY <1>2, <1>4
<1>7. \A s \in S : G[F[s]] = s  BY <1>1, <1>3, <1>4

<1>8. \A a,b \in T : G[a] = G[b] => a = b  BY <1>6
<1>9. \A s \in S : \E t \in T : G[t] = s  BY <1>3, <1>7
<1>10. G \in Bijection(T,S)  BY <1>5, <1>8, <1>9, Fun_IsBij

<1>11. F = JectionInverse(T,S,G)
  <2>10. ASSUME NEW s \in S  PROVE F[s] = CHOOSE t \in T : G[t] = s
    <3>1. PICK a \in T : G[a] = s  BY <1>3, <1>7
    <3>2. \A b \in T : G[b] = s => a = b  BY <3>1, <1>8
    <3>3. F[s] = a  BY <3>1, <1>6
    <3> QED BY <3>1, <3>2, <3>3
  <2> QED BY <2>10, <1>3  DEF JectionInverse

<1> QED BY <1>6, <1>7, <1>11, <1>10 DEF Fun_BijInverse_Qed





(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Subset of a bijection is a bijection.                                   *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
Fun_BijSubset_Qed(S,T,F,S1,T1,F1) ==
  /\ T1 \in SUBSET T
  /\ F1 \in Bijection(S1,T1)


THEOREM Fun_BijSubset ==
  ASSUME
    NEW S, NEW T, NEW F \in Bijection(S,T),
    NEW S1 \in SUBSET S
  PROVE
  LET
    T1 == {F[s] : s \in S1}
    F1 == [s \in S1 |-> F[s]]
  IN
  Fun_BijSubset_Qed(S,T,F,S1,T1,F1)
PROOF
  <1>1. PICK T1 : T1 = {F[s] : s \in S1}  OBVIOUS
  <1>2. PICK F1 : F1 = [s \in S1 |-> F[s]]  OBVIOUS
  
  <1> HIDE DEF Fun_BijProp_Qed
  <1>3. Fun_BijProp_Qed(S,T,F)  BY Fun_BijProp
  <1> USE DEF Fun_BijProp_Qed

  <1>4. F \in [S -> T]  BY <1>3
  <1>5. \A a,b \in S : F[a] = F[b] => a = b  BY <1>3
  <1>6. \A t \in T : \E s \in S : F[s] = t  BY <1>3
  
  <1>7. T1 \in SUBSET T  BY <1>1, <1>4
  
  <1>8. F1 \in [S1 -> T1]  BY <1>1, <1>2
  <1>9. \A a,b \in S1 : F1[a] = F1[b] => a = b  BY <1>2, <1>5
  <1>10. \A t \in T1 : \E s \in S1 : F1[s] = t  BY <1>1, <1>2, <1>6
  
  <1>11. F1 \in Bijection(S1,T1)  BY <1>8, <1>9, <1>10, Fun_IsBij
  
  <1> USE DEF Fun_BijSubset_Qed
  <1> QED BY <1>1, <1>2, <1>7, <1>11






(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* Given F an injection from S to T, then F is a bijection from S to F(S). *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_InjMeansBijImage ==
  ASSUME NEW S, NEW T,
         NEW F \in Injection(S,T),
         NEW FS, FS = {F[s] : s \in S}
  PROVE  F \in Bijection(S,FS)
BY DEF Bijection, Injection, Surjection








-----------------------------------------------------------------------------
(***************************************************************************)
(* `^{\large\bf \vspace{12pt}                                              *)
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
BY DEF ExistsInjection


THEOREM Fun_ExistsSurj ==
  \A S,T : ExistsSurjection(S,T)  <=>  Surjection(S,T) # {}
BY DEF ExistsSurjection


THEOREM Fun_ExistsBij ==
  \A S,T : ExistsBijection(S,T)  <=>  Bijection(S,T) # {}
BY DEF ExistsBijection




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
<1>. PICK x \in T : TRUE  OBVIOUS
<1>. [s \in S |-> IF s \in T THEN s ELSE x] \in Surjection(S,T)
  BY DEF Surjection
<1>. QED  BY DEF ExistsSurjection




(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* If there is a surjection from S to T, then there is an injection from T *)
(* to S.                                                                   *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_ExistsSurjMeansExistsRevInj ==
  ASSUME NEW S, NEW T
  PROVE  ExistsSurjection(S,T)  =>  ExistsInjection(T,S)
BY Fun_SurjInverse DEF ExistsSurjection, ExistsInjection



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
<1>. [s \in S |-> s] \in Bijection(S,S)  BY DEF Bijection, Injection, Surjection
<1>. QED  BY DEF ExistsBijection


THEOREM Fun_ExistsBijSymmetric ==
  ASSUME NEW S, NEW T, ExistsBijection(S,T)
  PROVE  ExistsBijection(T,S)
BY Fun_BijInverse DEF Fun_BijInverse_Qed, ExistsBijection


THEOREM Fun_ExistsBijTransitive ==
  ASSUME NEW S, NEW T, NEW U, ExistsBijection(S,T), ExistsBijection(T,U)  
  PROVE  ExistsBijection(S,U)
BY Fun_BijTransitive DEF ExistsBijection



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
BY Fun_ExistsBijReflexive DEF ExistsBijection, ExistsInjection, Bijection


THEOREM Fun_ExistsSurjReflexive ==
  ASSUME NEW S
  PROVE  ExistsSurjection(S,S)
BY Fun_ExistsBijReflexive DEF ExistsBijection, ExistsSurjection, Bijection


THEOREM Fun_ExistsInjTransitive ==
  ASSUME NEW S, NEW T, NEW U,
         ExistsInjection(S,T), ExistsInjection(T,U)
  PROVE  ExistsInjection(S,U)
BY Fun_InjTransitive DEF ExistsInjection


THEOREM Fun_ExistsSurjTransitive ==
  ASSUME NEW S, NEW T, NEW U,
         ExistsSurjection(S,T), ExistsSurjection(T,U)
  PROVE  ExistsSurjection(S,U)
BY Fun_SurjTransitive DEF ExistsSurjection


-----------------------------------------------------------------------------
(***************************************************************************)
(* `^{\large\bf \vspace{12pt}                                              *)
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
(* `^\url{http://www.proofwiki.org/wiki/Cantor-Bernstein-Schroeder_Theorem/Lemma}^' *)
(* retrieved April 29, 2013.                                               *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_CantorBernsteinSchroeder_Lemma ==
  ASSUME NEW S, NEW T, T \subseteq S, ExistsInjection(S,T)
  PROVE  ExistsBijection(S,T)
PROOF
  <1> PICK F \in Injection(S,T) : TRUE  BY Fun_ExistsInj
  
  <1> USE DEF Fun_InjProp_Qed
  <1>1. Fun_InjProp_Qed(S,T,F)  BY Fun_InjProp
  <1> USE DEF Fun_InjProp_Qed
  
  (*************************************************************************)
  (* Pick Y as S excluding T.                                              *)
  (*************************************************************************)
  <1>2. PICK Y : Y = S \ T  OBVIOUS
  
  (*************************************************************************)
  (* Define Ci[0] as Y, and Ci[i+1] as the image of Ci[i] under F.         *)
  (*************************************************************************)
  <1> DEFINE Ci[i \in Nat] ==
        IF i = 0 THEN Y ELSE {F[s] : s \in Ci[i-1]}
  <1> HIDE DEF Ci
  
  <1>3. \A i \in Nat : Ci[i] =
        IF i = 0 THEN Y ELSE {F[s] : s \in Ci[i-1]}
    (***********************************************************************)
    (* Use NatInductiveDef to prove that Ci equals its definition.         *)
    (***********************************************************************)
    <2> DEFINE
      f0       == Y
      Def(v,i) == {F[s] : s \in v}
      f        == CHOOSE f : f = [i \in Nat |-> IF i = 0 THEN f0 ELSE Def(f[i-1],i)]
    <2> SUFFICES \A i \in Nat : f[i] = IF i = 0 THEN f0 ELSE Def(f[i-1],i)  BY DEF Ci
    <2> HIDE DEF f0, Def, f
    <2> SUFFICES NatInductiveDefConclusion(f,f0,Def)  BY DEF NatInductiveDefConclusion
    <2> SUFFICES NatInductiveDefHypothesis(f,f0,Def)  BY NatInductiveDef
    <2> QED BY DEF NatInductiveDefHypothesis, f
  
  (*************************************************************************)
  (* Applying F to an element of Ci[i] produces an element of Ci[i+1].     *)
  (*************************************************************************)
  <1>4. ASSUME NEW i \in Nat, NEW s \in Ci[i]
        PROVE F[s] \in Ci[i+1]
        BY <1>3, SMT
  
  (*************************************************************************)
  (* Each element of Ci[i+1] is the application of F to some element in    *)
  (* Ci[i].                                                                *)
  (*************************************************************************)
  <1>5. ASSUME NEW i \in Nat, NEW t \in Ci[i+1]
        PROVE \E s \in Ci[i] : F[s] = t
        BY <1>3, SMT
    
  (*************************************************************************)
  (* Each Ci[i] \subseteq S.                                               *)
  (*************************************************************************)
  <1>6. \A i \in Nat : Ci[i] \subseteq S
    <2> DEFINE Prop(i) == Ci[i] \subseteq S
    <2> SUFFICES \A i \in Nat : Prop(i)  OBVIOUS
    <2>1. Prop(0)  BY <1>2, <1>3
    <2>2. ASSUME NEW i \in Nat, Prop(i)  PROVE Prop(i+1)
      <3> SUFFICES ASSUME NEW t \in Ci[i+1]  PROVE t \in S  OBVIOUS
      <3>1. PICK s \in Ci[i] : F[s] = t  BY <1>5
      <3>2. s \in S  BY <2>2
      <3> QED BY <3>1, <3>2, <1>1
    <2> HIDE DEF Prop
    <2> QED BY <2>1, <2>2, NatInduction, Isa

  (*************************************************************************)
  (* Pick C as the union of all Ci[i].                                     *)
  (*************************************************************************)
  <1>7. PICK C : C = UNION {Ci[i] : i \in Nat}  OBVIOUS
  <1>8. C \subseteq S  BY <1>6, <1>7
  
  (*************************************************************************)
  (* Pick FC as the image of C under F.                                    *)
  (*************************************************************************)
  <1>9. PICK FC : FC = {F[c] : c \in C}  OBVIOUS
  <1>10. FC \subseteq T  BY <1>1, <1>8, <1>9, Isa
  
  (*************************************************************************)
  (* C = Y \cup FC because Ci[0] = Y and Ci[i+1] = image of Ci[i] under F. *)
  (*************************************************************************)
  <1>11. C = Y \cup FC
    <2>1. ASSUME NEW c \in C  PROVE c \in Y \cup FC
      <3>1. PICK i \in Nat : c \in Ci[i]  BY <1>7
      <3>2. CASE i = 0  BY <3>1, <3>2, <1>3
      <3>3. CASE i # 0
        <4>1. PICK s \in Ci[i-1] : F[s] = c  BY <3>1, <3>3, <1>5, SMT
        <4>2. s \in C  BY <3>3, <1>7, SMT
        <4> QED BY <4>1, <4>2, <1>9
      <3> QED BY <3>2, <3>3
    <2>2. ASSUME NEW c \in Y \cup FC  PROVE c \in C
      <3>1. CASE c \in Y  BY <3>1, <1>3, <1>7
      <3>2. CASE c \in FC
        <4>1. PICK s \in C : F[s] = c  BY <3>2, <1>9
        <4>2. PICK i \in Nat : s \in Ci[i]  BY <4>1, <1>7
        <4>3. F[s] \in Ci[i+1]  BY <4>2, <1>4
        <4> QED BY <4>1, <4>3, <1>7, SMT
      <3> QED BY <3>1, <3>2
    <2> QED BY <2>1, <2>2
  
  (*************************************************************************)
  (* S \ C is the same as T \ FC.                                          *)
  (*************************************************************************)
  <1>12. S \ C = T \ FC  BY <1>2, <1>11

  (*************************************************************************)
  (* Pick H as F on C and the identity on S \ C.  Since F (restricted to   *)
  (* C) is a bijection from C to FC and S \ C = T \ FC, this makes H a     *)
  (* bijection from S to T.                                                *)
  (*************************************************************************)
  <1>13. PICK H : H = [s \in S |-> IF s \in C THEN F[s] ELSE s]  OBVIOUS
  <1>14. H \in Bijection(S,T)
    (***********************************************************************)
    (* A useful lemma.  If a \in C and b \notin C, then H[a] # H[b].       *)
    (***********************************************************************)
    <2>1. ASSUME NEW a \in S, NEW b \in S, a \in C, b \notin C  PROVE H[a] # H[b]
      <3>1. H[a] \in FC  BY <2>1, <1>1, <1>9, <1>13
      <3>2. H[b] \in T \ FC  BY <2>1, <1>12, <1>13
      <3> QED BY <3>1, <3>2
      
    <2>2. H \in [S -> T]
      <3> SUFFICES ASSUME NEW s \in S  PROVE H[s] \in T  BY <1>13
      <3>1. CASE s \in C  BY <3>1, <1>1, <1>10, <1>13
      <3>2. CASE s \notin C  BY <3>2, <1>12, <1>13
      <3> QED BY <3>1, <3>2
      
    <2>3. ASSUME NEW a \in S, NEW b \in S, H[a] = H[b]  PROVE a = b
      <3> H[a] = H[b]  BY <2>3
      <3>1. CASE a \in C /\ b \in C  BY <3>1, <1>1, <1>13
      <3>2. CASE a \in C /\ b \notin C  BY <3>2, <2>1  (* impossible by lemma *)
      <3>3. CASE a \notin C /\ b \in C  BY <3>3, <2>1  (* impossible by lemma *)
      <3>4. CASE a \notin C /\ b \notin C  BY <3>4, <1>13
      <3> QED BY <3>1, <3>2, <3>3, <3>4
      
    <2>4. ASSUME NEW t \in T  PROVE \E s \in S : H[s] = t
      <3>1. CASE t \in FC  BY <3>1, <1>8, <1>9, <1>13
      <3>2. CASE t \notin FC  BY <3>2, <1>12, <1>13
      <3> QED BY <3>1, <3>2
    
    <2> QED BY <2>2, <2>3, <2>4, Fun_IsBij
 
  <1> QED BY <1>14, Fun_ExistsBij





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

<1>1. PICK F : F \in Injection(S,T)  BY DEF ExistsInjection
<1>2. PICK G : G \in Injection(T,S)  BY DEF ExistsInjection
<1>. DEFINE RngG == {G[t] : t \in T}
            GF == [s \in S |-> G[F[s]]]
<1>3. RngG \subseteq S  BY <1>2 DEF Injection
<1>4. GF \in Injection(S, RngG)  BY <1>1, <1>2 DEF Injection
<1>5. ExistsBijection(S, RngG)  BY <1>3, <1>4, Fun_CantorBernsteinSchroeder_Lemma DEF ExistsInjection
<1>6. ExistsBijection(T, RngG)  BY <1>2, Fun_InjMeansBijImage DEF ExistsBijection
<1>. QED  BY <1>5, <1>6, Fun_ExistsBijSymmetric, Fun_ExistsBijTransitive



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
<1>. ExistsInjection(T,S)
  BY Fun_SurjInverse DEF ExistsInjection, ExistsSurjection
<1>. QED  BY Fun_CantorBernsteinSchroeder



THEOREM Fun_ExistSurjAndSurjThenBij == 
  ASSUME NEW S, NEW T,
         ExistsSurjection(S,T), ExistsSurjection(T,S)
  PROVE  ExistsBijection(S,T)
<1>. ExistsInjection(S,T)
  BY Fun_SurjInverse DEF ExistsInjection, ExistsSurjection
<1>2. QED  BY Fun_ExistInjAndSurjThenBij




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

<1>1. ExistsBijection(S,T) <=> ExistsBijection(T,S)
  BY Fun_ExistsBijSymmetric
<1>2. ExistsInjection(S,T) /\ ExistsInjection(T,S) => ExistsBijection(S,T)
  BY Fun_CantorBernsteinSchroeder
<1>3. \A S1, T1 :  ExistsBijection(S1,T1) => ExistsSurjection(S1,T1)
  BY DEF ExistsBijection, ExistsSurjection, Bijection
<1>4. \A S1,T1 : ExistsSurjection(S1,T1) => ExistsInjection(T1,S1)
  BY Fun_ExistsSurjMeansExistsRevInj
<1> QED BY <1>1, <1>2, <1>3, <1>4


-----------------------------------------------------------------------------
(***************************************************************************)
(* `^{\large\bf \vspace{12pt}                                              *)
(*  Facts about jections involving 1..n.                                   *)
(*  \vspace{12pt}}^'                                                       *)
(***************************************************************************)



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
PROOF
  (*************************************************************************)
  (* n \leq m means Injection exists.  This part is easy.                  *)
  (*************************************************************************)
  <1>1. ASSUME n \leq m PROVE [i \in 1..n |-> i] \in Injection(1..n, 1..m)
    BY SMT, <1>1 DEF Injection

  (*************************************************************************)
  (* Injection exists means n \leq m.  This part is harder.                *)
  (*************************************************************************)
  <1>2. ASSUME ExistsInjection(1..n,1..m)  PROVE n \leq m
    <2>. DEFINE P(mm) == \A nn \in Nat : nn > mm => Injection(1..nn, 1..mm) = {}
    <2>1. SUFFICES \A mm \in Nat : P(mm)  BY SMT, <1>2 DEF ExistsInjection
    <2>2. P(0)  BY Z3 DEF Injection
    <2>3. ASSUME NEW mm \in Nat, P(mm)  PROVE P(mm+1)
      <3>1. SUFFICES ASSUME NEW nn \in Nat, nn > mm+1,
                            NEW f \in Injection(1..nn, 1..mm+1)
                     PROVE  FALSE
        OBVIOUS
      <3>2. ASSUME NEW i \in 1..nn, f[i] = mm+1 PROVE FALSE
        <4>. DEFINE g == [j \in 1..nn-1 |-> IF j<i THEN f[j] ELSE f[j+1]]
        <4>1. nn-1 \in Nat /\ nn-1 > mm  BY SMT, <3>1
        <4>2. g \in Injection(1..nn-1, 1..mm)  BY SMT, <3>2 DEF Injection
        <4>. QED  BY <4>1, <4>2, P(mm) DEF Injection
      <3>3. ASSUME ~\E i \in 1..nn : f[i] = mm+1  PROVE FALSE
        <4>1. f \in Injection(1..nn, 1..mm)  BY SMT, <3>3 DEF Injection
        <4>. QED  BY SMT, <4>1, <3>1, P(mm)
      <3>. QED  BY <3>2, <3>3
    <2>. QED  BY Isa, NatInduction, <2>2, <2>3

  <1> QED BY <1>1, <1>2 DEF ExistsInjection






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

  (*************************************************************************)
  (* Pick the smallest m \in Nat for which there is a surjection from      *)
  (* 1..m to S.                                                            *)
  (*************************************************************************)
<1>1. PICK m \in Nat :
        /\ ExistsSurjection(1..m, S)
        /\ \A k \in Nat : k < m => ~ExistsSurjection(1..k, S)
  <2>. DEFINE NN == { m \in Nat : ExistsSurjection(1..m, S) }
  <2>1. PICK m \in NN : \A k \in NN : <<k, m>> \notin OpToRel(<, Nat)
     BY WFMin, NatLessThanWellFounded
  <2>. QED
    BY <2>1 DEF OpToRel

<1>2. m <= n  BY SMT, <1>1
  (*************************************************************************)
  (* Any surjection from 1..m to S is bijective.                           *)
  (*************************************************************************)
<1>3. PICK f \in Surjection(1..m, S) : TRUE  BY <1>1 DEF ExistsSurjection
<1>4. ASSUME f \notin Injection(1..m, S)  PROVE FALSE
  <2>1. f \in [1..m -> S]  BY <1>3 DEF Surjection
  <2>2. PICK i,j \in 1..m : i < j /\ f[i] = f[j]
    <3>1. PICK ii,jj \in 1..m : ii # jj /\ f[ii] = f[jj]
      BY <2>1, <1>4 DEF Injection
    <3>2. CASE ii < jj  BY <3>1, <3>2
    <3>3. CASE jj < ii  BY <3>1, <3>3
    <3>. QED  BY SMT, <3>1, <3>2, <3>3
  <2>3. m-1 \in Nat  BY SMT, <2>2
  <2>. DEFINE g == [k \in 1..m-1 |-> IF k=j THEN f[m] ELSE f[k]]
  <2>4. g \in Surjection(1..m-1, S)
    <3>1. g \in [1..m-1 -> S]  BY SMT, <2>1
    <3>2. ASSUME NEW s \in S  PROVE \E k \in 1..m-1 : g[k] = s
      <4>. PICK l \in 1..m : f[l] = s  BY <1>3 DEF Surjection
      <4>. QED  BY SMT, <2>2
    <3>. QED  BY <3>1, <3>2 DEF Surjection
  <2>. QED  BY SMT, <2>3, <2>4, <1>1 DEF ExistsSurjection

<1>. QED  BY <1>2, <1>3, <1>4 DEF ExistsBijection, Bijection    




(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* A surjection from some 1..n to S exists iff a bijection from some       *)
(* 1..m to S exists.                                                       *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_NatSurjEquivNatBij ==
  ASSUME NEW S
  PROVE  (\E n \in Nat : ExistsSurjection(1..n,S))
    <=>  (\E m \in Nat : ExistsBijection(1..m,S))
BY Fun_NatSurjImpliesNatBij, Fun_ExistsBijEquiv



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
BY SMT, Fun_NatInjLeq, Fun_ExistsBijEquiv, Fun_ExistsBijTransitive



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
<1>1. ASSUME ExistsBijection(1..0, S), S # {} PROVE FALSE
  <2>1. ExistsInjection(S, 1..0)  BY <1>1, Fun_ExistsBijEquiv
  <2>2. QED  BY SMT, <1>1, <2>1 DEF ExistsInjection, Injection
<1>2. ASSUME S = {}  PROVE ExistsBijection(1..0, S)
  BY SMT, <1>2, Fun_ExistsBijReflexive
<1>3. QED  BY <1>1, <1>2


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
<1>1. ASSUME NEW f \in Bijection(1..1, S)  PROVE \E s : S = {s}
  BY SMT DEF Bijection, Injection, Surjection
<1>2. ASSUME NEW s, S = {s}  PROVE [i \in 1..1 |-> s] \in Bijection(1..1, S)
  BY SMT, <1>2 DEF Bijection, Injection, Surjection
<1>. QED  BY <1>1, <1>2 DEF ExistsBijection




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

<1>1. CASE T = {}  BY Force, <1>1, Fun_NatBijEmpty
<1>2. CASE T # {}
  <2>0. ExistsSurjection(1..m, S)  BY Fun_ExistsBijEquiv
  <2>1. ExistsSurjection(S, T)  BY <1>2, Fun_ExistsSurjSubset
  <2>2. ExistsSurjection(1..m, T)  BY <2>0, <2>1, Fun_ExistsSurjTransitive
  <2>. QED  BY <2>2, Fun_NatSurjImpliesNatBij
<1> QED BY <1>1, <1>2
  



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

<1>1. PICK F \in Bijection(1..m, S) : TRUE  BY DEF ExistsBijection
<1>2. F \in [1..m -> S]  BY <1>1 DEF Bijection, Injection
<1>3. \A s \in S : \E i \in 1..m : F[i] = s  BY <1>1 DEF Bijection, Surjection
<1>4. \A i,j \in 1..m : F[i] = F[j] => i = j  BY <1>1 DEF Bijection, Injection

<1>. DEFINE G == [i \in 1..m+1 |-> IF i <= m THEN F[i] ELSE x]
<1>10. G \in [1..m+1 -> S \cup {x}]  BY SMT, <1>2
<1>20. ASSUME NEW t \in S \cup {x}  PROVE \E i \in 1..m+1 : G[i] = t  BY SMT, <1>3
<1>30. ASSUME NEW i \in 1..m+1, NEW j \in 1..m+1, G[i] = G[j]  PROVE i = j
  BY SMT, <1>2, <1>4, <1>30
<1>40. G \in Bijection(1..m+1, S \cup {x})
  BY <1>10, <1>20, <1>30 DEF Bijection, Injection, Surjection  
<1>. QED  BY <1>40 DEF ExistsBijection




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

<1>1. PICK n \in Nat : ExistsBijection(1..n, S \ {x})  BY Fun_NatBijSubset
<1>2. ExistsBijection(1..n+1, (S \ {x}) \cup {x})  BY <1>1, Fun_NatBijAddElem
<1>3. ExistsBijection(1..n+1, S)  BY <1>2
<1>4. n = m-1  BY SMT, <1>3, Fun_NatBijSame
<1>. QED  BY <1>1, <1>4



(* doesn't seem to be used anywhere, and is superseded in practice by cardinality theorems

(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* If there exists a bijection from 1..m to S (for some m \in Nat) and     *)
(* there exists a bijection from 1..n to T (for some n \in Nat), and S and *)
(* T are disjoint, then there exists a bijection from 1..(m+n) to S \cup   *)
(* T.                                                                      *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM Fun_NatBijDisjointUnion ==
  ASSUME
    NEW S, NEW m \in Nat, ExistsBijection(1..m,S),
    NEW T, NEW n \in Nat, ExistsBijection(1..n,T),
    S \cap T = {}
  PROVE
  ExistsBijection(1..(m+n),S \cup T)
PROOF
  (*************************************************************************)
  (* Restate the assumptions and then remove them from automatic use.  It  *)
  (* seems these assumptions cause some of the SMT appeals to fail.        *)
  (*************************************************************************)
  <1>1. ExistsBijection(1..m,S)  OBVIOUS
  <1>2. ExistsBijection(1..n,T)  OBVIOUS
  <1>3. S \cap T = {}  OBVIOUS
  <1> USE ONLY TRUE
  
  <1> USE DEF ExistsBijection
  <1> USE DEF Fun_BijProp_Qed
  
  (*************************************************************************)
  (* Proof by induction on n.                                              *)
  (*************************************************************************)
  <1> DEFINE
    Prop(i) ==
      \A T1 :
      ExistsBijection(1..i,T1) /\ T1 \cap S = {}  => 
      ExistsBijection(1..(m+i),S \cup T1)

  <1>4. \A i \in Nat : Prop(i)
    <2>1. Prop(0)
      (*********************************************************************)
      (* Base case.                                                        *)
      (*********************************************************************)
      <3>1. SUFFICES ASSUME NEW T1, ExistsBijection(1..0,T1), T1 \cap S = {}
            PROVE ExistsBijection(1..(m+0),S \cup T1)
            OBVIOUS
      <3>2. T1 = {}  BY <3>1, Fun_NatBijEmpty
      <3>3. m+0 = m  BY SMT
      <3>4. S \cup T1 = S  BY <3>2
      <3> QED BY <3>3, <3>4, <1>1

    <2>2. ASSUME NEW i \in Nat, Prop(i)  PROVE Prop(i+1)
      (*********************************************************************)
      (* Inductive case.                                                   *)
      (*********************************************************************)
      <3>1. PICK j \in Nat : j = i+1  BY SMT
      <3>2. SUFFICES ASSUME NEW T1, ExistsBijection(1..j,T1), T1 \cap S = {}
            PROVE ExistsBijection(1..(m+j),S \cup T1)
            BY <3>1

      <3>3. j # 0  BY <3>1, SMT
      <3>4. ~ExistsBijection(1..0,T1)  BY <3>2, <3>3, Fun_NatBijSame
      <3>5. T1 # {}  BY <3>4, Fun_NatBijEmpty
      
      (*********************************************************************)
      (* Construct T2 by removing element t from T1.                       *)
      (*********************************************************************)
      <3>6. PICK t : t \in T1  BY <3>5
      <3>7. t \notin S  BY <3>2, <3>6
      <3>8. PICK T2 : T2 = T1 \ {t}  OBVIOUS
      <3>9. t \notin T2  BY <3>8
      <3>10. T2 \subseteq T1  BY <3>8
      <3>11. T1 = T2 \cup {t}  BY <3>6, <3>8
      <3>12. T2 \cap S = {}  BY <3>2, <3>8
      
      (*********************************************************************)
      (* Show that there exists a bijection from 1..i to T2.               *)
      (*********************************************************************)
      <3>13. PICK j2 \in Nat : ExistsBijection(1..j2,T2)  BY <3>2, <3>10, Fun_NatBijSubset
      <3>14. ExistsBijection(1..(j2+1),T1)  BY <3>9, <3>11, <3>13, Fun_NatBijAddElem
      <3>15. j2+1 \in Nat  BY SMT
      <3>16. j = j2 + 1  BY <3>2, <3>14, <3>15, Fun_NatBijSame
      <3>17. j2 = i  BY <3>1, <3>16, SMT
      <3>18. ExistsBijection(1..(m+i),S \cup T2)  BY <3>12, <3>13, <3>17, <2>2

      (*********************************************************************)
      (* By the inductive hypothesis, there exists a bijection F from      *)
      (* 1..(m+i) to S \cup T2.                                            *)
      (*********************************************************************)
      <3>19. PICK F : F \in Bijection(1..(m+i),S \cup T2)  BY <3>18
      <3>20. Fun_BijProp_Qed(1..(m+i),S \cup T2,F)
        <4> HIDE DEF Fun_BijProp_Qed
        <4> QED BY <3>19, Fun_BijProp
      <3>21. F \in [1..(m+i) -> S \cup T2]  BY <3>20
      <3>22. \A s \in S \cup T2 : \E k \in 1..(m+i) : F[k] = s  BY <3>20
      <3>23. \A a,b \in 1..(m+i) : F[a] = F[b] => a = b  BY <3>20

      (*********************************************************************)
      (* Construct G by extending F to cover t.  G is a bijection from     *)
      (* 1..(m+j) to S \cup T1.                                            *)
      (*********************************************************************)
      <3>24. PICK G : G = [k \in 1..(m+j) |-> IF k \leq (m+i) THEN F[k] ELSE t]  OBVIOUS
      <3>25. G \in Bijection(1..(m+j),S \cup T1)
        <4>1. \A a \in 1..(m+j) : a \leq m+i => a \in 1..(m+i)  BY <3>1, SMT
        <4>2. \A a,b \in 1..(m+j) : a \leq m+i /\ ~(b \leq m+i) => G[a] # G[b]
              BY <4>1, <3>7, <3>9, <3>21, <3>24

        <4>3. G \in [1..(m+j) -> S \cup T1]
          (*****************************************************************)
          (* Function.                                                     *)
          (*****************************************************************)
          <5>1. SUFFICES ASSUME NEW k \in 1..(m+j)  PROVE G[k] \in S \cup T1  BY <3>24
          <5>2. CASE k \leq (m+i)
            <6>1. G[k] = F[k]  BY <5>2, <3>24
            <6>2. F[k] \in S \cup T2  BY <5>2, <4>1, <3>21
            <6> QED BY <6>1, <6>2, <3>10
          <5>3. CASE ~(k \leq (m+i))
            <6>1. G[k] = t  BY <5>3, <3>24
            <6> QED BY <6>1, <3>6
          <5> QED BY <5>2, <5>3
        <4>4. ASSUME NEW s \in S \cup T1  PROVE \E k \in 1..(m+j) : G[k] = s
          (*****************************************************************)
          (* Injective.                                                    *)
          (*****************************************************************)
          <5>1. CASE s \in S \cup T2
            <6>1. PICK k \in 1..(m+i) : F[k] = s  BY <5>1, <3>22
            <6>2. k \in 1..(m+j)  BY <3>1, SMT
            <6>3. k \leq m+i  BY SMT
            <6>4. G[k] = F[k]  BY <6>2, <6>3, <3>24
            <6> QED BY <6>1, <6>2, <6>4
          <5>2. CASE s = t
            <6>1. m+j \in 1..(m+j)  BY <3>3, SMT
            <6>2. ~(m+j \leq m+i)  BY <3>1, SMT
            <6>3. G[m+j] = t  BY <6>1, <6>2, <3>24
            <6> QED BY <6>1, <6>3, <5>2
          <5> QED BY <5>1, <5>2, <3>11
        <4>5. ASSUME NEW a \in 1..(m+j), NEW b \in 1..(m+j), G[a] = G[b]  PROVE a = b
          (*****************************************************************)
          (* Surjective.                                                   *)
          (*****************************************************************)
          <5> G[a] = G[b]  BY <4>5
          <5>1. CASE  (a \leq m+i) /\  (b \leq m+i)  BY <5>1, <4>1, <3>23, <3>24
          <5>2. CASE  (a \leq m+i) /\ ~(b \leq m+i)  BY <5>2, <4>2  (* impossible *)
          <5>3. CASE ~(a \leq m+i) /\  (b \leq m+i)  BY <5>3, <4>2  (* impossible *)
          <5>4. CASE ~(a \leq m+i) /\ ~(b \leq m+i)  BY <5>4, <3>1, SMT
          <5> QED BY <5>1, <5>2, <5>3, <5>4
        <4> QED BY <4>3, <4>4, <4>5, Fun_IsBij
      <3> QED BY <3>1, <3>25
    <2> HIDE DEF Prop
    <2> QED BY <2>1, <2>2, NatInduction
    
  <1> QED BY <1>1, <1>2, <1>3, <1>4

*)



=============================================================================
\* Modification History
\* Last modified Tue Jul 09 19:00:04 CEST 2013 by merz
\* Last modified Tue Jun 11 12:30:05 CEST 2013 by bhargav
\* Last modified Fri May 31 15:27:41 CEST 2013 by bhargav
\* Last modified Fri May 03 12:55:32 PDT 2013 by tomr
\* Created Thu Apr 11 10:36:10 PDT 2013 by tomr
