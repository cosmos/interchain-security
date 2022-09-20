---------------------- MODULE FiniteSetTheorems_proofs ----------------------
(***************************************************************************)
(* `^{\large\bf \vspace{12pt}                                              *)
(*  Facts about finite sets and their cardinality.                         *)
(*  Originally contributed by Tom Rodeheffer, MSR.                         *)
(*  \vspace{12pt}}^'                                                       *)
(***************************************************************************)

EXTENDS
  FiniteSets,
  Sequences,
  FunctionTheorems,
  WellFoundedInduction,
  TLAPS

(***************************************************************************)
(* Arithmetic lemma that is currently not proved.                          *)
(***************************************************************************)
LEMMA TwoExpLemma ==
  ASSUME NEW n \in Nat
  PROVE  2^(n+1) = 2^n + 2^n
PROOF OMITTED


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

<1>1. ASSUME IsFiniteSet(S)  PROVE \E n \in Nat : ExistsSurjection(1..n,S)
  <2>1. PICK Q \in Seq(S) : \A s \in S : \E i \in 1..Len(Q) : Q[i] = s
    BY <1>1 DEF IsFiniteSet
  <2>2. /\ Len(Q) \in Nat
        /\ Q \in Surjection(1..Len(Q),S)
    BY <2>1 DEF Surjection
  <2> QED BY <2>2 DEF ExistsSurjection

<1>2. ASSUME NEW n \in Nat, ExistsSurjection(1..n,S)  PROVE  IsFiniteSet(S)
  BY <1>2 DEF IsFiniteSet, ExistsSurjection, Surjection

<1> QED BY <1>1, <1>2


LEMMA FS_NatBijection ==
  ASSUME NEW S
  PROVE  IsFiniteSet(S) <=> \E n \in Nat : ExistsBijection(1..n,S)
BY FS_NatSurjection, Fun_NatSurjEquivNatBij


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
PROOF
  <1> DEFINE
    (***********************************************************************)
    (* Size of set T.                                                      *)
    (***********************************************************************)
    Size(T)  == CHOOSE i \in Nat : ExistsBijection(1..i,T)
    
    (***********************************************************************)
    (* Size function for subsets of S.                                     *)
    (***********************************************************************)
    SZ       == [ T \in SUBSET S |-> Size(T) ]
    
    (***********************************************************************)
    (* Formula part of the CS property for element T.                      *)
    (***********************************************************************)
    fn(CS,T) == IF T = {} THEN 0 ELSE 1 + CS[T \ {CHOOSE x : x \in T}] 
    
    (***********************************************************************)
    (* The CS property.                                                    *)
    (***********************************************************************)
    IsCS(CS) == CS = [T \in SUBSET S |-> fn(CS,T)]
    
    (***********************************************************************)
    (* CS function for subsets of S.  Since this is defined as CHOOSE      *)
    (* something that satisfies the CS property, we do not know that the   *)
    (* CS function actually satisfies the CS property until we know that   *)
    (* there exists something that satisfies the CS property.              *)
    (***********************************************************************)
    CS       == CHOOSE CS : IsCS(CS) 
  
  <1> HIDE DEF SZ, CS, fn
  

  (*************************************************************************)
  (* The SZ function satisfies the CS property.                            *)
  (*************************************************************************)
  <1>1. IsCS(SZ)
    (***********************************************************************)
    (* Use induction on the size of T to show that the values match at     *)
    (* each T \in SUBSET S.                                                *)
    (***********************************************************************)
    <2> DEFINE
      Prop(i) == \A T \in SUBSET S : ExistsBijection(1..i,T) => SZ[T] = fn(SZ,T)

    <2>1. \A i \in Nat : Prop(i)
      <3>1. Prop(0)
        (*******************************************************************)
        (* Base step.                                                      *)
        (*******************************************************************)
        <4>1. SUFFICES ASSUME NEW T \in SUBSET S, ExistsBijection(1..0,T)
                       PROVE  SZ[T] = fn(SZ,T)
              OBVIOUS
        <4>2. Size(T) = 0  BY <4>1, Fun_NatBijSame
        <4>3. T = {}  BY <4>1, Fun_NatBijEmpty
        <4>4. SZ[T] = 0  BY <4>2  DEF SZ
        <4>5. fn(SZ,T) = 0  BY <4>3  DEF fn
        <4> QED BY <4>4, <4>5
        
      <3>2. ASSUME NEW i \in Nat, Prop(i)  PROVE Prop(i+1)
        (*******************************************************************)
        (* Inductive step.                                                 *)
        (*******************************************************************)
        <4>1. PICK j \in Nat : j = i+1  BY Isa
        <4>2. j # 0  BY <4>1, SMT
        <4>3. i = j-1  BY <4>1, SMT
        <4>4. SUFFICES ASSUME NEW T \in SUBSET S, ExistsBijection(1..j,T)
                       PROVE  SZ[T] = fn(SZ,T)
              BY <4>1
        <4>5. ~ExistsBijection(1..0,T)  BY <4>2, <4>4, Fun_NatBijSame
        <4>6. T # {}  BY <4>5, Fun_NatBijEmpty
        <4>7. Size(T) = j  BY <4>4, Fun_NatBijSame
        <4>8. PICK t \in T : t = CHOOSE x : x \in T  BY <4>6
        <4>9. PICK U \in SUBSET S : U = T \ {t}  OBVIOUS
        <4>10. ExistsBijection(1..i,U)  BY <4>3, <4>4, <4>9, Fun_NatBijSubElem
        <4>11. SZ[U] = fn(SZ,U)  BY <4>10, <3>2
        <4>12. SZ[U] = i  BY <4>10, Fun_NatBijSame  DEF SZ
        <4>13. fn(SZ,T) = 1 + SZ[U]  BY <4>6, <4>8, <4>9  DEF fn
        <4>14. fn(SZ,T) = j  BY <4>1, <4>12, <4>13, SMT
        <4>15. SZ[T] = j  BY <4>7  DEF SZ
        <4> QED BY <4>14, <4>15

      <3> HIDE DEF Prop
      <3> QED BY Isa, <3>1, <3>2, NatInduction

    <2> SUFFICES ASSUME NEW T \in SUBSET S  PROVE SZ[T] = fn(SZ,T)  BY DEF SZ
    <2>2. PICK i \in Nat : ExistsBijection(1..i,T) BY Fun_NatBijSubset
    <2> QED BY <2>1, <2>2

    
  (*************************************************************************)
  (* Any two things that satisfy the CS property must be equal.            *)
  (*************************************************************************)
  <1>2. ASSUME
          NEW CS1, IsCS(CS1),
          NEW CS2, IsCS(CS2)
        PROVE CS1 = CS2
    (***********************************************************************)
    (* Use induction on the size of T to show that the values match at     *)
    (* each T \in SUBSET S.                                                *)
    (***********************************************************************)
    <2> DEFINE
      Prop(i) == \A T \in SUBSET S : ExistsBijection(1..i,T) => CS1[T] = CS2[T]

    <2>1. \A i \in Nat : Prop(i)
      <3>1. Prop(0)
        (*******************************************************************)
        (* Base step.                                                      *)
        (*******************************************************************)
        <4>1. SUFFICES ASSUME NEW T \in SUBSET S, ExistsBijection(1..0,T)
                       PROVE CS1[T] = CS2[T]
              OBVIOUS
        <4>2. T = {}  BY <4>1, Fun_NatBijEmpty
        <4>3. fn(CS1,T) = 0  BY <4>2  DEF fn
        <4>4. fn(CS2,T) = 0  BY <4>2  DEF fn
        <4> QED BY <4>3, <4>4, <1>2
        
      <3>2. ASSUME NEW i \in Nat, Prop(i)  PROVE Prop(i+1)
        (*******************************************************************)
        (* Inductive step.                                                 *)
        (*******************************************************************)
        <4>1. PICK j \in Nat : j = i+1  BY Isa
        <4>2. j # 0  BY <4>1, SMT
        <4>3. i = j-1  BY <4>1, SMT
        <4>4. SUFFICES ASSUME NEW T \in SUBSET S, ExistsBijection(1..j,T)
              PROVE CS1[T] = CS2[T]
              BY <4>1
        <4>5. ~ExistsBijection(1..0,T)  BY <4>2, <4>4, Fun_NatBijSame
        <4>6. T # {}  BY <4>5, Fun_NatBijEmpty
        <4>7. PICK t \in T : t = CHOOSE x : x \in T  BY <4>6
        <4>8. PICK U \in SUBSET S : U = T \ {t}  OBVIOUS
        <4>9. ExistsBijection(1..i,U)  BY <4>3, <4>4, <4>8, Fun_NatBijSubElem
        <4>10. CS1[U] = CS2[U]  BY <4>9, <3>2
        <4>11. CS1[T] = 1 + CS1[U]  BY <4>6, <4>7, <4>8, <1>2  DEF fn
        <4>12. CS2[T] = 1 + CS2[U]  BY <4>6, <4>7, <4>8, <1>2  DEF fn
        <4> QED BY <4>10, <4>11, <4>12
        
      <3> HIDE DEF Prop
      <3> QED BY Isa, <3>1, <3>2, NatInduction
    
    <2> SUFFICES ASSUME NEW T \in SUBSET S  PROVE CS1[T] = CS2[T]  BY <1>2
    <2>2. PICK i \in Nat : ExistsBijection(1..i,T)  BY Fun_NatBijSubset
    <2> QED BY <2>1, <2>2
  
    
  (*************************************************************************)
  (* Since SZ satisfies the CS property, the CS function must satisfy the  *)
  (* CS property.  And it must be the same as SZ.                          *)
  (*************************************************************************)
  <1>3. IsCS(CS)  BY <1>1  DEF CS
  <1>4. CS = SZ  BY <1>1, <1>2, <1>3


  <1>5. Cardinality(S) = CS[S]  BY DEF Cardinality, CS, fn
  <1>6. S \in SUBSET S  OBVIOUS
  <1>7. SZ[S] = Size(S)  BY <1>6  DEF SZ
  <1>8. Size(S) = n  BY Fun_NatBijSame
  <1> QED BY <1>4, <1>5, <1>7, <1>8


(***************************************************************************)
(* Corollary: a surjection from 1..n to S provides a cardinality bound.    *)
(***************************************************************************)
THEOREM FS_SurjCardinalityBound ==
  ASSUME NEW S, NEW n \in Nat, ExistsSurjection(1..n, S)
  PROVE  Cardinality(S) <= n
BY Fun_NatSurjImpliesNatBij, FS_CountingElements


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
BY FS_NatBijection, FS_CountingElements



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
BY FS_CardinalityType, Fun_ExistsBijTransitive, FS_CountingElements,
   FS_NatBijection


THEOREM FS_SameCardinalityBij ==
  ASSUME NEW S, NEW T, IsFiniteSet(S), IsFiniteSet(T),
         Cardinality(S) = Cardinality(T)
  PROVE  ExistsBijection(S,T)
BY FS_CardinalityType, Fun_ExistsBijSymmetric, Fun_ExistsBijTransitive


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

<1>1. SUFFICES ASSUME NEW a \in S, NEW b \in S, a # b, f[a] = f[b]
      PROVE FALSE
  BY DEF Injection, Surjection
<1>. DEFINE n == Cardinality(S)
<1>. n \in Nat  BY FS_CardinalityType
<1>. PICK g \in Bijection(1..n, S) : TRUE
  BY FS_CardinalityType DEF ExistsBijection
<1>2. PICK i,j \in 1 .. n : 
          /\ i < j 
          /\ \/ g[i] = a /\ g[j] = b
             \/ g[i] = b /\ g[j] = a
  <2>1. PICK i,j \in 1 .. n : i # j /\ g[i] = a /\ g[j] = b
    BY <1>1 DEF Bijection, Surjection
  <2>2. CASE i < j  BY <2>1, <2>2
  <2>3. CASE i > j  BY <2>1, <2>3
  <2>. QED  BY <2>1, <2>2, <2>3
<1>. n-1 \in Nat  BY <1>2
<1>. DEFINE h == [ k \in 1 .. n-1 |-> IF k=j THEN f[g[n]] ELSE f[g[k]] ]
<1>3. h \in Surjection(1..n-1, T)
  <2>1. h \in [1..n-1 -> T]  BY DEF Bijection, Surjection
  <2>2. ASSUME NEW t \in T  PROVE \E k \in 1..n-1 : h[k] = t
    <3>1. PICK s \in S : f[s] = t  BY DEF Surjection
    <3>2. PICK l \in 1..n : g[l] = s  BY DEF Bijection, Surjection
    <3>. QED  BY <1>1, <1>2, <3>1, <3>2
  <2>. QED  BY <2>1, <2>2 DEF Surjection
<1>4. Cardinality(T) <= n-1  BY <1>3, FS_SurjCardinalityBound DEF ExistsSurjection
<1>. QED  BY <1>4


(***************************************************************************)
(* `.  .'                                                                  *)
(*                                                                         *)
(* The image of a finite set is finite.                                    *)
(* NB: Note that any function is a surjection on its range by theorem      *)
(*     Fun_RangeProperties.                                                *)
(*                                                                         *)
(* `.  .'                                                                  *)
(***************************************************************************)
THEOREM FS_Surjection ==
  ASSUME NEW S, NEW T, NEW f \in Surjection(S,T), IsFiniteSet(S)
  PROVE  /\ IsFiniteSet(T)
         /\ Cardinality(T) <= Cardinality(S)
         /\ Cardinality(T) = Cardinality(S) <=> f \in Injection(S,T)

<1>1. /\ Cardinality(S) \in Nat
      /\ ExistsBijection(1 .. Cardinality(S), S)
  BY FS_CardinalityType
<1>2. ExistsSurjection(1 .. Cardinality(S), T)
  BY <1>1, Fun_ExistsBijEquiv, Fun_ExistsSurjTransitive DEF ExistsSurjection
<1>4. IsFiniteSet(T) /\ Cardinality(T) <= Cardinality(S)
  BY <1>1, <1>2, FS_NatSurjection, FS_SurjCardinalityBound
<1>5. ASSUME Cardinality(T) = Cardinality(S)  PROVE f \in Injection(S,T)
  BY <1>5, FS_SurjSameCardinalityImpliesInj
<1>6. ASSUME f \in Injection(S,T)  PROVE Cardinality(T) = Cardinality(S)
  <2>1. ExistsBijection(S, T)  BY <1>6 DEF Bijection, ExistsBijection
  <2>2. ExistsBijection(1..Cardinality(S), T)
    BY <1>1, <2>1, Fun_ExistsBijTransitive
  <2>. QED  BY <1>1, <2>2, FS_CountingElements
<1>. QED  BY <1>4, <1>5, <1>6


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

<1>1. IsFiniteSet({}) /\ Cardinality({}) = 0
  BY Fun_NatBijEmpty, FS_NatBijection, FS_CountingElements, Zenon
<1>2. ASSUME NEW S, IsFiniteSet(S), Cardinality(S) = 0
      PROVE  S = {}
  BY <1>2, FS_CardinalityType, Fun_NatBijEmpty
<1>. QED  BY <1>1, <1>2



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
<1>1. CASE x \notin S
  BY <1>1, FS_CardinalityType, Fun_NatBijAddElem, FS_NatBijection, 
     FS_CountingElements
<1>. QED  BY <1>1  \* the case "x \in S" is trivial


THEOREM FS_RemoveElement ==
  ASSUME NEW S, NEW x, IsFiniteSet(S)
  PROVE  /\ IsFiniteSet(S \ {x})
         /\ Cardinality(S \ {x}) =
            IF x \in S THEN Cardinality(S)-1 ELSE Cardinality(S)
<1>1. CASE x \in S
  BY <1>1, FS_CardinalityType, Fun_NatBijSubElem, FS_NatBijection, 
     FS_CountingElements, FS_EmptySet
<1>. QED  BY <1>1  \* the case "x \notin S" is trivial


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

<1>1. \A x : IsFiniteSet({x}) /\ Cardinality({x}) = 1
  BY FS_EmptySet, FS_AddElement
<1>2. ASSUME NEW S, IsFiniteSet(S), Cardinality(S) = 1
      PROVE  \E x : S = {x}
  BY <1>2, FS_CardinalityType, Fun_NatBijSingleton
<1>. QED  BY <1>1, <1>2




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
\* NB: Changing the last implication to an equivalence breaks proofs

<1>1. /\ Cardinality(S) \in Nat
      /\ ExistsBijection(1 .. Cardinality(S), S)
  BY FS_CardinalityType
<1>2. PICK n \in Nat : ExistsBijection(1..n, T) /\ n <= Cardinality(S)
  BY <1>1, Fun_NatBijSubset
<1>3. ASSUME Cardinality(S) = Cardinality(T), S # T
      PROVE  FALSE
  <2>1. PICK x \in S \ T : TRUE  BY <1>3
  <2>2. /\ IsFiniteSet(S \ {x})
        /\ Cardinality(S \ {x}) = Cardinality(S) - 1
    BY <2>1, FS_RemoveElement
  <2>3. T \subseteq S \ {x}  BY <2>1
  <2>4. PICK m \in Nat : ExistsBijection(1..m, T) /\ m <= Cardinality(S)-1
    BY <2>2, <2>3, FS_CardinalityType, Fun_NatBijSubset
  <2>. QED  BY <2>4, <1>3, FS_CountingElements
<1>. QED  BY <1>2, <1>3, FS_NatBijection, FS_CountingElements



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

<1>1. CASE a <= b
  BY <1>1, Fun_ExistsBijInterval, FS_NatBijection, FS_CountingElements
<1>2. CASE a > b  
  <2>1. a..b = {}  BY <1>2
  <2>. QED  BY <2>1, <1>2, FS_EmptySet, Zenon
<1>. QED  BY <1>1, <1>2


THEOREM FS_BoundedSetOfNaturals ==
  ASSUME NEW S \in SUBSET Nat, NEW n \in Nat,
         \A s \in S : s <= n
  PROVE  /\ IsFiniteSet(S)
         /\ Cardinality(S) \leq n+1
<1>1. S \subseteq 0 .. n  OBVIOUS
<1>2. IsFiniteSet(0..n) /\ Cardinality(0..n) = n+1  BY FS_Interval
<1>. QED  BY <1>1, <1>2, FS_Subset, Zenon


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
<1>.  DEFINE Q(n) == \A T : IsFiniteSet(T) /\ Cardinality(T) = n => P(T)
<1>1. SUFFICES \A n \in Nat : Q(n)  BY FS_CardinalityType
<1>2. Q(0)  BY FS_EmptySet, Zenon
<1>3. ASSUME NEW n \in Nat, Q(n),
             NEW T, IsFiniteSet(T), Cardinality(T) = n+1
      PROVE  P(T)
  <2>1. PICK x \in T : TRUE  BY <1>3, FS_EmptySet
  <2>2. /\ IsFiniteSet(T \ {x})
        /\ Cardinality(T \ {x}) = n
    BY <1>3, FS_RemoveElement, Isa
  <2>3. P(T \ {x})  BY <2>2, Q(n)
  <2>4. P((T \ {x}) \cup {x})  BY <2>2, <2>3
  <2>. QED  BY <2>4
<1>4. QED  BY <1>2, <1>3, NatInduction, Isa



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
BY FS_Subset DEF FiniteSubsetsOf


(*****************************************************************************)
(*  The formulation of the following theorem doesn't require S being finite. *)
(*  If S is finite, it implies                                               *)
(*       IsWellFoundedOn(StrictSubsetOrdering(S), SUBSET S)                  *)
(*  using lemma FS_FiniteSubsetsOfFinite.                                    *)
(*****************************************************************************)
THEOREM FS_StrictSubsetOrderingWellFounded ==
  ASSUME NEW S
  PROVE  IsWellFoundedOn(StrictSubsetOrdering(S), FiniteSubsetsOf(S))

<1>1. \A T \in FiniteSubsetsOf(S) : Cardinality(T) \in Nat
  BY FS_CardinalityType, FS_Subset DEF FiniteSubsetsOf
<1>2. IsWellFoundedOn(PreImage(Cardinality, FiniteSubsetsOf(S), OpToRel(<,Nat)),
                       FiniteSubsetsOf(S))
  BY <1>1, PreImageWellFounded, NatLessThanWellFounded, Isa
<1>3. StrictSubsetOrdering(S) \cap (FiniteSubsetsOf(S) \X FiniteSubsetsOf(S))
       \subseteq PreImage(Cardinality, FiniteSubsetsOf(S), OpToRel(<, Nat))
  BY FS_Subset, <1>1
     DEF StrictSubsetOrdering, FiniteSubsetsOf, PreImage, OpToRel
<1>. QED  BY <1>2, <1>3, IsWellFoundedOnSubrelation



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
<1>. DEFINE SubS == SUBSET S
<1>1. IsWellFoundedOn(StrictSubsetOrdering(S), SubS)
  BY FS_FiniteSubsetsOfFinite, FS_StrictSubsetOrderingWellFounded, Zenon
<1>2. \A T \in SubS : 
          (\A U \in SetLessThan(T, StrictSubsetOrdering(S), SubS) : P(U))
          => P(T)
  BY DEF SetLessThan, StrictSubsetOrdering
<1>. HIDE DEF SubS
<1>3. \A T \in SubS : P(T)  BY ONLY <1>1, <1>2, WFInduction, IsaM("blast")
<1>. QED  BY <1>3 DEF SubS


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

<1>. DEFINE P(A) == /\ IsFiniteSet(S \cup A)
                    /\ Cardinality(S \cup A) =
                           Cardinality(S) + Cardinality(A) - Cardinality(S \cap A)
<1>1. P({})  BY FS_EmptySet, FS_CardinalityType
<1>2. ASSUME NEW A, NEW x, IsFiniteSet(A), P(A), x \notin A
      PROVE  P(A \cup {x})
  <2>1. IsFiniteSet(S \cup (A \cup {x}))  BY P(A), FS_AddElement, Isa
  <2>. /\ IsFiniteSet(S \cup A)
       /\ IsFiniteSet(S \cap A)
       /\ Cardinality(S) \in Nat
       /\ Cardinality(A) \in Nat
       /\ Cardinality(S \cap A) \in Nat
    BY P(A), FS_Subset, FS_CardinalityType
  <2>2. Cardinality(A \cup {x}) = Cardinality(A) + 1
    BY <1>2, FS_AddElement
  <2>3. CASE x \in S
    <3>1. Cardinality(S \cup (A \cup {x})) = Cardinality(S \cup A)  BY <2>3, Zenon
    <3>2. Cardinality(S \cap (A \cup {x})) = Cardinality((S \cap A) \cup {x})  BY <2>3, Zenon
    <3>3. Cardinality(S \cap (A \cup {x})) = Cardinality(S \cap A) + 1
      BY <3>2, <1>2, FS_AddElement
    <3>. QED  BY <3>1, <3>3, <2>2, <2>1, P(A)
  <2>4. CASE x \notin S
    <3>1. Cardinality((S \cup A) \cup {x}) = Cardinality(S \cup A) + 1
      BY <1>2, <2>4, FS_AddElement
    <3>1a. Cardinality(S \cup (A \cup {x})) = Cardinality(S \cup A) + 1  BY <3>1, Zenon
    <3>2. Cardinality(S \cap (A \cup {x})) = Cardinality(S \cap A)  BY <2>4, Zenon
    <3>. QED  BY <3>1a, <3>2, <2>2, <2>1, P(A)
  <2>. QED  BY <2>3, <2>4
<1>. HIDE DEF P
<1>. P(T)  BY <1>1, <1>2, FS_Induction, IsaM("blast")
<1>. QED  BY DEF P



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

<1>. /\ IsFiniteSet(S)
     /\ IsFiniteSet(T)
     /\ Cardinality(S) \in Nat
     /\ Cardinality(T) \in Nat
     /\ Cardinality(U) \in Nat
     /\ Cardinality(S \cap T) \in Nat
     /\ Cardinality(S \cup T) <= Cardinality(U)
  BY FS_Subset, FS_CardinalityType
<1>1. Cardinality(S \cup T) =
        Cardinality(S) + Cardinality(T) - Cardinality(S \cap T)
  BY FS_Union, Zenon
<1>2. Cardinality(S \cap T) # 0  BY <1>1
<1>3. QED  BY <1>2, FS_EmptySet, Zenon




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
BY FS_Subset



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

<1>. /\ IsFiniteSet(S \ T)
     /\ IsFiniteSet(S \cap T)
     /\ Cardinality(S \ T) \in Nat
     /\ Cardinality(S \cap T) \in Nat
  BY FS_Subset, FS_CardinalityType
<1>2. Cardinality(S \ T) = Cardinality(S) - Cardinality(S \cap T)
  <2>1. Cardinality(S) = Cardinality((S \cap T) \cup (S \ T))  BY Zenon
  <2>2. Cardinality((S \cap T) \cup (S \ T)) = 
        Cardinality(S \cap T) + Cardinality(S \ T) - Cardinality((S \cap T) \cap (S \ T))
    BY FS_Union, Zenon
  <2>3. Cardinality((S \cap T) \cap (S \ T)) = 0  BY FS_EmptySet, Zenon
  <2>. QED  BY <2>1, <2>2, <2>3
<1>3. QED  BY <1>2
      


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

<1>. DEFINE P(U) == (\A T \in U : IsFiniteSet(T)) => IsFiniteSet(UNION U)
<1>1. P({})  BY FS_EmptySet
<1>2. ASSUME NEW U, NEW x, P(U), x \notin U
      PROVE  P(U \cup {x})
  BY <1>2, FS_Union, Isa
<1>. HIDE DEF P
<1>. P(S)  BY <1>1, <1>2, FS_Induction, IsaM("blast")
<1>. QED  BY DEF P



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

<1>. DEFINE P(A) == /\ IsFiniteSet(S \X A)
                    /\ Cardinality(S \X A) = Cardinality(S) * Cardinality(A)
<1>1. P({})
  <2>1. /\ S \X {} = {}
        /\ IsFiniteSet(S \X {})
        /\ Cardinality(S \X {}) = 0
        /\ Cardinality({}) = 0
        /\ Cardinality(S) \in Nat
    BY FS_EmptySet, FS_CardinalityType, Zenon
  <2>. QED  BY <2>1
<1>2. ASSUME NEW A, NEW x, IsFiniteSet(A), P(A), x \notin A
      PROVE  P(A \cup {x})
  <2>. /\ Cardinality(A) \in Nat
       /\ Cardinality(S) \in Nat
    BY <1>2, FS_CardinalityType
  <2>. DEFINE SX == { <<s,x>> : s \in S }
  <2>1. /\ IsFiniteSet(A \cup {x})
        /\ Cardinality(A \cup {x}) = Cardinality(A) + 1
    BY <1>2, FS_AddElement
  <2>2. S \X (A \cup {x}) = (S \X A) \cup SX
    BY <1>2, Isa
  <2>3. ExistsBijection(S, SX)
    <3>. DEFINE f  == [s \in S |-> <<s,x>>]
    <3>. f \in Bijection(S, SX)  BY DEF Bijection, Injection, Surjection
    <3>. QED  BY DEF ExistsBijection
  <2>4. /\ IsFiniteSet(SX)
        /\ Cardinality(SX) = Cardinality(S)
    BY <2>3, FS_Bijection
  <2>5. /\ IsFiniteSet(S \X (A \cup {x}))
         /\ Cardinality(S \X (A \cup {x})) = 
              Cardinality(S \X A) + Cardinality(SX) - Cardinality((S \X A) \cap SX) 
    BY <2>2, <2>4, P(A), FS_Union, Isa
  <2>6. (S \X A) \cap SX = {}  BY <1>2
  <2>7. Cardinality((S \X A) \cap SX) = 0  BY <2>6, FS_EmptySet, Zenon
  <2>. QED  BY <2>1, <2>5, <2>4, <2>7, P(A)
<1>. HIDE DEF P
<1>. P(T)  BY <1>1, <1>2, FS_Induction, IsaM("blast")
<1>. QED  BY DEF P




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

<1>. DEFINE P(A) == /\ IsFiniteSet(SUBSET A)
                    /\ Cardinality(SUBSET A) = 2^Cardinality(A)
<1>1. P({})
  <2>1. /\ IsFiniteSet({{}})
        /\ Cardinality({{}}) = 1
    BY FS_Singleton, Zenon
  <2>2. 1 = 2^0  OBVIOUS
  <2>. QED  BY <2>1, <2>2, FS_EmptySet, Zenon
<1>2. ASSUME NEW A, NEW x, IsFiniteSet(A), x \notin A, P(A)
      PROVE  P(A \cup {x})
  <2>. DEFINE Ax == {B \cup {x} : B \in SUBSET A}
  <2>1. Cardinality(A \cup {x}) = Cardinality(A) + 1  BY <1>2, FS_AddElement
  <2>2. 2^Cardinality(A \cup {x}) = 2^Cardinality(A) + 2^Cardinality(A)
    BY <2>1, <1>2, FS_CardinalityType, TwoExpLemma, Zenon
  <2>3. SUBSET (A \cup {x}) = (SUBSET A) \cup Ax  BY <1>2, Isa
  <2>4. ExistsBijection(SUBSET A, Ax)
    <3>. DEFINE f == [B \in SUBSET A |-> B \cup {x}]
    <3>1. ASSUME NEW B \in SUBSET A, NEW C \in SUBSET A, f[B] = f[C]
          PROVE  B = C
      BY <3>1, <1>2, Zenon
    <3>2. f \in Surjection(SUBSET A, Ax)  BY DEF Surjection
    <3>3. f \in Bijection(SUBSET A, Ax)
      BY <3>1, <3>2 DEF Bijection, Injection
    <3>. QED  BY <3>3 DEF ExistsBijection
  <2>5. /\ IsFiniteSet(Ax)
        /\ Cardinality(Ax) = Cardinality(SUBSET A)
    BY <2>4, P(A), FS_Bijection
  <2>6. /\ IsFiniteSet(SUBSET (A \cup {x}))
        /\ Cardinality(SUBSET (A \cup {x})) =
             Cardinality(SUBSET A) + Cardinality(Ax) - Cardinality((SUBSET A) \cap Ax)
    BY <2>3, <2>5, P(A), FS_Union, Isa
  <2>7. (SUBSET A) \cap Ax = {}  BY <1>2
  <2>8. Cardinality((SUBSET A) \cap Ax) = 0  BY <2>7, FS_EmptySet, Zenon
  <2>. QED  BY <2>2, <2>5, <2>6, <2>8, P(A), FS_CardinalityType
<1>. HIDE DEF P
<1>. P(S)  BY <1>1, <1>2, FS_Induction, IsaM("blast")
<1>. QED  BY DEF P





    
=============================================================================
\* Modification History
\* Last modified Fri Feb 14 21:24:26 GMT-03:00 2014 by merz
\* Last modified Thu Jul 04 15:15:07 CEST 2013 by bhargav
\* Last modified Tue Jun 04 11:44:51 CEST 2013 by bhargav
\* Last modified Fri May 03 12:02:51 PDT 2013 by tomr
\* Created Fri Oct 05 15:04:18 PDT 2012 by tomr