--------------------- MODULE WellFoundedInduction_proofs --------------------
(***************************************************************************)
(* This module contains useful theorems for inductive proofs and recursive *)
(* definitions based on a well-founded ordering.                           *)
(*                                                                         *)
(* Most of the statements of the theorems are decomposed in terms of       *)
(* definitions.  This is done for two reasons:                             *)
(*                                                                         *)
(*  - It makes it easier for the backends to instantiate the theorems      *)
(*    when those definitions are not expanded.  In fact, at the moment     *)
(*    the provers can't prove any of those theorems from the theorem       *)
(*    itself if the definitions are made usable.                           *)
(*                                                                         *)
(*  - It can be convenient when writing proofs to use those definitions    *)
(*    rather than having to write out their expansions.                    *)
(*                                                                         *)
(* A relation is represented as a set of ordered pairs, where we write     *)
(* <<x, y>> \in R instead of x R y.  It is more convenient to represent    *)
(* relations this way rather than as operators such as < .                 *)
(***************************************************************************)
EXTENDS NaturalsInduction, TLAPS

(***************************************************************************)
(* The following defines what it means for a relation R to be transitively *)
(* closed on a set S.  In this and other definitions, we think of R as a   *)
(* relation on S, meaning that it is a subset of S \X S.  However, this is *)
(* not necessary.  Our results do not require this as a hypothesis, and it *)
(* is often convenient to apply them when R is a relation on a set         *)
(* containing S as a subset.  They're even true (though uninteresting) if  *)
(* R and S \X S are disjoint sets.                                         *)
(***************************************************************************)
IsTransitivelyClosedOn(R, S) ==
   \A i, j, k \in S : (<<i, j>> \in R)  /\ (<<j, k>> \in  R)  
                         => (<<i, k>> \in R)
(***************************************************************************)
(* If we think of R as a less-than relation, then R is well founded on S   *)
(* iff there is no "infinitely descending" sequence of elements of S.  The *)
(* canonical example of a well founded relation is the ordinary less-than  *)
(* relation on the natural numbers.                                        *)
(*                                                                         *)
(* A S with a well-founded ordering is often called well-ordered.          *)
(***************************************************************************)
IsWellFoundedOn(R, S) == 
    ~ \E f \in [Nat -> S] : \A n \in Nat : <<f[n+1], f[n]>> \in R

LEMMA EmptyIsWellFounded == \A S : IsWellFoundedOn({}, S)
BY DEF IsWellFoundedOn


LEMMA IsWellFoundedOnSubset ==
        ASSUME NEW R, NEW S, NEW T \in SUBSET S,
               IsWellFoundedOn(R,S)
        PROVE  IsWellFoundedOn(R,T)
BY DEF IsWellFoundedOn


LEMMA IsWellFoundedOnSubrelation ==
       ASSUME NEW S, NEW R, NEW RR, RR \cap (S \X S) \subseteq R,
              IsWellFoundedOn(R,S)
       PROVE  IsWellFoundedOn(RR,S)
<1>1. SUFFICES ASSUME NEW f \in [Nat -> S],
                      \A n \in Nat : <<f[n+1], f[n]>> \in RR
               PROVE  FALSE
  BY DEF IsWellFoundedOn
<1>2. \A n \in Nat : <<f[n+1], f[n]>> \in RR \cap (S \X S)
  BY Isa, <1>1
<1>. QED
  BY <1>2 DEF IsWellFoundedOn

(***************************************************************************)
(* If we think of R as a less-than relation on S, then the following is    *)
(* the set of elements of S that are less than x.                          *)
(***************************************************************************)
SetLessThan(x, R, S) ==  {y \in S : <<y, x>> \in R}

(***************************************************************************)
(* If we think of R as a less-than relation on S, then R is well-founded   *)
(* iff every non-empty subset of S has a minimal element.                  *)
(***************************************************************************)

THEOREM WFMin ==
         ASSUME NEW R, NEW S, 
                IsWellFoundedOn(R, S),
                NEW T, T \subseteq S, T # {}
         PROVE  \E x \in T : \A y \in T : ~ (<<y, x>> \in R)
<1> SUFFICES ASSUME \A x \in T : \E y \in T : <<y, x>> \in R
             PROVE  FALSE
  OBVIOUS
<1> DEFINE f0 == CHOOSE x \in T : TRUE
           Def(v, n) == CHOOSE x \in T : <<x, v>> \in R
           f[n \in Nat] == IF n = 0 THEN f0 ELSE Def(f[n-1], n)
<1>1. NatInductiveDefConclusion(f, f0, Def)
  <2>1. NatInductiveDefHypothesis(f, f0, Def)
    BY DEF NatInductiveDefHypothesis
  <2>2. QED
    BY <2>1, NatInductiveDef   
<1>2. f \in [Nat -> T]
  <2>1. f0 \in T
    OBVIOUS
  <2>2. \A v \in T, n \in Nat \ {0} : Def(v, n) \in T
    OBVIOUS
  <2>3. QED
    BY <1>1, <2>1, <2>2, NatInductiveDefType, Isa
<1>3. ASSUME NEW n \in Nat 
      PROVE  <<f[n+1], f[n]>> \in R 
  <2>1. /\ n+1 \in Nat
        /\ n+1 # 0
        /\ (n+1)-1 = n
    BY Isa
  <2>2. f[n+1] = Def(f[(n+1)-1], n+1)
     BY <2>1, <1>1 DEF NatInductiveDefConclusion
  <2>3. QED
    BY <2>1, <2>2, <1>2
<1>4. QED
  BY <1>2, <1>3 DEF IsWellFoundedOn


THEOREM MinWF ==
         ASSUME NEW R, NEW S,
                \A T \in SUBSET S : T # {} => \E x \in T : \A y \in T : ~ (<<y, x>> \in R)
         PROVE  IsWellFoundedOn(R,S)
<1> SUFFICES ASSUME NEW f \in [Nat -> S],
                    \A n \in Nat : <<f[n+1], f[n]>> \in R
             PROVE  FALSE
  BY DEF IsWellFoundedOn
<1> DEFINE T == { f[n] : n \in Nat }
<1>1. T \subseteq S
  OBVIOUS
<1>2. \A x \in T : \E y \in T : <<y,x>> \in R
  BY Isa
<1> QED
  BY <1>1, <1>2

(***************************************************************************)
(* The two following lemmas are simple consequences of theorem WFMin.      *)
(***************************************************************************)
LEMMA WellFoundedIsIrreflexive ==
        ASSUME NEW R, NEW S, NEW x \in S,
               IsWellFoundedOn(R, S)
        PROVE  <<x, x>> \notin R
<1>1. \E z \in {x} : \A y \in {x} : <<y,z>> \notin R
  BY WFMin, IsaM("blast")
<1>2. QED
  BY <1>1


LEMMA WellFoundedIsAsymmetric ==
        ASSUME NEW R, NEW S, NEW x \in S, NEW y \in S,
               IsWellFoundedOn(R,S),
               <<x,y>> \in R, <<y,x>> \in R
        PROVE  FALSE
<1>1. \E u \in {x,y} : \A v \in {x,y} : <<v,u>> \notin R
  BY WFMin, IsaM("blast")
<1>2. QED
  BY <1>1

(***************************************************************************)
(* The following lemmas are simple facts about operator SetLessThan.       *)
(***************************************************************************)
LEMMA WFSetLessThanIrreflexive ==
        ASSUME NEW R, NEW S, NEW x \in S,
               IsWellFoundedOn(R,S)
        PROVE  x \notin SetLessThan(x,R,S)
BY WellFoundedIsIrreflexive DEF SetLessThan


LEMMA SetLessTransitive ==
        ASSUME NEW R, NEW S, NEW x \in S, NEW y \in SetLessThan(x,R,S),
               IsTransitivelyClosedOn(R, S)
        PROVE  SetLessThan(y, R, S) \subseteq SetLessThan(x, R, S)
BY DEF SetLessThan, IsTransitivelyClosedOn

----------------------------------------------------------------------------
(***************************************************************************)
(* The following theorem is the basis for proof by induction over a        *)
(* well-founded set.  It generalizes theorem GeneralNatInduction of module *)
(* NaturalsInduction.                                                      *)
(***************************************************************************)
THEOREM WFInduction ==
          ASSUME NEW P(_), NEW R, NEW S,
                 IsWellFoundedOn(R, S),
                 \A x \in S : (\A y \in SetLessThan(x, R, S) : P(y))
                    => P(x)
          PROVE  \A x \in S : P(x)
<1> DEFINE T == {x \in S : ~P(x)}
<1>1. SUFFICES ASSUME T # {}
               PROVE  FALSE
  OBVIOUS
<1>2. PICK x \in T : \A y \in T : ~ (<<y, x>> \in R)
  BY <1>1, WFMin
<1>3. QED
  BY <1>2 DEF SetLessThan

(***************************************************************************)
(* Theorem WFInductiveDef below justifies recursive definitions based on a *)
(* well-founded ordering.  We first prove it with the hypothesis that the  *)
(* ordering is transitively closed.  We prove the theorem for an arbitrary *)
(* well-founded relation by applying the special case to its transitive    *)
(* closure.                                                                *)
(***************************************************************************)
WFDefOn(R, S, Def(_,_)) == 
   \A g, h : 
      \A x \in S :
         (\A y \in SetLessThan(x, R, S) : g[y] = h[y])
           => (Def(g,x) = Def(h,x))

OpDefinesFcn(f, S, Def(_,_)) ==
   f =  CHOOSE g : g = [x \in S |-> Def(g, x)]

WFInductiveDefines(f, S, Def(_,_)) ==
     f = [x \in S |-> Def(f, x)]
                                          
WFInductiveUnique(S, Def(_,_)) ==
  \A g, h : /\ WFInductiveDefines(g, S, Def)
            /\ WFInductiveDefines(h, S, Def)
            => (g = h)

THEOREM WFDefOnUnique ==
          ASSUME NEW Def(_,_), NEW R, NEW S,
                 IsWellFoundedOn(R, S), WFDefOn(R, S, Def)
          PROVE  WFInductiveUnique(S, Def)
<1>0. SUFFICES ASSUME NEW g, NEW h,
                      WFInductiveDefines(g, S, Def),
                      WFInductiveDefines(h, S, Def)
               PROVE  g = h
  BY DEF WFInductiveUnique
<1> SUFFICES \A x \in S : g[x] = h[x]
  BY <1>0 DEF WFInductiveDefines
<1>1. ASSUME NEW x \in S,
             \A y \in SetLessThan(x, R, S) : g[y] = h[y]
      PROVE  g[x] = h[x]
  <2>1. Def(g,x) = Def(h,x)
    BY <1>1 DEF WFDefOn
  <2>2. QED
    BY <1>0, <2>1 DEF WFInductiveDefines
<1>2. QED
  BY <1>1, WFInduction, Isa

LEMMA WFInductiveDefLemma ==
        ASSUME NEW Def(_,_), NEW R, NEW S, NEW f,
               IsWellFoundedOn(R, S),
               IsTransitivelyClosedOn(R, S),
               WFDefOn(R, S, Def),
               OpDefinesFcn(f, S, Def)
        PROVE  WFInductiveDefines(f, S, Def)
<1> DEFINE LT(x) == {x} \cup SetLessThan(x, R, S)
<1>1. ASSUME NEW x \in S
      PROVE  /\ LT(x) = {x} \cup UNION {LT(y) : y \in SetLessThan(x, R, S)}
             /\ (x \in LT(x)) /\ (SetLessThan(x, R, S) \subseteq LT(x))
             /\ \A y \in LT(x) : SetLessThan(y, R, S) \subseteq LT(x)
             /\ \A y \in LT(x) : LT(y) \subseteq LT(x)
             /\ LT(x) \subseteq S
  BY Isa DEF SetLessThan, IsTransitivelyClosedOn
<1> HIDE DEF LT  \** from now on, (mostly) use properties in step <1>1 rather than the definition

<1> DEFINE F(x) == CHOOSE g : g = [y \in LT(x) |-> Def(g, y)]
           ff == [x \in S |-> F(x)[x]]
<1> HIDE DEF ff

<1>2. \A x \in S : ff[x] = Def(ff,x)
  <2>1. SUFFICES ASSUME NEW x \in S,
                        \A y \in SetLessThan(x, R, S) : ff[y] = Def(ff,y)
                 PROVE  ff[x] = Def(ff,x)
    BY WFInduction, Isa
  <2>2. WFInductiveUnique(LT(x), Def)
    <3>1. LT(x) \subseteq S
      BY <1>1
    <3>2. IsWellFoundedOn(R, LT(x))
      BY <3>1, IsWellFoundedOnSubset
    <3>3. \A z \in LT(x) : SetLessThan(z, R, LT(x)) = SetLessThan(z, R, S)
      BY DEF LT, SetLessThan, IsTransitivelyClosedOn
    <3>4. WFDefOn(R, LT(x), Def)
      BY <3>1, <3>3, IsaM("blast") DEF WFDefOn
    <3>. QED
      BY <3>2, <3>4, WFDefOnUnique
  <2> DEFINE g == [y \in LT(x) |-> Def(ff, y)]
  <2>3. Def(ff,x) = Def(g,x)
    BY <1>1 (* x \in LT(x) *), <2>1 DEF WFDefOn
  <2>4. ASSUME NEW y \in SetLessThan(x, R, S)
        PROVE  Def(ff,y) = Def(g,y)
     <3>1. y \in S
       BY DEF SetLessThan
     <3>2. \A z \in SetLessThan(y, R, S) : ff[z] = g[z]
       BY <2>1, SetLessTransitive DEF LT
     <3>3. QED
       BY <3>1, <3>2 DEF WFDefOn      
  <2>5. WFInductiveDefines(g, LT(x), Def)
    BY <2>3, <2>4 DEF WFInductiveDefines, LT
  <2>6. WFInductiveDefines(F(x), LT(x), Def)
    BY <2>5 DEF WFInductiveDefines
  <2>7. g = F(x)
    BY <2>5, <2>6, <2>2 DEF WFInductiveUnique
  <2>. QED
    BY <1>1, <2>7 DEF ff

<1>3. QED
  <2>1. WFInductiveDefines(ff, S, Def)
    BY <1>2 DEF WFInductiveDefines, ff
  <2>2. QED
    BY <2>1 DEF WFInductiveDefines, OpDefinesFcn

(***************************************************************************)
(* The following defines the transitive closure of the relation R on S.    *)
(* More precisely, it is the transitive closure of the restriction of R    *)
(* to S.  We give an abstract definition of transitive closure as the      *)
(* smallest relation that contains R (restricted to S \X S) and that is    *)
(* transitively closed, then prove some relevant properties.               *)
(***************************************************************************)
TransitiveClosureOn(R,S) ==
   { ss \in S \X S : 
        \A U \in SUBSET (S \X S) :
           /\ R \cap S \X S \subseteq U
           /\ IsTransitivelyClosedOn(U, S)
           => ss \in U }  

LEMMA TransitiveClosureThm ==
         \A R, S : 
           /\ R \cap S \X S \subseteq TransitiveClosureOn(R, S)
           /\ IsTransitivelyClosedOn(TransitiveClosureOn(R, S), S)
<1> TAKE R, S
<1>1. R \cap S \X S \subseteq TransitiveClosureOn(R, S)
  BY DEF TransitiveClosureOn
<1>2. IsTransitivelyClosedOn(TransitiveClosureOn(R, S), S)
  BY DEF TransitiveClosureOn, IsTransitivelyClosedOn
<1>3. QED
  BY <1>1, <1>2

LEMMA TransitiveClosureMinimal ==
        ASSUME NEW R, NEW S, NEW U \in SUBSET (S \X S),
               R \cap S \X S \subseteq U,
               IsTransitivelyClosedOn(U,S)
        PROVE  TransitiveClosureOn(R,S) \subseteq U
BY DEF TransitiveClosureOn

(***************************************************************************)
(* The following lemmas are consequences of the two previous ones. The     *)
(* first three state closure properties of transitive closure, the fourth  *)
(* lemma allows one to chop off a step in the underlying relation for any  *)
(* pair in the transitive closure.                                         *)
(***************************************************************************)

LEMMA TCTCTC ==
       ASSUME NEW R, NEW S, NEW i \in S, NEW j \in S, NEW k \in S,
              <<i,j>> \in TransitiveClosureOn(R,S),
              <<j,k>> \in TransitiveClosureOn(R,S)
       PROVE  <<i,k>> \in TransitiveClosureOn(R,S)
BY TransitiveClosureThm DEF IsTransitivelyClosedOn

LEMMA TCRTC ==
       ASSUME NEW R, NEW S, NEW i \in S, NEW j \in S, NEW k \in S,
              <<i,j>> \in TransitiveClosureOn(R,S), <<j,k>> \in R
       PROVE  <<i,k>> \in TransitiveClosureOn(R,S)
BY TransitiveClosureThm, TCTCTC

LEMMA RTCTC ==
       ASSUME NEW R, NEW S, NEW i \in S, NEW j \in S, NEW k \in S,
              <<i,j>> \in R, <<j,k>> \in TransitiveClosureOn(R,S)
       PROVE  <<i,k>> \in TransitiveClosureOn(R,S)
BY TransitiveClosureThm, TCTCTC

LEMMA TransitiveClosureChopLast ==
        ASSUME NEW R, NEW S, NEW i \in S, NEW k \in S, <<i,k>> \in TransitiveClosureOn(R,S)
        PROVE  \E j \in S : /\ <<j,k>> \in R
                            /\ i = j \/ <<i,j>> \in TransitiveClosureOn(R,S)
<1> DEFINE U == { ss \in S \X S : \E s \in S : /\ <<s, ss[2]>> \in R
                                               /\ ss[1] = s \/ <<ss[1], s>> \in TransitiveClosureOn(R,S) }
<1>1. R \cap S \X S \subseteq U
  <2> SUFFICES ASSUME NEW x \in S, NEW y \in S, <<x,y>> \in R
               PROVE  <<x,y>> \in U
    BY IsaM("blast")
  <2> QED
    OBVIOUS
<1>2. U \subseteq TransitiveClosureOn(R,S)
  <2> SUFFICES ASSUME NEW x \in S, NEW y \in S, <<x,y>> \in U
               PROVE  <<x,y>> \in TransitiveClosureOn(R,S)
    BY IsaM("blast")
  <2> QED
    BY TransitiveClosureThm DEF IsTransitivelyClosedOn
<1>3. IsTransitivelyClosedOn(U,S)
  <2>1. SUFFICES ASSUME NEW x \in S, NEW y \in S, NEW z \in S,
                        <<x,y>> \in U, <<y,z>> \in U
                 PROVE  <<x,z>> \in U
    BY DEF IsTransitivelyClosedOn
  <2>2. <<x,y>> \in TransitiveClosureOn(R,S)
    BY <2>1, <1>2
  <2>3. PICK s \in S : /\ <<s,z>> \in R
                       /\ y=s \/ <<y,s>> \in TransitiveClosureOn(R,S)
    BY <2>1
  <2>4. <<x,s>> \in TransitiveClosureOn(R,S)
    BY <2>2, <2>3, TransitiveClosureThm DEF IsTransitivelyClosedOn
  <2> QED
    BY <2>3, <2>4
<1>4. QED
  <2>1. TransitiveClosureOn(R,S) \subseteq U
    BY <1>1, <1>3, TransitiveClosureMinimal
  <2>2. QED
    BY <2>1

(***************************************************************************)
(* NB: In a similar way to the preceding lemma, one could prove            *)
(*     ASSUME NEW R, NEW S, NEW x \in S, NEW y \in S,                      *)
(*            <<x,y>> \in TransitiveClosureOn(R,S)                         *)
(*     PROVE  \E n \in Nat : \E f \in [0..(n+1) -> S] :                    *)
(*               /\ \A i \in 0..n : <<f[i], f[i+1]>> \in R                 *)
(*               /\ x = f[0] /\ y = f[n+1]                                 *)
(* which provides a more constructive characterization of transitive       *)
(* closure. The converse theorem would be proved by induction on n,        *)
(* using the above closure properties.                                     *)
(***************************************************************************)

THEOREM TransitiveClosureWF ==
          ASSUME NEW R, NEW S, IsWellFoundedOn(R,S)
          PROVE  IsWellFoundedOn(TransitiveClosureOn(R, S), S)
<1> SUFFICES ASSUME NEW T \in SUBSET S, T # {}
             PROVE  \E x \in T : \A y \in T : ~(<<y,x>> \in TransitiveClosureOn(R, S))
  BY MinWF
(* It is tempting to simply pick a minimal element x in T w.r.t. relation R as the witness,
   but that wouldn't work in general because there may be elements below x in the transitive
   closure of R. So we complete T w.r.t. the transitive closure in an appropriate way and
   pick a minimal element in that larger set. *)
<1> DEFINE TT == T \cup { j \in S : \E i,k \in T : /\ <<i,j>> \in TransitiveClosureOn(R,S)
                                                   /\ <<j,k>> \in TransitiveClosureOn(R,S) }
<1>1. PICK x \in TT : \A y \in TT : ~(<<y,x>> \in R)
  BY WFMin
<1>2. x \in T
  <2>1. ASSUME NEW i \in T, NEW k \in T,
               <<i,x>> \in TransitiveClosureOn(R,S),
               <<x,k>> \in TransitiveClosureOn(R,S)
        PROVE  FALSE
    <3>1. PICK j \in S : /\ <<j,x>> \in R
                         /\ i=j \/ <<i,j>> \in TransitiveClosureOn(R,S)
      BY <2>1, TransitiveClosureChopLast
    <3>2. j \in TT
      <4>1. CASE <<i,j>> \in TransitiveClosureOn(R,S)
        BY <3>1, <4>1, <2>1, RTCTC
      <4>2. QED
        BY <3>1, <4>1
    <3>3. QED
      BY <3>1, <3>2, <1>1
  <2>2. QED
    BY <2>1
<1>3. ASSUME NEW y \in T, <<y,x>> \in TransitiveClosureOn(R, S)
      PROVE  FALSE
  <2>1. PICK j \in S : /\ <<j,x>> \in R
                       /\ y=j \/ <<y,j>> \in TransitiveClosureOn(R,S)
    BY <1>3, TransitiveClosureChopLast
  <2>2. j \in TT
    <3>1. CASE <<y,j>> \in TransitiveClosureOn(R,S)
      BY <1>2, <3>1, <2>1, TransitiveClosureThm
    <3>2. QED
      BY <2>1, <3>1
  <2>3. QED
    BY <2>1, <2>2, <1>1
<1> QED
  BY <1>2, <1>3

THEOREM WFInductiveDef ==
          ASSUME NEW Def(_,_), NEW R, NEW S, NEW f,
                 IsWellFoundedOn(R, S),
                 WFDefOn(R, S, Def),
                 OpDefinesFcn(f, S, Def)
          PROVE  WFInductiveDefines(f, S, Def)
<1> DEFINE TC == TransitiveClosureOn(R, S)
<1>1. IsTransitivelyClosedOn(TC, S)
  BY TransitiveClosureThm
<1>2. IsWellFoundedOn(TC, S) 
  BY TransitiveClosureWF
<1>3. WFDefOn(TC, S, Def)
  <2>1. \A x \in S : SetLessThan(x, R, S) \subseteq SetLessThan(x, TC, S)
    BY TransitiveClosureThm DEF SetLessThan
  <2>2. QED
    BY <2>1 DEF WFDefOn
<1>4. QED 
 BY <1>1, <1>2, <1>3, WFInductiveDefLemma

(***************************************************************************)
(* Theorem WFInductiveDef allows us to conclude that a recursively defined *)
(* function satisfies its recursion equation.  The following result allows *)
(* us to deduce the range of this function.                                *)
(***************************************************************************)
THEOREM WFInductiveDefType == 
          ASSUME NEW Def(_,_), NEW f, NEW R, NEW S, NEW T,
                 T # {},
                 IsWellFoundedOn(R, S),
                 WFDefOn(R, S, Def),
                 WFInductiveDefines(f, S, Def),
                 \A g \in [S -> T], s \in S : Def(g, s) \in T
          PROVE  f \in [S -> T]
<1>1. \A s \in S : f[s] \in T
  <2>1. SUFFICES ASSUME NEW s \in S,
                      \A x \in SetLessThan(s, R, S) : f[x] \in T 
               PROVE  f[s] \in T
    BY ONLY <2>1, IsWellFoundedOn(R, S), WFInduction, IsaM("auto")
  <2>2. PICK t0 : t0 \in T
    OBVIOUS
  <2> DEFINE g == [x \in S |-> IF x \in SetLessThan(s, R, S) THEN f[x] ELSE t0]
  <2>3. /\ g \in [S -> T]
        /\ \A x \in SetLessThan(s, R, S) : g[x] = f[x]
    <3> SetLessThan(s, R, S) \subseteq S
      BY DEF SetLessThan
    <3> QED
      BY <2>1, <2>2
  <2>4. Def(f,s) = Def(g,s)
    BY <2>3 DEF WFDefOn
  <2>5. QED
    BY <2>3, <2>4 DEF WFInductiveDefines, WFDefOn
<1>2. QED
  BY <1>1 DEF WFInductiveDefines
 
 ---------------------------------------------------------------------------- 
(***************************************************************************)
(* Below are some theorems that allow us to derive some useful             *)
(* well-founded relations from a given well-founded relation.  First, we   *)
(* define the operator OpToRel that constructs a relation (a set of        *)
(* ordered pairs) from a relation expressed as an operator.                *)
(***************************************************************************)
OpToRel(_\prec_, S) == {ss \in S \X S : ss[1] \prec ss[2]}

(***************************************************************************)
(* To construct well-founded relations from the less-than relation on the  *)
(* natural numbers, we first prove that it is well-founded.                *)
(***************************************************************************)
THEOREM NatLessThanWellFounded == IsWellFoundedOn(OpToRel(<,Nat), Nat)
<1> DEFINE R == OpToRel(<,Nat)
<1>1. SUFFICES ASSUME NEW ff \in [Nat -> Nat],
                      \A n \in Nat : ff[n+1] < ff[n] 
               PROVE  FALSE 
  BY DEF  IsWellFoundedOn, OpToRel                      

<1> DEFINE P(n) == \E f \in [Nat -> Nat] : 
                      /\ \A m \in Nat : <<f[m+1], f[m]>> \in R 
                      /\ f[0] = n
<1>1a. P(ff[0])
  BY <1>1, IsaM("auto") DEF OpToRel
<1>2. ASSUME NEW n \in Nat, 
                 \A m \in 0..(n-1) : ~ P(m)
      PROVE  ~ P(n)
  <2> SUFFICES ASSUME NEW f \in [Nat -> Nat],
                      \A m \in Nat : <<f[m+1], f[m]>> \in R ,
                      f[0] = n
               PROVE  FALSE
    OBVIOUS
  <2> DEFINE g[i \in Nat] == f[i+1]
  <2>1. g \in [Nat -> Nat]
    BY ONLY f \in [Nat -> Nat], IsaM("auto")
  <2>2. \A i \in Nat : <<g[i+1], g[i]>> \in R
    BY IsaM("auto")
  <2>3. g[0] \in 0..(n-1)
    BY <2>2, Z3 DEF OpToRel
  <2>4 QED
    BY <2>1, <2>2, <2>3, <1>2
<1>3. ~ P(ff[0])
  <2> HIDE DEF P
  <2> \A n \in Nat : ~ P(n)
    BY ONLY <1>2, GeneralNatInduction, IsaM("auto")
  <2> QED
    BY DEF P
<1>4. QED
    BY <1>1a, <1>3

(***************************************************************************)
(* The next definition would be easier to read if we used the TLA+         *)
(* construct {<<x, y>> \in T : ...  }.  However, TLAPS does not suport     *)
(* that notation.  (It's meaning is rather complicated in the general case *)
(* when T is not a Cartesian product of sets.)                             *)
(***************************************************************************)
PreImage(f(_), S, R) == {ss \in S \X S : <<f(ss[1]), f(ss[2])>> \in R}

THEOREM PreImageWellFounded == 
          ASSUME NEW S, NEW T, NEW R, NEW f(_),
                 \A s \in S : f(s) \in T,
                 IsWellFoundedOn(R, T)
          PROVE  IsWellFoundedOn(PreImage(f, S, R), S)
<1> SUFFICES ASSUME NEW g \in [Nat -> S],
                    \A n \in Nat : <<g[n+1], g[n]>> \in PreImage(f, S, R)
             PROVE  FALSE
 BY DEF IsWellFoundedOn
<1> DEFINE gg[n \in Nat] ==  f(g[n])
<1>1. ASSUME NEW n \in Nat
      PROVE  <<gg[n+1], gg[n]>> \in R
  BY IsaM("auto") DEF PreImage
<1> QED
 BY <1>1 DEF IsWellFoundedOn

(***************************************************************************)
(* We now prove that the lexicographical ordering on the Cartesian product *)
(* of two well-ordered sets is well-ordered.                               *)
(***************************************************************************)
LexPairOrdering(R1, R2, S1, S2) ==
     {ss \in (S1 \X S2) \X (S1 \X S2) : 
         \/ <<ss[1][1], ss[2][1]>> \in R1
         \/ /\ ss[1][1] = ss[2][1]
            /\ <<ss[1][2], ss[2][2]>> \in R2}
                           
THEOREM WFLexPairOrdering ==
          ASSUME NEW R1, NEW R2, NEW S1, NEW S2, 
                 IsWellFoundedOn(R1, S1),
                 IsWellFoundedOn(R2, S2)
          PROVE  IsWellFoundedOn(LexPairOrdering(R1, R2, S1, S2), S1 \X S2)
<1> SUFFICES ASSUME NEW T \in SUBSET (S1 \X S2), T # {}
             PROVE  \E x \in T : \A y \in T : <<y,x>> \notin LexPairOrdering(R1, R2, S1, S2)
  BY MinWF
<1> DEFINE T1 == { tt[1] : tt \in T }
<1>1. PICK x1 \in T1 : \A y1 \in T1 : <<y1,x1>> \notin R1
  <2>1. T1 \subseteq S1 /\ T1 # {}
    OBVIOUS
  <2>2. QED
    BY <2>1, WFMin
<1> DEFINE T2 == { tt[2] : tt \in { uu \in T : uu[1] = x1 } }
<1>2. PICK x2 \in T2 : \A y2 \in T2 : <<y2,x2>> \notin R2
  <2>1. T2 \subseteq S2 /\ T2 # {}
    OBVIOUS
  <2>2. QED
    BY <2>1, WFMin
<1>3. <<x1, x2>> \in T
  BY IsaM("force")
<1>4. ASSUME NEW t \in T,
             << t, <<x1,x2>> >> \in LexPairOrdering(R1, R2, S1, S2)
      PROVE  FALSE
  <2>1. CASE << t[1], x1 >> \in R1
    BY <1>1, <2>1
  <2>2. CASE t[1] = x1 /\ << t[2], x2 >> \in R2
    BY <1>2, <2>2
  <2>3. QED
    BY <2>1, <2>2, <1>4 DEF LexPairOrdering
<1> QED
  BY <1>3, <1>4

(***************************************************************************)
(* The preceding theorem generalizes in the obvious way to the Cartesian   *)
(* product of a finite number of well-ordered sets.  However, the          *)
(* statement of the general theorem is rather complicated, so we state it  *)
(* for the most useful case: the Cartesian product of n copies of the same *)
(* set.                                                                    *)
(***************************************************************************)
LexProductOrdering(R, S, n) ==
   { ff \in [1..n -> S] \X [1..n -> S] :
       \E j \in 1..n : 
          /\ \A i \in 1..(j-1) : ff[1][i] = ff[2][i]
          /\ <<ff[1][j], ff[2][j]>> \in R }

THEOREM WFLexProductOrdering ==
  ASSUME NEW R, NEW S, NEW n \in Nat,
         IsWellFoundedOn(R, S)
  PROVE  IsWellFoundedOn(LexProductOrdering(R, S, n), [1..n -> S])
<1> DEFINE LPO(m) == LexProductOrdering(R, S, m)
<1> DEFINE P(m) == IsWellFoundedOn(LPO(m), [1..m -> S])
<1>1. P(0)
  BY 1..0 = {}, EmptyIsWellFounded DEF LexProductOrdering
<1>2. ASSUME NEW m \in Nat, P(m)
      PROVE  P(m+1)
  <2>1. IsWellFoundedOn(LexPairOrdering(LPO(m), R, [1..m -> S], S), [1..m -> S] \X S)
    BY <1>2, WFLexPairOrdering
  (*************************************************************************)
  (* Pairs of m-tuples over S in [1..m ->S] and an element of S are        *)
  (* isomorphic to (m+1)-tuples over S, and the following function         *)
  (* establishes this isomorphism. We will then apply the theorem about    *)
  (* preimages to prove the desired result.                                *)
  (*************************************************************************)
  <2> DEFINE g(ss) == << [i \in 1..m |-> ss[i]], ss[m+1] >>
  <2>2. 1 .. m+1 = 1..m \union {m+1}
    OBVIOUS
  <2>3. IsWellFoundedOn(PreImage(g, [1..m+1 -> S], LexPairOrdering(LPO(m), R, [1..m -> S], S)),
                         [1..m+1 -> S])
    <3>1. \A ss \in [1..m+1 -> S] : g(ss) \in [1..m -> S] \X S
      BY <2>2
    <3> HIDE DEF g
    <3>2. QED
      BY <2>1, <3>1, PreImageWellFounded
  <2>4. LPO(m+1) = PreImage(g, [1..m+1 -> S], LexPairOrdering(LPO(m), R, [1..m -> S], S))
    <3>1. LPO(m+1) \subseteq PreImage(g, [1..m+1 -> S], LexPairOrdering(LPO(m), R, [1..m -> S], S))
      <4> SUFFICES ASSUME NEW x \in [1..m+1 -> S], NEW y \in [1..m+1 -> S],
                          NEW j \in 1 .. m+1,
                          \A i \in 1..j-1 : x[i] = y[i],
                          <<x[j], y[j]>> \in R
                   PROVE  <<x,y>> \in PreImage(g, [1..m+1 -> S], LexPairOrdering(LPO(m), R, [1..m -> S], S))
        BY Isa DEF LexProductOrdering
      <4>1. \A i \in 1 .. j-1 : i \in 1 .. m
        OBVIOUS
      <4>2. << g(x), g(y) >> \in LexPairOrdering(LPO(m), R, [1..m -> S], S)
        <5>1. CASE j \in 1..m
          <6>1. << g(x)[1], g(y)[1] >> \in LPO(m)
            BY <2>2, <4>1, <5>1 DEF LexProductOrdering
          <6>2. QED
            BY <6>1, <2>2 DEF LexPairOrdering
        <5>2. CASE j = m+1
          <6>1. /\ g(x)[1] = g(y)[1]
                /\ << g(x)[2], g(y)[2] >> \in R
            BY <2>2, <5>2, IsaM("force")
          <6>2. QED
            BY <6>1, <2>2 DEF LexPairOrdering
        <5>3. QED
          BY <2>2, <5>1, <5>2
      <4>3. QED
        BY <4>2 DEF PreImage
    <3>2. PreImage(g, [1..m+1 -> S], LexPairOrdering(LPO(m), R, [1..m -> S], S)) \subseteq LPO(m+1)
      <4> SUFFICES ASSUME NEW x \in [1..m+1 -> S], NEW y \in [1..m+1 -> S],
                          << g(x), g(y) >> \in LexPairOrdering(LPO(m), R, [1..m -> S], S)
                   PROVE  <<x,y>> \in LPO(m+1)
        BY IsaM("auto") DEF PreImage
      <4>1. CASE << g(x)[1], g(y)[1] >> \in LPO(m)
        <5> HIDE DEF g
        <5>1. PICK j \in 1..m : /\ \A i \in 1..j-1 : g(x)[1][i] = g(y)[1][i]
                                /\ << g(x)[1][j], g(y)[1][j] >> \in R
          BY <4>1 DEF LexProductOrdering
        <5>3. /\ g(x)[1][j] = x[j]
              /\ \A i \in 1..j-1 : g(x)[1][i] = x[i]
              /\ g(y)[1][j] = y[j]
              /\ \A i \in 1..j-1 : g(y)[1][i] = y[i]
          BY <2>2, SMT DEF g
        <5> QED
          BY <5>1, <5>3, <2>2 DEF LexProductOrdering
      <4>2. CASE g(x)[1] = g(y)[1] /\ << g(x)[2], g(y)[2] >> \in R
        <5>1. <<x[m+1], y[m+1]>> \in R
          BY <4>2
        <5>2. \A i \in 1..m : /\ g(x)[1][i] = x[i]
                              /\ g(y)[1][i] = y[i]
          OBVIOUS
        <5>3. \A i \in 1..(m+1)-1 : x[i] = y[i]
          BY <4>2, <5>2, IsaM("auto")
        <5> QED
          BY <5>1, <5>3 DEF LexProductOrdering
      <4> QED
        BY <4>1, <4>2 DEF LexPairOrdering
    <3>3. QED
      BY <3>1, <3>2
  <2> QED
    BY <2>3, <2>4
<1>3. \A m \in Nat : P(m)
  BY <1>1, <1>2, NatInduction, IsaM("auto")
<1>4. QED
  BY <1>3

=============================================================================
\* Modification History
\* Last modified Thu Feb 13 18:26:54 GMT-03:00 2014 by merz
\* Last modified Sun Jan 01 18:39:23 CET 2012 by merz
\* Last modified Wed Nov 23 10:13:18 PST 2011 by lamport
