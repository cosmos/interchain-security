----------------------------- MODULE Bags --------------------------------
(**************************************************************************)
(* A bag, also called a multiset, is a set that can contain multiple      *)
(* copies of the same element.  A bag can have infinitely many elements,  *)
(* but only finitely many copies of any single element.                   *)
(*                                                                        *)
(* We represent a bag in the usual way as a function whose range is a     *)
(* subset of the positive integers.  An element e belongs to bag B iff e  *)
(* is in the domain of B, in which case bag B contains B[e] copies of e.  *)
(**************************************************************************)
EXTENDS TLC, TLAPS,
        FiniteSetTheorems,
        SequenceTheorems
        
LOCAL INSTANCE Naturals
 
IsABag(B) == 
  (************************************************************************)
  (* True iff B is a bag.                                                 *)
  (************************************************************************)
  B \in [DOMAIN B -> {n \in Nat : n > 0}]

BagToSet(B) == DOMAIN B
  (************************************************************************)
  (* The set of elements at least one copy of which is in B.              *)
  (************************************************************************)

SetToBag(S) == [e \in S |-> 1]  
  (************************************************************************)
  (* The bag that contains one copy of every element of the set S.        *)
  (************************************************************************)
    
BagIn(e,B) == e \in BagToSet(B)
  (************************************************************************)
  (* The \in operator for bags.                                           *)
  (************************************************************************)

EmptyBag == SetToBag({})

B1 (+) B2  ==
  (************************************************************************)
  (* The union of bags B1 and B2.                                         *)
  (************************************************************************)
  [e \in (DOMAIN B1) \cup (DOMAIN B2) |->
      (IF e \in DOMAIN B1 THEN B1[e] ELSE 0) 
    + (IF e \in DOMAIN B2 THEN B2[e] ELSE 0) ]
  
B1 (-) B2  == 
  (************************************************************************)
  (* The bag B1 with the elements of B2 removed--that is, with one copy   *)
  (* of an element removed from B1 for each copy of the same element in   *)
  (* B2.  If B2 has at least as many copies of e as B1, then B1 (-) B2    *)
  (* has no copies of e.                                                  *)
  (************************************************************************)
  LET B == [e \in DOMAIN B1 |-> IF e \in DOMAIN B2 THEN B1[e] - B2[e]
                                                   ELSE B1[e]]
  IN  [e \in {d \in DOMAIN B : B[d] > 0} |-> B[e]]

LOCAL Sum(f) ==
        (******************************************************************)
        (* The sum of f[x] for all x in DOMAIN f.  The definition assumes *)
        (* that f is a Nat-valued function and that f[x] equals 0 for all *)
        (* but a finite number of elements x in DOMAIN f.                 *)
        (******************************************************************)
        LET DSum[S \in SUBSET DOMAIN f] ==
               LET elt == CHOOSE e \in S : TRUE
               IN  IF S = {} THEN 0
                             ELSE f[elt] + DSum[S \ {elt}]
        IN  DSum[DOMAIN f]

BagUnion(S) ==
  (************************************************************************)
  (* The bag union of all elements of the set S of bags.                  *)
  (************************************************************************)
  [e \in UNION {BagToSet(B) : B \in S} |->
    Sum( [B \in S |-> IF BagIn(e, B) THEN B[e] ELSE 0] ) ]

B1 \sqsubseteq B2  ==
  (************************************************************************)
  (* The subset operator for bags.  B1 \sqsubseteq B2 iff, for all e, bag *)
  (* B2 has at least as many copies of e as bag B1 does.                  *)
  (************************************************************************)
  /\ (DOMAIN B1) \subseteq (DOMAIN B2)
  /\ \A e \in DOMAIN B1 : B1[e] \leq B2[e]

SubBag(B) ==
  (************************************************************************)
  (* The set of all subbags of bag B.                                     *)
  (*                                                                      *)
  (* The following definition is not the one described in the TLA+ book,  *)
  (* but rather one that TLC can evaluate.                                *)
  (************************************************************************)

  LET RemoveFromDom(x, f) == [y \in (DOMAIN f) \ {x} |-> f[y]]
      Combine(x, BagSet) == 
         BagSet \cup 
          {[y \in (DOMAIN f) \cup {x} |-> IF y = x THEN i ELSE f[y]] :
                f \in BagSet, i \in 1..B[x]}
      Biggest == LET Range1 == {B[x] : x \in DOMAIN B}
                 IN  IF Range1 = {} THEN 0
                                   ELSE CHOOSE r \in Range1 :
                                           \A s \in Range1 : r \geq s
      RSB[BB \in UNION {[S -> 1..Biggest] : S \in SUBSET DOMAIN B}] ==
        IF BB = << >> THEN {<< >>}
                      ELSE LET x == CHOOSE x \in DOMAIN BB : TRUE
                           IN  Combine(x, RSB[RemoveFromDom(x, BB)])
  IN RSB[B]

  (*******************  Here is the definition from the TLA+ book. ********
  LET AllBagsOfSubset == 
        (******************************************************************)
        (* The set of all bags SB such that BagToSet(SB) \subseteq        *)
        (* BagToSet(B).                                                   *)
        (******************************************************************)
        UNION {[SB -> {n \in Nat : n > 0}] : SB \in SUBSET BagToSet(B)}  
  IN  {SB \in AllBagsOfSubset : \A e \in DOMAIN SB : SB[e] \leq B[e]}
  ***************************************************************************)

BagOfAll(F(_), B) ==
  (************************************************************************)
  (* The bag analog of the set {F(x) : x \in B} for a set B. It's the bag *)
  (* that contains, for each element e of B, one copy of F(e) for every   *)
  (* copy of e in B. This defines a bag iff, for any value v, the set of  *)
  (* e in B such that F(e) = v is finite.                                 *)
  (************************************************************************)
  [e \in {F(d) : d \in BagToSet(B)} |-> 
     Sum( [d \in BagToSet(B) |-> IF F(d) = e THEN B[d] ELSE 0] ) ]

BagCardinality(B) ==
  (************************************************************************)
  (* If B is a finite bag (one such that BagToSet(B) is a finite set),    *)
  (* then this is its cardinality (the total number of copies of elements *)
  (* in B).  Its value is unspecified if B is infinite.                   *)
  (************************************************************************)
  Sum(B)

CopiesIn(e, B) ==
  (************************************************************************)
  (* If B is a bag, then CopiesIn(e, B) is the number of copies of e in   *)
  (* B. If ~BagIn(e, B), then CopiesIn(e, B) = 0.                         *)
  (************************************************************************)
  
  IF BagIn(e, B) THEN B[e] ELSE 0
  
Scaling(n, B) ==  
  (************************************************************************)
  (* If B is a bag, then Scaling(e, B) is the Bag containing the same     *)
  (* elements of B with n times their copies                              *)
  (************************************************************************)
  IF n>0 THEN [i \in DOMAIN B |-> n*B[i] ] ELSE EmptyBag 

(***************************************************************************)
(* Converts the Sequence into a bag                                        *)
(***************************************************************************)

SeqToBag(seq) == [ x \in Range(seq) |-> Cardinality({i \in DOMAIN seq: seq[i]=x}) ]



(***************************************************************************)
(* \sqsubseteq is a PARTIAL ORDER relattion                                *)
(***************************************************************************)

(*AntiSymmetry*)
THEOREM Bags_SqsubseteqPO_AntiSymmetry == ASSUME NEW A, NEW B, IsABag(A), IsABag(B), A \sqsubseteq B, B \sqsubseteq A  
                     PROVE A = B
<1>1. DOMAIN A = DOMAIN B
      BY DEF \sqsubseteq
<1>2. (\A i \in DOMAIN A: A[i]<=B[i]) /\ (\A i \in DOMAIN B: B[i]<=A[i])
      BY DEF \sqsubseteq
<1>3. \A i \in DOMAIN A: A[i]=B[i]
      BY <1>1, <1>2, SMT DEF IsABag
<1>4. A \in [DOMAIN A -> {n \in Nat: n>0}] /\ B \in [DOMAIN B -> {n \in Nat: n>0}]    
      BY DEF IsABag
<1>5. QED
      BY <1>4, <1>3, <1>1 

(*Reflexivity*)
THEOREM Bags_SqsubsetPO_Reflexivity == ASSUME NEW B, IsABag(B)
                                  PROVE B \sqsubseteq B
BY SMT DEF \sqsubseteq, IsABag                                  

(*Transitivity*)            
THEOREM Bags_SqsubseteqPO_Transitivity == ASSUME NEW A, NEW B, NEW C, IsABag(A), IsABag(B), IsABag(C), A \sqsubseteq B, B \sqsubseteq C
                             PROVE A \sqsubseteq C
<1>1. DOMAIN A \subseteq DOMAIN C /\ DOMAIN A \subseteq DOMAIN B
      BY DEF \sqsubseteq
<1>2. (\A i \in DOMAIN A: A[i] <= B[i]) /\ (\A i \in DOMAIN B: B[i]<=C[i] )
      BY <1>1 DEF \sqsubseteq, IsABag
<1>3. \A i \in DOMAIN A: B[i]<=C[i]
      BY <1>1, <1>2
<1>4. \A i \in DOMAIN A: A[i]<=C[i]
      BY <1>3, <1>2, SMT DEF IsABag      
<1>.QED                     
    BY <1>1, <1>4 DEF \sqsubseteq

(***************************************************************************)
(* Lemmas on EmptyBags                                                     *)
(***************************************************************************)

    
THEOREM Bags_EmptyBag == ASSUME NEW B, IsABag(B)
                         PROVE  /\ IsABag(EmptyBag)
                                /\ B=EmptyBag <=> DOMAIN B ={}
                                /\ DOMAIN EmptyBag ={}
                                /\ EmptyBag \sqsubseteq B
                                /\ \A e: ~BagIn(e, EmptyBag)
<1>1.  DOMAIN EmptyBag = {}
       BY DEF EmptyBag, SetToBag     
<1>2. IsABag(EmptyBag)
      <2>1. \A i \in DOMAIN EmptyBag: EmptyBag[i] \in {n \in Nat: n>0}
            BY <1>1
      <2>2. QED
            BY <2>1 DEF IsABag, EmptyBag, SetToBag             
<1>3. B=EmptyBag => DOMAIN B ={}
      BY DEF EmptyBag, SetToBag
<1>4. ASSUME DOMAIN B ={} PROVE B=EmptyBag
      <2>1. B \in [{} -> {n \in Nat: n>0}] /\ EmptyBag \in [{} -> {n \in Nat: n>0}]
            BY <1>4 DEF EmptyBag, IsABag, SetToBag
      <2>2. DOMAIN B = DOMAIN EmptyBag
            BY <1>4 DEF EmptyBag, SetToBag
      <2>3. \A i \in DOMAIN B : B[i]=EmptyBag[i]
            BY <1>4 DEF EmptyBag, SetToBag
      <2>4. QED
            BY <2>3, <2>2, <2>1 
<1>5. EmptyBag \sqsubseteq B     
      BY <1>1 DEF \sqsubseteq
<1>6. ASSUME ~(\A e: ~BagIn(e, EmptyBag)) PROVE FALSE
      <2>1. \E e: BagIn(e, EmptyBag)
            BY <1>6
      <2>2. PICK e : BagIn(e, EmptyBag)
            BY <2>1
      <2>3. QED
            BY <2>2, <1>1 DEF BagIn, BagToSet
<1>7. QED
      BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6

(***************************************************************************)
(* Lemmas on Scalng Operator for Bags                                      *)
(***************************************************************************)

THEOREM Bags_Scaling == ASSUME NEW B, IsABag(B), NEW n \in Nat, NEW m \in Nat
                        PROVE /\ IsABag(Scaling(n, B)) 
                              /\ Scaling(n, EmptyBag)=EmptyBag
                              /\ Scaling(0, B)=EmptyBag
                              /\ Scaling(1, B)= B
                              /\ Scaling((n*m), B) = Scaling(n, Scaling(m, B))
                              /\ n>0 => DOMAIN(Scaling(n, B))= DOMAIN B   
PROOF
<1>1. IsABag(Scaling(n, B))
      <2>1. CASE n=0
            <3>1. Scaling(n, B)= EmptyBag
                  BY <2>1 DEF Scaling
            <3>2. QED 
                  BY <3>1, Bags_EmptyBag
      <2>2. CASE n>0
            BY <2>2, SMT DEF IsABag, Scaling        
      <2>3. QED      
            BY <2>1, <2>2, SMT                  
            
<1>2. Scaling(n, EmptyBag)=EmptyBag
      <2>1. DOMAIN Scaling(n, EmptyBag)={}
            BY Bags_EmptyBag DEF Scaling 
      <2>2. IsABag(Scaling(n, EmptyBag))
            BY Bags_EmptyBag, SMT DEF Scaling, EmptyBag, SetToBag, IsABag
      <2>. QED
           BY <2>1, <2>2, Bags_EmptyBag
<1>3. Scaling(0, B)=EmptyBag
      BY DEF Scaling 
<1>4. Scaling(1, B)= B
      BY SMT DEF Scaling, IsABag                
<1>5. Scaling((n*m), B) = Scaling(n, Scaling(m, B))
      <2>1. CASE m>0 /\ n>0 
            <3>1. n*m>0
                  BY <2>1, SMT
            <3>2. QED
                  BY <3>1, <2>1, SMT DEF Scaling, IsABag
      <2>2. CASE m>0 /\ n=0
            <3>1. n*m=0
                  BY <2>2, SMT
            <3>2. QED
                  BY <3>1, <2>2, SMT DEF Scaling, IsABag
      <2>3. CASE m=0 /\ n>0
            <3>1. Scaling(n, Scaling(m, B))=EmptyBag
                  BY <2>3, <1>2, <1>3      
            <3>2. Scaling(n*m, B)=EmptyBag
                  BY <2>3, SMT DEF Scaling, IsABag
            <3>3.  QED      
                  BY <3>1, <3>2
      <2>4. CASE m=0 /\ n=0
            <3>1. n*m=0
                  BY <2>4, SMT
            <3>2. QED
                  BY <3>1, <2>4, SMT DEF Scaling, IsABag
      <2>5. QED
            BY SMT, <2>1, <2>2, <2>3, <2>4
<1>6. ASSUME n>0 PROVE DOMAIN Scaling(n, B)=DOMAIN B
      <2>1. QED
            BY <1>6, <1>1 DEF Scaling, IsABag                   
<1> QED 
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6


(***************************************************************************)
(* SetToBag and BagToSet are inverse of each other                         *)
(***************************************************************************)

THEOREM Bags_Inverse == ASSUME NEW S
                        PROVE BagToSet(SetToBag(S))=S
BY DEF SetToBag, BagToSet                  

THEOREM Bags_Inverse1 == ASSUME NEW B, IsABag(B)
                         PROVE SetToBag(BagToSet(B)) \sqsubseteq B
<1>1. DOMAIN SetToBag(BagToSet(B)) \subseteq DOMAIN B
      BY DEF SetToBag, BagToSet, \sqsubseteq, IsABag
<1>2. \A i \in DOMAIN SetToBag(BagToSet(B)): SetToBag(BagToSet(B))[i] <= B[i]
      <2>1. TAKE i \in DOMAIN SetToBag(BagToSet(B))
      <2>2. QED 
            BY <2>1, SMT DEF SetToBag, BagToSet, IsABag
<1>3. QED
      BY <1>1, <1>2 DEF \sqsubseteq

(***************************************************************************)
(* SetToBag Preserves Equality                                             *)
(***************************************************************************)

THEOREM Bags_SetToBagEquality == ASSUME NEW A, NEW B
                                 PROVE A=B <=> SetToBag(A)=SetToBag(B)
<1>1. A=B => SetToBag(A) = SetToBag(B)
      BY DEF SetToBag
<1>2. ASSUME SetToBag(A)=SetToBag(B) PROVE A=B
      <2>1. BagToSet(SetToBag(A))=BagToSet(SetToBag(B))
            BY <1>2 
      <2>2. QED
            BY <2>1, Bags_Inverse            
<1>3. QED            
      BY <1>1, <1>2

(***************************************************************************)
(* Union of Bags                                                           *)
(***************************************************************************)

THEOREM Bags_Union == 
  ASSUME NEW B1, NEW B2, IsABag(B1), IsABag(B2)
  PROVE  /\ IsABag(B1(+)B2)
         /\ DOMAIN(B1 (+) B2) = DOMAIN B1 \cup DOMAIN B2
         /\ \A e : CopiesIn(e, B1(+)B2) = CopiesIn(e,B1) + CopiesIn(e,B2)
BY DEF IsABag, (+), CopiesIn, BagIn, BagToSet

(***************************************************************************)
(* Differene of Bags                                                       *)
(***************************************************************************)

THEOREM Bags_Difference == 
  ASSUME NEW B1, NEW B2, IsABag(B1), IsABag(B2)
  PROVE  /\ IsABag(B1(-)B2)
         /\ DOMAIN (B1 (-) B2) = {e \in DOMAIN B1 : e \notin DOMAIN B2 \/ B1[e] > B2[e]}
         /\ \A e : CopiesIn(e, B1 (-) B2) = IF BagIn(e, B1(-)B2) THEN CopiesIn(e,B1) - CopiesIn(e,B2) ELSE 0
<1>. DEFINE B == [e \in DOMAIN B1 |-> IF e \in DOMAIN B2 THEN B1[e] - B2[e]
                                                         ELSE B1[e]]
            D == {d \in DOMAIN B1 : B[d] > 0}
<1>1. B \in [DOMAIN B1 -> Int]
  BY DEF IsABag
<1>2. B1 (-) B2 = [e \in D |-> B[e]]
  BY DEF (-)
<1>3. D = {e \in DOMAIN B1 : e \notin DOMAIN B2 \/ B1[e] > B2[e]}
  BY DEF IsABag
<1>4. \A e \in D : B[e] = B1[e] - (IF e \in DOMAIN B2 THEN B2[e] ELSE 0)
  BY DEF IsABag
<1>. HIDE DEF B
<1>. QED
  BY <1>1, <1>2, <1>3, <1>4 DEF IsABag, CopiesIn, BagIn, BagToSet

(***************************************************************************)
(* Union is Commutative                                                    *)
(***************************************************************************)

THEOREM Bags_UnionCommutative == ASSUME NEW B1, NEW B2, IsABag(B1), IsABag(B2)
                               PROVE B1(+)B2 = B2(+)B1      
<1>1. DOMAIN(B1(+)B2) = DOMAIN(B2(+)B1)
      BY DEF (+) 
<1>2. B1(+)B2 \in [DOMAIN(B1(+)B2) -> {n \in Nat: n>0}] /\ B2(+)B1 \in [DOMAIN(B1(+)B2) -> {n \in Nat: n>0}]
      BY <1>1, Bags_Union DEF IsABag 
<1>3. \A i \in DOMAIN(B1(+)B2): (B1(+)B2)[i] = (B2(+)B1)[i]
      <2>1. TAKE i \in DOMAIN(B1(+)B2)
      <2>.  QED
            BY SMT, <2>1 DEF (+), IsABag
<1>4. QED
      BY <1>1, <1>2, <1>3  
      
(***************************************************************************)
(* Unon is Associative                                                     *)
(***************************************************************************)                      

THEOREM Bags_UnionAssociative == ASSUME NEW B1, NEW B2, NEW B3, IsABag(B1), IsABag(B2), IsABag(B3)
                                 PROVE (B1(+)B2)(+)B3 = B1(+)(B2(+)B3)
BY DEF IsABag, (+)

(***************************************************************************)
(* Given Bags B1, B2 then B1 \sqsubseteq B1(+)B2                           *)
(***************************************************************************)
      
THEOREM Bags_UnionSqSubset == ASSUME NEW B1, NEW B2, IsABag(B1), IsABag(B2)
                              PROVE B1 \sqsubseteq B1(+)B2
<1>1. IsABag(B1(+)B2)
      BY Bags_Union
<1>2. DOMAIN B1 \subseteq DOMAIN(B1(+)B2)
      BY DEF (+)
<1>3. \A i \in DOMAIN B1: B1[i]<=(B1(+)B2)[i]
      <2>1. TAKE i \in DOMAIN B1
      <2>2. QED
            BY <2>1, <1>1, SMT DEF IsABag, \sqsubseteq, (+)
<1>4. QED
      BY <1>2, <1>3 DEF \sqsubseteq, (+)       

(***************************************************************************)
(* Given Bag B1, B1 \sqsubseteq Scaling(n, B1) for all n>0                 *)
(***************************************************************************)

THEOREM Bags_ScalingSqSubseteq == ASSUME NEW B, IsABag(B), NEW n \in Nat, NEW m \in Nat, m<n
                                  PROVE Scaling(m, B) \sqsubseteq Scaling(n, B)
<1>1. CASE m>0 /\ n>0
      <2>1. DOMAIN Scaling(m, B)= DOMAIN Scaling(n, B)
      BY <1>1, Bags_Scaling 
      <2>2. \A i \in DOMAIN Scaling(m, B): Scaling(m, B)[i]<= Scaling(n, B)[i]
            <3>1. TAKE i \in DOMAIN Scaling(m, B)
            <3>2. QED
                  BY <1>1, SMT DEF Scaling, IsABag
      <2>3. QED
            BY <2>1, <2>2 DEF \sqsubseteq     
<1>2. CASE m=0 /\ n>0
      <2>1. Scaling(m, B)=EmptyBag
            BY <1>2, Bags_Union DEF Scaling
      <2>2. QED
            BY <2>1, Bags_EmptyBag, Bags_Scaling
<1>3. CASE m>0 /\ n=0 \* Impossible Case
      BY <1>3, SMT      
<1>4. CASE m=0 /\ n=0 \* Impossible Case
      BY <1>4, SMT
<1>5. QED
      BY <1>1, <1>2, <1>3, <1>4, SMT                                 

(***************************************************************************)
(* Given Bags A and B, A(-)B \sqsubseteq A                                 *)
(***************************************************************************)

THEOREM Bags_DifferenceSqsubset == ASSUME NEW A, NEW B, IsABag(A), IsABag(B)
                                   PROVE A(-)B \sqsubseteq A 
<1>1. DOMAIN(A(-)B) \subseteq DOMAIN A
      BY DEF (-) 
<1>2. \A i \in DOMAIN(A(-)B) : (A(-)B)[i] <= A[i]
      <2>1. TAKE i \in DOMAIN(A(-)B)
      <2>2. QED
            BY <2>1, SMT DEF (-), IsABag
<1>3. QED                   
      BY <1>1, <1>2 DEF \sqsubseteq     
  
(***************************************************************************)
(* EmptyBag is Addidtive Identity                                          *)
(***************************************************************************)  

THEOREM Bags_EmptyBagOperations == ASSUME NEW B, IsABag(B)
                                   PROVE /\ B (+) EmptyBag = B
                                         /\ B (-) EmptyBag = B
<1>1. B (+) EmptyBag = B
      <2>1. IsABag(B(+)EmptyBag) 
            BY Bags_EmptyBag, Bags_Union
      <2>2. DOMAIN(B(+)EmptyBag) = DOMAIN B
            BY Bags_EmptyBag DEF (+)
      <2>3. B \in [DOMAIN B -> {n \in Nat : n>0}] /\ B(+)EmptyBag \in [DOMAIN B -> {n \in Nat : n>0}]
            BY <2>1, <2>2 DEF IsABag
      <2>4. \A i \in DOMAIN B: (B(+)EmptyBag)[i]=B[i]
            <3>1. TAKE i \in DOMAIN B
            <3>2. QED
                  BY <3>1, SMT DEF EmptyBag, (+), IsABag, SetToBag
      <2>5. QED 
           BY <2>2, <2>3, <2>4     
<1>2. B (-) EmptyBag = B
      <2>1. /\ IsABag(B(-)EmptyBag)
            /\ DOMAIN(B (-) EmptyBag) = DOMAIN B
            BY Bags_EmptyBag, Bags_Difference, Isa
      <2>3. B \in [DOMAIN B -> {n \in Nat : n>0}] /\ B(-)EmptyBag \in [DOMAIN B -> {n \in Nat : n>0}]
            BY <2>1 DEF IsABag
      <2>4. \A i \in DOMAIN B: (B(-)EmptyBag)[i]=B[i]
            <3>1. TAKE i \in DOMAIN B 
            <3>2. QED
                  BY <3>1 DEF EmptyBag, (-), IsABag, SetToBag       
      <2>5. QED 
            BY <2>1, <2>3, <2>4           
<1>3. QED
      BY <1>1, <1>2
      
(***************************************************************************)
(* SetToBag of a set is a Bag                                              *)
(***************************************************************************)      

THEOREM Bags_SetToBagIsABag == ASSUME NEW S
                               PROVE IsABag(SetToBag(S))
BY DEF IsABag, SetToBag

(***************************************************************************)
(* CopiesIn Monotone w.r.t \sqsubseteq                                     *)
(***************************************************************************)
  
THEOREM Bags_CopiesInBagsInMonotone ==
  ASSUME NEW B1, NEW B2, NEW e, IsABag(B1), IsABag(B2), B1 \sqsubseteq B2 
  PROVE  /\ BagIn(e, B1) => BagIn(e, B2)
         /\ CopiesIn(e, B1) <= CopiesIn(e, B2)
<1>1. ASSUME BagIn(e, B1) PROVE BagIn(e, B2)
      BY <1>1 DEF BagIn, BagToSet, \sqsubseteq
<1>2. CopiesIn(e, B1) <= CopiesIn(e, B2)
      <2>1. CASE BagIn(e, B1)
            BY <2>1 DEF CopiesIn, BagIn, \sqsubseteq, BagToSet
      <2>2. CASE ~BagIn(e, B1)
            BY <2>2, SMT DEF \sqsubseteq, IsABag, CopiesIn, BagIn, BagToSet      
      <2>3. QED
            BY <2>1, <2>2        
<1>3. QED
      BY <1>1, <1>2


(***************************************************************************)
(* Given Bag B and Natural n, CopiesIn(e, Scaling(n, B))=n*CopiesIn(e, B)  *)
(***************************************************************************)
      
THEOREM Bags_CopiesInScaling == ASSUME NEW B, IsABag(B), NEW n \in Nat, NEW e
                                 PROVE CopiesIn(e, Scaling(n, B))=n*CopiesIn(e, B)
PROOF 
<1>1. CASE n=0
      BY <1>1, Bags_Scaling, Bags_EmptyBag, SMT DEF CopiesIn, IsABag
<1>2. CASE n>0
      BY <1>2, SMT DEF CopiesIn, IsABag, Scaling, BagIn, BagToSet
<1>3. QED
      BY <1>1, <1>2, SMT
 
(***************************************************************************)
(* Given set S, CopiesIn(e, SetToBag(S))=IF e \in B THEN 1 ELSE 0          *)
(***************************************************************************)
 
THEOREM Bags_CopiesInSetToBag == ASSUME NEW B, NEW e
                                 PROVE CopiesIn(e, SetToBag(B))=IF e \in B THEN 1 ELSE 0
PROOF 
<1>1. ASSUME e \in B PROVE CopiesIn(e, SetToBag(B))=1
      BY <1>1 DEF CopiesIn, BagIn, BagToSet, SetToBag
<1>2. ASSUME e \notin B PROVE CopiesIn(e, SetToBag(B))=0
      BY <1>2 DEF CopiesIn, BagIn, BagToSet, SetToBag
<1>3. QED
      BY <1>2, <1>1                                       

(***************************************************************************)
(* Given sequence seq, SeqToBag(seq) is a Bag                              *)
(***************************************************************************)

THEOREM Bags_IsABagSeqToBag ==
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  IsABag(SeqToBag(seq))
<1>1. \A x \in DOMAIN SeqToBag(seq): SeqToBag(seq)[x] \in Nat \ {0}
  <2>1. TAKE x \in DOMAIN SeqToBag(seq)
  <2>2. SeqToBag(seq)[x] \in Nat \ {0}
    <3>1. CASE seq = << >>
       <4>1. DOMAIN SeqToBag(seq)= {}
         BY <3>1 DEF Range, SeqToBag
       <4>2. QED
         BY <4>1, Bags_EmptyBag
    <3>2. CASE seq # << >>
       <4>1. {i \in DOMAIN seq: seq[i]=x }#{}
         BY <2>1, <3>2 DEF SeqToBag, Range
       <4>. IsFiniteSet({i \in DOMAIN seq: seq[i]=x })    
         <5>1. {i \in DOMAIN seq: seq[i]=x } \subseteq DOMAIN seq
            OBVIOUS
         <5>2. IsFiniteSet(DOMAIN seq)
           BY SeqDef, FS_Interval
         <5>3. QED
           BY <5>1, <5>2, FS_Subset              
       <4>2. QED 
         BY <4>1, SMT, FS_EmptySet, FS_CardinalityType DEF SeqToBag                        
    <3>3. QED
      BY <3>1, <3>2
  <2>3. QED
    BY <2>2 DEF SeqToBag
<1>2. QED
      BY <1>1 DEF IsABag, SeqToBag

=============================================================================

(* Last modified on Fri 26 Jan 2007 at  8:45:03 PST by lamport *)

 6 Apr 99 : Modified version for standard module set
 7 Dec 98 : Corrected error found by Stephan Merz.
 6 Dec 98 : Modified comments based on suggestions by Lyle Ramshaw.
 5 Dec 98 : Initial version.
