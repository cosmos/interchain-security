----------------------- MODULE SequenceTheorems_proofs ----------------------
(***************************************************************************)
(* This module contains the proofs for theorems about sequences and the    *)
(* corresponding operations.                                               *)
(***************************************************************************)
EXTENDS Sequences, Integers, WellFoundedInduction, Functions, TLAPS


(***************************************************************************)
(* Elementary properties about Seq(S)                                      *)
(***************************************************************************)

LEMMA SeqDef == \A S : Seq(S) = UNION {[1..n -> S] : n \in Nat}
OBVIOUS

THEOREM ElementOfSeq ==
   ASSUME NEW S, NEW seq \in Seq(S),
          NEW n \in 1..Len(seq)
   PROVE  seq[n] \in S
OBVIOUS
 
THEOREM EmptySeq ==
   ASSUME NEW S
   PROVE /\ << >> \in Seq(S)
         /\ \A seq \in Seq(S) : (seq = << >>) <=> (Len(seq) = 0)
OBVIOUS

THEOREM LenProperties == 
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  /\ Len(seq) \in Nat
         /\ seq \in [1..Len(seq) -> S]
         /\ DOMAIN seq = 1 .. Len(seq) 
OBVIOUS

THEOREM ExceptSeq ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW i \in 1 .. Len(seq), NEW e \in S
  PROVE  /\ [seq EXCEPT ![i] = e] \in Seq(S)
         /\ Len([seq EXCEPT ![i] = e]) = Len(seq)
         /\ \A j \in 1 .. Len(seq) : [seq EXCEPT ![i] = e][j] = IF j=i THEN e ELSE seq[j]
<1>. DEFINE exc == [seq EXCEPT ![i] = e]
<1>1. \A j \in 1 .. Len(seq) : exc[j] = IF j=i THEN e ELSE seq[j]
  BY DOMAIN exc = 1 .. Len(seq), Zenon
<1>. QED
  BY <1>1

THEOREM IsASeq ==
  ASSUME NEW n \in Nat, NEW e(_), NEW S,
         \A i \in 1..n : e(i) \in S
  PROVE  [i \in 1..n |-> e(i)] \in Seq(S)
OBVIOUS

THEOREM SeqEqual ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S),
         Len(s) = Len(t), \A i \in 1 .. Len(s) : s[i] = t[i]
  PROVE  s = t
<1>1. /\ DOMAIN s = 1 .. Len(s)
      /\ DOMAIN t = 1 .. Len(s)
      /\ s = [i \in DOMAIN s |-> s[i]]
      /\ t = [i \in DOMAIN t |-> t[i]]
  OBVIOUS
<1>. QED
  BY <1>1, Zenon

(***************************************************************************
                 Concatenation (\o) And Properties                      
***************************************************************************)

THEOREM ConcatProperties ==
  ASSUME NEW S, NEW s1 \in Seq(S), NEW s2 \in Seq(S)
  PROVE  /\ s1 \o s2 \in Seq(S)
         /\ Len(s1 \o s2) = Len(s1) + Len(s2)
         /\ \A i \in 1 .. Len(s1) + Len(s2) : (s1 \o s2)[i] =
                     IF i <= Len(s1) THEN s1[i] ELSE s2[i - Len(s1)]
OBVIOUS

THEOREM ConcatEmptySeq ==
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  /\ seq \o << >> = seq
         /\ << >> \o seq = seq
OBVIOUS

THEOREM ConcatAssociative ==
  ASSUME NEW S, NEW s1 \in Seq(S), NEW s2 \in Seq(S), NEW s3 \in Seq(S)
  PROVE  (s1 \o s2) \o s3 = s1 \o (s2 \o s3)
OBVIOUS

THEOREM ConcatSimplifications ==
  ASSUME NEW S
  PROVE  /\ \A s,t \in Seq(S) : s \o t = s <=> t = <<>>
         /\ \A s,t \in Seq(S) : s \o t = t <=> s = <<>>
         /\ \A s,t \in Seq(S) : s \o t = <<>> <=> s = <<>> /\ t = <<>>
         /\ \A s,t,u \in Seq(S) : s \o t = s \o u <=> t = u
         /\ \A s,t,u \in Seq(S) : s \o u = t \o u <=> s = t
<1>1. /\ \A s,t \in Seq(S) : s \o t = s <=> t = <<>>
      /\ \A s,t \in Seq(S) : s \o t = t <=> s = <<>>
      /\ \A s,t \in Seq(S) : s \o t = <<>> <=> s = <<>> /\ t = <<>>
  OBVIOUS
<1>2. \A s,t,u \in Seq(S) : s \o t = s \o u <=> t = u
  <2>. SUFFICES ASSUME NEW s \in Seq(S), NEW t \in Seq(S), NEW u \in Seq(S),
                       s \o t = s \o u
                PROVE  t = u
    BY Zenon
  <2>1. Len(t) = Len(u)  OBVIOUS
  <2>2. \A i \in 1 .. Len(t) : t[i] = (s \o t)[i + Len(s)]  OBVIOUS
  <2>3. \A i \in 1 .. Len(u) : u[i] = (s \o u)[i + Len(s)]  OBVIOUS
  <2>. QED  BY <2>1, <2>2, <2>3, SeqEqual
<1>3. \A s,t,u \in Seq(S) : s \o u = t \o u <=> s = t
  <2>. SUFFICES ASSUME NEW s \in Seq(S), NEW t \in Seq(S), NEW u \in Seq(S),
                       s \o u = t \o u
                PROVE  s = t
    BY Zenon
  <2>1. Len(s) = Len(t)  OBVIOUS
  <2>2. \A i \in 1 .. Len(s) : s[i] = (s \o u)[i]  OBVIOUS
  <2>3. \A i \in 1 .. Len(t) : t[i] = (t \o u)[i]  OBVIOUS
  <2>. QED  BY <2>1, <2>2, <2>3, SeqEqual
<1>. QED  BY <1>1, <1>2, <1>3, Zenon

(***************************************************************************)
(*                     SubSeq, Head and Tail                               *)
(***************************************************************************)

THEOREM SubSeqProperties ==
  ASSUME NEW S,
         NEW s \in Seq(S),
         NEW m \in 1 .. Len(s)+1,
         NEW n \in m-1 .. Len(s)
  PROVE  /\ SubSeq(s,m,n) \in Seq(S)
         /\ Len(SubSeq(s, m, n)) = n-m+1
         /\ \A i \in 1 .. n-m+1 : SubSeq(s,m,n)[i] = s[m+i-1]
<1>1. CASE n \in m .. Len(s)
  BY <1>1
<1>2. CASE n = m-1
  <2>. DEFINE sub == SubSeq(s,m,m-1)
  <2>1. /\ sub = << >>
        /\ n-m+1 = 0
        /\ \A i \in 1 .. n-m+1 : sub[i] \in S /\ SubSeq(s,m,n)[i] = s[m+i-1]
    BY <1>2
  <2>2. Len(sub) = n-m+1
    BY <2>1, Zenon
  <2>. QED
    BY <1>2, <2>1, <2>2, Isa
<1>. QED
  BY <1>1, <1>2

THEOREM SubSeqEmpty ==
  ASSUME NEW s, NEW m \in Int, NEW n \in Int, n < m
  PROVE  SubSeq(s,m,n) = << >>
OBVIOUS

THEOREM HeadTailProperties ==
   ASSUME NEW S,
          NEW seq \in Seq(S), seq # << >>
   PROVE  /\ Head(seq) \in S
          /\ Tail(seq) \in Seq(S)
          /\ Len(Tail(seq)) = Len(seq)-1
          /\ \A i \in 1 .. Len(Tail(seq)) : Tail(seq)[i] = seq[i+1]
OBVIOUS


THEOREM TailIsSubSeq ==
  ASSUME NEW S,
         NEW seq \in Seq(S), seq # << >>
  PROVE  Tail(seq) = SubSeq(seq, 2, Len(seq))
OBVIOUS

THEOREM SubSeqRestrict ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW n \in 0 .. Len(seq)
  PROVE  SubSeq(seq, 1, n) = Restrict(seq, 1 .. n)
BY DEF Restrict

THEOREM HeadTailOfSubSeq ==
  ASSUME NEW S, NEW seq \in Seq(S),
         NEW m \in 1 .. Len(seq), NEW n \in m .. Len(seq)
  PROVE  /\ Head(SubSeq(seq,m,n)) = seq[m]
         /\ Tail(SubSeq(seq,m,n)) = SubSeq(seq, m+1, n)
OBVIOUS

THEOREM SubSeqRecursiveFirst ==
  ASSUME NEW S, NEW seq \in Seq(S),
         NEW m \in 1 .. Len(seq), NEW n \in m .. Len(seq)
  PROVE  SubSeq(seq, m, n) = << seq[m] >> \o SubSeq(seq, m+1, n)
<1>. DEFINE lhs == SubSeq(seq, m, n)
            rhs == << seq[m] >> \o SubSeq(seq, m+1, n)
<1>1. /\ lhs \in Seq(S)
      /\ rhs \in Seq(S)
  OBVIOUS
<1>2. Len(lhs) = Len(rhs)
  <2>1. Len(lhs) = n-m+1
    BY SubSeqProperties
  <2>2. /\ m+1 \in 1 .. Len(seq)+1
        /\ n \in (m+1)-1 .. Len(seq)
    OBVIOUS
  <2>3. Len(SubSeq(seq, m+1, n)) = n - (m+1) + 1
    BY <2>2, SubSeqProperties, Zenon
  <2>. QED
    BY <2>1, <2>3
<1>3. ASSUME NEW i \in 1 .. Len(lhs)
      PROVE  lhs[i] = rhs[i]
  OBVIOUS
<1>. QED
  BY <1>1, <1>2, <1>3, SeqEqual

THEOREM SubSeqRecursiveSecond ==
  ASSUME NEW S, NEW seq \in Seq(S),
         NEW m \in 1 .. Len(seq), NEW n \in m .. Len(seq)
  PROVE  SubSeq(seq, m, n) = SubSeq(seq, m, n-1) \o << seq[n] >>
<1>. DEFINE lhs == SubSeq(seq, m, n)
            mid == SubSeq(seq, m, n-1)
            rhs == mid \o << seq[n] >>
<1>1. /\ lhs \in Seq(S)
      /\ mid \in Seq(S)
      /\ rhs \in Seq(S)
      /\ <<seq[n]>> \in Seq(S)
  OBVIOUS
<1>2. Len(lhs) = n-m+1
  BY SubSeqProperties
<1>3. Len(mid) = (n-1) - m + 1
  BY m \in 1 .. Len(seq)+1, n-1 \in m-1 .. Len(seq), SubSeqProperties
<1>4. Len(lhs) = Len(rhs)
  BY <1>2, <1>3
<1>5. ASSUME NEW i \in 1 .. Len(lhs)
      PROVE  lhs[i] = rhs[i]
  <2>1. lhs[i] = seq[m+i-1]
    OBVIOUS
  <2>2. rhs[i] = seq[m+i-1]
    <3>1. i \in 1 .. (Len(mid) + Len(<<seq[n]>>))
      BY <1>4, <1>5
    <3>2. CASE i \in 1 .. (Len(lhs)-1)
      BY <3>2
    <3>3. CASE ~(i \in 1 .. (Len(lhs)-1))
      <4>1. i = Len(lhs) /\ ~(i <= Len(mid))
        BY <3>3, <1>2, <1>3
      <4>2. rhs[i] = <<seq[n]>>[i - Len(mid)]
        BY <1>1, <3>1, <4>1, ConcatProperties, Zenon
      <4>3. /\ i - Len(mid) = 1
            /\ n = m+i-1
        BY <4>1, <1>2, <1>3
      <4>. QED
        BY <4>2, <4>3, Isa
    <3>. QED
      BY <3>2, <3>3
  <2>. QED
    BY <2>1, <2>2
<1>. QED
  BY <1>1, <1>4, <1>5, SeqEqual

THEOREM SubSeqFull ==
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  SubSeq(seq, 1, Len(seq)) = seq
OBVIOUS

(*****************************************************************************)
(* Adjacent subsequences can be concatenated to obtain a longer subsequence. *)
(*****************************************************************************)
THEOREM ConcatAdjacentSubSeq ==
  ASSUME NEW S, NEW seq \in Seq(S), 
         NEW m \in 1 .. Len(seq)+1, 
         NEW k \in m-1 .. Len(seq), 
         NEW n \in k .. Len(seq)
  PROVE  SubSeq(seq, m, k) \o SubSeq(seq, k+1, n) = SubSeq(seq, m, n)
<1>. DEFINE lhs == SubSeq(seq, m, k) \o SubSeq(seq, k+1, n)
<1>. /\ SubSeq(seq, m, k) \in Seq(S)
     /\ SubSeq(seq, k+1, n) \in Seq(S)
     /\ SubSeq(seq, m, n) \in Seq(S)
     /\ lhs \in Seq(S)
  OBVIOUS
<1>1. Len(SubSeq(seq, m, k)) = k-m+1
  BY SubSeqProperties
<1>2. Len(SubSeq(seq, k+1,n)) = n-k
  BY k+1 \in 1 .. Len(seq)+1, n \in (k+1)-1 .. Len(seq), n-k = n-(k+1)+1, SubSeqProperties
<1>3. Len(SubSeq(seq, m, n)) = n-m+1
  BY n \in m-1 .. Len(seq), SubSeqProperties
<1>4. Len(lhs) = Len(SubSeq(seq, m, n))
  BY <1>1, <1>2, <1>3
<1>5. ASSUME NEW i \in 1 .. Len(lhs)
      PROVE  lhs[i] = SubSeq(seq, m, n)[i]
  <2>0. 1 .. Len(lhs) = (1 .. k-m+1) \cup (k-m+2 .. n-m+1)
    BY <1>4, <1>3
  <2>1. CASE i \in 1 .. k-m+1
    <3>1. lhs[i] = SubSeq(seq, m, k)[i]
      BY <2>1, <1>1, <1>2, ConcatProperties, i <= Len(SubSeq(seq, m, k))
    <3>2. SubSeq(seq, m, k)[i] = seq[m+i-1]  BY <2>1, SubSeqProperties
    <3>3. SubSeq(seq, m, n)[i] = seq[m+i-1]  BY <2>1, SubSeqProperties
    <3>. QED  BY <3>1, <3>2, <3>3
  <2>2. CASE i \in k-m+2 .. n-m+1
    <3>1. /\ i \in 1 .. Len(SubSeq(seq,m,k)) + Len(SubSeq(seq,k+1,n))
          /\ ~(i <= Len(SubSeq(seq, m, k)))
      BY <1>1, <1>2, <2>2
    <3>2. lhs[i] = SubSeq(seq, k+1, n)[i - Len(SubSeq(seq,m,k))]
      BY <3>1, ConcatProperties
    <3>3. i - Len(SubSeq(seq,m,k)) \in 1 .. n-k
      BY <2>2, <1>1
    <3>4. SubSeq(seq, k+1, n)[i - Len(SubSeq(seq,m,k))] = seq[m+i-1]
      BY <3>3, <1>1, SubSeqProperties
    <3>5. SubSeq(seq, m, n)[i] = seq[m+i-1]
      BY <1>4, <1>3, SubSeqProperties
    <3>. QED  BY <3>2, <3>4, <3>5
  <2>. QED  BY <2>0, <2>1, <2>2
<1>. QED  BY <1>4, <1>5, SeqEqual

(***************************************************************************)
(*                 Append, InsertAt, Cons & RemoveAt                       *)
(* Append(seq, elt) appends element elt at the end of sequence seq         *)
(* Cons(elt, seq) prepends element elt at the beginning of sequence seq    *)
(* InsertAt(seq, i, elt) inserts element elt in the position i and pushes  *)
(* the                                                                     *)
(*                        original element at i to i+1 and so on           *)
(* RemoveAt(seq, i) removes the element at position i                      *)
(***************************************************************************)

THEOREM AppendProperties ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW elt \in S
  PROVE  /\ Append(seq, elt) \in Seq(S)
         /\ Append(seq, elt) # << >>
         /\ Len(Append(seq, elt)) = Len(seq)+1
         /\ \A i \in 1.. Len(seq) : Append(seq, elt)[i] = seq[i]
         /\ Append(seq, elt)[Len(seq)+1] = elt
OBVIOUS

THEOREM AppendIsConcat ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW elt \in S
  PROVE  Append(seq, elt) = seq \o <<elt>>
OBVIOUS

THEOREM HeadTailAppend ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW elt
  PROVE  /\ Head(Append(seq, elt)) = IF seq = <<>> THEN elt ELSE Head(seq)
         /\ Tail(Append(seq, elt)) = IF seq = <<>> THEN <<>> ELSE Append(Tail(seq), elt)
<1>1. CASE seq = <<>>
  <2>1. Append(seq, elt) = <<elt>>  BY <1>1
  <2>. QED BY <1>1, <2>1  
<1>2. CASE seq # <<>>
  <2>1. Head(Append(seq, elt)) = Head(seq)  BY <1>2
  <2>2. Tail(Append(seq, elt)) = Append(Tail(seq), elt)  BY <1>2
  <2>. QED  BY <2>1, <2>2, <1>2
<1>. QED  BY <1>1, <1>2

Cons(elt, seq) == <<elt>> \o seq

THEOREM ConsProperties ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW elt \in S
  PROVE /\ Cons(elt, seq) \in Seq(S)
        /\ Cons(elt, seq) # <<>> 
        /\ Len(Cons(elt, seq)) = Len(seq)+1
        /\ Head(Cons(elt, seq)) = elt
        /\ Tail(Cons(elt, seq)) = seq
        /\ Cons(elt, seq)[1] = elt
        /\ \A i \in 1 .. Len(seq) : Cons(elt, seq)[i+1] = seq[i]
BY DEF Cons

THEOREM ConsEmpty ==
  \A x : Cons(x, << >>) = << x >>
BY DEF Cons

THEOREM ConsHeadTail ==
  ASSUME NEW S, NEW seq \in Seq(S), seq # << >>
  PROVE  Cons(Head(seq), Tail(seq)) = seq
BY DEF Cons

THEOREM ConsAppend ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW x \in S, NEW y \in S
  PROVE  Cons(x, Append(seq, y)) = Append(Cons(x,seq), y)
BY AppendIsConcat DEF Cons

THEOREM ConsInjective ==
  ASSUME NEW S, NEW e \in S, NEW s \in Seq(S), NEW f \in S, NEW t \in Seq(S)
  PROVE  Cons(e,s) = Cons(f,t) <=> e = f /\ s = t
<1>1. SUFFICES ASSUME Cons(e,s) = Cons(f,t) PROVE e=f /\ s=t
  OBVIOUS
<1>2. /\ Head(Cons(e,s)) = Head(Cons(f,t))
      /\ Tail(Cons(e,s)) = Tail(Cons(f,t))
  BY <1>1
<1>. QED  BY ONLY <1>2, ConsProperties, Isa

InsertAt(seq,i,elt) == SubSeq(seq, 1, i-1) \o <<elt>> \o SubSeq(seq, i, Len(seq))

THEOREM InsertAtProperties ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW i \in 1 .. Len(seq)+1, NEW elt \in S
  PROVE  /\ InsertAt(seq,i,elt) \in Seq(S)
         /\ Len(InsertAt(seq,i,elt)) = Len(seq)+1
         /\ \A j \in 1 .. Len(seq)+1 : InsertAt(seq,i,elt)[j] =
                     IF j<i THEN seq[j]
                     ELSE IF j=i THEN elt
                     ELSE seq[j-1]
<1>. DEFINE left == SubSeq(seq, 1, i-1)
            mid  == <<elt>>
            right == SubSeq(seq, i, Len(seq))
<1>1. /\ left \in Seq(S)
      /\ mid \in Seq(S)
      /\ right \in Seq(S)
      /\ InsertAt(seq,i,elt) \in Seq(S)
  BY DEF InsertAt
<1>l. Len(left) = (i-1) - 1 + 1
  BY 1 \in 1 .. (Len(seq)+1), i-1 \in (1-1) .. Len(seq), SubSeqProperties, Zenon
<1>r. Len(right) = Len(seq) - i + 1
  BY Len(seq) \in (i-1) .. Len(seq), SubSeqProperties, Zenon
<1>2. Len(InsertAt(seq,i,elt)) = Len(seq)+1
  BY <1>l, <1>r DEF InsertAt
<1>3. ASSUME NEW j \in 1 .. Len(seq)+1
      PROVE  InsertAt(seq,i,elt)[j] = IF j<i THEN seq[j]
                                      ELSE IF j=i THEN elt
                                      ELSE seq[j-1]
  <2>1. CASE j \in 1 .. i-1
    BY <2>1 DEF InsertAt
  <2>2. CASE j = i
    <3>1. /\ j \in 1 .. Len(left) + Len(mid)
          /\ ~(j <= Len(left))
          /\ <<elt>>[j - Len(left)] = elt
      BY <2>2, <1>l
    <3>2. (left \o mid)[j] = elt
      BY <1>1, <3>1, ConcatProperties
    <3>3. /\ j \in 1 .. (Len(left \o mid) + Len(right))
          /\ j <= Len(left \o mid)
          /\ left \o mid \in Seq(S)
      BY <2>2, <1>l, <1>r
    <3>4. ((left \o mid) \o right)[j] = (left \o mid)[j]
      BY <1>1, <3>3, ConcatProperties DEF InsertAt
    <3>. QED
      BY <3>4, <3>2, <2>2 DEF InsertAt
  <2>3. CASE j \in i+1 .. Len(seq)+1
    <3>1. ~(j < i) /\ j # i
      BY <2>3
    <3>2. /\ j \in 1 .. (Len(left \o mid) + Len(right))
          /\ ~(j <= Len(left \o mid))
          /\ left \o mid \in Seq(S)
      BY <1>l, <1>r, <2>3
    <3>3. ((left \o mid) \o right)[j] = right[j - Len(left \o mid)]
      BY <1>1, <3>2, ConcatProperties
    <3>4. /\ Len(seq) \in i-1 .. Len(seq)
          /\ j - Len(left \o mid) \in 1 .. (Len(seq) - i + 1)
      BY <2>3, <1>l
    <3>5. right[j - Len(left \o mid)] = seq[i + (j - Len(left \o mid)) - 1]
      BY <3>4, SubSeqProperties
    <3>6. right[j - Len(left \o mid)] = seq[j-1]
      BY <3>5, <1>l
    <3>. QED
      BY <3>1, <3>3, <3>6 DEF InsertAt
  <2>. QED
    BY <2>1, <2>2, <2>3
<1>. QED
  BY <1>1, <1>2, <1>3

RemoveAt(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

THEOREM RemoveAtProperties ==
   ASSUME NEW S, NEW seq \in Seq(S),
          NEW i \in 1..Len(seq)
   PROVE  /\ RemoveAt(seq,i) \in Seq(S)
          /\ Len(RemoveAt(seq,i)) = Len(seq) - 1
          /\ \A j \in 1 .. Len(seq)-1 : RemoveAt(seq,i)[j] = IF j<i THEN seq[j] ELSE seq[j+1]
<1>. DEFINE left == SubSeq(seq, 1, i-1)
            right == SubSeq(seq, i+1, Len(seq))
<1>1. Len(left) = i-1
  BY 1 \in 1 .. Len(seq)+1, i-1 \in (1-1) .. Len(seq), (i-1) - 1 + 1 = i-1,
     SubSeqProperties, Zenon
<1>2. Len(right) = Len(seq) - i
  BY i+1 \in 1 .. Len(seq)+1, Len(seq) \in (i+1)-1 .. Len(seq), Len(seq) - (i+1) + 1 = Len(seq)-i,
     SubSeqProperties, Zenon
<1>3. /\ left \in Seq(S)
      /\ right \in Seq(S)
      /\ RemoveAt(seq,i) \in Seq(S)
  BY DEF RemoveAt
<1>4. Len(RemoveAt(seq,i)) = Len(seq) - 1
  BY <1>1, <1>2 DEF RemoveAt
<1>5. ASSUME NEW j \in 1 .. Len(seq)-1
      PROVE  RemoveAt(seq,i)[j] = IF j<i THEN seq[j] ELSE seq[j+1]
  <2>1. CASE j \in 1 .. i-1
    BY <2>1 DEF RemoveAt
  <2>2. CASE j \in i .. Len(seq)-1
    <3>1. /\ j \in 1 .. Len(left) + Len(right)
          /\ ~(j <= Len(left))
      BY <2>2, <1>1, <1>2
    <3>2. RemoveAt(seq,i)[j] = right[j - Len(left)]
      BY <1>3, <3>1, ConcatProperties, Zenon DEF RemoveAt
    <3>3. /\ i+1 \in 1 .. Len(seq)+1
          /\ Len(seq) \in (i+1)-1 .. Len(seq)
          /\ j - (i-1) \in 1 .. Len(seq) - (i+1) + 1
       BY <2>2
    <3>4. right[j - (i-1)] = seq[(i+1) + (j - (i-1)) - 1]
      BY <3>3, SubSeqProperties, Zenon
    <3>. QED
      BY <3>2, <3>4, <2>2, <1>1
  <2>. QED
    BY <2>1, <2>2
<1>. QED
  BY <1>3, <1>4, <1>5

(***************************************************************************)
(*            Front & Last                                                 *)
(*                                                                         *)
(*  Front(seq)   sequence formed by removing the last element              *)
(*  Last(seq)    last element of the sequence                              *)
(*                                                                         *)
(*  These operators are to Append what Head and Tail are to Cons.          *)
(***************************************************************************)

Front(seq) == SubSeq(seq, 1, Len(seq)-1)
Last(seq) == seq[Len(seq)]

THEOREM FrontProperties ==
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  /\ Front(seq) \in Seq(S)
         /\ Len(Front(seq)) = IF seq = << >> THEN 0 ELSE Len(seq)-1                    
         /\ \A i \in 1 .. Len(seq)-1 : Front(seq)[i] = seq[i]
<1>1. CASE seq = << >>
  <2>1. /\ Len(seq) = 0
        /\ Front(seq) = << >>
    BY <1>1 DEF Front
  <2>. QED  BY <2>1
<1>2. CASE seq # << >>
  <2>1. /\ 1 \in 1 .. (Len(seq)+1)
        /\ Len(seq)-1 \in (1-1) .. Len(seq)
    BY <1>2
  <2>2. /\ SubSeq(seq, 1, Len(seq)-1) \in Seq(S)
        /\ Len(SubSeq(seq, 1, Len(seq)-1)) = Len(seq)-1-1+1
        /\ \A i \in 1 .. Len(seq)-1-1+1 : SubSeq(seq,1,Len(seq)-1)[i] = seq[1+i-1]
    BY <2>1, SubSeqProperties, Zenon
  <2>. QED
    BY <1>2, <2>2 DEF Front
<1>. QED  BY <1>1, <1>2

THEOREM FrontOfEmpty == Front(<< >>) = << >>
BY SubSeqEmpty DEF Front

THEOREM LastProperties ==
  ASSUME NEW S, NEW seq \in Seq(S), seq # << >>
  PROVE  /\ Last(seq) \in S 
         /\ Append(Front(seq), Last(seq)) = seq 
<1>1. Last(seq) \in S
  BY DEF Last
<1>2. Append(Front(seq), Last(seq)) = seq
  <2>1. /\ 1 \in 1 .. Len(seq)
        /\ Len(seq) \in 1 .. Len(seq)
    OBVIOUS
  <2>2. Front(seq) \o << Last(seq) >> = SubSeq(seq, 1, Len(seq))
    BY <2>1, SubSeqRecursiveSecond, Zenon DEF Front, Last
  <2>. QED   BY <2>2
<1>. QED  BY <1>1, <1>2

THEOREM FrontLastOfSubSeq ==
  ASSUME NEW S, NEW seq \in Seq(S),
         NEW m \in 1 .. Len(seq), NEW n \in m .. Len(seq)
  PROVE  /\ Front(SubSeq(seq,m,n)) = SubSeq(seq, m, n-1)
         /\ Last(SubSeq(seq,m,n)) = seq[n]
BY DEF Front, Last

THEOREM FrontLastAppend ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW e \in S
  PROVE  /\ Front(Append(seq, e)) = seq
         /\ Last(Append(seq, e)) = e
BY DEF Front, Last

THEOREM AppendInjective ==
  ASSUME NEW S, NEW e \in S, NEW s \in Seq(S), NEW f \in S, NEW t \in Seq(S)
  PROVE  Append(s,e) = Append(t,f) <=> s = t /\ e = f
<1>1. SUFFICES ASSUME Append(s,e) = Append(t,f) PROVE s=t /\ e=f
  OBVIOUS
<1>2. /\ Front(Append(s,e)) = Front(Append(t,f))
      /\ Last(Append(s,e)) = Last(Append(t,f))
  BY <1>1
<1>. QED
  BY ONLY <1>2, FrontLastAppend

(***************************************************************************)
(* As a corollary of the previous theorems it follows that a sequence is   *)
(* either empty or can be obtained by appending an element to a sequence.  *)
(***************************************************************************)
THEOREM SequenceEmptyOrAppend == 
  ASSUME NEW S, NEW seq \in Seq(S), seq # << >>
  PROVE \E s \in Seq(S), elt \in S : seq = Append(s, elt)
BY FrontProperties, LastProperties
     
(***************************************************************************)
(*                   REVERSE SEQUENCE And Properties                       *)
(*    Reverse(seq) --> Reverses the sequence seq                           *)
(***************************************************************************)

Reverse(seq) == [j \in 1 .. Len(seq) |-> seq[Len(seq)-j+1] ]

THEOREM ReverseProperties ==
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  /\ Reverse(seq) \in Seq(S)
         /\ Len(Reverse(seq)) = Len(seq)
         /\ Reverse(Reverse(seq)) = seq
BY DEF Reverse

THEOREM ReverseEmpty == Reverse(<< >>) = << >>
BY DEF Reverse

THEOREM ReverseEqual ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), Reverse(s) = Reverse(t)
  PROVE  s = t
<1>1. Len(s) = Len(t)  BY DEF Reverse
<1>2. ASSUME NEW i \in 1 .. Len(s)
      PROVE  s[i] = t[i]
  <2>1. Reverse(s)[Len(s)-i+1] = Reverse(t)[Len(s)-i+1]  OBVIOUS
  <2>. QED  BY <2>1 DEF Reverse
<1>. QED  BY <1>1, <1>2, SeqEqual

THEOREM ReverseEmptyIffEmpty ==
  ASSUME NEW S, NEW seq \in Seq(S), Reverse(seq) = <<>>
  PROVE  seq = <<>>
BY <<>> \in Seq(S), ReverseEmpty, ReverseEqual, Zenon

THEOREM ReverseConcat == 
  ASSUME NEW S, NEW s1 \in Seq(S), NEW s2 \in Seq(S)
  PROVE  Reverse(s1 \o s2) = Reverse(s2) \o Reverse(s1)
BY DEF Reverse

THEOREM ReverseAppend ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW e \in S
  PROVE  Reverse(Append(seq,e)) = Cons(e, Reverse(seq))
BY DEF Reverse, Cons

THEOREM ReverseCons ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW e \in S
  PROVE  Reverse(Cons(e,seq)) = Append(Reverse(seq), e)
BY DEF Reverse, Cons

THEOREM ReverseSingleton == \A x : Reverse(<< x >>) = << x >>
BY DEF Reverse

THEOREM ReverseSubSeq ==
  ASSUME NEW S, NEW seq \in Seq(S),
         NEW m \in 1..Len(seq), NEW n \in 1..Len(seq)
  PROVE  Reverse(SubSeq(seq, m , n)) = SubSeq(Reverse(seq), Len(seq)-n+1, Len(seq)-m+1)
BY DEF Reverse

THEOREM ReversePalindrome ==
  ASSUME NEW S, NEW seq \in Seq(S),
         Reverse(seq) = seq
  PROVE  Reverse(seq \o seq) = seq \o seq
BY ReverseConcat, Zenon

THEOREM LastEqualsHeadReverse ==
  ASSUME NEW S, NEW seq \in Seq(S), seq # << >>
  PROVE  Last(seq) = Head(Reverse(seq))
BY DEF Last, Reverse

THEOREM ReverseFrontEqualsTailReverse ==
  ASSUME NEW S, NEW seq \in Seq(S), seq # << >>
  PROVE  Reverse(Front(seq)) = Tail(Reverse(seq))
<1>. DEFINE lhs == Reverse(Front(seq))
            rhs == Tail(Reverse(seq))
<1>1. /\ lhs \in Seq(S)
      /\ rhs \in Seq(S)
      /\ Len(lhs) = Len(seq) - 1
      /\ Len(rhs) = Len(seq) - 1
  BY FrontProperties, ReverseProperties
<1>3. ASSUME NEW i \in 1 .. Len(seq)-1
      PROVE  lhs[i] = rhs[i]
  <2>1. /\ Len(Front(seq)) = Len(seq)-1
        /\ i \in 1 .. Len(Front(seq))
    BY FrontProperties
  <2>2. lhs[i] = Front(seq)[Len(seq)-i]
    BY <2>1 DEF Reverse
  <2>4. Front(seq)[Len(seq)-i] = seq[Len(seq)-i]
    BY FrontProperties
  <2>5. rhs[i] = seq[Len(seq)-i]
    BY DEF Reverse
  <2>. QED
    BY <2>2, <2>4, <2>5
<1>. QED
  BY <1>1, <1>3, SeqEqual


(***************************************************************************)
(* Induction principles for sequences                                      *)
(***************************************************************************)

THEOREM SequencesInductionAppend ==
  ASSUME NEW P(_), NEW S, 
         P(<< >>),
         \A s \in Seq(S), e \in S : P(s) => P(Append(s,e))
  PROVE  \A seq \in Seq(S) : P(seq)
<1>. DEFINE Q(n) == \A seq \in Seq(S) : Len(seq) = n => P(seq)
<1>1. SUFFICES \A k \in Nat : Q(k)
  OBVIOUS
<1>2. Q(0)
  OBVIOUS
<1>3. ASSUME NEW n \in Nat, Q(n)
      PROVE  Q(n+1)
  <2>1. ASSUME NEW s \in Seq(S), Len(s) = n+1
        PROVE P(s)
    <3>1. /\ Front(s) \in Seq(S)
          /\ Last(s) \in S
          /\ Len(Front(s)) = n
          /\ Append(Front(s), Last(s)) = s
      BY <2>1, FrontProperties, LastProperties 
    <3>2. P(Front(s))
      BY <1>3, <3>1
    <3>3. QED
      BY <3>1, <3>2, Zenon                  
  <2>. QED
    BY <2>1          
<1>4. QED
  BY <1>2, <1>3, NatInduction, Isa
      
THEOREM SequencesInductionCons == 
  ASSUME NEW P(_), NEW S,
         P(<< >>),
         \A s \in Seq(S), e \in S : P(s) => P(Cons(e,s))
  PROVE \A seq \in Seq(S) : P(seq)
<1>. DEFINE Q(n) == \A seq \in Seq(S) : Len(seq) = n => P(seq)
<1>1. SUFFICES \A k \in Nat : Q(k)
  OBVIOUS
<1>2. Q(0)
  OBVIOUS
<1>3. ASSUME NEW n \in Nat, Q(n)
      PROVE  Q(n+1)
  <2>1. ASSUME NEW s \in Seq(S), Len(s) = n+1
        PROVE P(s)
    <3>1. /\ Tail(s) \in Seq(S)
          /\ Head(s) \in S
          /\ Len(Tail(s)) = n
          /\ Cons(Head(s), Tail(s)) = s
      BY <2>1, ConsHeadTail 
    <3>2. P(Tail(s))
      BY <1>3, <3>1, Zenon
    <3>3. QED
      BY <3>1, <3>2, Zenon                  
  <2>. QED
    BY <2>1          
<1>4. QED
  BY <1>2, <1>3, NatInduction, Isa

(***************************************************************************)
(*                          RANGE OF SEQUENCE                              *)
(***************************************************************************)

THEOREM RangeOfSeq == 
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  Range(seq) \in SUBSET S
BY DEF Range

THEOREM RangeEquality == 
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE Range(seq) = { seq[i] : i \in 1 .. Len(seq) }
<1>1. DOMAIN seq = 1 .. Len(seq)
  OBVIOUS
<1>2. QED
  BY <1>1, Zenon DEF Range

(* The range of the reverse sequence equals that of the original one. *)
THEOREM RangeReverse == 
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE Range(Reverse(seq)) = Range(seq)
<1>1. Range(Reverse(seq)) \subseteq Range(seq)
  BY RangeEquality DEF Reverse
<1>2. Range(seq) \subseteq Range(Reverse(seq))
  BY RangeEquality DEF Reverse
<1>3. QED
  BY <1>1, <1>2, Zenon

(* Range of concatenation of sequences is the union of the ranges *)
THEOREM RangeConcatenation == 
  ASSUME NEW S, NEW s1 \in Seq(S), NEW s2 \in Seq(S)
  PROVE  Range(s1 \o s2) = Range(s1) \cup Range(s2)
<1>1. Range(s1) \subseteq Range(s1 \o s2)
  BY DEF Range
<1>2. Range(s2) \subseteq Range(s1 \o s2)
  <2>1. SUFFICES ASSUME NEW i \in 1 .. Len(s2)
                 PROVE  s2[i] \in Range(s1 \o s2)
    BY RangeEquality
  <2>2. /\ Len(s1)+i \in 1 .. Len(s1 \o s2)
        /\ (s1 \o s2)[Len(s1)+i] = s2[i]
    OBVIOUS
  <2>. QED
    BY <2>2, RangeEquality
<1>3. Range(s1 \o s2) \subseteq Range(s1) \cup Range(s2)
  <2>1. SUFFICES ASSUME NEW i \in 1 .. Len(s1 \o s2)
                 PROVE  (s1 \o s2)[i] \in Range(s1) \cup Range(s2)
    BY LenProperties, ConcatProperties, Zenon DEF Range
  <2>2. CASE i \in 1 .. Len(s1)
    BY RangeEquality
  <2>3. CASE i \in Len(s1)+1 .. Len(s1 \o s2)
    BY RangeEquality
  <2>. QED
    BY <2>2, <2>3
<1>. QED
  BY <1>1, <1>2, <1>3, Zenon

(***************************************************************************)
(* Prefixes and suffixes of sequences.                                     *)
(***************************************************************************)

IsPrefix(s,t) == \E u \in Seq(Range(t)) : t = s \o u
IsStrictPrefix(s,t) == IsPrefix(s,t) /\ s # t

IsSuffix(s,t) == \E u \in Seq(Range(t)) : t = u \o s
IsStrictSuffix(s,t) == IsSuffix(s,t) /\ s # t

(***************************************************************************)
(* The following theorem gives three alternative characterizations of      *)
(* prefixes. It also implies that any prefix of a sequence t is at most    *)
(* as long as t.                                                           *)
(***************************************************************************)
THEOREM IsPrefixProperties ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  /\ IsPrefix(s,t) <=> \E u \in Seq(S) : t = s \o u
         /\ IsPrefix(s,t) <=> Len(s) <= Len(t) /\ s = SubSeq(t, 1, Len(s))
         /\ IsPrefix(s,t) <=> Len(s) <= Len(t) /\ s = Restrict(t, DOMAIN s)
<1>1. ASSUME IsPrefix(s,t) PROVE Len(s) <= Len(t)
  BY <1>1 DEF IsPrefix
<1>2. IsPrefix(s,t) <=> \E u \in Seq(S) : t = s \o u
  <2>1. ASSUME NEW u \in Seq(Range(t)), t = s \o u
        PROVE  u \in Seq(S)
    BY DEF Range
  <2>2. ASSUME NEW u \in Seq(S), t = s \o u
        PROVE  u \in Seq(Range(t))
    <3>1. \A i \in 1 .. Len(u) : u[i] \in Range(u)
      BY DOMAIN u = 1 .. Len(u) DEF Range
    <3>2. \A i \in 1 .. Len(u) : u[i] \in Range(t)
      BY <2>2, <3>1, RangeConcatenation
    <3>. QED  BY <3>2
  <2>. QED  BY <2>1, <2>2 DEF IsPrefix
<1>3. IsPrefix(s,t) <=> Len(s) <= Len(t) /\ s = SubSeq(t, 1, Len(s))
  <2>1. ASSUME IsPrefix(s,t) 
        PROVE Len(s) <= Len(t) /\ s = SubSeq(t, 1, Len(s))
    <3>1. Len(s) <= Len(t)  BY <2>1, <1>1
    <3>2. /\ 1 \in 1 .. Len(t)+1
          /\ Len(s) \in 1-1 .. Len(t)
          /\ Len(s) = Len(s) - 1 + 1
      BY <3>1
    <3>3. Len(s) = Len(SubSeq(t, 1, Len(s)))
      BY <3>2, SubSeqProperties, Zenon
    <3>4. ASSUME NEW i \in 1 .. Len(s)
          PROVE  s[i] = SubSeq(t, 1, Len(s))[i]
      BY <3>2, <2>1, SubSeqProperties DEF IsPrefix
    <3>. QED  BY <3>1, <3>3, <3>4, SeqEqual
  <2>2. ASSUME Len(s) <= Len(t), s = SubSeq(t, 1, Len(s))
        PROVE IsPrefix(s,t)
    <3>1. /\ 1 \in 1 .. Len(t)+1
          /\ Len(s) \in 1-1 .. Len(t)
          /\ Len(t) \in Len(s) .. Len(t)
      BY <2>2
    <3>2. t = s \o SubSeq(t, Len(s)+1, Len(t))
      BY <2>2, <3>1, ConcatAdjacentSubSeq, SubSeqFull, Zenon
    <3>3. SubSeq(t, Len(s)+1, Len(t)) \in Seq(S)  OBVIOUS
    <3>. QED  BY <3>2, <3>3, <1>2
  <2>. QED  BY <2>1, <2>2
<1>4. IsPrefix(s,t) <=> Len(s) <= Len(t) /\ s = Restrict(t, DOMAIN s)
  <2>1. /\ DOMAIN s = 1 .. Len(s)
        /\ Len(s) <= Len(t) <=> Len(s) \in 0 .. Len(t)
    OBVIOUS
  <2>. QED
    BY <1>3, <2>1, SubSeqRestrict, Zenon
<1>. QED  BY <1>2, <1>3, <1>4

THEOREM IsStrictPrefixProperties ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  /\ IsStrictPrefix(s,t) <=> \E u \in Seq(S) : u # << >> /\ t = s \o u
         /\ IsStrictPrefix(s,t) <=> Len(s) < Len(t) /\ s = SubSeq(t, 1, Len(s))
         /\ IsStrictPrefix(s,t) <=> Len(s) < Len(t) /\ s = Restrict(t, DOMAIN s)
         /\ IsStrictPrefix(s,t) <=> IsPrefix(s,t) /\ Len(s) < Len(t)
BY IsPrefixProperties DEF IsStrictPrefix

THEOREM IsPrefixElts ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), NEW i \in 1 .. Len(s),
         IsPrefix(s,t)
  PROVE  s[i] = t[i]
BY IsPrefixProperties

THEOREM EmptyIsPrefix ==
  ASSUME NEW S, NEW s \in Seq(S)
  PROVE  /\ IsPrefix(<<>>, s)
         /\ IsPrefix(s, <<>>) <=> s = <<>>
         /\ IsStrictPrefix(<<>>, s) <=> s # <<>>
         /\ ~ IsStrictPrefix(s, <<>>)
BY IsPrefixProperties, IsStrictPrefixProperties

THEOREM IsPrefixConcat ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  IsPrefix(s, s \o t)
BY IsPrefixProperties, ConcatProperties, Zenon

THEOREM IsPrefixAppend ==
  ASSUME NEW S, NEW s \in Seq(S), NEW e \in S
  PROVE  IsPrefix(s, Append(s,e))
<1>1. /\ <<e>> \in Seq(S)
      /\ Append(s,e) = s \o <<e>>
  OBVIOUS
<1>. QED  BY <1>1, IsPrefixConcat, Zenon

THEOREM FrontIsPrefix ==
  ASSUME NEW S, NEW s \in Seq(S)
  PROVE  /\ IsPrefix(Front(s), s)
         /\ s # <<>> => IsStrictPrefix(Front(s), s)
<1>1. CASE s = << >>
  BY <1>1, FrontOfEmpty, EmptyIsPrefix
<1>2. CASE s # << >>
  BY <1>2, IsPrefixProperties, FrontProperties DEF Front, IsStrictPrefix
<1>. QED  BY <1>1, <1>2

(***************************************************************************)
(* (Strict) prefixes on sequences form a (strict) partial order, and       *)
(* the strict ordering is well-founded.                                    *)
(***************************************************************************)
THEOREM IsPrefixPartialOrder ==
  ASSUME NEW S
  PROVE  /\ \A s \in Seq(S) : IsPrefix(s,s)
         /\ \A s,t \in Seq(S) : IsPrefix(s,t) /\ IsPrefix(t,s) => s = t
         /\ \A s,t,u \in Seq(S) : IsPrefix(s,t) /\ IsPrefix(t,u) => IsPrefix(s,u)
BY IsPrefixProperties

THEOREM ConcatIsPrefix ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), NEW u \in Seq(S),
         IsPrefix(s \o t, u)
  PROVE  IsPrefix(s, u)
<1>1. /\ s \o t \in Seq(S)
      /\ IsPrefix(s, s \o t)
  BY IsPrefixConcat
<1>. QED  BY <1>1, IsPrefixPartialOrder, Zenon

THEOREM ConcatIsPrefixCancel ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), NEW u \in Seq(S)
  PROVE  IsPrefix(s \o t, s \o u) <=> IsPrefix(t, u)
<1>1. ASSUME IsPrefix(t,u) PROVE IsPrefix(s \o t, s \o u)
  <2>1. PICK v \in Seq(S) : u = t \o v  BY <1>1, IsPrefixProperties
  <2>2. s \o u = (s \o t) \o v  BY <2>1
  <2>. QED  BY s \o t \in Seq(S), s \o u \in Seq(S), <2>2, IsPrefixProperties, Zenon
<1>2. ASSUME IsPrefix(s \o t, s \o u) PROVE IsPrefix(t,u)
  <2>1. PICK v \in Seq(S) : s \o u = (s \o t) \o v
    BY <1>2, s \o t \in Seq(S), s \o u \in Seq(S), IsPrefixProperties, Isa
  <2>2. s \o u = s \o (t \o v)
    BY <2>1
  <2>3. u = t \o v
    BY t \o v \in Seq(S), <2>2, ConcatSimplifications, IsaM("blast")
  <2>. QED  BY <2>3, IsPrefixProperties, Zenon
<1>. QED  BY <1>1, <1>2

THEOREM ConsIsPrefixCancel ==
  ASSUME NEW S, NEW e \in S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  IsPrefix(Cons(e,s), Cons(e,t)) <=> IsPrefix(s,t)
BY <<e>> \in Seq(S), ConcatIsPrefixCancel, Zenon DEF Cons

THEOREM ConsIsPrefix ==
  ASSUME NEW S, NEW e \in S, NEW s \in Seq(S), NEW u \in Seq(S),
         IsPrefix(Cons(e,s), u)
  PROVE  /\ e = Head(u)
         /\ IsPrefix(s, Tail(u))
<1>. <<e>> \in Seq(S)
  OBVIOUS
<1>1. IsPrefix(<<e>>, u)
  BY ConcatIsPrefix, Zenon DEF Cons
<1>2. PICK v \in Seq(S) : u = Cons(e, v)
  BY <1>1, IsPrefixProperties, Isa DEF Cons
<1>3. /\ e = Head(u)
      /\ v = Tail(u)
      /\ IsPrefix(Cons(e,s), Cons(e, Tail(u)))
  BY <1>2, ConsProperties, Isa
<1>. QED
  BY <1>3, ConsIsPrefixCancel, Zenon

THEOREM IsStrictPrefixStrictPartialOrder ==
  ASSUME NEW S
  PROVE  /\ \A s \in Seq(S) : ~ IsStrictPrefix(s,s)
         /\ \A s,t \in Seq(S) : IsStrictPrefix(s,t) => ~ IsStrictPrefix(t,s)
         /\ \A s,t,u \in Seq(S) : IsStrictPrefix(s,t) /\ IsStrictPrefix(t,u) => IsStrictPrefix(s,u)
BY IsStrictPrefixProperties

THEOREM IsStrictPrefixWellFounded ==
  ASSUME NEW S
  PROVE  IsWellFoundedOn(OpToRel(IsStrictPrefix, Seq(S)), Seq(S))
<1>1. IsWellFoundedOn(PreImage(Len, Seq(S), OpToRel(<, Nat)), Seq(S))
  BY NatLessThanWellFounded, PreImageWellFounded, \A s \in Seq(S) : Len(s) \in Nat, Blast
<1>2. OpToRel(IsStrictPrefix, Seq(S)) \subseteq PreImage(Len, Seq(S), OpToRel(<, Nat))
  BY IsStrictPrefixProperties DEF PreImage, OpToRel
<1>. QED
  BY <1>1, <1>2, IsWellFoundedOnSubrelation, Zenon

THEOREM SeqStrictPrefixInduction ==
  ASSUME NEW P(_), NEW S,
         \A t \in Seq(S) : (\A s \in Seq(S) : IsStrictPrefix(s,t) => P(s)) => P(t)
  PROVE  \A s \in Seq(S) : P(s)
<1>1. \A t \in Seq(S) : 
         (\A s \in SetLessThan(t, OpToRel(IsStrictPrefix, Seq(S)), Seq(S)) : P(s))
         => P(t)
  BY DEF SetLessThan, OpToRel
<1>. QED  BY WFInduction, IsStrictPrefixWellFounded, <1>1, Blast

(***************************************************************************)
(* Similar theorems about suffixes.                                        *)
(***************************************************************************)

THEOREM IsSuffixProperties ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  /\ IsSuffix(s,t) <=> \E u \in Seq(S) : t = u \o s
         /\ IsSuffix(s,t) <=> Len(s) <= Len(t) /\ s = SubSeq(t, Len(t)-Len(s)+1, Len(t))
         /\ IsSuffix(s,t) <=> IsPrefix(Reverse(s), Reverse(t))
<1>1. IsSuffix(s,t) <=> \E u \in Seq(S) : t = u \o s
  <2>1. ASSUME NEW u \in Seq(Range(t)), t = u \o s
        PROVE  u \in Seq(S)
    BY DEF Range
  <2>2. ASSUME NEW u \in Seq(S), t = u \o s
        PROVE  u \in Seq(Range(t))
    <3>1. \A i \in 1 .. Len(u) : u[i] \in Range(u)
      BY DOMAIN u = 1 .. Len(u) DEF Range
    <3>2. \A i \in 1 .. Len(u) : u[i] \in Range(t)
      BY <2>2, <3>1, RangeConcatenation
    <3>. QED  BY <3>2
  <2>. QED  BY <2>1, <2>2 DEF IsSuffix
<1>2. IsSuffix(s,t) <=> Len(s) <= Len(t) /\ s = SubSeq(t, Len(t)-Len(s)+1, Len(t))
  <2>1. ASSUME IsSuffix(s,t)
        PROVE  Len(s) <= Len(t) /\ s = SubSeq(t, Len(t)-Len(s)+1, Len(t))
    <3>1. Len(s) <= Len(t)
      BY <2>1 DEF IsSuffix
    <3>2. /\ Len(t) - Len(s) + 1 \in 1 .. Len(t)+1
          /\ Len(t) \in (Len(t) - Len(s) + 1) - 1 .. Len(t)
          /\ Len(t) - (Len(t) - Len(s) + 1) + 1 = Len(s)
      BY <3>1
    <3>3. Len(s) = Len(SubSeq(t, Len(t)-Len(s)+1, Len(t)))
      BY <3>2, SubSeqProperties, Zenon
    <3>4. ASSUME NEW i \in 1 .. Len(s)
          PROVE  s[i] = SubSeq(t, Len(t)-Len(s)+1, Len(t))[i]
      BY <3>2, <2>1, SubSeqProperties DEF IsSuffix
    <3>. QED  BY <3>1, <3>3, <3>4, SeqEqual
  <2>2. ASSUME Len(s) <= Len(t), s = SubSeq(t, Len(t)-Len(s)+1, Len(t))
        PROVE  IsSuffix(s,t)
    <3>1. /\ 1 \in 1 .. Len(t)+1
          /\ Len(t)-Len(s) \in 1-1 .. Len(t)
          /\ Len(t) \in Len(t)-Len(s) .. Len(t)
      BY <2>2
    <3>2. t = SubSeq(t, 1, Len(t) - Len(s)) \o s
      BY <2>2, <3>1, ConcatAdjacentSubSeq, SubSeqFull, Zenon
    <3>3. SubSeq(t, 1, Len(t) - Len(s)) \in Seq(S)  OBVIOUS
    <3>. QED  BY <3>2, <3>3, <1>1
  <2>. QED  BY <2>1, <2>2
<1>3. IsSuffix(s,t) <=> IsPrefix(Reverse(s), Reverse(t))
  <2>. /\ Reverse(s) \in Seq(S)
       /\ Reverse(t) \in Seq(S)
    BY ReverseProperties
  <2>1. ASSUME IsSuffix(s,t)
        PROVE  IsPrefix(Reverse(s), Reverse(t))
    <3>1. PICK u \in Seq(S) : t = u \o s
      BY <2>1, <1>1
    <3>2. /\ Reverse(u) \in Seq(S)
          /\ Reverse(t) = Reverse(s) \o Reverse(u)
      BY <3>1, ReverseProperties, ReverseConcat, Zenon
    <3>. QED  BY <3>2, IsPrefixProperties, Zenon
  <2>2. ASSUME IsPrefix(Reverse(s), Reverse(t))
        PROVE  IsSuffix(s,t)
    <3>1. PICK u \in Seq(S) : Reverse(t) = Reverse(s) \o u
      BY <2>2, IsPrefixProperties
    <3>2. /\ Reverse(u) \in Seq(S)
          /\ Reverse(Reverse(t)) = Reverse(u) \o Reverse(Reverse(s))
      BY <3>1, ReverseProperties, ReverseConcat, Zenon
    <3>. QED  BY <3>2, <1>1, ReverseProperties, Zenon
  <2>. QED  BY <2>1, <2>2
<1>. QED  BY <1>1, <1>2, <1>3

THEOREM IsStrictSuffixProperties ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  /\ IsStrictSuffix(s,t) <=> \E u \in Seq(S) : u # << >> /\ t = u \o s
         /\ IsStrictSuffix(s,t) <=> Len(s) < Len(t) /\ IsSuffix(s,t)
         /\ IsStrictSuffix(s,t) <=> Len(s) < Len(t) /\ s = SubSeq(t, Len(t)-Len(s)+1, Len(t))
         /\ IsStrictSuffix(s,t) <=> IsStrictPrefix(Reverse(s), Reverse(t))
<1>1. ASSUME IsStrictSuffix(s,t)
      PROVE  /\ \E u \in Seq(S) : u # << >> /\ t = u \o s
             /\ Len(s) < Len(t)
             /\ IsSuffix(s,t)
             /\ s = SubSeq(t, Len(t)-Len(s)+1, Len(t))
             /\ IsStrictPrefix(Reverse(s), Reverse(t))
  <2>1. IsSuffix(s,t) /\ s # t
    BY <1>1 DEF IsStrictSuffix
  <2>2. PICK u \in Seq(S) : t = u \o s
    BY <2>1, IsSuffixProperties
  <2>3. u # << >>
    BY <2>2, <1>1 DEF IsStrictSuffix
  <2>4. Len(s) < Len(t)
    BY <2>2, <2>3
  <2>5. s = SubSeq(t, Len(t)-Len(s)+1, Len(t))
    BY <2>1, IsSuffixProperties
  <2>6. IsStrictPrefix(Reverse(s), Reverse(t))
    BY <2>1, IsSuffixProperties, ReverseEqual DEF IsStrictPrefix
  <2>. QED  BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6
<1>2. ASSUME NEW u \in Seq(S), u # << >>, t = u \o s
      PROVE  IsStrictSuffix(s,t)
  <2>1. IsSuffix(s,t)  BY <1>2, IsSuffixProperties, Zenon
  <2>2. s # t  BY <1>2
  <2>. QED  BY <2>1, <2>2 DEF IsStrictSuffix 
<1>3. ASSUME Len(s) < Len(t), IsSuffix(s,t)
      PROVE  IsStrictSuffix(s,t)
  BY <1>3, IsSuffixProperties DEF IsStrictSuffix
<1>4. ASSUME Len(s) < Len(t), s = SubSeq(t, Len(t)-Len(s)+1, Len(t))
      PROVE  IsStrictSuffix(s,t)
  BY <1>4, IsSuffixProperties DEF IsStrictSuffix
<1>5. ASSUME IsStrictPrefix(Reverse(s), Reverse(t))
      PROVE  IsStrictSuffix(s,t)
  BY <1>5, IsSuffixProperties DEF IsStrictPrefix, IsStrictSuffix
<1>. QED  BY <1>1, <1>2, <1>3, <1>4, <1>5

THEOREM IsSuffixElts ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), NEW i \in 1 .. Len(s),
         IsSuffix(s,t)
  PROVE  s[i] = t[Len(t) - Len(s) + i]
BY IsSuffixProperties

THEOREM EmptyIsSuffix ==
  ASSUME NEW S, NEW s \in Seq(S)
  PROVE  /\ IsSuffix(<<>>, s)
         /\ IsSuffix(s, <<>>) <=> s = <<>>
         /\ IsStrictSuffix(<<>>, s) <=> s # <<>>
         /\ ~ IsStrictSuffix(s, <<>>)
BY IsSuffixProperties, IsStrictSuffixProperties

THEOREM IsSuffixConcat ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  IsSuffix(s, t \o s)
BY IsSuffixProperties, ConcatProperties, Zenon

THEOREM IsStrictSuffixCons ==
  ASSUME NEW S, NEW s \in Seq(S), NEW e \in S
  PROVE  IsStrictSuffix(s, Cons(e,s))
BY IsStrictSuffixProperties DEF Cons

THEOREM TailIsSuffix ==
  ASSUME NEW S, NEW s \in Seq(S)
  PROVE  /\ IsSuffix(Tail(s), s)
         /\ s # <<>> => IsStrictSuffix(Tail(s), s)
<1>1. CASE s = <<>>
  BY <1>1, Tail(<<>>) = <<>>, EmptyIsSuffix
<1>2. CASE s # <<>>
  <2>. Head(s) \in S /\ Tail(s) \in Seq(S)
    BY <1>2
  <2>1. IsStrictSuffix(Tail(s), Cons(Head(s), Tail(s)))
    BY IsStrictSuffixCons, Zenon
  <2>. QED  BY <1>2, <2>1, ConsHeadTail DEF IsStrictSuffix
<1>. QED  BY <1>1, <1>2

THEOREM IsSuffixPartialOrder ==
  ASSUME NEW S
  PROVE  /\ \A s \in Seq(S) : IsSuffix(s,s)
         /\ \A s,t \in Seq(S) : IsSuffix(s,t) /\ IsSuffix(t,s) => s = t
         /\ \A s,t,u \in Seq(S) : IsSuffix(s,t) /\ IsSuffix(t,u) => IsSuffix(s,u)
<1>1. ASSUME NEW s \in Seq(S) PROVE IsSuffix(s,s)
  BY IsSuffixProperties
<1>2. ASSUME NEW s \in Seq(S), NEW t \in Seq(S), IsSuffix(s,t), IsSuffix(t,s)
      PROVE  s = t
  <2>1. PICK v \in Seq(S) : t = v \o s
    BY <1>2, IsSuffixProperties
  <2>2. PICK w \in Seq(S) : s = w \o t
    BY <1>2, IsSuffixProperties
  <2>3. /\ v \o w \in Seq(S)
        /\ (v \o w) \o t = t
    BY <2>1, <2>2
  <2>. QED  BY <2>2, <2>3
<1>3. ASSUME NEW s \in Seq(S), NEW t \in Seq(S), NEW u \in Seq(S),
             IsSuffix(s,t), IsSuffix(t,u)
      PROVE  IsSuffix(s,u)
  <2>1. PICK v \in Seq(S) : t = v \o s
    BY <1>3, IsSuffixProperties
  <2>2. PICK w \in Seq(S) : u = w \o t
    BY <1>3, IsSuffixProperties
  <2>3. /\ w \o v \in Seq(S)
        /\ u = (w \o v) \o s
    BY <2>1, <2>2
  <2>. QED  BY <2>3, IsSuffixProperties, Zenon
<1>. QED  BY <1>1, <1>2, <1>3

THEOREM ConcatIsSuffix ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), NEW u \in Seq(S),
         IsSuffix(s \o t, u)
  PROVE  IsSuffix(t, u)
<1>1. /\ s \o t \in Seq(S)
      /\ IsSuffix(t, s \o t)
  BY IsSuffixConcat
<1>. QED  BY <1>1, IsSuffixPartialOrder, Zenon

THEOREM ConcatIsSuffixCancel ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), NEW u \in Seq(S)
  PROVE  IsSuffix(s \o t, u \o t) <=> IsSuffix(s, u)
<1>1. ASSUME IsSuffix(s, u) PROVE IsSuffix(s \o t, u \o t)
  <2>1. PICK v \in Seq(S) : u = v \o s  BY <1>1, IsSuffixProperties
  <2>2. u \o t = v \o (s \o t)  BY <2>1
  <2>. QED  BY s \o t \in Seq(S), u \o t \in Seq(S), <2>2, IsSuffixProperties, ZenonT(20)
<1>2. ASSUME IsSuffix(s \o t, u \o t) PROVE IsSuffix(s, u)
  <2>1. PICK v \in Seq(S) : u \o t = v \o (s \o t)
    BY <1>2, s \o t \in Seq(S), u \o t \in Seq(S), IsSuffixProperties, Isa
  <2>2. u \o t = (v \o s) \o t
    BY <2>1
  <2>3. u = v \o s
    BY v \o s \in Seq(S), <2>2, ConcatSimplifications
  <2>. QED  BY <2>3, IsSuffixProperties, Zenon
<1>. QED  BY <1>1, <1>2

THEOREM AppendIsSuffixCancel ==
  ASSUME NEW S, NEW e \in S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  IsSuffix(Append(s,e), Append(t,e)) <=> IsSuffix(s,t)
BY <<e>> \in Seq(S), ConcatIsSuffixCancel, AppendIsConcat, Isa

THEOREM AppendIsSuffix ==
  ASSUME NEW S, NEW e \in S, NEW s \in Seq(S), NEW u \in Seq(S),
         IsSuffix(Append(s,e), u)
  PROVE  /\ e = Last(u)
         /\ IsSuffix(s, Front(u))
<1>. <<e>> \in Seq(S)
  OBVIOUS
<1>1. IsSuffix(<<e>>, u)
  BY ConcatIsSuffix, AppendIsConcat, Isa
<1>2. PICK v \in Seq(S) : u = Append(v,e)
  BY <1>1, IsSuffixProperties, AppendIsConcat, Isa
<1>3. /\ e = Last(u)
      /\ v = Front(u)
      /\ IsSuffix(Append(s,e), Append(Front(u),e))
  BY <1>2, FrontLastAppend
<1>. QED
  BY <1>3, AppendIsSuffixCancel, Zenon

THEOREM IsStrictSuffixStrictPartialOrder ==
  ASSUME NEW S
  PROVE  /\ \A s \in Seq(S) : ~ IsStrictSuffix(s,s)
         /\ \A s,t \in Seq(S) : IsStrictSuffix(s,t) => ~ IsStrictSuffix(t,s)
         /\ \A s,t,u \in Seq(S) : IsStrictSuffix(s,t) /\ IsStrictSuffix(t,u) => IsStrictSuffix(s,u)
<1>1. ASSUME NEW s \in Seq(S) PROVE ~ IsStrictSuffix(s,s)
  BY DEF IsStrictSuffix
<1>2. ASSUME NEW s \in Seq(S), NEW t \in Seq(S), IsStrictSuffix(s,t)
      PROVE  ~ IsStrictSuffix(t,s)
  BY <1>2, IsSuffixPartialOrder DEF IsStrictSuffix
<1>3. ASSUME NEW s \in Seq(S), NEW t \in Seq(S), NEW u \in Seq(S),
             IsStrictSuffix(s,t), IsStrictSuffix(t,u)
      PROVE  IsStrictSuffix(s,u)
  <2>1. /\ IsSuffix(s,t) /\ Len(s) < Len(t)
        /\ IsSuffix(t,u) /\ Len(t) < Len(u)
    BY <1>3, IsStrictSuffixProperties
  <2>2. IsSuffix(s,u)
    BY <2>1, IsSuffixPartialOrder, Zenon
  <2>3. Len(s) < Len(u)
    BY <2>1
  <2>. QED  BY <2>2, <2>3, IsStrictSuffixProperties
<1>4. QED  BY <1>1, <1>2, <1>3

THEOREM IsStrictSuffixWellFounded ==
  ASSUME NEW S
  PROVE  IsWellFoundedOn(OpToRel(IsStrictSuffix, Seq(S)), Seq(S))
<1>1. IsWellFoundedOn(PreImage(Len, Seq(S), OpToRel(<, Nat)), Seq(S))
  BY NatLessThanWellFounded, PreImageWellFounded, \A s \in Seq(S) : Len(s) \in Nat, Blast
<1>2. OpToRel(IsStrictSuffix, Seq(S)) \subseteq PreImage(Len, Seq(S), OpToRel(<, Nat))
  BY IsStrictSuffixProperties DEF PreImage, OpToRel
<1>. QED
  BY <1>1, <1>2, IsWellFoundedOnSubrelation, Zenon

THEOREM SeqStrictSuffixInduction ==
  ASSUME NEW P(_), NEW S,
         \A t \in Seq(S) : (\A s \in Seq(S) : IsStrictSuffix(s,t) => P(s)) => P(t)
  PROVE  \A s \in Seq(S) : P(s)
<1>1. \A t \in Seq(S) : 
         (\A s \in SetLessThan(t, OpToRel(IsStrictSuffix, Seq(S)), Seq(S)) : P(s))
         => P(t)
  BY DEF SetLessThan, OpToRel
<1>. QED  BY WFInduction, IsStrictSuffixWellFounded, <1>1, Blast

(***************************************************************************)
(* Since the (strict) prefix and suffix orderings on sequences are         *)
(* well-founded, they can be used for defining recursive functions.        *)
(* The operators OpDefinesFcn, WFInductiveDefines, and WFInductiveUnique   *)
(* are defined in module WellFoundedInduction.                             *)
(***************************************************************************)

StrictPrefixesDetermineDef(S, Def(_,_)) ==
   \A g,h : \A seq \in Seq(S) :
      (\A pre \in Seq(S) : IsStrictPrefix(pre,seq) => g[pre] = h[pre])
      => Def(g, seq) = Def(h, seq)

LEMMA StrictPrefixesDetermineDef_WFDefOn ==
  ASSUME NEW S, NEW Def(_,_), StrictPrefixesDetermineDef(S, Def)
  PROVE  WFDefOn(OpToRel(IsStrictPrefix, Seq(S)), Seq(S), Def)
BY Isa DEF StrictPrefixesDetermineDef, WFDefOn, OpToRel, SetLessThan

THEOREM PrefixRecursiveSequenceFunctionUnique ==
  ASSUME NEW S, NEW Def(_,_), StrictPrefixesDetermineDef(S, Def)
  PROVE  WFInductiveUnique(Seq(S), Def)
BY StrictPrefixesDetermineDef_WFDefOn, IsStrictPrefixWellFounded, WFDefOnUnique

THEOREM PrefixRecursiveSequenceFunctionDef ==
  ASSUME NEW S, NEW Def(_,_), NEW f,
         StrictPrefixesDetermineDef(S, Def),
         OpDefinesFcn(f, Seq(S), Def)
  PROVE  WFInductiveDefines(f, Seq(S), Def)
BY StrictPrefixesDetermineDef_WFDefOn, IsStrictPrefixWellFounded, WFInductiveDef

THEOREM PrefixRecursiveSequenceFunctionType ==
  ASSUME NEW S, NEW T, NEW Def(_,_), NEW f,
         T # {},
         StrictPrefixesDetermineDef(S, Def),
         WFInductiveDefines(f, Seq(S), Def),
         \A g \in [Seq(S) -> T], s \in Seq(S) : Def(g,s) \in T
  PROVE  f \in [Seq(S) -> T]
<1>1. IsWellFoundedOn(OpToRel(IsStrictPrefix, Seq(S)), Seq(S))
  BY IsStrictPrefixWellFounded
<1>2. WFDefOn(OpToRel(IsStrictPrefix, Seq(S)), Seq(S), Def)
  BY StrictPrefixesDetermineDef_WFDefOn
<1>. QED
  BY <1>1, <1>2, WFInductiveDefType, Isa

StrictSuffixesDetermineDef(S, Def(_,_)) ==
   \A g,h : \A seq \in Seq(S) :
      (\A suf \in Seq(S) : IsStrictSuffix(suf,seq) => g[suf] = h[suf])
      => Def(g, seq) = Def(h, seq)

LEMMA StrictSuffixesDetermineDef_WFDefOn ==
  ASSUME NEW S, NEW Def(_,_), StrictSuffixesDetermineDef(S, Def)
  PROVE  WFDefOn(OpToRel(IsStrictSuffix, Seq(S)), Seq(S), Def)
BY Isa DEF StrictSuffixesDetermineDef, WFDefOn, OpToRel, SetLessThan

THEOREM SuffixRecursiveSequenceFunctionUnique ==
  ASSUME NEW S, NEW Def(_,_), StrictSuffixesDetermineDef(S, Def)
  PROVE  WFInductiveUnique(Seq(S), Def)
BY StrictSuffixesDetermineDef_WFDefOn, IsStrictSuffixWellFounded, WFDefOnUnique

THEOREM SuffixRecursiveSequenceFunctionDef ==
  ASSUME NEW S, NEW Def(_,_), NEW f,
         StrictSuffixesDetermineDef(S, Def),
         OpDefinesFcn(f, Seq(S), Def)
  PROVE  WFInductiveDefines(f, Seq(S), Def)
BY StrictSuffixesDetermineDef_WFDefOn, IsStrictSuffixWellFounded, WFInductiveDef

THEOREM SuffixRecursiveSequenceFunctionType ==
  ASSUME NEW S, NEW T, NEW Def(_,_), NEW f,
         T # {},
         StrictSuffixesDetermineDef(S, Def),
         WFInductiveDefines(f, Seq(S), Def),
         \A g \in [Seq(S) -> T], s \in Seq(S) : Def(g,s) \in T
  PROVE  f \in [Seq(S) -> T]
<1>1. IsWellFoundedOn(OpToRel(IsStrictSuffix, Seq(S)), Seq(S))
  BY IsStrictSuffixWellFounded
<1>2. WFDefOn(OpToRel(IsStrictSuffix, Seq(S)), Seq(S), Def)
  BY StrictSuffixesDetermineDef_WFDefOn
<1>. QED
  BY <1>1, <1>2, WFInductiveDefType, Isa

(***************************************************************************)
(* The following theorems justify ``primitive recursive'' functions over   *)
(* sequences, with a base case for the empty sequence and recursion along  *)
(* either the Tail or the Front of a non-empty sequence.                   *)
(***************************************************************************)

TailInductiveDefHypothesis(f, S, f0, Def(_,_)) ==
  f = CHOOSE g : g = [s \in Seq(S) |-> IF s = <<>> THEN f0 ELSE Def(g[Tail(s)], s)]

TailInductiveDefConclusion(f, S, f0, Def(_,_)) ==
  f = [s \in Seq(S) |-> IF s = <<>> THEN f0 ELSE Def(f[Tail(s)], s)]

THEOREM TailInductiveDef ==
  ASSUME NEW S, NEW Def(_,_), NEW f, NEW f0,
         TailInductiveDefHypothesis(f, S, f0, Def)
  PROVE  TailInductiveDefConclusion(f, S, f0, Def)
<1>. DEFINE Op(h,s) == IF s = <<>> THEN f0 ELSE Def(h[Tail(s)], s)
<1>1. StrictSuffixesDetermineDef(S, Op)
  <2>. SUFFICES ASSUME NEW g, NEW h, NEW seq \in Seq(S),
                       \A suf \in Seq(S) : IsStrictSuffix(suf, seq) => g[suf] = h[suf]
                PROVE  Op(g, seq) = Op(h, seq)
    BY DEF StrictSuffixesDetermineDef, Zenon
  <2>1. CASE seq = <<>>
    BY <2>1
  <2>2. CASE seq # <<>>
    <3>1. /\ Tail(seq) \in Seq(S)
          /\ IsStrictSuffix(Tail(seq), seq)
      BY <2>2, TailIsSuffix
    <3>2. g[Tail(seq)] = h[Tail(seq)]
      BY <3>1, Zenon
    <3>. QED
      BY <2>2, <3>2
  <2>. QED  BY <2>1, <2>2
<1>2. OpDefinesFcn(f, Seq(S), Op)
  BY DEF OpDefinesFcn, TailInductiveDefHypothesis
<1>3. WFInductiveDefines(f, Seq(S), Op)
  BY <1>1, <1>2, SuffixRecursiveSequenceFunctionDef
<1>. QED  BY <1>3 DEF WFInductiveDefines, TailInductiveDefConclusion

THEOREM TailInductiveDefType ==
  ASSUME NEW S, NEW Def(_,_), NEW f, NEW f0, NEW T,
         TailInductiveDefConclusion(f, S, f0, Def),
         f0 \in T,
         \A v \in T, s \in Seq(S) : s # <<>> => Def(v,s) \in T
  PROVE  f \in [Seq(S) -> T]
<1>. SUFFICES \A s \in Seq(S) : f[s] \in T
  BY DEF TailInductiveDefConclusion
<1>1. f[<<>>] \in T
  BY <<>> \in Seq(S) DEF TailInductiveDefConclusion
<1>2. ASSUME NEW seq \in Seq(S), NEW e \in S, f[seq] \in T
      PROVE  f[Cons(e, seq)] \in T
  <2>1. /\ Cons(e, seq) \in Seq(S)
        /\ Cons(e, seq) # <<>>
        /\ Tail(Cons(e, seq)) = seq
    BY ConsProperties
  <2>2. f[Cons(e, seq)] = Def(f[seq], Cons(e,seq))
    BY <2>1 DEF TailInductiveDefConclusion
  <2>. QED  BY <1>2, <2>1, <2>2
<1>. QED  BY <1>1, <1>2, SequencesInductionCons, Isa

FrontInductiveDefHypothesis(f, S, f0, Def(_,_)) ==
  f = CHOOSE g : g = [s \in Seq(S) |-> IF s = <<>> THEN f0 ELSE Def(g[Front(s)], s)]

FrontInductiveDefConclusion(f, S, f0, Def(_,_)) ==
  f = [s \in Seq(S) |-> IF s = <<>> THEN f0 ELSE Def(f[Front(s)], s)]

THEOREM FrontInductiveDef ==
  ASSUME NEW S, NEW Def(_,_), NEW f, NEW f0,
         FrontInductiveDefHypothesis(f, S, f0, Def)
  PROVE  FrontInductiveDefConclusion(f, S, f0, Def)
<1>. DEFINE Op(h,s) == IF s = <<>> THEN f0 ELSE Def(h[Front(s)], s)
<1>1. StrictPrefixesDetermineDef(S, Op)
  <2>. SUFFICES ASSUME NEW g, NEW h, NEW seq \in Seq(S),
                       \A pre \in Seq(S) : IsStrictPrefix(pre, seq) => g[pre] = h[pre]
                PROVE  Op(g, seq) = Op(h, seq)
    BY DEF StrictPrefixesDetermineDef, Zenon
  <2>1. CASE seq = <<>>
    BY <2>1
  <2>2. CASE seq # <<>>
    <3>1. /\ Front(seq) \in Seq(S)
          /\ IsStrictPrefix(Front(seq), seq)
      BY <2>2, FrontProperties, FrontIsPrefix
    <3>2. g[Front(seq)] = h[Front(seq)]
      BY <3>1, Zenon
    <3>. QED
      BY <2>2, <3>2
  <2>. QED  BY <2>1, <2>2
<1>2. OpDefinesFcn(f, Seq(S), Op)
  BY DEF OpDefinesFcn, FrontInductiveDefHypothesis
<1>3. WFInductiveDefines(f, Seq(S), Op)
  BY <1>1, <1>2, PrefixRecursiveSequenceFunctionDef
<1>. QED  BY <1>3 DEF WFInductiveDefines, FrontInductiveDefConclusion

THEOREM FrontInductiveDefType ==
  ASSUME NEW S, NEW Def(_,_), NEW f, NEW f0, NEW T,
         FrontInductiveDefConclusion(f, S, f0, Def),
         f0 \in T,
         \A v \in T, s \in Seq(S) : s # <<>> => Def(v,s) \in T
  PROVE  f \in [Seq(S) -> T]
<1>. SUFFICES \A s \in Seq(S) : f[s] \in T
  BY DEF FrontInductiveDefConclusion
<1>1. f[<<>>] \in T
  BY <<>> \in Seq(S) DEF FrontInductiveDefConclusion
<1>2. ASSUME NEW seq \in Seq(S), NEW e \in S, f[seq] \in T
      PROVE  f[Append(seq, e)] \in T
  <2>1. /\ Append(seq, e) \in Seq(S)
        /\ Append(seq, e) # <<>>
        /\ Front(Append(seq, e)) = seq
    BY AppendProperties, FrontLastAppend
  <2>2. f[Append(seq, e)] = Def(f[seq], Append(seq, e))
    BY <2>1 DEF FrontInductiveDefConclusion
  <2>. QED  BY <1>2, <2>1, <2>2
<1>. QED  BY <1>1, <1>2, SequencesInductionAppend, Isa

=============================================================================
