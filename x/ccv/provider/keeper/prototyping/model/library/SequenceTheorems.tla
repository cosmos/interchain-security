----------------------- MODULE SequenceTheorems -----------------------------
(***************************************************************************)
(* This module contains a library of theorems about sequences and the      *)
(* corresponding operations.                                               *)
(***************************************************************************)
EXTENDS Sequences, Integers, WellFoundedInduction, Functions, TLAPS


(***************************************************************************)
(* Elementary properties about Seq(S)                                      *)
(***************************************************************************)

LEMMA SeqDef == \A S : Seq(S) = UNION {[1..n -> S] : n \in Nat}

THEOREM ElementOfSeq ==
   ASSUME NEW S, NEW seq \in Seq(S),
          NEW n \in 1..Len(seq)
   PROVE  seq[n] \in S
 
THEOREM EmptySeq ==
   ASSUME NEW S
   PROVE /\ << >> \in Seq(S)
         /\ \A seq \in Seq(S) : (seq = << >>) <=> (Len(seq) = 0)

THEOREM LenProperties == 
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  /\ Len(seq) \in Nat
         /\ seq \in [1..Len(seq) -> S]
         /\ DOMAIN seq = 1 .. Len(seq) 

THEOREM ExceptSeq ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW i \in 1 .. Len(seq), NEW e \in S
  PROVE  /\ [seq EXCEPT ![i] = e] \in Seq(S)
         /\ Len([seq EXCEPT ![i] = e]) = Len(seq)
         /\ \A j \in 1 .. Len(seq) : [seq EXCEPT ![i] = e][j] = IF j=i THEN e ELSE seq[j]

THEOREM IsASeq ==
  ASSUME NEW n \in Nat, NEW e(_), NEW S,
         \A i \in 1..n : e(i) \in S
  PROVE  [i \in 1..n |-> e(i)] \in Seq(S)

THEOREM SeqEqual ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S),
         Len(s) = Len(t), \A i \in 1 .. Len(s) : s[i] = t[i]
  PROVE  s = t

(***************************************************************************
                 Concatenation (\o) And Properties                      
***************************************************************************)

THEOREM ConcatProperties ==
  ASSUME NEW S, NEW s1 \in Seq(S), NEW s2 \in Seq(S)
  PROVE  /\ s1 \o s2 \in Seq(S)
         /\ Len(s1 \o s2) = Len(s1) + Len(s2)
         /\ \A i \in 1 .. Len(s1) + Len(s2) : (s1 \o s2)[i] =
                     IF i <= Len(s1) THEN s1[i] ELSE s2[i - Len(s1)]

THEOREM ConcatEmptySeq ==
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  /\ seq \o << >> = seq
         /\ << >> \o seq = seq

THEOREM ConcatAssociative ==
  ASSUME NEW S, NEW s1 \in Seq(S), NEW s2 \in Seq(S), NEW s3 \in Seq(S)
  PROVE  (s1 \o s2) \o s3 = s1 \o (s2 \o s3)

THEOREM ConcatSimplifications ==
  ASSUME NEW S
  PROVE  /\ \A s,t \in Seq(S) : s \o t = s <=> t = <<>>
         /\ \A s,t \in Seq(S) : s \o t = t <=> s = <<>>
         /\ \A s,t \in Seq(S) : s \o t = <<>> <=> s = <<>> /\ t = <<>>
         /\ \A s,t,u \in Seq(S) : s \o t = s \o u <=> t = u
         /\ \A s,t,u \in Seq(S) : s \o u = t \o u <=> s = t

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

THEOREM SubSeqEmpty ==
  ASSUME NEW s, NEW m \in Int, NEW n \in Int, n < m
  PROVE  SubSeq(s,m,n) = << >>

THEOREM HeadTailProperties ==
   ASSUME NEW S,
          NEW seq \in Seq(S), seq # << >>
   PROVE  /\ Head(seq) \in S
          /\ Tail(seq) \in Seq(S)
          /\ Len(Tail(seq)) = Len(seq)-1
          /\ \A i \in 1 .. Len(Tail(seq)) : Tail(seq)[i] = seq[i+1]

THEOREM TailIsSubSeq ==
  ASSUME NEW S,
         NEW seq \in Seq(S), seq # << >>
  PROVE  Tail(seq) = SubSeq(seq, 2, Len(seq))

THEOREM SubSeqRestrict ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW n \in 0 .. Len(seq)
  PROVE  SubSeq(seq, 1, n) = Restrict(seq, 1 .. n)

THEOREM HeadTailOfSubSeq ==
  ASSUME NEW S, NEW seq \in Seq(S),
         NEW m \in 1 .. Len(seq), NEW n \in m .. Len(seq)
  PROVE  /\ Head(SubSeq(seq,m,n)) = seq[m]
         /\ Tail(SubSeq(seq,m,n)) = SubSeq(seq, m+1, n)

THEOREM SubSeqRecursiveFirst ==
  ASSUME NEW S, NEW seq \in Seq(S),
         NEW m \in 1 .. Len(seq), NEW n \in m .. Len(seq)
  PROVE  SubSeq(seq, m, n) = << seq[m] >> \o SubSeq(seq, m+1, n)

THEOREM SubSeqRecursiveSecond ==
  ASSUME NEW S, NEW seq \in Seq(S),
         NEW m \in 1 .. Len(seq), NEW n \in m .. Len(seq)
  PROVE  SubSeq(seq, m, n) = SubSeq(seq, m, n-1) \o << seq[n] >>

THEOREM SubSeqFull ==
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  SubSeq(seq, 1, Len(seq)) = seq

(*****************************************************************************)
(* Adjacent subsequences can be concatenated to obtain a longer subsequence. *)
(*****************************************************************************)
THEOREM ConcatAdjacentSubSeq ==
  ASSUME NEW S, NEW seq \in Seq(S), 
         NEW m \in 1 .. Len(seq)+1, 
         NEW k \in m-1 .. Len(seq), 
         NEW n \in k .. Len(seq)
  PROVE  SubSeq(seq, m, k) \o SubSeq(seq, k+1, n) = SubSeq(seq, m, n)

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

THEOREM AppendIsConcat ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW elt \in S
  PROVE  Append(seq, elt) = seq \o <<elt>>

THEOREM HeadTailAppend ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW elt
  PROVE  /\ Head(Append(seq, elt)) = IF seq = <<>> THEN elt ELSE Head(seq)
         /\ Tail(Append(seq, elt)) = IF seq = <<>> THEN <<>> ELSE Append(Tail(seq), elt)

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

THEOREM ConsEmpty ==
  \A x : Cons(x, << >>) = << x >>

THEOREM ConsHeadTail ==
  ASSUME NEW S, NEW seq \in Seq(S), seq # << >>
  PROVE  Cons(Head(seq), Tail(seq)) = seq

THEOREM ConsAppend ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW x \in S, NEW y \in S
  PROVE  Cons(x, Append(seq, y)) = Append(Cons(x,seq), y)

THEOREM ConsInjective ==
  ASSUME NEW S, NEW e \in S, NEW s \in Seq(S), NEW f \in S, NEW t \in Seq(S)
  PROVE  Cons(e,s) = Cons(f,t) <=> e = f /\ s = t

InsertAt(seq,i,elt) == SubSeq(seq, 1, i-1) \o <<elt>> \o SubSeq(seq, i, Len(seq))

THEOREM InsertAtProperties ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW i \in 1 .. Len(seq)+1, NEW elt \in S
  PROVE  /\ InsertAt(seq,i,elt) \in Seq(S)
         /\ Len(InsertAt(seq,i,elt)) = Len(seq)+1
         /\ \A j \in 1 .. Len(seq)+1 : InsertAt(seq,i,elt)[j] =
                     IF j<i THEN seq[j]
                     ELSE IF j=i THEN elt
                     ELSE seq[j-1]

RemoveAt(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

THEOREM RemoveAtProperties ==
   ASSUME NEW S, NEW seq \in Seq(S),
          NEW i \in 1..Len(seq)
   PROVE  /\ RemoveAt(seq,i) \in Seq(S)
          /\ Len(RemoveAt(seq,i)) = Len(seq) - 1
          /\ \A j \in 1 .. Len(seq)-1 : RemoveAt(seq,i)[j] = IF j<i THEN seq[j] ELSE seq[j+1]

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

THEOREM FrontOfEmpty == Front(<< >>) = << >>

THEOREM LastProperties ==
  ASSUME NEW S, NEW seq \in Seq(S), seq # << >>
  PROVE  /\ Last(seq) \in S 
         /\ Append(Front(seq), Last(seq)) = seq 

THEOREM FrontLastOfSubSeq ==
  ASSUME NEW S, NEW seq \in Seq(S),
         NEW m \in 1 .. Len(seq), NEW n \in m .. Len(seq)
  PROVE  /\ Front(SubSeq(seq,m,n)) = SubSeq(seq, m, n-1)
         /\ Last(SubSeq(seq,m,n)) = seq[n]

THEOREM FrontLastAppend ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW e \in S
  PROVE  /\ Front(Append(seq, e)) = seq
         /\ Last(Append(seq, e)) = e

THEOREM AppendInjective ==
  ASSUME NEW S, NEW e \in S, NEW s \in Seq(S), NEW f \in S, NEW t \in Seq(S)
  PROVE  Append(s,e) = Append(t,f) <=> s = t /\ e = f

(***************************************************************************)
(* As a corollary of the previous theorems it follows that a sequence is   *)
(* either empty or can be obtained by appending an element to a sequence.  *)
(***************************************************************************)
THEOREM SequenceEmptyOrAppend == 
  ASSUME NEW S, NEW seq \in Seq(S), seq # << >>
  PROVE \E s \in Seq(S), elt \in S : seq = Append(s, elt)
     
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

THEOREM ReverseEmpty == Reverse(<< >>) = << >>

THEOREM ReverseEqual ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), Reverse(s) = Reverse(t)
  PROVE  s = t

THEOREM ReverseEmptyIffEmpty ==
  ASSUME NEW S, NEW seq \in Seq(S), Reverse(seq) = <<>>
  PROVE  seq = <<>>

THEOREM ReverseConcat == 
  ASSUME NEW S, NEW s1 \in Seq(S), NEW s2 \in Seq(S)
  PROVE  Reverse(s1 \o s2) = Reverse(s2) \o Reverse(s1)

THEOREM ReverseAppend ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW e \in S
  PROVE  Reverse(Append(seq,e)) = Cons(e, Reverse(seq))

THEOREM ReverseCons ==
  ASSUME NEW S, NEW seq \in Seq(S), NEW e \in S
  PROVE  Reverse(Cons(e,seq)) = Append(Reverse(seq), e)

THEOREM ReverseSingleton == \A x : Reverse(<< x >>) = << x >>

THEOREM ReverseSubSeq ==
  ASSUME NEW S, NEW seq \in Seq(S),
         NEW m \in 1..Len(seq), NEW n \in 1..Len(seq)
  PROVE  Reverse(SubSeq(seq, m , n)) = SubSeq(Reverse(seq), Len(seq)-n+1, Len(seq)-m+1)

THEOREM ReversePalindrome ==
  ASSUME NEW S, NEW seq \in Seq(S),
         Reverse(seq) = seq
  PROVE  Reverse(seq \o seq) = seq \o seq

THEOREM LastEqualsHeadReverse ==
  ASSUME NEW S, NEW seq \in Seq(S), seq # << >>
  PROVE  Last(seq) = Head(Reverse(seq))

THEOREM ReverseFrontEqualsTailReverse ==
  ASSUME NEW S, NEW seq \in Seq(S), seq # << >>
  PROVE  Reverse(Front(seq)) = Tail(Reverse(seq))

(***************************************************************************)
(* Induction principles for sequences                                      *)
(***************************************************************************)

THEOREM SequencesInductionAppend ==
  ASSUME NEW P(_), NEW S, 
         P(<< >>),
         \A s \in Seq(S), e \in S : P(s) => P(Append(s,e))
  PROVE  \A seq \in Seq(S) : P(seq)
      
THEOREM SequencesInductionCons == 
  ASSUME NEW P(_), NEW S,
         P(<< >>),
         \A s \in Seq(S), e \in S : P(s) => P(Cons(e,s))
  PROVE \A seq \in Seq(S) : P(seq)

(***************************************************************************)
(*                          RANGE OF SEQUENCE                              *)
(***************************************************************************)

THEOREM RangeOfSeq == 
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  Range(seq) \in SUBSET S

THEOREM RangeEquality == 
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE Range(seq) = { seq[i] : i \in 1 .. Len(seq) }

(* The range of the reverse sequence equals that of the original one. *)
THEOREM RangeReverse == 
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE Range(Reverse(seq)) = Range(seq)

(* Range of concatenation of sequences is the union of the ranges *)
THEOREM RangeConcatenation == 
  ASSUME NEW S, NEW s1 \in Seq(S), NEW s2 \in Seq(S)
  PROVE  Range(s1 \o s2) = Range(s1) \cup Range(s2)

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

THEOREM IsStrictPrefixProperties ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  /\ IsStrictPrefix(s,t) <=> \E u \in Seq(S) : u # << >> /\ t = s \o u
         /\ IsStrictPrefix(s,t) <=> Len(s) < Len(t) /\ s = SubSeq(t, 1, Len(s))
         /\ IsStrictPrefix(s,t) <=> Len(s) < Len(t) /\ s = Restrict(t, DOMAIN s)
         /\ IsStrictPrefix(s,t) <=> IsPrefix(s,t) /\ Len(s) < Len(t)

THEOREM IsPrefixElts ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), NEW i \in 1 .. Len(s),
         IsPrefix(s,t)
  PROVE  s[i] = t[i]

THEOREM EmptyIsPrefix ==
  ASSUME NEW S, NEW s \in Seq(S)
  PROVE  /\ IsPrefix(<<>>, s)
         /\ IsPrefix(s, <<>>) <=> s = <<>>
         /\ IsStrictPrefix(<<>>, s) <=> s # <<>>
         /\ ~ IsStrictPrefix(s, <<>>)

THEOREM IsPrefixConcat ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  IsPrefix(s, s \o t)

THEOREM IsPrefixAppend ==
  ASSUME NEW S, NEW s \in Seq(S), NEW e \in S
  PROVE  IsPrefix(s, Append(s,e))

THEOREM FrontIsPrefix ==
  ASSUME NEW S, NEW s \in Seq(S)
  PROVE  /\ IsPrefix(Front(s), s)
         /\ s # <<>> => IsStrictPrefix(Front(s), s)

(***************************************************************************)
(* (Strict) prefixes on sequences form a (strict) partial order, and       *)
(* the strict ordering is well-founded.                                    *)
(***************************************************************************)
THEOREM IsPrefixPartialOrder ==
  ASSUME NEW S
  PROVE  /\ \A s \in Seq(S) : IsPrefix(s,s)
         /\ \A s,t \in Seq(S) : IsPrefix(s,t) /\ IsPrefix(t,s) => s = t
         /\ \A s,t,u \in Seq(S) : IsPrefix(s,t) /\ IsPrefix(t,u) => IsPrefix(s,u)

THEOREM ConcatIsPrefix ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), NEW u \in Seq(S),
         IsPrefix(s \o t, u)
  PROVE  IsPrefix(s, u)

THEOREM ConcatIsPrefixCancel ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), NEW u \in Seq(S)
  PROVE  IsPrefix(s \o t, s \o u) <=> IsPrefix(t, u)

THEOREM ConsIsPrefixCancel ==
  ASSUME NEW S, NEW e \in S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  IsPrefix(Cons(e,s), Cons(e,t)) <=> IsPrefix(s,t)

THEOREM ConsIsPrefix ==
  ASSUME NEW S, NEW e \in S, NEW s \in Seq(S), NEW u \in Seq(S),
         IsPrefix(Cons(e,s), u)
  PROVE  /\ e = Head(u)
         /\ IsPrefix(s, Tail(u))

THEOREM IsStrictPrefixStrictPartialOrder ==
  ASSUME NEW S
  PROVE  /\ \A s \in Seq(S) : ~ IsStrictPrefix(s,s)
         /\ \A s,t \in Seq(S) : IsStrictPrefix(s,t) => ~ IsStrictPrefix(t,s)
         /\ \A s,t,u \in Seq(S) : IsStrictPrefix(s,t) /\ IsStrictPrefix(t,u) => IsStrictPrefix(s,u)

THEOREM IsStrictPrefixWellFounded ==
  ASSUME NEW S
  PROVE  IsWellFoundedOn(OpToRel(IsStrictPrefix, Seq(S)), Seq(S))

THEOREM SeqStrictPrefixInduction ==
  ASSUME NEW P(_), NEW S,
         \A t \in Seq(S) : (\A s \in Seq(S) : IsStrictPrefix(s,t) => P(s)) => P(t)
  PROVE  \A s \in Seq(S) : P(s)

(***************************************************************************)
(* Similar theorems about suffixes.                                        *)
(***************************************************************************)

THEOREM IsSuffixProperties ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  /\ IsSuffix(s,t) <=> \E u \in Seq(S) : t = u \o s
         /\ IsSuffix(s,t) <=> Len(s) <= Len(t) /\ s = SubSeq(t, Len(t)-Len(s)+1, Len(t))
         /\ IsSuffix(s,t) <=> IsPrefix(Reverse(s), Reverse(t))

THEOREM IsStrictSuffixProperties ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  /\ IsStrictSuffix(s,t) <=> \E u \in Seq(S) : u # << >> /\ t = u \o s
         /\ IsStrictSuffix(s,t) <=> Len(s) < Len(t) /\ IsSuffix(s,t)
         /\ IsStrictSuffix(s,t) <=> Len(s) < Len(t) /\ s = SubSeq(t, Len(t)-Len(s)+1, Len(t))
         /\ IsStrictSuffix(s,t) <=> IsStrictPrefix(Reverse(s), Reverse(t))

THEOREM IsSuffixElts ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), NEW i \in 1 .. Len(s),
         IsSuffix(s,t)
  PROVE  s[i] = t[Len(t) - Len(s) + i]

THEOREM EmptyIsSuffix ==
  ASSUME NEW S, NEW s \in Seq(S)
  PROVE  /\ IsSuffix(<<>>, s)
         /\ IsSuffix(s, <<>>) <=> s = <<>>
         /\ IsStrictSuffix(<<>>, s) <=> s # <<>>
         /\ ~ IsStrictSuffix(s, <<>>)

THEOREM IsSuffixConcat ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  IsSuffix(s, t \o s)

THEOREM IsStrictSuffixCons ==
  ASSUME NEW S, NEW s \in Seq(S), NEW e \in S
  PROVE  IsStrictSuffix(s, Cons(e,s))

THEOREM TailIsSuffix ==
  ASSUME NEW S, NEW s \in Seq(S)
  PROVE  /\ IsSuffix(Tail(s), s)
         /\ s # <<>> => IsStrictSuffix(Tail(s), s)

THEOREM IsSuffixPartialOrder ==
  ASSUME NEW S
  PROVE  /\ \A s \in Seq(S) : IsSuffix(s,s)
         /\ \A s,t \in Seq(S) : IsSuffix(s,t) /\ IsSuffix(t,s) => s = t
         /\ \A s,t,u \in Seq(S) : IsSuffix(s,t) /\ IsSuffix(t,u) => IsSuffix(s,u)

THEOREM ConcatIsSuffix ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), NEW u \in Seq(S),
         IsSuffix(s \o t, u)
  PROVE  IsSuffix(t, u)

THEOREM ConcatIsSuffixCancel ==
  ASSUME NEW S, NEW s \in Seq(S), NEW t \in Seq(S), NEW u \in Seq(S)
  PROVE  IsSuffix(s \o t, u \o t) <=> IsSuffix(s, u)

THEOREM AppendIsSuffixCancel ==
  ASSUME NEW S, NEW e \in S, NEW s \in Seq(S), NEW t \in Seq(S)
  PROVE  IsSuffix(Append(s,e), Append(t,e)) <=> IsSuffix(s,t)

THEOREM AppendIsSuffix ==
  ASSUME NEW S, NEW e \in S, NEW s \in Seq(S), NEW u \in Seq(S),
         IsSuffix(Append(s,e), u)
  PROVE  /\ e = Last(u)
         /\ IsSuffix(s, Front(u))

THEOREM IsStrictSuffixStrictPartialOrder ==
  ASSUME NEW S
  PROVE  /\ \A s \in Seq(S) : ~ IsStrictSuffix(s,s)
         /\ \A s,t \in Seq(S) : IsStrictSuffix(s,t) => ~ IsStrictSuffix(t,s)
         /\ \A s,t,u \in Seq(S) : IsStrictSuffix(s,t) /\ IsStrictSuffix(t,u) => IsStrictSuffix(s,u)

THEOREM IsStrictSuffixWellFounded ==
  ASSUME NEW S
  PROVE  IsWellFoundedOn(OpToRel(IsStrictSuffix, Seq(S)), Seq(S))

THEOREM SeqStrictSuffixInduction ==
  ASSUME NEW P(_), NEW S,
         \A t \in Seq(S) : (\A s \in Seq(S) : IsStrictSuffix(s,t) => P(s)) => P(t)
  PROVE  \A s \in Seq(S) : P(s)

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

THEOREM PrefixRecursiveSequenceFunctionUnique ==
  ASSUME NEW S, NEW Def(_,_), StrictPrefixesDetermineDef(S, Def)
  PROVE  WFInductiveUnique(Seq(S), Def)

THEOREM PrefixRecursiveSequenceFunctionDef ==
  ASSUME NEW S, NEW Def(_,_), NEW f,
         StrictPrefixesDetermineDef(S, Def),
         OpDefinesFcn(f, Seq(S), Def)
  PROVE  WFInductiveDefines(f, Seq(S), Def)

THEOREM PrefixRecursiveSequenceFunctionType ==
  ASSUME NEW S, NEW T, NEW Def(_,_), NEW f,
         T # {},
         StrictPrefixesDetermineDef(S, Def),
         WFInductiveDefines(f, Seq(S), Def),
         \A g \in [Seq(S) -> T], s \in Seq(S) : Def(g,s) \in T
  PROVE  f \in [Seq(S) -> T]

StrictSuffixesDetermineDef(S, Def(_,_)) ==
   \A g,h : \A seq \in Seq(S) :
      (\A suf \in Seq(S) : IsStrictSuffix(suf,seq) => g[suf] = h[suf])
      => Def(g, seq) = Def(h, seq)

LEMMA StrictSuffixesDetermineDef_WFDefOn ==
  ASSUME NEW S, NEW Def(_,_), StrictSuffixesDetermineDef(S, Def)
  PROVE  WFDefOn(OpToRel(IsStrictSuffix, Seq(S)), Seq(S), Def)

THEOREM SuffixRecursiveSequenceFunctionUnique ==
  ASSUME NEW S, NEW Def(_,_), StrictSuffixesDetermineDef(S, Def)
  PROVE  WFInductiveUnique(Seq(S), Def)

THEOREM SuffixRecursiveSequenceFunctionDef ==
  ASSUME NEW S, NEW Def(_,_), NEW f,
         StrictSuffixesDetermineDef(S, Def),
         OpDefinesFcn(f, Seq(S), Def)
  PROVE  WFInductiveDefines(f, Seq(S), Def)

THEOREM SuffixRecursiveSequenceFunctionType ==
  ASSUME NEW S, NEW T, NEW Def(_,_), NEW f,
         T # {},
         StrictSuffixesDetermineDef(S, Def),
         WFInductiveDefines(f, Seq(S), Def),
         \A g \in [Seq(S) -> T], s \in Seq(S) : Def(g,s) \in T
  PROVE  f \in [Seq(S) -> T]

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

THEOREM TailInductiveDefType ==
  ASSUME NEW S, NEW Def(_,_), NEW f, NEW f0, NEW T,
         TailInductiveDefConclusion(f, S, f0, Def),
         f0 \in T,
         \A v \in T, s \in Seq(S) : s # <<>> => Def(v,s) \in T
  PROVE  f \in [Seq(S) -> T]

FrontInductiveDefHypothesis(f, S, f0, Def(_,_)) ==
  f = CHOOSE g : g = [s \in Seq(S) |-> IF s = <<>> THEN f0 ELSE Def(g[Front(s)], s)]

FrontInductiveDefConclusion(f, S, f0, Def(_,_)) ==
  f = [s \in Seq(S) |-> IF s = <<>> THEN f0 ELSE Def(f[Front(s)], s)]

THEOREM FrontInductiveDef ==
  ASSUME NEW S, NEW Def(_,_), NEW f, NEW f0,
         FrontInductiveDefHypothesis(f, S, f0, Def)
  PROVE  FrontInductiveDefConclusion(f, S, f0, Def)

THEOREM FrontInductiveDefType ==
  ASSUME NEW S, NEW Def(_,_), NEW f, NEW f0, NEW T,
         FrontInductiveDefConclusion(f, S, f0, Def),
         f0 \in T,
         \A v \in T, s \in Seq(S) : s # <<>> => Def(v,s) \in T
  PROVE  f \in [Seq(S) -> T]

=============================================================================
