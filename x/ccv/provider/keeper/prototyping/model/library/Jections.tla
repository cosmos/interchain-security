------------------------------ MODULE Jections ------------------------------
(***************************************************************************)
(* `^{\large\bf \vspace{12pt}                                              *)
(*  Definition of injection, surjection, and bijection.                    *)
(*  \vspace{12pt}}^'                                                       *)
(***************************************************************************)


(***************************************************************************)
(* A map is an injection iff each element in the domain maps to a distinct *)
(* element in the range.                                                   *)
(***************************************************************************)
Injection(S,T) == { M \in [S -> T] : \A a,b \in S : M[a] = M[b] => a = b }


(***************************************************************************)
(* A map is a surjection iff for each element in the range there is some   *)
(* element in the domain that maps to it.                                  *)
(***************************************************************************)
Surjection(S,T) == { M \in [S -> T] : \A t \in T : \E s \in S : M[s] = t }


(***************************************************************************)
(* A map is a bijection iff it is both an injection and a surjection.      *)
(***************************************************************************)
Bijection(S,T) == Injection(S,T) \cap Surjection(S,T)


(***************************************************************************)
(* An injection, surjection, or bijection exists if the corresponding set  *)
(* is nonempty.                                                            *)
(***************************************************************************)
ExistsInjection(S,T)  == Injection(S,T) # {}
ExistsSurjection(S,T) == Surjection(S,T) # {}
ExistsBijection(S,T)  == Bijection(S,T) # {}


(***************************************************************************)
(* The inverse of a jection.                                               *)
(***************************************************************************)
JectionInverse(S,T,M) == [t \in T |-> CHOOSE s \in S : M[s] = t]

JectionInverseSets(S, T, M, B) == { s \in S : M[s] \in B } 
=============================================================================
\* Modification History
\* Last modified Wed Jun 05 12:14:19 CEST 2013 by bhargav
\* Last modified Fri May 03 12:55:35 PDT 2013 by tomr
\* Created Thu Apr 11 10:30:48 PDT 2013 by tomr
