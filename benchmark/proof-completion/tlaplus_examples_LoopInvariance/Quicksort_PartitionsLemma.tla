----------------------------- MODULE Quicksort_PartitionsLemma -----------------------------
(***************************************************************************)
(* This module contains an abstract version of the Quicksort algorithm.    *)
(* If you are not already familiar with that algorithm, you should look it *)
(* up on the Web and understand how it works--including what the partition *)
(* procedure does, without worrying about how it does it.  The version     *)
(* presented here does not specify a partition procedure, but chooses in a *)
(* single step an arbitrary value that is the result that any partition    *)
(* procedure may produce.                                                  *)
(*                                                                         *)
(* The module also has a structured informal proof of Quicksort's partial  *)
(* correctness property--namely, that if it terminates, it produces a      *)
(* sorted permutation of the original sequence.  As described in the note  *)
(* "Proving Safety Properties", the proof uses the TLAPS proof system to   *)
(* check the decomposition of the proof into substeps, and to check some   *)
(* of the substeps whose proofs are trivial.                               *)
(*                                                                         *)
(* The version of Quicksort described here sorts a finite sequence of      *)
(* integers.  It is one of the examples in Section 7.3 of "Proving Safety  *)
(* Properties", which is at                                                *)
(*                                                                         *)
(*    http://lamport.azurewebsites.net/tla/proving-safety.pdf              *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLAPS, SequenceTheorems, FiniteSetTheorems
  (*************************************************************************)
  (* This statement imports some standard modules, including ones used by  *)
  (* the TLAPS proof system.                                               *)
  (*************************************************************************)

(***************************************************************************)
(* To aid in model checking the spec, we assume that the sequence to be    *)
(* sorted are elements of a set Values of integers.                        *)
(***************************************************************************)
CONSTANT Values
ASSUME ValAssump == Values \subseteq Int

(***************************************************************************)
(* We define PermsOf(s) to be the set of permutations of a sequence s of   *)
(* integers.  In TLA+, a sequence is a function whose domain is the set    *)
(* 1..Len(s).  A permutation of s is the composition of s with a           *)
(* permutation of its domain.  It is defined as follows, where:            *)
(*                                                                         *)
(*  - Automorphisms(S) is the set of all permutations of S, if S is a      *)
(*    finite set--that is all functions f from S to S such that every      *)
(*    element y of S is the image of some element of S under f.            *)
(*                                                                         *)
(*  - f ** g  is defined to be the composition of the functions f and g.   *)
(*                                                                         *)
(* In TLA+, DOMAIN f is the domain of a function f.                        *)
(***************************************************************************)
Automorphisms(S) == { f \in [S -> S] : 
                        \A y \in S : \E x \in S : f[x] = y }

f ** g == [x \in DOMAIN g |-> f[g[x]]]

PermsOf(s) == { s ** f : f \in Automorphisms(DOMAIN s) }

LEMMA AutomorphismsCompose ==
    ASSUME NEW S, NEW f \in Automorphisms(S), NEW g \in Automorphisms(S)
    PROVE  f ** g \in Automorphisms(S)
PROOF OMITTED

LEMMA PermsOfLemma ==
    ASSUME NEW T, NEW s \in Seq(T), NEW t \in PermsOf(s)
    PROVE  /\ t \in Seq(T)
           /\ Len(t) = Len(s)
           /\ \A i \in 1 .. Len(s) : \E j \in 1 .. Len(s) : t[i] = s[j]
           /\ \A i \in 1 .. Len(s) : \E j \in 1 .. Len(t) : t[j] = s[i]
PROOF OMITTED

LEMMA PermsOfPermsOf ==
    ASSUME NEW T, NEW s \in Seq(T), NEW t \in PermsOf(s), NEW u \in PermsOf(t)
    PROVE  u \in PermsOf(s)
PROOF OMITTED

(**************************************************************************)
(* We define Max(S) and Min(S) to be the maximum and minimum,             *)
(* respectively, of a finite, non-empty set S of integers.                *)
(**************************************************************************)
Max(S) == CHOOSE x \in S : \A y \in S : x >= y
Min(S) == CHOOSE x \in S : \A y \in S : x =< y

LEMMA MinIsMin == 
    ASSUME NEW S \in SUBSET Int, NEW x \in S, \A y \in S : x <= y
    PROVE  x = Min(S)
PROOF OMITTED

LEMMA MaxIsMax == 
    ASSUME NEW S \in SUBSET Int, NEW x \in S, \A y \in S : x >= y
    PROVE  x = Max(S)
PROOF OMITTED

LEMMA NonemptyMin ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S), NEW x \in S
    PROVE  /\ Min(S) \in S 
           /\ Min(S) <= x
PROOF OMITTED

LEMMA NonemptyMax ==
    ASSUME NEW S \in SUBSET Int, IsFiniteSet(S), NEW x \in S
    PROVE  /\ Max(S) \in S
           /\ x <= Max(S)
PROOF OMITTED

LEMMA IntervalMinMax ==
    ASSUME NEW i \in Int, NEW j \in Int, i <= j
    PROVE  i = Min(i .. j) /\ j = Max(i .. j)
PROOF OMITTED

(***************************************************************************)
(* The operator Partitions is defined so that if I is an interval that's a *)
(* subset of 1..Len(s) and p \in Min(I) ..  Max(I)-1, the Partitions(I, p, *)
(* seq) is the set of all new values of sequence seq that a partition      *)
(* procedure is allowed to produce for the subinterval I using the pivot   *)
(* index p.  That is, it's the set of all permutations of seq that leaves  *)
(* seq[i] unchanged if i is not in I and permutes the values of seq[i] for *)
(* i in I so that the values for i =< p are less than or equal to the      *)
(* values for i > p.                                                       *)
(***************************************************************************)
Partitions(I, p, s) ==
  {t \in PermsOf(s) : 
      /\ \A i \in (1..Len(s)) \ I : t[i] = s[i]
      /\ \A i \in I : \E j \in I : t[i] = s[j]
      /\ \A i, j \in I : (i =< p) /\ (p < j) => (t[i] =< t[j])}

LEMMA PartitionsLemma ==
    ASSUME NEW T, NEW s \in Seq(T), NEW I \in SUBSET (1 .. Len(s)),
           NEW p \in I, NEW t \in Partitions(I, p, s)
    PROVE  /\ t \in Seq(T)
           /\ Len(t) = Len(s)
           /\ \A i \in (1 .. Len(s)) \ I : t[i] = s[i]
           /\ \A i \in I : \E j \in I : t[i] = s[j]
           /\ \A i,j \in I : i <= p /\ p < j => t[i] <= t[j]
PROOF OBVIOUS

(***************************************************************************)
(* Our algorithm has three variables:                                      *)
(*                                                                         *)
(*    seq  : The array to be sorted.                                       *)
(*                                                                         *)
(*    seq0 : Holds the initial value of seq, for checking the result.      *)
(*                                                                         *)
(*    U : A set of intervals that are subsets of 1..Len(seq0), an interval *)
(*        being a nonempty set I of integers that equals Min(I)..Max(I).   *)
(*        Initially, U equals the set containing just the single interval  *)
(*        consisting of the entire set 1..Len(seq0).                       *)
(*                                                                         *)
(* The algorithm repeatedly does the following:                            *)
(*                                                                         *)
(*    - Chose an arbitrary interval I in U.                                *)
(*                                                                         *)
(*    - If I consists of a single element, remove I from U.                *)
(*                                                                         *)
(*    - Otherwise:                                                         *)
(*        - Let I1 be an initial interval of I and I2 be the rest of I.    *)
(*        - Let newseq be an array that's the same as seq except that the  *)
(*          elements seq[x] with x in I are permuted so that               *)
(*          newseq[y] =< newseq[z] for any y in I1 and z in I2.            *)
(*        - Set seq to newseq.                                             *)
(*        - Remove I from U and add I1 and I2 to U.                        *)
(*                                                                         *)
(* It stops when U is empty.  Below is the algorithm written in PlusCal.   *)
(***************************************************************************)
 
(***************************************************************************
--fair algorithm Quicksort {
  variables  seq \in Seq(Values) \ {<< >>}, seq0 = seq,  U = {1..Len(seq)};
  { a: while (U # {}) 
        { with (I \in U) 
            { if (Cardinality(I) = 1) 
                { U := U \ {I} } 
              else 
                { with (p \in Min(I) .. (Max(I)-1),
                        I1 = Min(I)..p,
                        I2 = (p+1)..Max(I),
                        newseq \in Partitions(I, p, seq))
                    { seq := newseq ;
                      U := (U \ {I}) \cup {I1, I2} }      }  }  }  }  }

****************************************************************************)
(***************************************************************************)
(* Below is the TLA+ translation of the PlusCal code.                      *)
(***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES pc, seq, seq0, U

vars == << pc, seq, seq0, U >>

Init == (* Global variables *)
        /\ seq \in Seq(Values) \ {<< >>}
        /\ seq0 = seq
        /\ U = {1..Len(seq)}
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF U # {}
           THEN /\ \E I \in U:
                     IF Cardinality(I) = 1
                        THEN /\ U' = U \ {I}
                             /\ seq' = seq
                        ELSE /\ \E p \in Min(I) .. (Max(I)-1):
                                  LET I1 == Min(I)..p IN
                                    LET I2 == (p+1)..Max(I) IN
                                      \E newseq \in Partitions(I, p, seq):
                                        /\ seq' = newseq
                                        /\ U' = ((U \ {I}) \cup {I1, I2})
                /\ pc' = "a"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << seq, U >>
     /\ seq0' = seq0

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION
(***************************************************************************)
(* PCorrect is the postcondition invariant that the algorithm should       *)
(* satisfy.  You can use TLC to check this for a model in which Seq(S) is  *)
(* redefined to equal the set of sequences of at elements in S with length *)
(* at most 4.  A little thought shows that it then suffices to let Values  *)
(* be a set of 4 integers.                                                 *)
(***************************************************************************)
PCorrect == (pc = "Done") => 
               /\ seq \in PermsOf(seq0)
               /\ \A p, q \in 1..Len(seq) : p < q => seq[p] =< seq[q] 

(***************************************************************************)
(* Below are some definitions leading up to the definition of the          *)
(* inductive invariant Inv used to prove the postcondition PCorrect.  The  *)
(* partial TLA+ proof follows.  As explained in "Proving Safety            *)
(* Properties", you can use TLC to check the level-<1> proof steps.  TLC   *)
(* can do those checks on a model in which all sequences have length at    *)
(* most 3.                                                                 *)
(***************************************************************************)
UV == U \cup {{i} : i \in 1..Len(seq) \ UNION U}

DomainPartitions == {DP \in SUBSET SUBSET (1..Len(seq0)) :
                      /\ (UNION DP) = 1..Len(seq0)
                      \* /\ \A I \in DP : I = Min(I)..Max(I)
                      /\ \A I \in DP : \E mn,mx \in 1 .. Len(seq0) : I = mn .. mx
                      /\ \A I, J \in DP : (I # J) => (I \cap J = {}) }

RelSorted(I, J) == \A i \in I, j \in J : (i < j) => (seq[i] =< seq[j])
 
TypeOK == /\ seq \in Seq(Values) \ {<<>>}
          /\ seq0 \in Seq(Values) \ {<<>>}
          /\ U \in SUBSET ( (SUBSET (1..Len(seq0))) \ {{}} )
          /\ pc \in {"a", "Done"}

Inv == /\ TypeOK
       /\ (pc = "Done") => (U = {})
       /\ UV \in DomainPartitions
       /\ seq \in PermsOf(seq0)
       /\ UNION UV = 1..Len(seq0)
       /\ \A I, J \in UV : (I # J) => RelSorted(I, J)

=============================================================================
\* Created Mon Jun 27 08:20:07 PDT 2016 by lamport
