------------------------------ MODULE Boulanger_TypeCorrectScaffold ----------------------------
(***************************************************************************)
(* This is a PlusCal encoding of the Boulangerie Algorithm of Yoram Moses  *)
(* and Katia Patkin--a variant of the Bakery Algorithm--and a proof that   *)
(* it implements mutual exclusion.  The bakery algorithm appeared in       *)
(*                                                                         *)
(*   Leslie Lamport                                                        *)
(*   A New Solution of Dijkstra's Concurrent Programming Problem           *)
(*   Communications of the ACM 17, 8   (August 1974), 453-455              *)
(*                                                                         *)
(* The PlusCal encoding differs from the Moses-Patkin algorithm in one     *)
(* respect.  To enter the critical section, the PlusCal version examines   *)
(* other processes one at a time--in the while loop at label w1.  The      *)
(* Moses-Patkin algorithm performs those examinations in parallel.         *)
(* Because PlusCal does not allow sub-processes, it would be difficult     *)
(* (but not impossible) to express that algorithm in PlusCal.  It would be *)
(* easy to express their version in TLA+ (for example, by modifying the    *)
(* TLA+ translation of the PlusCal code), and it should be straightforward *)
(* to convert the invariance proof presented here to a proof of the more   *)
(* general version.  I will leave that as an exercise for others.          *)
(*                                                                         *)
(* I started with a PlusCal encoding and invariance proof of the Bakery    *)
(* Algorithm.  The only non-obvious part of that encoding is how it        *)
(* represented the safe registers assumed by the algorithm, which are      *)
(* registers in which reads and writes are not atomic.  A safe register is *)
(* represented by a variable r whose value is written by performing some   *)
(* number of atomic writes of non-deterministically chosen "legal" values  *)
(* to r followed by a single write of the desired value.  A read of the    *)
(* register is performed by a single atomic read of r.  It can be shown    *)
(* that this captures the semantics of a safe register.                    *)
(*                                                                         *)
(* Starting from the PlusCal version of the Bakery Algorithm, it was easy  *)
(* to modify it to the Boulangerie Algorithm (with the simplification      *)
(* described above).  I model checked the algorithm on some small models   *)
(* to convince myself that there were no trivial errors that would be      *)
(* likely to arise from an error in the encoding.  I then modified the     *)
(* invariant by a combination of a bit of thinking and a fair amount of    *)
(* trial and error, finding errors in the invariant by model checking very *)
(* small models.  (I checked it on two processes with chosen numbers       *)
(* restricted to be at most 3.)                                            *)
(*                                                                         *)
(* When checking on a small model revealed no error in the invariant, I    *)
(* checked the proof with TLAPS (the TLA+ proof system).  The high level   *)

(* as for the Bakery Algorithm.  TLAPS checks this simple four-step proof  *)
(* for the Bakery Algorithm with terminal BY proofs that just tell it to   *)
(* use the necessary assumptions and to expand all definitions.  This      *)

(* that checks inductive invariance.                                       *)
(*                                                                         *)
(* When a proof doesn't go through, one keeps decomposing the proof of the *)
(* steps that aren't proved until one sees what the problem is.  This      *)
(* decomposition is done with little thinking and no typing using the      *)
(* Toolbox's Decompose Proof command.  (The Toolbox is the IDE for the     *)

(* consisting of subgoals essentially of the form A /\ Bi => C for the     *)
(* disjuncts Bi of B.  Two of those subgoals weren't proved.  I decomposed *)
(* them both for several levels until I saw that in one of them, some step *)
(* wasn't preserving the part of the invariant that asserts                *)
(* type-correctness.  I then quickly found the culprit: a silly error in   *)
(* the type invariant in which I had in one place written the set Proc of  *)
(* process numbers instead of the set Nat of natural numbers.  After       *)

(* could on that step, one substep remained unproved.  (I think it was at  *)

(* decomposition was a two-way case split, which I did by manually         *)
(* entering another level of subproof.  One of those cases weren't proved, *)
(* so I tried another two-way case split on it.  That worked.  I then made *)

(* its proof with it.  With that additional fact, TLAPS was able to prove  *)

(*                                                                         *)
(* The entire proof now is about 70 lines.  I only typed 20 of those 70    *)
(* lines.  The rest either came from the original Bakery Algorithm         *)
(* (8-line) proof or were generated by the Decompose Proof Command.        *)
(*                                                                         *)
(* I don't know how much time I actually spent writing the algorithm and   *)
(* its proof.  Except for the final compaction of the (correct) proof of   *)

(* spent tracking down bugs in the Toolbox.  We are in the process of      *)
(* moving the Toolbox to a new version of Eclipse, and there are many bugs *)
(* that must be fixed before it's ready to be released.  I would estimate  *)
(* that it would have taken me less than 4 hours without Toolbox bugs.  I  *)
(* find it remarkable how little thinking the whole thing took.            *)
(*                                                                         *)
(* This whole process was a lot easier than trying to write a convincing   *)
(* hand proof--a proof that I would regard as adequate to justify          *)
(* publication of the proof.                                               *)
(***************************************************************************)

EXTENDS BoulangerModel

(***************************************************************************)
(* We first declare N to be the number of processes, and we assume that N  *)
(* is a natural number.                                                    *)
(***************************************************************************)

(***************************************************************************)
(* We define Procs to be the set {1, 2, ...  , N} of processes.            *)
(***************************************************************************)

(***************************************************************************)
(* \prec is defined to be the lexicographical less-than relation on pairs  *)
(* of numbers.                                                             *)
(***************************************************************************)

(***       this is a comment containing the PlusCal code *

--algorithm Boulanger
{ variable num = [i \in Procs |-> 0], flag = [i \in Procs |-> FALSE];
  fair process (p \in Procs)
    variables unchecked = {}, max = 0, nxt = 1, previous = -1 ;
    { ncs:- while (TRUE) 
            { e1:   either { flag[self] := ~ flag[self] ;
                             goto e1 }
                    or     { flag[self] := TRUE;
                             unchecked := Procs \ {self} ;
                             max := 0
                           } ;     
              e2:   while (unchecked # {}) 
                      { with (i \in unchecked) 
                          { unchecked := unchecked \ {i};
                            if (num[i] > max) { max := num[i] }
                          }
                      };
              e3:   either { with (k \in Nat) { num[self] := k } ;
                             goto e3 }
                    or     { num[self] := max + 1 } ;
              e4:   either { flag[self] := ~ flag[self] ;
                             goto e4 }
                    or     { flag[self] := FALSE;
                               unchecked := IF num[self] = 1
                                              THEN 1..(self-1)
                                              ELSE Procs \ {self} 
                           } ;
              w1:   while (unchecked # {}) 
                      {     with (i \in unchecked) { nxt := i };
                            await ~ flag[nxt];
                            previous := -1 ;
                        w2: if ( \/ num[nxt] = 0
                                 \/ <<num[self], self>> \prec <<num[nxt], nxt>>
                                 \/  /\ previous # -1 
                                     /\ num[nxt] # previous)
                                { unchecked := unchecked \ {nxt};
                                  if (unchecked = {}) {goto cs}
                                  else {goto w1} 
                                }
                              else { previous := num[nxt] ;
                                     goto w2 }
                                                           
                      } ;
              cs:   skip ;  \* the critical section;
              exit: either { with (k \in Nat) { num[self] := k } ;
                             goto exit }
                    or     { num[self] := 0 } 
            }
    }
}

    this ends the comment containing the PlusCal code
*************)

\* BEGIN TRANSLATION  (this begins the translation of the PlusCal code)

\* END TRANSLATION   (this ends the translation of the PlusCal code)

(***************************************************************************)
(* MutualExclusion asserts that two distinct processes are in their        *)
(* critical sections.                                                      *)
(***************************************************************************)
MutualExclusion == \A i,j \in Procs : (i # j) => ~ /\ pc[i] = "cs"
                                                   /\ pc[j] = "cs"
(***************************************************************************)
(* The Inductive Invariant                                                 *)
(*                                                                         *)
(* TypeOK is the type-correctness invariant.                               *)
(***************************************************************************)
TypeOK == /\ num \in [Procs -> Nat]
          /\ flag \in [Procs -> BOOLEAN]
          /\ unchecked \in [Procs -> SUBSET Procs]
          /\ max \in [Procs -> Nat]
          /\ nxt \in [Procs -> Procs]
          /\ pc \in [Procs -> {"ncs", "e1", "e2", "e3",
                               "e4", "w1", "w2", "cs", "exit"}]
          /\ previous \in [Procs -> Nat \cup {-1}]             

=============================================================================
