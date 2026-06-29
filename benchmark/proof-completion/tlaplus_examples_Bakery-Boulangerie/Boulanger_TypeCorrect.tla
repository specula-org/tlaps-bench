------------------------------ MODULE Boulanger_TypeCorrect ----------------------------
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
(* proof, consisting of steps <1>1 - <1>4, are standard and are the same   *)
(* as for the Bakery Algorithm.  TLAPS checks this simple four-step proof  *)
(* for the Bakery Algorithm with terminal BY proofs that just tell it to   *)
(* use the necessary assumptions and to expand all definitions.  This      *)
(* didn't work for the hard part of the Boulangerie Algorithm--step <1>2   *)
(* that checks inductive invariance.                                       *)
(*                                                                         *)
(* When a proof doesn't go through, one keeps decomposing the proof of the *)
(* steps that aren't proved until one sees what the problem is.  This      *)
(* decomposition is done with little thinking and no typing using the      *)
(* Toolbox's Decompose Proof command.  (The Toolbox is the IDE for the     *)
(* TLA+ tools.) Step <1>2 has the form A /\ B => C, where B is a           *)
(* disjunction, and the Decompose Proof command produces a level-<2> proof *)
(* consisting of subgoals essentially of the form A /\ Bi => C for the     *)
(* disjuncts Bi of B.  Two of those subgoals weren't proved.  I decomposed *)
(* them both for several levels until I saw that in one of them, some step *)
(* wasn't preserving the part of the invariant that asserts                *)
(* type-correctness.  I then quickly found the culprit: a silly error in   *)
(* the type invariant in which I had in one place written the set Proc of  *)
(* process numbers instead of the set Nat of natural numbers.  After       *)
(* correcting that error, only one of the level-<2> subgoals remained      *)
(* unproved: step <2>5.  Using the Decompose Proof command as far as I     *)
(* could on that step, one substep remained unproved.  (I think it was at  *)
(* level <5>.) Looking at what the proof obligations were, the obvious     *)
(* decomposition was a two-way case split, which I did by manually         *)
(* entering another level of subproof.  One of those cases weren't proved, *)
(* so I tried another two-way case split on it.  That worked.  I then made *)
(* that substep to the first step of the (level <3>) proof of <2>5, moving *)
(* its proof with it.  With that additional fact, TLAPS was able to prove  *)
(* <2>5 in one more step (the QED step).                                   *)
(*                                                                         *)
(* The entire proof now is about 70 lines.  I only typed 20 of those 70    *)
(* lines.  The rest either came from the original Bakery Algorithm         *)
(* (8-line) proof or were generated by the Decompose Proof Command.        *)
(*                                                                         *)
(* I don't know how much time I actually spent writing the algorithm and   *)
(* its proof.  Except for the final compaction of the (correct) proof of   *)
(* <2>5, the entire exercise took me two days.  However, most of that was  *)
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

EXTENDS Boulanger

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

THEOREM TypeCorrect == Spec => []TypeOK
PROOF OBVIOUS

(***************************************************************************)
(* Before(i, j) is a condition that implies that num[i] > 0 and, if j is   *)
(* trying to enter its critical section and i does not change num[i], then *)
(* j either has or will choose a value of num[j] for which                 *)
(*                                                                         *)
(*     <<num[i],i>> \prec <<num[j],j>>                                     *)
(*                                                                         *)
(* is true.                                                                *)
(***************************************************************************)
Before(i,j) == /\ num[i] > 0
               /\ \/ pc[j] \in {"ncs", "e1", "exit"}
                  \/ /\ pc[j] = "e2"
                     /\ \/ i \in unchecked[j]
                        \/ max[j] >= num[i]
                        \/ (j > i) /\ (max[j] + 1 = num[i])
                  \/ /\ pc[j] = "e3"
                     /\ \/ max[j] >= num[i]
                        \/ (j > i) /\ (max[j] + 1 = num[i])
                  \/ /\ pc[j] \in {"e4", "w1", "w2"}
                     /\ <<num[i],i>> \prec <<num[j],j>>
                     /\ (pc[j] \in {"w1", "w2"}) => (i \in unchecked[j])
                  \/ /\ num[i] = 1
                     /\ i < j

(***************************************************************************)
(* Inv is the complete inductive invariant.                                *)
(***************************************************************************)  
IInv == \A i \in Procs : 
             /\ (pc[i] \in {"ncs", "e1", "e2"}) => (num[i] = 0)
             /\ (pc[i] \in {"e4", "w1", "w2", "cs"}) => (num[i] # 0)
             /\ (pc[i] \in {"e2", "e3"}) => flag[i] 
             /\ (pc[i] = "w2") => (nxt[i] # i)
             /\ (pc[i] \in {"e2", "w1", "w2"}) => i \notin unchecked[i]
             /\ (pc[i] \in {"w1", "w2"}) =>
                   \A j \in (Procs \ unchecked[i]) \ {i} : Before(i, j)
             /\ /\ pc[i] = "w2"
                /\ \/ (pc[nxt[i]] = "e2") /\ (i \notin unchecked[nxt[i]])
                   \/ pc[nxt[i]] = "e3"
                => max[nxt[i]] >= num[i]
             /\ /\ pc[i] = "w2"
                /\ previous[i] # -1 
                /\ previous[i] # num[nxt[i]]
                /\ pc[nxt[i]] \in {"e4", "w1", "w2", "cs"}
                => Before(i, nxt[i])             
             /\ (pc[i] = "cs") => \A j \in Procs \ {i} : Before(i, j)

Inv == TypeOK /\ IInv
(***************************************************************************)
(* Proof of Mutual Exclusion                                               *)
(*                                                                         *)
(* This is a standard invariance proof, where <1>2 asserts that any step   *)
(* of the algorithm (including a stuttering step) starting in a state in   *)
(* which Inv is true leaves Inv true.  Step <1>4 follows easily from       *)
(* <1>1-<1>3 by simple temporal reasoning, checked by the PTL              *)
(* (Propositional Temporal Logic) backend prover.                          *)
(***************************************************************************)
Trying(i) == pc[i] = "e1"
InCS(i)   == pc[i] = "cs"
DeadlockFree == (\E i \in Procs : Trying(i)) ~> (\E i \in Procs : InCS(i))
StarvationFree == \A i \in Procs : Trying(i) ~> InCS(i)
=============================================================================
\* Created Thu Nov 21 15:54:32 PST 2013 by lamport
