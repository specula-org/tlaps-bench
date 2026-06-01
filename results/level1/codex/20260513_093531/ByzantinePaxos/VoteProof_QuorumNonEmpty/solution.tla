----------------------------- MODULE VoteProof_QuorumNonEmpty ------------------------------ 
(***************************************************************************)
(* This is a high-level consensus algorithm in which a set of processes    *)
(* called `acceptors' cooperatively choose a value.  The algorithm uses    *)
(* numbered ballots, where a ballot is a round of voting.  Acceptors cast  *)
(* votes in ballots, casting at most one vote per ballot.  A value is      *)
(* chosen when a large enough set of acceptors, called a `quorum', have    *)
(* all voted for the same value in the same ballot.                        *)
(*                                                                         *)
(* Ballots are not executed in order.  Different acceptors may be          *)
(* concurrently performing actions for different ballots.                  *)
(***************************************************************************)
EXTENDS Integers , FiniteSets, TLC, TLAPS

\* THEOREM SMT == TRUE (*{ by (smt) }*)
-----------------------------------------------------------------------------
CONSTANT Value,     \* As in module Consensus, the set of choosable values.
         Acceptor,  \* The set of all acceptors.
         Quorum     \* The set of all quorums.
 
(***************************************************************************)
(* The following assumption asserts that a quorum is a set of acceptors,   *)
(* and the fundamental assumption we make about quorums: any two quorums   *)
(* have a non-empty intersection.                                          *)
(***************************************************************************)
ASSUME QA == /\ \A Q \in Quorum : Q \subseteq Acceptor
             /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}  
 
THEOREM QuorumNonEmpty == \A Q \in Quorum : Q # {}
PROOF
  <1>1. SUFFICES ASSUME NEW Q \in Quorum
                  PROVE Q # {}
    OBVIOUS
  <1>2. \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}
    BY QA DEF QA
  <1>3. Q \cap Q # {}
    BY <1>2
  <1> QED
    BY <1>3

===============================================================================
