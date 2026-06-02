------------------------------- MODULE Voting_QuorumNonEmpty ------------------------------- 
(***************************************************************************)
(* This is a high-level algorithm in which a set of processes              *)
(* cooperatively choose a value.                                           *)
(***************************************************************************)
EXTENDS Integers, TLAPS
-----------------------------------------------------------------------------
CONSTANT Value,     \* The set of choosable values.
         Acceptor,  \* A set of processes that will choose a value.
         Quorum     \* The set of "quorums", where a quorum" is a 
                    \*   "large enough" set of acceptors

(***************************************************************************)
(* Here are the assumptions we make about quorums.                         *)
(***************************************************************************)
ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Acceptor
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}  

THEOREM QuorumNonEmpty == \A Q \in Quorum : Q # {}
PROOF OBVIOUS

=============================================================================