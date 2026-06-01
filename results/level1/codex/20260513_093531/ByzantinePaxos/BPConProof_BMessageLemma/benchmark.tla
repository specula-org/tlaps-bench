
---------------------------- MODULE BPConProof_BMessageLemma ------------------------------
(***************************************************************************)
(* This module specifies a Byzantine Paxos algorithm--a version of Paxos   *)
(* in which failed acceptors and leaders can be malicious.  It is an       *)
(* abstraction and generalization of the Castro-Liskov algorithm in        *)
(*                                                                         *)
(*    author = "Miguel Castro and Barbara Liskov",                         *)
(*    title = "Practical byzantine fault tolerance and proactive           *)
(*             recovery",                                                  *)
(*    journal = ACM Transactions on Computer Systems,                      *)
(*    volume = 20,                                                         *)
(*    number = 4,                                                          *)
(*    year = 2002,                                                         *)
(*    pages = "398--461"                                                   *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, TLAPS
-----------------------------------------------------------------------------
(***************************************************************************)
(* We need the following trivial axioms and theorem about finite sets.     *)
(***************************************************************************)
AXIOM EmptySetFinite == IsFiniteSet({})

AXIOM SingletonSetFinite == \A e : IsFiniteSet({e})

AXIOM ImageOfFiniteSetFinite == 
         \A S, f : IsFiniteSet(S) => IsFiniteSet({f[x] : x \in S})

AXIOM SubsetOfFiniteSetFinite == 
        \A S, T : IsFiniteSet(T) /\ (S \subseteq T) => IsFiniteSet(S)

AXIOM UnionOfFiniteSetsFinite == 
        \A S, T : IsFiniteSet(T) /\ IsFiniteSet(S)  => IsFiniteSet(S \cup T)

THEOREM OnePlusFinite == \A S, e : IsFiniteSet(S) => IsFiniteSet(S \cup {e})
  PROOF OMITTED

TestAxioms ==
   \* SingletonSetFinite
   /\ \A e \in 1..3 : IsFiniteSet({e})
   
   \* ImageOfFiniteSetFinite
   /\ \A S, T \in SUBSET (1..4): \A f \in [S -> T] : 
        IsFiniteSet(S) => IsFiniteSet({f[x] : x \in S})
        
   \* SubsetOfFiniteSetFinite
   /\ \A S, T \in SUBSET (1..4) : 
        IsFiniteSet(T) /\ (S \subseteq T) => IsFiniteSet(S)
        
   \* UnionOfFiniteSetsFinite
   /\ \A S, T \in SUBSET (1..4) : 
        IsFiniteSet(T) /\ IsFiniteSet(S)  => IsFiniteSet(S \cup T)
----------------------------------------------------------------------------
(***************************************************************************)
(* The sets Value and Ballot are the same as in the Voting and             *)
(* PaxosConsensus specs.                                                   *)
(***************************************************************************)
CONSTANT Value

Ballot == Nat

(***************************************************************************)
(* As in module PConProof, we define None to be an unspecified value that  *)
(* is not an element of Value.                                             *)
(***************************************************************************)
None == CHOOSE v : v \notin Value
-----------------------------------------------------------------------------  
(***************************************************************************)
(* We pretend that which acceptors are good and which are malicious is     *)
(* specified in advance.  Of course, the algorithm executed by the good    *)
(* acceptors makes no use of which acceptors are which.  Hence, we can     *)
(* think of the sets of good and malicious acceptors as "prophecy          *)
(* constants" that are used only for showing that the algorithm implements *)
(* the AbstratPaxosConsensus spec.                                         *)
(*                                                                         *)
(* We can assume that a maximal set of acceptors are bad, since a bad      *)
(* acceptor is allowed to do anything--including ating like a good one.    *)
(*                                                                         *)
(* The basic idea is that the good acceptors try to execute the Paxos      *)
(* consensus algorithm, while the bad acceptors may try to prevent them.   *)
(*                                                                         *)
(* We do not distinguish between faulty and non-faulty leaders.  Safety    *)
(* must be preserved even if all leaders are malicious, so we allow any    *)
(* leader to send any syntactically correct message at any time.  (In an   *)
(* implementation, syntactically incorrect messages are simply ignored by  *)
(* non-faulty acceptors and have no effect.) Assumptions about leader      *)
(* behavior are required only for liveness.                                *)
(***************************************************************************)
CONSTANTS Acceptor,       \* The set of good (non-faulty) acceptors.
          FakeAcceptor,   \* The set of possibly malicious (faulty) acceptors.
          ByzQuorum,     
            (***************************************************************)
            (* A Byzantine quorum is set of acceptors that includes a      *)
            (* quorum of good ones.  In the case that there are 2f+1 good  *)
            (* acceptors and f bad ones, a Byzantine quorum is any set of  *)
            (* 2f+1 acceptors.                                             *)
            (***************************************************************)
          WeakQuorum     
            (***************************************************************)
            (* A weak quorum is a set of acceptors that includes at least  *)
            (* one good one.  If there are f bad acceptors, then a weak    *)
            (* quorum is any set of f+1 acceptors.                         *)
            (***************************************************************)

(***************************************************************************)
(* We define ByzAcceptor to be the set of all real or fake acceptors.      *)
(***************************************************************************)
ByzAcceptor == Acceptor \cup FakeAcceptor

(***************************************************************************)
(* As in the Paxos consensus algorithm, we assume that the set of ballot   *)
(* numbers and -1 is disjoint from the set of all (real and fake)          *)
(* acceptors.                                                              *)
(***************************************************************************)
ASSUME BallotAssump == (Ballot \cup {-1}) \cap ByzAcceptor = {}

(***************************************************************************)
(* The following are the assumptions about acceptors and quorums that are  *)
(* needed to ensure safety of our algorithm.                               *)
(***************************************************************************)
ASSUME BQA == 
          /\ Acceptor \cap FakeAcceptor = {}
          /\ \A Q \in ByzQuorum : Q \subseteq ByzAcceptor
          /\ \A Q1, Q2 \in ByzQuorum : Q1 \cap Q2 \cap Acceptor # {}
          /\ \A Q \in WeakQuorum : /\ Q \subseteq ByzAcceptor
                                   /\ Q \cap Acceptor # {}

(***************************************************************************)
(* The following assumption is not needed for safety, but it will be       *)
(* needed to ensure liveness.                                              *)
(***************************************************************************)
ASSUME BQLA == 
          /\ \E Q \in ByzQuorum : Q \subseteq Acceptor 
          /\ \E Q \in WeakQuorum : Q \subseteq Acceptor 
-----------------------------------------------------------------------------
(***************************************************************************)
(* We now define the set BMessage of all possible messages.                *)
(***************************************************************************)
1aMessage == [type : {"1a"},  bal : Ballot]
  (*************************************************************************)
  (* Type 1a messages are the same as in module PConProof.                 *)
  (*************************************************************************)
  
1bMessage == 
  (*************************************************************************)
  (* A 1b message serves the same function as a 1b message in ordinary     *)
  (* Paxos, where the mbal and mval components correspond to the mbal and  *)
  (* mval components in the 1b messages of PConProof.  The m2av component  *)
  (* is set containing all records with val and bal components equal to    *)
  (* the corresponding of components of a 2av message that the acceptor    *)
  (* has sent, except containing for each val only the record              *)
  (* corresponding to the 2av message with the highest bal component.      *)
  (*************************************************************************)
  [type : {"1b"}, bal : Ballot, 
   mbal : Ballot \cup {-1}, mval : Value \cup {None},
   m2av : SUBSET [val : Value, bal : Ballot],
   acc : ByzAcceptor]

1cMessage == 
  (*************************************************************************)
  (* Type 1c messages are the same as in PConProof.                        *)
  (*************************************************************************)
  [type : {"1c"}, bal : Ballot, val : Value] 

2avMessage ==
  (*************************************************************************)
  (* When an acceptor receives a 1c message, it relays that message's      *)
  (* contents to the other acceptors in a 2av message.  It does this only  *)
  (* for the first 1c message it receives for that ballot; it can receive  *)
  (* a second 1c message only if the leader is malicious, in which case it *)
  (* ignores that second 1c message.                                       *)
  (*************************************************************************)
   [type : {"2av"}, bal : Ballot, val : Value, acc : ByzAcceptor]

2bMessage == [type : {"2b"}, acc : ByzAcceptor, bal : Ballot, val : Value]
  (*************************************************************************)
  (* 2b messages are the same as in ordinary Paxos.                        *)
  (*************************************************************************)

BMessage == 
  1aMessage \cup 1bMessage \cup 1cMessage \cup 2avMessage \cup 2bMessage

(***************************************************************************)
(* We will need the following simple fact about these sets of messages.    *)
(***************************************************************************)
LEMMA BMessageLemma ==
         \A m \in BMessage :
           /\ (m \in 1aMessage) <=>  (m.type = "1a")
           /\ (m \in 1bMessage) <=>  (m.type = "1b")
           /\ (m \in 1cMessage) <=>  (m.type = "1c")
           /\ (m \in 2avMessage) <=>  (m.type = "2av")
           /\ (m \in 2bMessage) <=>  (m.type = "2b")
PROOF OBVIOUS

==============================================================================