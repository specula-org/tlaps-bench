---------------------------- MODULE BPConProofModel ------------------------------

EXTENDS Integers, FiniteSets, FiniteSetTheorems, TLAPS

CONSTANT Value

Ballot == Nat

None == CHOOSE v : v \notin Value

CONSTANTS Acceptor,       
          FakeAcceptor,   
          ByzQuorum,

          WeakQuorum

ByzAcceptor == Acceptor \cup FakeAcceptor

ASSUME BallotAssump == (Ballot \cup {-1}) \cap ByzAcceptor = {}

ASSUME BQA ==
          /\ Acceptor \cap FakeAcceptor = {}
          /\ \A Q \in ByzQuorum : Q \subseteq ByzAcceptor
          /\ \A Q1, Q2 \in ByzQuorum : Q1 \cap Q2 \cap Acceptor # {}
          /\ \A Q \in WeakQuorum : /\ Q \subseteq ByzAcceptor
                                   /\ Q \cap Acceptor # {}

ASSUME BQLA ==
          /\ \E Q \in ByzQuorum : Q \subseteq Acceptor
          /\ \E Q \in WeakQuorum : Q \subseteq Acceptor

1bMessage ==

  [type : {"1b"}, bal : Ballot,
   mbal : Ballot \cup {-1}, mval : Value \cup {None},
   m2av : SUBSET [val : Value, bal : Ballot],
   acc : ByzAcceptor]

2avMessage ==

   [type : {"2av"}, bal : Ballot, val : Value, acc : ByzAcceptor]

2bMessage == [type : {"2b"}, acc : ByzAcceptor, bal : Ballot, val : Value]

=============================================================================
