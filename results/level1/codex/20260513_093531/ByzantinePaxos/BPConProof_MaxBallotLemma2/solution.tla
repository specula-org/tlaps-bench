
---------------------------- MODULE BPConProof_MaxBallotLemma2 ------------------------------
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
  PROOF OMITTED

-----------------------------------------------------------------------------


(****************************************************************************
We now give the algorithm.  The basic idea is that the set Acceptor of
real acceptors emulate an execution of the PaxosConsensus algorithm
with Acceptor as its set of acceptors.  Of course, they must do that
without knowing which of the other processes in ByzAcceptor are real
acceptors and which are fake acceptors.  In addition, they don't know
whether a leader is behaving according to the PaxosConsensus algorithm
or if it is malicious.

The main idea of the algorithm is that, before performing an action of
the PaxosConsensus algorithm, a good acceptor determines that this
action is actually enabled in that algorithm.  Since an action is
enabled by the receipt of one or more messages, the acceptor has to
determine that the enabling messages are legal PaxosConsensus messages.
Because PaxosConsensus allows a 1a message to be sent at any time, the
only acceptor action whose enabling messages must be checked is the
Phase2b action.  It is enabled iff the appropriate 1c message and 2a
message are legal.  The 1c message is legal iff the leader has received
the necessary 1b messages.  The acceptor therefore maintains a set of
1b messages that it knows have been sent, and checks that those 1b
messages enable the sending of the 1c message.

A 2a message is legal in the PaxosConsensus algorithm iff (i) the
corresponding 1c message is legal and (ii) it is the only 2a message
that the leader sends.  In the BPCon algorithm, there are no 
explicit 2a messages.  They are implicitly sent by the acceptors
when they send enough 2av messages.

We leave unspecified how an acceptor discovers what 1b messages have
been sent.  In the Castro-Liskov algorithm, this is done by having
acceptors relay messages sent by other acceptors.  An acceptor knows
that a 1b message has been sent if it receives it directly or else
receives a copy from a weak Byzantine quorum of acceptors.  A
(non-malicious) leader must determine what 1b messages acceptors know
about so it chooses a value so that a quorum of acceptors will act on
its Phase1c message and cause that value to be chosen.  However, this
is necessary only for liveness, so we ignore this for now.

In other implementations of our algorithm, the leader sends along with
the 1c message a proof that the necessary 1b messages have been sent.
The easiest way to do this is to have acceptors digitally sign their 1b
messages, so a copy of the message proves that it has been sent (by the
acceptor indicated in the message's acc field).  The necessary proofs
can also be constructed using only message authenticators (like the
ones used in the Castro-Liskov algorithm); how this is done is
described elsewhere.

In the abstract algorithm presented here, which we call
BPCon, we do not specify how acceptors learn what 1b
messages have been sent.  We simply introduce a variable knowsSent such
that knowsSent[a] represents the set of 1b messages that (good)
acceptor a knows have been sent, and have an action that
nondeterministically adds sent 1b messages to this set.

--algorithm BPCon {
  (**************************************************************************
The variables:

    maxBal[a]  = Highest ballot in which acceptor a has participated.

    maxVBal[a] = Highest ballot in which acceptor a has cast a vote
                 (sent a 2b message); or -1 if it hasn't cast a vote.

    maxVVal[a] = Value acceptor a has voted for in ballot maxVBal[a],
                  or None if maxVBal[a] = -1.

    2avSent[a] = A set of records in [val : Value, bal : Ballot] 
                 describing the 2av messages that a has sent.  A
                 record is added to this set, and any element with
                 a the same val field (and lower bal field) removed 
                 when a sends a 2av message.

    knownSent[a] = The set of 1b messages that acceptor a knows have
                   been sent.

    bmsgs = The set of all messages that have been sent.  See the
            discussion of the msgs variable in module PConProof
            to understand our modeling of message passing.
  **************************************************************************)
  variables maxBal  = [a \in Acceptor |-> -1],
            maxVBal = [a \in Acceptor |-> -1] ,
            maxVVal = [a \in Acceptor |-> None] ,
            2avSent = [a \in Acceptor |-> {}],
            knowsSent = [a \in Acceptor |-> {}],
            bmsgs = {} 
  define {
    sentMsgs(type, bal) == {m \in bmsgs: m.type = type /\ m.bal = bal}
    
    KnowsSafeAt(ac, b, v) ==
      (*********************************************************************)
      (* True for an acceptor ac, ballot b, and value v iff the set of 1b  *)
      (* messages in knowsSent[ac] implies that value v is safe at ballot  *)
      (* b in the PaxosConsensus algorithm being emulated by the good      *)
      (* acceptors.  To understand the definition, see the definition of   *)
      (* ShowsSafeAt in module PConProof and recall (a) the meaning of the *)
      (* mCBal and mCVal fields of a 1b message and (b) that the set of    *)
      (* real acceptors in a ByzQuorum forms a quorum of the               *)
      (* PaxosConsensus algorithm.                                         *)
      (*********************************************************************)
      LET S == {m \in knowsSent[ac] : m.bal = b}
      IN  \/ \E BQ \in ByzQuorum : 
               \A a \in BQ : \E m \in S : /\ m.acc = a 
                                          /\ m.mbal = -1
          \/ \E c \in 0..(b-1):
               /\ \E BQ \in ByzQuorum : 
                    \A a \in BQ : \E m \in S : /\ m.acc = a
                                               /\ m.mbal =< c
                                               /\ (m.mbal = c) => (m.mval = v)
               /\ \E WQ \in WeakQuorum :
                    \A a \in WQ : 
                      \E m \in S : /\ m.acc = a
                                   /\ \E r \in m.m2av : /\ r.bal >= c
                                                        /\ r.val = v
   }

  (*************************************************************************)
  (* We now describe the processes' actions as macros.                     *)
  (*                                                                       *)
  (* As in the Paxos consensus algorithm, a ballot `self' leader (good or  *)
  (* malicious) can execute a Phase1a ation at any time.                   *)
  (*************************************************************************)
  macro Phase1a() { bmsgs := bmsgs \cup {[type |-> "1a", bal |-> self]} ; }

  (*************************************************************************)
  (* The acceptor's Phase1b ation is similar to that of the PaxosConsensus *)
  (* algorithm.                                                            *)
  (*************************************************************************)
  macro Phase1b(b) {
   when (b > maxBal[self]) /\ (sentMsgs("1a", b) # {}) ;
   maxBal[self] := b ;
   bmsgs := bmsgs \cup {[type  |-> "1b", bal |-> b, acc |-> self,
                         m2av |-> 2avSent[self],
                         mbal |-> maxVBal[self], mval |-> maxVVal[self]]};
   }

  (*************************************************************************)
  (* A good ballot `self' leader can send a phase 1c message for value v   *)
  (* if it knows that the messages in knowsSent[a] for a Quorum of (good)  *)
  (* acceptors imply that they know that v is safe at ballot `self', and   *)
  (* that they can convince any other acceptor that the appropriate 1b     *)
  (* messages have been sent to that it will also know that v is safe at   *)
  (* ballot `self'.                                                        *)
  (*                                                                       *)
  (* A malicious ballot `self' leader can send any phase 1c messages it    *)
  (* wants (including one that a good leader could send).  We prove safety *)
  (* with a Phase1c ation that allows a leader to be malicious.  To prove  *)
  (* liveness, we will have to assume a good leader that sends only        *)
  (* correct 1c messages.                                                  *)
  (*                                                                       *)
  (* As in the PaxosConsensus algorithm, we allow a Phase1c action to send *)
  (* a set of Phase1c messages.  (This is not done in the Castro-Liskov    *)
  (* algorithm, but seems natural in light of the PaxosConsensus           *)
  (* algorithm.)                                                           *)
  (*************************************************************************)
  macro Phase1c() {
    with (S \in SUBSET [type : {"1c"}, bal : {self}, val : Value]) {  
      bmsgs := bmsgs \cup S }
   }

  (*************************************************************************)
  (* If acceptor `self' receives a ballot b phase 1c message with value v, *)
  (* it relays v in a phase 2av message if                                 *)
  (*                                                                       *)
  (*   - it has not already sent a 2av message in this or a later          *)
  (*     ballot and                                                        *)
  (*                                                                       *)
  (*   - the messages in knowsSent[self] show it that v is safe at b in    *)
  (*     the non-Byzantine Paxos consensus algorithm being emulated.       *)
  (*************************************************************************)
  macro Phase2av(b) {
    when /\ maxBal[self] =< b  
         /\ \A r \in 2avSent[self] : r.bal < b ;
            \* We could just as well have used r.bal # b in this condition.
    with (m \in {ms \in sentMsgs("1c", b) : KnowsSafeAt(self, b, ms.val)}) {
       bmsgs := bmsgs \cup 
                 {[type |-> "2av", bal |-> b, val |-> m.val, acc |-> self]};
       2avSent[self] :=  {r \in 2avSent[self] : r.val # m.val} 
                           \cup {[val |-> m.val, bal |-> b]}
      } ;
    maxBal[self]  := b ;
   }

  (*************************************************************************)
  (* Acceptor `self' can send a phase 2b message with value v if it has    *)
  (* received phase 2av messages from a Byzantine quorum, which implies    *)
  (* that a quorum of good acceptors assert that this is the first 1c      *)
  (* message sent by the leader and that the leader was allowed to send    *)
  (* that message.  It sets maxBal[self], maxVBal[self], and maxVVal[self] *)
  (* as in the non-Byzantine algorithm.                                    *)
  (*************************************************************************)
  macro Phase2b(b) {
    when maxBal[self] =< b ;
    with (v \in {vv \in Value : 
                   \E Q \in ByzQuorum :
                      \A aa \in Q : 
                         \E m \in sentMsgs("2av", b) : /\ m.val = vv
                                                       /\ m.acc = aa} ) {
        bmsgs := bmsgs \cup 
                  {[type |-> "2b", acc |-> self, bal |-> b, val |-> v]} ;
        maxVVal[self] := v ;
      } ;
    maxBal[self] := b ;
    maxVBal[self] := b
   }
  
  (*************************************************************************)
  (* At any time, an acceptor can learn that some set of 1b messages were  *)
  (* sent (but only if they atually were sent).                            *)
  (*************************************************************************)
  macro LearnsSent(b) {
    with (S \in SUBSET sentMsgs("1b", b)) {
       knowsSent[self] := knowsSent[self] \cup S
     }
   }
  (*************************************************************************)
  (* A malicious acceptor `self' can send any acceptor message indicating  *)
  (* that it is from itself.  Since a malicious acceptor could allow other *)
  (* malicious processes to forge its messages, this action could          *)
  (* represent the sending of the message by any malicious process.        *)
  (*************************************************************************)
  macro FakingAcceptor() {
    with ( m \in { mm \in 1bMessage \cup 2avMessage \cup 2bMessage : 
                   mm.acc = self} ) {
         bmsgs := bmsgs \cup {m}
     }
   }
  
  (*************************************************************************)
  (* We combine these individual actions into a complete algorithm in the  *)
  (* usual way, with separate process declarations for the acceptor,       *)
  (* leader, and fake acceptor processes.                                  *)
  (*************************************************************************)
  process (acceptor \in Acceptor) {
    acc: while (TRUE) { 
           with (b \in Ballot) {either Phase1b(b) or Phase2av(b) 
                                  or Phase2b(b) or LearnsSent(b)}
    }
   }

  process (leader \in Ballot) {
    ldr: while (TRUE) {
          either Phase1a() or Phase1c() 
         }
   }

  process (facceptor \in FakeAcceptor) {
     facc : while (TRUE) { FakingAcceptor() }
   }
}

Below is the TLA+ translation, as produced by the translator.  (Some
blank lines have been removed.)
**************************************************************************)
\* BEGIN TRANSLATION
VARIABLES maxBal, maxVBal, maxVVal, 2avSent, knowsSent, bmsgs

(* define statement *)
sentMsgs(type, bal) == {m \in bmsgs: m.type = type /\ m.bal = bal}

KnowsSafeAt(ac, b, v) ==
  LET S == {m \in knowsSent[ac] : m.bal = b}
  IN  \/ \E BQ \in ByzQuorum :
           \A a \in BQ : \E m \in S : /\ m.acc = a
                                      /\ m.mbal = -1
      \/ \E c \in 0..(b-1):
           /\ \E BQ \in ByzQuorum :
                \A a \in BQ : \E m \in S : /\ m.acc = a
                                           /\ m.mbal =< c
                                           /\ (m.mbal = c) => (m.mval = v)
           /\ \E WQ \in WeakQuorum :
                \A a \in WQ :
                  \E m \in S : /\ m.acc = a
                               /\ \E r \in m.m2av : /\ r.bal >= c
                                                    /\ r.val = v

vars == << maxBal, maxVBal, maxVVal, 2avSent, knowsSent, bmsgs >>

ProcSet == (Acceptor) \cup (Ballot) \cup (FakeAcceptor)

Init == (* Global variables *)
        /\ maxBal = [a \in Acceptor |-> -1]
        /\ maxVBal = [a \in Acceptor |-> -1]
        /\ maxVVal = [a \in Acceptor |-> None]
        /\ 2avSent = [a \in Acceptor |-> {}]
        /\ knowsSent = [a \in Acceptor |-> {}]
        /\ bmsgs = {}

acceptor(self) == \E b \in Ballot:
                    \/ /\ (b > maxBal[self]) /\ (sentMsgs("1a", b) # {})
                       /\ maxBal' = [maxBal EXCEPT ![self] = b]
                       /\ bmsgs' = (bmsgs \cup {[type  |-> "1b", bal |-> b, acc |-> self,
                                                 m2av |-> 2avSent[self],
                                                 mbal |-> maxVBal[self], mval |-> maxVVal[self]]})
                       /\ UNCHANGED <<maxVBal, maxVVal, 2avSent, knowsSent>>
                    \/ /\ /\ maxBal[self] =< b
                          /\ \A r \in 2avSent[self] : r.bal < b
                       /\ \E m \in {ms \in sentMsgs("1c", b) : KnowsSafeAt(self, b, ms.val)}:
                            /\ bmsgs' = (bmsgs \cup
                                          {[type |-> "2av", bal |-> b, val |-> m.val, acc |-> self]})
                            /\ 2avSent' = [2avSent EXCEPT ![self] = {r \in 2avSent[self] : r.val # m.val}
                                                                      \cup {[val |-> m.val, bal |-> b]}]
                       /\ maxBal' = [maxBal EXCEPT ![self] = b]
                       /\ UNCHANGED <<maxVBal, maxVVal, knowsSent>>
                    \/ /\ maxBal[self] =< b
                       /\ \E v \in {vv \in Value :
                                      \E Q \in ByzQuorum :
                                         \A aa \in Q :
                                            \E m \in sentMsgs("2av", b) : /\ m.val = vv
                                                                          /\ m.acc = aa}:
                            /\ bmsgs' = (bmsgs \cup
                                          {[type |-> "2b", acc |-> self, bal |-> b, val |-> v]})
                            /\ maxVVal' = [maxVVal EXCEPT ![self] = v]
                       /\ maxBal' = [maxBal EXCEPT ![self] = b]
                       /\ maxVBal' = [maxVBal EXCEPT ![self] = b]
                       /\ UNCHANGED <<2avSent, knowsSent>>
                    \/ /\ \E S \in SUBSET sentMsgs("1b", b):
                            knowsSent' = [knowsSent EXCEPT ![self] = knowsSent[self] \cup S]
                       /\ UNCHANGED <<maxBal, maxVBal, maxVVal, 2avSent, bmsgs>>

leader(self) == /\ \/ /\ bmsgs' = (bmsgs \cup {[type |-> "1a", bal |-> self]})
                   \/ /\ \E S \in SUBSET [type : {"1c"}, bal : {self}, val : Value]:
                           bmsgs' = (bmsgs \cup S)
                /\ UNCHANGED << maxBal, maxVBal, maxVVal, 2avSent, knowsSent >>

facceptor(self) == /\ \E m \in { mm \in 1bMessage \cup 2avMessage \cup 2bMessage :
                                 mm.acc = self}:
                        bmsgs' = (bmsgs \cup {m})
                   /\ UNCHANGED << maxBal, maxVBal, maxVVal, 2avSent, 
                                   knowsSent >>

Next == (\E self \in Acceptor: acceptor(self))
           \/ (\E self \in Ballot: leader(self))
           \/ (\E self \in FakeAcceptor: facceptor(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION
-----------------------------------------------------------------------------
(***************************************************************************)
(* As in module PConProof, we now rewrite the next-state relation in a     *)
(* form more convenient for writing proofs.                                *)
(***************************************************************************)
Phase1b(self, b) == 
  /\ (b > maxBal[self]) /\ (sentMsgs("1a", b) # {})
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ bmsgs' = bmsgs \cup {[type  |-> "1b", bal |-> b, acc |-> self,
                           m2av |-> 2avSent[self],
                           mbal |-> maxVBal[self], mval |-> maxVVal[self]]}
  /\ UNCHANGED <<maxVBal, maxVVal, 2avSent, knowsSent>>

Phase2av(self, b) == 
  /\ maxBal[self] =< b
  /\ \A r \in 2avSent[self] : r.bal < b
  /\ \E m \in {ms \in sentMsgs("1c", b) : KnowsSafeAt(self, b, ms.val)}:
       /\ bmsgs' = bmsgs \cup
                    {[type |-> "2av", bal |-> b, val |-> m.val, acc |-> self]}
       /\ 2avSent' = [2avSent EXCEPT 
                        ![self] = {r \in 2avSent[self] : r.val # m.val} 
                                    \cup {[val |-> m.val, bal |-> b]}]
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ UNCHANGED <<maxVBal, maxVVal, knowsSent>>

Phase2b(self, b) ==
  /\ maxBal[self] =< b
  /\ \E v \in {vv \in Value :
                 \E Q \in ByzQuorum :
                    \A a \in Q :
                       \E m \in sentMsgs("2av", b) : /\ m.val = vv
                                                     /\ m.acc = a }:
       /\ bmsgs' = (bmsgs \cup
                     {[type |-> "2b", acc |-> self, bal |-> b, val |-> v]})
       /\ maxVVal' = [maxVVal EXCEPT ![self] = v]
  /\ maxBal' = [maxBal EXCEPT ![self] = b]
  /\ maxVBal' = [maxVBal EXCEPT ![self] = b]
  /\ UNCHANGED <<2avSent, knowsSent>>

LearnsSent(self, b) == 
 /\ \E S \in SUBSET sentMsgs("1b", b):
       knowsSent' = [knowsSent EXCEPT ![self] = knowsSent[self] \cup S]
 /\ UNCHANGED <<maxBal, maxVBal, maxVVal, 2avSent, bmsgs>> 

Phase1a(self) == 
  /\ bmsgs' = (bmsgs \cup {[type |-> "1a", bal |-> self]})
  /\ UNCHANGED << maxBal, maxVBal, maxVVal, 2avSent, knowsSent >>

Phase1c(self) ==
  /\ \E S \in SUBSET [type : {"1c"}, bal : {self}, val : Value]:
                        bmsgs' = (bmsgs \cup S)
  /\ UNCHANGED << maxBal, maxVBal, maxVVal, 2avSent, knowsSent >>

FakingAcceptor(self) ==
  /\ \E m \in { mm \in 1bMessage \cup 2avMessage \cup 2bMessage : mm.acc = self} :
         bmsgs' = (bmsgs \cup {m})
  /\ UNCHANGED << maxBal, maxVBal, maxVVal, 2avSent, knowsSent >>
-----------------------------------------------------------------------------
(***************************************************************************)
(* The following lemma describes how the next-state relation Next can be   *)
(* written in terms of the actions defined above.                          *)
(***************************************************************************)
LEMMA NextDef == 
 Next = \/ \E self \in Acceptor :
             \E b \in Ballot : \/ Phase1b(self, b) 
                               \/ Phase2av(self, b) 
                               \/ Phase2b(self,b)
                               \/ LearnsSent(self, b) 
        \/ \E self \in Ballot : \/ Phase1a(self)
                                \/ Phase1c(self)
        \/ \E self \in FakeAcceptor : FakingAcceptor(self)
  PROOF OMITTED

-----------------------------------------------------------------------------
(***************************************************************************)
(*                        THE REFINEMENT MAPPING                           *)
(***************************************************************************)

(***************************************************************************)
(* We define a quorum to be the set of acceptors in a Byzantine quorum.    *)
(* The quorum assumption QA of module PConProof, which we here call        *)
(* QuorumTheorem, follows easily from the definition and assumption BQA.   *)
(***************************************************************************)
Quorum == {S \cap Acceptor : S \in ByzQuorum}

THEOREM QuorumTheorem == 
         /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {} 
         /\ \A Q \in Quorum : Q \subseteq Acceptor
  PROOF OMITTED

msgsOfType(t) == {m \in bmsgs : m.type = t }

acceptorMsgsOfType(t) == {m \in msgsOfType(t) : m.acc \in  Acceptor}
 
1bRestrict(m) == [type |-> "1b", acc |-> m.acc, bal |-> m.bal, 
                  mbal |-> m.mbal, mval |-> m.mval]

1bmsgs == { 1bRestrict(m) : m \in acceptorMsgsOfType("1b") }

1cmsgs == {m \in msgsOfType("1c") :
                   \E a \in Acceptor : KnowsSafeAt(a, m.bal, m.val)}

2amsgs == {m \in [type : {"2a"}, bal : Ballot, val : Value] :
             \E Q \in Quorum :
               \A a \in Q :
                 \E m2av \in acceptorMsgsOfType("2av") : 
                    /\ m2av.acc = a
                    /\ m2av.bal = m.bal
                    /\ m2av.val = m.val }

msgs == msgsOfType("1a") \cup 1bmsgs \cup 1cmsgs \cup 2amsgs 
         \cup acceptorMsgsOfType("2b")

(***************************************************************************)
(* We now define PmaxBal, the state function with which we instantiate the *)
(* variable maxBal of PConProof.  The reason we don't just instantiate it  *)
(* with the variable maxBal is that maxBal[a] can change when acceptor `a' *)
(* performs a Phase2av ation, which does not correspond to any acceptor    *)
(* action of the PConProof algorithm.  We want PmaxBal[a] to change only   *)
(* when `a' performs a Phase1b or Phase2b ation--that is, when it sends a  *)
(* 1b or 2b message.  Thus, we define PmaxBal[a] to be the largest bal     *)
(* field of all 1b and 2b messages sent by `a'.                            *)
(*                                                                         *)
(* To define PmaxBal, we need to define an operator MaxBallot so that      *)
(* MaxBallot(S) is the largest element of S if S is non-empty a finite set *)
(* consisting of ballot numbers and possibly the value -1.                 *)
(***************************************************************************)
MaxBallot(S) ==  
  IF S = {} THEN -1
            ELSE CHOOSE mb \in S : \A x \in S : mb  >= x

(***************************************************************************)
(* To prove that the CHOOSE in this definition actually does choose a      *)
(* maximum of S when S is nonempty, we need the following trivial fact.    *)
(* It has been checked by TLC with -5..5 substituted for Int.              *)
(***************************************************************************)
AXIOM FiniteSetHasMax == 
        \A S \in SUBSET Int :
          IsFiniteSet(S) /\ (S # {}) => \E max \in S : \A x \in S : max >= x

(***************************************************************************)
(* Our proofs use this property of MaxBallot.                              *)
(***************************************************************************)
THEOREM MaxBallotProp  ==
         \A S \in SUBSET (Ballot \cup {-1}) : 
            IsFiniteSet(S) => 
              IF S = {} THEN MaxBallot(S) = -1
                        ELSE /\ MaxBallot(S) \in S
                             /\ \A x \in S : MaxBallot(S) >= x
  PROOF OMITTED

LEMMA MaxBallotLemma1 ==
          \A S \in SUBSET (Ballot \cup {-1}) : 
            IsFiniteSet(S) => 
              \A y \in S :
               (\A x \in S : y >= x) => (y = MaxBallot(S))
  PROOF OMITTED

LEMMA MaxBallotLemma2 ==
         \A S, T \in SUBSET (Ballot \cup {-1}) :
            IsFiniteSet(S) /\ IsFiniteSet(T) =>
              MaxBallot(S \cup T) = IF MaxBallot(S) >= MaxBallot(T)
                                      THEN MaxBallot(S)
                                      ELSE MaxBallot(T)
PROOF
  <1>1. SUFFICES ASSUME NEW S \in SUBSET (Ballot \cup {-1}),
                        NEW T \in SUBSET (Ballot \cup {-1}),
                        IsFiniteSet(S) /\ IsFiniteSet(T)
                 PROVE  MaxBallot(S \cup T) =
                          IF MaxBallot(S) >= MaxBallot(T)
                            THEN MaxBallot(S)
                            ELSE MaxBallot(T)
    OBVIOUS
  <1>2. S \cup T \in SUBSET (Ballot \cup {-1})
    OBVIOUS
  <1>3. IsFiniteSet(S \cup T)
    BY <1>1, UnionOfFiniteSetsFinite
  <1>4. MaxBallot(S) >= -1
    <2>1. CASE S = {}
      BY <1>1, <2>1, MaxBallotProp
    <2>2. CASE S # {}
      <3>1. MaxBallot(S) \in S
        BY <1>1, <2>2, MaxBallotProp
      <3>2. MaxBallot(S) \in Ballot \cup {-1}
        BY <1>1, <3>1
      <3>3. QED BY <3>2, SMT DEF Ballot
    <2>3. QED BY <2>1, <2>2
  <1>5. MaxBallot(T) >= -1
    <2>1. CASE T = {}
      BY <1>1, <2>1, MaxBallotProp
    <2>2. CASE T # {}
      <3>1. MaxBallot(T) \in T
        BY <1>1, <2>2, MaxBallotProp
      <3>2. MaxBallot(T) \in Ballot \cup {-1}
        BY <1>1, <3>1
      <3>3. QED BY <3>2, SMT DEF Ballot
    <2>3. QED BY <2>1, <2>2
  <1>5a. MaxBallot(S) \in Int
    <2>1. CASE S = {}
      BY <1>1, <2>1, MaxBallotProp, SMT
    <2>2. CASE S # {}
      <3>1. MaxBallot(S) \in S
        BY <1>1, <2>2, MaxBallotProp
      <3>2. MaxBallot(S) \in Ballot \cup {-1}
        BY <1>1, <3>1
      <3>3. QED BY <3>2, SMT DEF Ballot
    <2>3. QED BY <2>1, <2>2
  <1>5b. MaxBallot(T) \in Int
    <2>1. CASE T = {}
      BY <1>1, <2>1, MaxBallotProp, SMT
    <2>2. CASE T # {}
      <3>1. MaxBallot(T) \in T
        BY <1>1, <2>2, MaxBallotProp
      <3>2. MaxBallot(T) \in Ballot \cup {-1}
        BY <1>1, <3>1
      <3>3. QED BY <3>2, SMT DEF Ballot
    <2>3. QED BY <2>1, <2>2
  <1>6. CASE S = {}
    <2>1. MaxBallot(S) = -1
      BY <1>1, <1>6, MaxBallotProp
    <2>2. S \cup T = T
      BY <1>6
    <2>3. CASE MaxBallot(S) >= MaxBallot(T)
      <3>1. MaxBallot(S \cup T) = MaxBallot(S)
        BY <1>5a, <1>5b, <1>5, <2>1, <2>2, <2>3, SMT
      <3>2. QED BY <2>3, <3>1
    <2>4. CASE MaxBallot(S) < MaxBallot(T)
      <3>1. MaxBallot(S \cup T) = MaxBallot(T)
        BY <2>2
      <3>2. ~(MaxBallot(S) >= MaxBallot(T))
        BY <1>5a, <1>5b, <2>4, SMT
      <3>3. QED BY <3>1, <3>2
    <2>5. MaxBallot(S) >= MaxBallot(T) \/ MaxBallot(S) < MaxBallot(T)
      BY <1>5a, <1>5b, SMT
    <2>6. QED BY <2>3, <2>4, <2>5
  <1>7. CASE T = {}
    <2>1. MaxBallot(T) = -1
      BY <1>1, <1>7, MaxBallotProp
    <2>2. S \cup T = S
      BY <1>7
    <2>3. MaxBallot(S) >= MaxBallot(T)
      BY <1>4, <2>1
    <2>4. QED BY <2>2, <2>3
  <1>8. CASE S # {} /\ T # {}
    <2>1. MaxBallot(S) \in S /\ \A x \in S : MaxBallot(S) >= x
      BY <1>1, <1>8, MaxBallotProp
    <2>2. MaxBallot(T) \in T /\ \A x \in T : MaxBallot(T) >= x
      BY <1>1, <1>8, MaxBallotProp
    <2>3. CASE MaxBallot(S) >= MaxBallot(T)
      <3>1. MaxBallot(S) \in S \cup T
        BY <2>1
      <3>2. \A x \in S \cup T : MaxBallot(S) >= x
        <4>1. SUFFICES ASSUME NEW x \in S \cup T
                         PROVE  MaxBallot(S) >= x
          OBVIOUS
        <4>2. CASE x \in S
          BY <2>1, <4>2
        <4>3. CASE x \in T
          <5>1. MaxBallot(T) >= x
            BY <2>2, <4>3
          <5>2. x \in Ballot \cup {-1}
            BY <1>1, <4>3
          <5>3. x \in Int
            BY <5>2, SMT DEF Ballot
          <5>4. QED BY <1>5a, <1>5b, <2>3, <5>1, <5>3, SMT
        <4>4. QED BY <4>1, <4>2, <4>3
      <3>3. MaxBallot(S) = MaxBallot(S \cup T)
        BY <1>2, <1>3, <3>1, <3>2, MaxBallotLemma1
      <3>4. MaxBallot(S \cup T) = MaxBallot(S)
        BY <3>3
      <3>5. QED BY <2>3, <3>4
    <2>4. CASE MaxBallot(S) < MaxBallot(T)
      <3>1. MaxBallot(T) \in S \cup T
        BY <2>2
      <3>2. \A x \in S \cup T : MaxBallot(T) >= x
        <4>1. SUFFICES ASSUME NEW x \in S \cup T
                         PROVE  MaxBallot(T) >= x
          OBVIOUS
        <4>2. CASE x \in T
          BY <2>2, <4>2
        <4>3. CASE x \in S
          <5>1. MaxBallot(S) >= x
            BY <2>1, <4>3
          <5>2. x \in Ballot \cup {-1}
            BY <1>1, <4>3
          <5>3. x \in Int
            BY <5>2, SMT DEF Ballot
          <5>4. QED BY <1>5a, <1>5b, <2>4, <5>1, <5>3, SMT
        <4>4. QED BY <4>1, <4>2, <4>3
      <3>3. MaxBallot(T) = MaxBallot(S \cup T)
        BY <1>2, <1>3, <3>1, <3>2, MaxBallotLemma1
      <3>4. MaxBallot(S \cup T) = MaxBallot(T)
        BY <3>3
      <3>5. ~(MaxBallot(S) >= MaxBallot(T))
        BY <1>5a, <1>5b, <2>4, SMT
      <3>6. QED BY <3>4, <3>5
    <2>5. MaxBallot(S) >= MaxBallot(T) \/ MaxBallot(S) < MaxBallot(T)
      BY <1>5a, <1>5b, SMT
    <2>6. QED BY <2>3, <2>4, <2>5
  <1>9. S = {} \/ T = {} \/ (S # {} /\ T # {})
    OBVIOUS
  <1>10. QED BY <1>6, <1>7, <1>8, <1>9

==============================================================================
