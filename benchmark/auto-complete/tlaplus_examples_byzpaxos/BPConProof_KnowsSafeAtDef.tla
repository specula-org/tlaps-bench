---------------------------- MODULE BPConProof_KnowsSafeAtDef ------------------------------
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

EXTENDS BPConProof

(***************************************************************************)
(* The sets Value and Ballot are the same as in the Voting and             *)
(* PConProof specs.                                                        *)
(***************************************************************************)

(***************************************************************************)
(* As in module PConProof, we define None to be an unspecified value that  *)
(* is not an element of Value.                                             *)
(***************************************************************************)
(***************************************************************************)
(* We pretend that which acceptors are good and which are malicious is     *)
(* specified in advance.  Of course, the algorithm executed by the good    *)
(* acceptors makes no use of which acceptors are which.  Hence, we can     *)
(* think of the sets of good and malicious acceptors as "prophecy          *)
(* constants" that are used only for showing that the algorithm implements *)
(* the PCon algorithm.                                                     *)
(*                                                                         *)
(* We can assume that a maximal set of acceptors are bad, since a bad      *)
(* acceptor is allowed to do anything--including acting like a good one.   *)
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
            (***************************************************************)
            (* A Byzantine quorum is set of acceptors that includes a      *)
            (* quorum of good ones.  In the case that there are 2f+1 good  *)
            (* acceptors and f bad ones, a Byzantine quorum is any set of  *)
            (* 2f+1 acceptors.                                             *)
            (***************************************************************)
            (***************************************************************)
            (* A weak quorum is a set of acceptors that includes at least  *)
            (* one good one.  If there are f bad acceptors, then a weak    *)
            (* quorum is any set of f+1 acceptors.                         *)
            (***************************************************************)

(***************************************************************************)
(* We define ByzAcceptor to be the set of all real or fake acceptors.      *)
(***************************************************************************)

(***************************************************************************)
(* As in the Paxos consensus algorithm, we assume that the set of ballot   *)
(* numbers and -1 is disjoint from the set of all (real and fake)          *)
(* acceptors.                                                              *)
(***************************************************************************)

(***************************************************************************)
(* The following are the assumptions about acceptors and quorums that are  *)
(* needed to ensure safety of our algorithm.                               *)
(***************************************************************************)

(***************************************************************************)
(* The following assumption is not needed for safety, but it will be       *)
(* needed to ensure liveness.                                              *)
(***************************************************************************)
(***************************************************************************)
(* We now define the set BMessage of all possible messages.                *)
(***************************************************************************)
1aMessage == [type : {"1a"},  bal : Ballot]
  (*************************************************************************)
  (* Type 1a messages are the same as in module PConProof.                 *)
  (*************************************************************************)

1cMessage ==
  (*************************************************************************)
  (* Type 1c messages are the same as in PConProof.                        *)
  (*************************************************************************)
  [type : {"1c"}, bal : Ballot, val : Value]

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

(****************************************************************************
We now give the algorithm.  The basic idea is that the set Acceptor of
real acceptors emulate an execution of the PCon algorithm with
Acceptor as its set of acceptors.  Of course, they must do that
without knowing which of the other processes in ByzAcceptor are real
acceptors and which are fake acceptors.  In addition, they don't know
whether a leader is behaving according to the PCon algorithm or if it
is malicious.

The main idea of the algorithm is that, before performing an action of
the PCon algorithm, a good acceptor determines that this action is
actually enabled in that algorithm.  Since an action is enabled by the
receipt of one or more messages, the acceptor has to determine that
the enabling messages are legal PCon messages.  Because algorithm PCon
allows a 1a message to be sent at any time, the only acceptor action
whose enabling messages must be checked is the Phase2b action.  It is
enabled iff the appropriate 1c message and 2a message are legal.  The
1c message is legal iff the leader has received the necessary 1b
messages.  The acceptor therefore maintains a set of 1b messages that
it knows have been sent, and checks that those 1b messages enable the
sending of the 1c message.

A 2a message is legal in the PCon algorithm iff (i) the corresponding
1c message is legal and (ii) it is the only 2a message that the leader
sends.  In the BPCon algorithm, there are no explicit 2a messages.
They are implicitly sent by the acceptors when they send enough 2av
messages.

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
                 the same val field (and lower bal field) removed
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
  (* The following two macros send a message and a set of messages,        *)
  (* respectively.  These macros are so simple that they're hardly worth   *)
  (* introducing, but they do make the processes a little easier to read.  *)
  (*************************************************************************)
  macro SendMessage(m) { bmsgs := bmsgs \cup {m} }
  macro SendSetOfMessages(S) { bmsgs := bmsgs \cup S }

  (*************************************************************************)
  (* As in the Paxos consensus algorithm, a ballot `self' leader (good or  *)
  (* malicious) can execute a Phase1a ation at any time.                   *)
  (*************************************************************************)
  macro Phase1a() { SendMessage([type |-> "1a", bal |-> self]) }

  (*************************************************************************)
  (* The acceptor's Phase1b ation is similar to that of the PaxosConsensus *)
  (* algorithm.                                                            *)
  (*************************************************************************)
  macro Phase1b(b) {
   when (b > maxBal[self]) /\ (sentMsgs("1a", b) # {}) ;
   maxBal[self] := b ;
   SendMessage([type |-> "1b", bal |-> b, acc |-> self, m2av |-> 2avSent[self],
                mbal |-> maxVBal[self], mval |-> maxVVal[self]])
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
      SendSetOfMessages(S) }
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
       SendMessage([type |-> "2av", bal |-> b, val |-> m.val, acc |-> self]) ;
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
        SendMessage([type |-> "2b", acc |-> self, bal |-> b, val |-> v]) ;
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
         SendMessage(m)
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

(* define statement *)

ProcSet == (Acceptor) \cup (Ballot) \cup (FakeAcceptor)

\* END TRANSLATION
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
(***************************************************************************)
(* The following lemma describes how the next-state relation Next can be   *)
(* written in terms of the actions defined above.                          *)
(***************************************************************************)
LEMMA NextDef ==
 Next <=> \/ \E self \in Acceptor :
                \E b \in Ballot : \/ Phase1b(self, b)
                                  \/ Phase2av(self, b)
                                  \/ Phase2b(self,b)
                                  \/ LearnsSent(self, b)
          \/ \E self \in Ballot : \/ Phase1a(self)
                                  \/ Phase1c(self)
          \/ \E self \in FakeAcceptor : FakingAcceptor(self)
PROOF OMITTED
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

(***************************************************************************)
(* We now define refinement mapping under which our algorithm implements   *)
(* the algorithm of module PConProof.  First, we define the set msgs that  *)
(* implements the variable of the same name in PConProof.  There are two   *)
(* non-obvious parts of the definition.                                    *)
(*                                                                         *)
(* 1.  The 1c messages in msgs should just be the ones that are            *)
(* legal--that is, messages whose value is safe at the indicated ballot.   *)
(* The obvious way to define legality is in terms of 1b messages that have *)
(* been sent.  However, this has the effect that sending a 1b message can  *)
(* add both that 1b message and one or more 1c messages to msgs.  Proving  *)
(* implementation under this refinement mapping would require adding a     *)
(* stuttering variable.  Instead, we define the 1c message to be legal if  *)
(* the set of 1b messages that some acceptor knows were sent confirms its  *)
(* legality.  Thus, those 1c messages are added to msgs by the LearnsSent  *)
(* ation, which has no other effect on the refinement mapping.             *)
(*                                                                         *)
(* 2.  A 2a message is added to msgs when a quorum of acceptors have       *)
(* reacted to it by sending a 2av message.                                 *)
(***************************************************************************)
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
(* action of the PCon algorithm.  We want PmaxBal[a] to change only        *)
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
(* maximum of S when S is nonempty, we need the following fact.            *)
(***************************************************************************)
LEMMA FiniteSetHasMax ==
        ASSUME NEW S \in SUBSET Int, IsFiniteSet(S), S # {}
        PROVE  \E max \in S : \A x \in S : max >= x
PROOF OMITTED

(***************************************************************************)
(* Our proofs use this property of MaxBallot.                              *)
(***************************************************************************)
THEOREM MaxBallotProp  ==
  ASSUME NEW S \in SUBSET (Ballot \cup {-1}),
         IsFiniteSet(S)
  PROVE  IF S = {} THEN MaxBallot(S) = -1
                   ELSE /\ MaxBallot(S) \in S
                        /\ \A x \in S : MaxBallot(S) >= x
PROOF OMITTED

(***************************************************************************)
(* We now prove a couple of lemmas about MaxBallot.                        *)
(***************************************************************************)
LEMMA MaxBallotLemma1 ==
        ASSUME NEW S \in SUBSET (Ballot \cup {-1}),
               IsFiniteSet(S),
               NEW y \in S, \A x \in S : y >= x
        PROVE  y = MaxBallot(S)
PROOF OMITTED

LEMMA MaxBallotLemma2 ==
  ASSUME NEW S \in SUBSET (Ballot \cup {-1}),
         NEW T \in SUBSET (Ballot \cup {-1}),
         IsFiniteSet(S), IsFiniteSet(T)
  PROVE  MaxBallot(S \cup T) = IF MaxBallot(S) >= MaxBallot(T)
                               THEN MaxBallot(S) ELSE MaxBallot(T)
PROOF OMITTED

(***************************************************************************)
(* We finally come to our definition of PmaxBal, the state function        *)
(* substituted for variable maxBal of module PConProof by our refinement   *)
(* mapping.  We also prove a couple of lemmas about PmaxBal.               *)
(***************************************************************************)

1bOr2bMsgs == {m \in bmsgs : m.type \in {"1b", "2b"}}

PmaxBal == [a \in Acceptor |->
              MaxBallot({m.bal : m \in {ma \in 1bOr2bMsgs :
                                           ma.acc = a}})]

LEMMA PmaxBalLemma1 ==
         ASSUME NEW m ,
                bmsgs' = bmsgs \cup {m},
                m.type # "1b" /\ m.type # "2b"
         PROVE  PmaxBal' = PmaxBal
PROOF OMITTED

LEMMA PmaxBalLemma2 ==
        ASSUME NEW m,
               bmsgs' = bmsgs \cup {m},
               NEW a \in Acceptor,
               m.acc # a
        PROVE  PmaxBal'[a] = PmaxBal[a]
PROOF OMITTED

(***************************************************************************)
(* Finally, we define the refinement mapping.  As before, for any operator *)
(* op defined in module PConProof, the following INSTANCE statement        *)
(* defines P!op to be the operator obtained from op by the indicated       *)
(* substitutions, along with the implicit substitutions                    *)
(*                                                                         *)
(*     Acceptor <- Acceptor,                                               *)
(*     Quorum   <- Quorum                                                  *)
(*     Value    <- Value                                                   *)
(*     maxVBal  <- maxVBal                                                 *)
(*     maxVVal  <- maxVVal                                                 *)
(*     msgs     <- msgs                                                    *)
(***************************************************************************)
P == INSTANCE PConProof WITH maxBal <- PmaxBal
(***************************************************************************)
(* We now define the inductive invariant Inv used in our proof.  It is     *)
(* defined to be the conjunction of a number of separate invariants that   *)
(* we define first, starting with the ever-present type-correctness        *)
(* invariant.                                                              *)
(***************************************************************************)
TypeOK == /\ maxBal  \in [Acceptor -> Ballot \cup {-1}]
          /\ 2avSent \in [Acceptor -> SUBSET [val : Value, bal : Ballot]]
          /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVVal \in [Acceptor -> Value \cup {None}]
          /\ knowsSent \in [Acceptor -> SUBSET 1bMessage]
          /\ bmsgs \subseteq BMessage

(***************************************************************************)
(* To use the definition of PmaxBal, we need to know that the set of 1b    *)
(* and 2b messages in bmsgs is finite.  This is asserted by the following  *)
(* invariant.  Note that the set bmsgs is not necessarily finite because   *)
(* we allow a Phase1c action to send an infinite number of 1c messages.    *)
(***************************************************************************)
bmsgsFinite == IsFiniteSet(1bOr2bMsgs)

(***************************************************************************)
(* The following lemma is used to prove the invariance of bmsgsFinite.     *)
(***************************************************************************)
LEMMA FiniteMsgsLemma ==
        ASSUME NEW m, bmsgsFinite, bmsgs' = bmsgs \cup {m}
        PROVE  bmsgsFinite'
PROOF OMITTED

(***************************************************************************)
(* Invariant 1bInv1 asserts that if (good) acceptor `a' has mCBal[a] # -1, *)
(* then there is a 1c message for ballot mCBal[a] and value mCVal[a] in    *)
(* the emulated execution of algorithm PCon.                               *)
(***************************************************************************)
1bInv1 == \A m \in bmsgs  :
             /\ m.type = "1b"
             /\ m.acc \in Acceptor
             => \A r \in m.m2av :
                [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs

(***************************************************************************)
(* Invariant 1bInv2 asserts that an acceptor sends at most one 1b message  *)
(* for any ballot.                                                         *)
(***************************************************************************)
1bInv2 == \A m1, m2 \in bmsgs  :
             /\ m1.type = "1b"
             /\ m2.type = "1b"
             /\ m1.acc \in Acceptor
             /\ m1.acc = m2.acc
             /\ m1.bal = m2.bal
             => m1 = m2

(***************************************************************************)
(* Invariant 2avInv1 asserts that an acceptor sends at most one 2av        *)
(* message in any ballot.                                                  *)
(***************************************************************************)
2avInv1 == \A m1, m2 \in bmsgs :
             /\ m1.type = "2av"
             /\ m2.type = "2av"
             /\ m1.acc \in Acceptor
             /\ m1.acc = m2.acc
             /\ m1.bal = m2.bal
             => m1 = m2

(***************************************************************************)
(* Invariant 2avInv2 follows easily from the meaning (and setting) of      *)
(* 2avSent.                                                                *)
(***************************************************************************)
2avInv2 == \A m \in bmsgs :
             /\ m.type = "2av"
             /\ m.acc \in Acceptor
             => \E r \in 2avSent[m.acc] : /\ r.val = m.val
                                          /\ r.bal >= m.bal

(***************************************************************************)
(* Invariant 2avInv3 asserts that an acceptor sends a 2av message only if  *)
(* the required 1c message exists in the emulated execution of             *)
(* algorithm PConf.                                                        *)
(***************************************************************************)
2avInv3 == \A m \in bmsgs :
             /\ m.type = "2av"
             /\ m.acc \in Acceptor
             => [type |-> "1c", bal |-> m.bal, val |-> m.val] \in msgs

(***************************************************************************)
(* Invariant maxBalInv is a simple consequence of the fact that an         *)
(* acceptor `a' sets maxBal[a] to b whenever it sends a 1b, 2av, or 2b     *)
(* message in ballot b.                                                    *)
(***************************************************************************)
maxBalInv == \A m \in bmsgs :
               /\ m.type \in {"1b", "2av", "2b"}
               /\ m.acc \in Acceptor
               => m.bal =< maxBal[m.acc]

(***************************************************************************)
(* Invariant accInv asserts some simple relations between the variables    *)
(* local to an acceptor, as well as the fact that acceptor `a' sets        *)
(* maxCBal[a] to b and maxCVal[a] to v only if there is a ballot-b 1c      *)
(* message for value c in the simulated execution of the PCon              *)
(* algorithm.                                                              *)
(***************************************************************************)
accInv == \A a \in Acceptor :
            \A r \in 2avSent[a] :
              /\ r.bal =< maxBal[a]
              /\ [type |-> "1c", bal |-> r.bal, val |-> r.val] \in msgs

(***************************************************************************)
(* Invariant knowsSentInv simply asserts that for any acceptor `a',        *)
(* knowsSent[a] is a set of 1b messages that have actually been sent.      *)
(***************************************************************************)
knowsSentInv == \A a \in Acceptor : knowsSent[a] \subseteq msgsOfType("1b")

Inv ==
 TypeOK /\ bmsgsFinite /\ 1bInv1 /\ 1bInv2 /\ maxBalInv  /\ 2avInv1 /\ 2avInv2
   /\ 2avInv3 /\ accInv /\ knowsSentInv
(***************************************************************************)
(* We now prove some simple lemmas that are useful for reasoning about     *)
(* PmaxBal.                                                                *)
(***************************************************************************)
LEMMA PMaxBalLemma3 ==
        ASSUME TypeOK,
               bmsgsFinite,
               NEW a \in Acceptor
        PROVE  LET S == {m.bal : m \in {ma \in bmsgs :
                                           /\ ma.type \in {"1b", "2b"}
                                           /\ ma.acc = a}}
               IN  /\ IsFiniteSet(S)
                   /\ S \in SUBSET Ballot
PROOF OMITTED

LEMMA PmaxBalLemma4 ==
        ASSUME TypeOK,
               maxBalInv,
               bmsgsFinite,
               NEW a \in Acceptor
        PROVE  PmaxBal[a] =< maxBal[a]
PROOF OMITTED

LEMMA PmaxBalLemma5 ==
        ASSUME TypeOK, bmsgsFinite, NEW a \in Acceptor
        PROVE  PmaxBal[a] \in Ballot \cup {-1}
PROOF OMITTED

(***************************************************************************)
(* Now comes a bunch of useful lemmas.                                     *)
(***************************************************************************)

(***************************************************************************)
(* We first prove that P!NextDef is a valid theorem and give it the name   *)
(* PNextDef.  This requires proving that the assumptions of module         *)
(* PConProof are satisfied by the refinement mapping.  Note that           *)
(* P!NextDef!: is an abbreviation for the statement of theorem P!NextDef   *)
(* -- that is, for the statement of theorem NextDef of module PConProof    *)
(* under the substitutions of the refinement mapping.                      *)
(***************************************************************************)
LEMMA PNextDef == P!NextDef!:
PROOF OMITTED

(***************************************************************************)
(* For convenience, we define operators corresponding to subexpressions    *)
(* that appear in the definition of KnowsSafeAt.                           *)
(***************************************************************************)
KSet(a, b) == {m \in knowsSent[a] : m.bal = b}
KS1(S) == \E BQ \in ByzQuorum : \A a \in BQ :
             \E m \in S : m.acc = a /\ m.mbal = -1
KS2(v,b,S) == \E c \in 0 .. (b-1) :
   /\ \E BQ \in ByzQuorum : \A a \in BQ :
         \E m \in S : /\ m.acc = a
                      /\ m.mbal =< c
                      /\ (m.mbal = c) => (m.mval = v)
   /\ \E WQ \in WeakQuorum : \A a \in WQ :
         \E m \in S : /\ m.acc = a
                      /\ \E r \in m.m2av : /\ r.bal >= c
                                           /\ r.val = v

(***************************************************************************)
(* The following lemma asserts the obvious relation between KnowsSafeAt    *)
(* and the top-level definitions KS1, KS2, and KSet.  The second conjunct  *)
(* is, of course, the primed version of the first.                         *)
(***************************************************************************)
LEMMA KnowsSafeAtDef ==
        \A a, b, v :
           /\ KnowsSafeAt(a, b, v) <=> KS1(KSet(a,b)) \/ KS2(v, b, KSet(a, b))
           /\ KnowsSafeAt(a, b, v)' <=> KS1(KSet(a,b)') \/ KS2(v, b, KSet(a, b)')
PROOF OBVIOUS

(***************************************************************************)
(* The following lemma is the primed version of MsgsTypeLemma.  That is,   *)
(* its statement is just the statement of MsgsTypeLemma primed.  It        *)
(* follows from MsgsTypeLemma by the meta-theorem that if we can prove a   *)
(* state-predicate F as a (top-level) theorem, then we can deduce F'. This *)
(* is an instance of propositional temporal-logic reasoning. Alternatively *)
(* the lemma could be proved using the same reasoning used for the         *)
(* unprimed version of the theorem.                                        *)
(***************************************************************************)

(***************************************************************************)
(* The following lemma describes how msgs is changed by the actions of the *)
(* algorithm.                                                              *)
(***************************************************************************)

(***************************************************************************)
(* We now come to the proof of invariance of our inductive invariant Inv.  *)
(***************************************************************************)

(***************************************************************************)
(* We next use the invariance of Inv to prove that algorithm BPCon         *)
(* implements algorithm PCon under the refinement mapping                  *)
(* defined by the INSTANCE statement above.                                *)
(***************************************************************************)
AbstractSpec == P!Spec

(***************************************************************************)
(* To see how learning is implemented, we must describe how to determine   *)
(* that a value has been chosen.  This is done by the following definition *)
(* of `chosen' to be the set of chosen values.                             *)
(***************************************************************************)
chosen == {v \in Value : \E BQ \in ByzQuorum, b \in Ballot :
                           \A a \in BQ : \E m \in msgs : /\ m.type = "2b"
                                                         /\ m.acc  = a
                                                         /\ m.bal  = b
                                                         /\ m.val  = v}
(***************************************************************************)
(* The correctness of our definition of `chosen' is expressed by the       *)
(* following theorem, which asserts that if a value is in `chosen', then   *)
(* it is also in the set `chosen' of the emulated execution of the         *)
(* PCon algorithm.                                                         *)
(*                                                                         *)
(* The state function `chosen' does not necessarily equal the              *)
(* corresponding state function of the PCon algorithm.  It                 *)
(* requires every (real or fake) acceptor in a ByzQuorum to vote for (send *)
(* 2b messages) for a value v in the same ballot for v to be in `chosen'   *)
(* for the BPCon algorithm, but it requires only that every (real)         *)
(* acceptor in a Quorum vote for v in the same ballot for v to be in the   *)
(* set `chosen' of the emulated execution of algorithm PCon.               *)
(*                                                                         *)
(* Liveness for BPCon requires that, under suitable assumptions, some      *)
(* value is eventually in `chosen'.  Since we can't assume that a fake     *)
(* acceptor does anything useful, liveness requires the assumption that    *)
(* there is a ByzQuorum composed entirely of real acceptors (the first     *)
(* conjunct of assumption BQLA).                                           *)
(***************************************************************************)

==============================================================================
