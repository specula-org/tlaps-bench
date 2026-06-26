------------------------------ MODULE TPaxosWithProof_PrepareMsgInv --------------------------------
(*
Specification of the consensus protocol in PaxosStore.
See [PaxosStore@VLDB2017](https://www.vldb.org/pvldb/vol10/p1730-lin.pdf)
by Tencent.
In this version (adopted from "PaxosStore.tla"):
- Client-restricted config (Ballot)
- Message types (i.e., "Prepare", "Accept", "ACK") are deleted.
No state flags (such as "Prepare", "Wait-Prepare", "Accept", "Wait-Accept"
are needed.
- Choose value from a quorum in Accept.
*)
EXTENDS TPaxosWithProof

LEMMA NoneNotAValue == None \notin Value
PROOF OMITTED

AllBallot == Ballot \cup {-1}
AllValue == Value \cup {None}
MaxBallot == Cardinality(Ballot) - 1

State == [maxBal: Ballot \cup {-1},
         maxVBal: Ballot \cup {-1}, maxVVal: Value \cup {None}]

(*
For simplicity, in this specification, we choose to send the complete state
of a participant each time. When receiving such a message, the participant
processes only the "partial" state it needs.
*)
Message == [from: Participant,
            to : SUBSET Participant,
            state: [Participant -> [maxBal: Ballot \cup {-1},
                                    maxVBal: Ballot \cup {-1},
                                    maxVVal: Value \cup {None}]]]

TypeOK ==
    /\ state \in [Participant -> [Participant -> State]]
\*    /\ \A p \in Participant: state[p] \in [Participant -> State]
\*    /\ \A p \in Participant, q \in Participant:
\*            /\ state[p][q].maxBal \in AllBallot
\*            /\ state[p][q].maxVBal \in AllBallot
\*            /\ state[p][q].maxVVal \in AllValue
    /\ msgs \subseteq Message

(*
p \in Participant starts the prepare phase by issuing a ballot b \in Ballot.
*)
(*
q \in Participant updates its own state state[q] according to the actual state
pp of p \in Participant extracted from a message m \in Message it receives.
This is called by OnMessage(q).
Note: pp is m.state[p]; it may not be equal to state[p][p] at the time
UpdateState is called.
*)
\*        [state EXCEPT
\*            ![q] = [state[q] EXCEPT
\*                       ![q] = [state[q][q] EXCEPT
\*                                 !.maxBal = maxB, \* make promise first and then accept
\*                                 !.maxVBal = (IF (maxB <= pp.maxVBal)  \* accept
\*                                             THEN pp.maxVBal ELSE @),
\*                                 !.maxVVal = (IF (maxB <= pp.maxVBal)  \* accept
\*                                             THEN pp.maxVVal ELSE @)
\*                                 !.maxVBal = IF
\*                                                (
\*                                                state[q][q].maxBal <= pp.maxVBal
\*                                                /\ pp.maxBal <= pp.maxVBal
\*                                                )
\*                                             THEN pp.maxVBal ELSE @,
\*                                 !.maxVVal = IF (
\*                                                state[q][q].maxBal <= pp.maxVBal
\*                                                /\ pp.maxBal <= pp.maxVBal
\*                                                )
\*                                             THEN pp.maxVVal ELSE @
\*                               ],
\*                      ![p] = [state[q][p] EXCEPT
\*                                !.maxBal = Max(@, pp.maxBal),
\*                                !.maxVBal = Max(@, pp.maxVBal),
\*                                !.maxVVal = (IF (state[q][p].maxVBal < pp.maxVBal)
\*                                            THEN pp.maxVVal ELSE @)
\*                              ]
\*                    ]
\*         ]
\*

\*                  ![q][p].maxBal = Max(@, pp.maxBal),
\*                  ![q][p].maxVBal = Max(@, pp.maxVBal),
\*                  ![q][p].maxVVal = IF state[q][p].maxVBal < pp.maxVBal
\*                                    THEN pp.maxVVal ELSE @,
\*                  ![q][q].maxBal = maxB, \* make promise first and then accept
\*                  ![q][q].maxVBal = IF maxB <= pp.maxVBal  \* accept
\*                                    THEN pp.maxVBal ELSE @,
\*                  ![q][q].maxVVal = IF maxB <= pp.maxVBal  \* accept
\*                                    THEN pp.maxVVal ELSE @]
(*
q \in Participant receives and processes a message in Message.
*)
\*               THEN msgs' = (msgs \ {m}) \cup {qm, nm}
\*               ELSE msgs' = (msgs \ {m}) \cup {qm}
(*
p \in Participant starts the accept phase by issuing the ballot b \in Ballot
with value v \in Value.
*)
VotedForIn(a, b, v) == \E m \in msgs:
                            /\ m.from = a
                            /\ m.state[a].maxBal = b
                            /\ m.state[a].maxVBal = b
                            /\ m.state[a].maxVVal = v

ChosenIn(b, v) == \E Q \in Quorum:
                    \A a \in Q: VotedForIn(a, b, v)

Chosen(v) == \E b \in Ballot: ChosenIn(b, v)

ChosenP(p) == \* the set of values chosen by p \in Participant
    {v \in Value : \E b \in Ballot :
                       \E Q \in Quorum: \A q \in Q: /\ state[p][q].maxVBal = b
                                                    /\ state[p][q].maxVVal = v}

chosen == UNION {ChosenP(p) : p \in Participant}

Consistency == \*Cardinality(chosen) <= 1
   \A v1, v2 \in Value: Chosen(v1) /\ Chosen(v2) => (v1 = v2)

WontVoteIn(a, b) == /\ \A v \in Value: ~ VotedForIn(a, b, v)
                    /\ state[a][a].maxBal > b

SafeAt(b, v) ==
        \A c \in 0..(b-1):
            \E Q \in Quorum:
                \A a \in Q: VotedForIn(a, c, v) \/ WontVoteIn(a, c)

MsgInv ==
    \A m \in msgs:
        LET p == m.from
            curState == m.state[p]
         IN /\ curState.maxBal >= curState.maxVBal
            /\ curState.maxBal # curState.maxVBal
                => /\ curState.maxBal =< state[p][p].maxBal
                   /\ \A c \in (curState.maxVBal + 1)..(curState.maxBal - 1):
                        ~ \E v \in Value: VotedForIn(p, c, v)
            /\ curState.maxBal = curState.maxVBal \* exclude (-1,-1,None)
                => /\ SafeAt(curState.maxVBal, curState.maxVVal)
                   /\ \A ma \in msgs: (ma.state[ma.from].maxBal = curState.maxBal
                                       /\ ma.state[ma.from].maxBal = ma.state[ma.from].maxVBal)
                                    => ma.state[ma.from].maxVVal = curState.maxVVal
            /\\/ /\ curState.maxVVal \in Value
                 /\ curState.maxVBal \in Ballot
                 /\ VotedForIn(m.from, curState.maxVBal, curState.maxVVal)
              \/ /\ curState.maxVVal = None
                 /\ curState.maxVBal = -1
            /\ curState.maxBal \in Ballot
            /\ m.from \notin m.to
            /\ \A q \in Participant: /\ m.state[q].maxVBal <= state[q][q].maxVBal
                                     /\ m.state[q].maxBal <= state[q][q].maxBal
AccInv ==
    \A a \in Participant:
        /\ (state[a][a].maxVBal = -1) <=> (state[a][a].maxVVal = None)
        /\ \A q \in Participant: state[a][q].maxVBal <= state[a][q].maxBal
        /\ (state[a][a].maxVBal >= 0) => VotedForIn(a, state[a][a].maxVBal, state[a][a].maxVVal)
        /\ \A c \in Ballot: c > state[a][a].maxVBal
            => ~ \E v \in Value: VotedForIn(a, c, v)
        /\ \A q \in Participant:
            /\ state[a][a].maxBal >= state[q][a].maxBal
            /\ state[a][a].maxVBal >= state[q][a].maxVBal
        /\ \A q \in Participant:
                state[a][q].maxBal \in Ballot
                        => \E m \in msgs:
                              /\ m.from = q
                              /\ m.state[q].maxBal = state[a][q].maxBal
                              /\ m.state[q].maxVBal = state[a][q].maxVBal
                              /\ m.state[q].maxVVal = state[a][q].maxVVal

Inv == MsgInv /\ AccInv /\ TypeOK
LEMMA VotedInv ==
        MsgInv /\ TypeOK =>
            \A a \in Participant, b \in Ballot, v \in Value:
                VotedForIn(a, b, v) => SafeAt(b, v)
PROOF OMITTED

LEMMA MaxBigger == \A a \in Ballot \cup {-1}, b \in Ballot: Max(a, b) >= a /\ Max(a, b) >= b
PROOF OMITTED

LEMMA MaxTypeOK == \A a \in AllBallot, b \in Ballot: Max(a, b) \in Ballot
PROOF OMITTED

LEMMA UpdateStateBiggerProperty ==
     ASSUME NEW q \in Participant, NEW p \in Participant, NEW pp \in
                [maxBal: Ballot \cup {-1},
                maxVBal: Ballot \cup {-1}, maxVVal: Value \cup {None}],
                UpdateState(q, p, pp), TypeOK
     PROVE  /\ state'[q][q].maxBal \in AllBallot
            /\ state'[q][q].maxBal >= state[q][q].maxBal
PROOF OMITTED

LEMMA UpdateStateTypeOKProperty ==
     ASSUME NEW q \in Participant, NEW p \in Participant, NEW pp \in State,
                UpdateState(q, p, pp), TypeOK
     PROVE state' \in [Participant -> [Participant -> State]]
PROOF OMITTED

LEMMA OnMessageBiggerProperty ==
     ASSUME NEW q \in Participant, OnMessage(q), TypeOK
     PROVE  state'[q][q].maxBal >= state[q][q].maxBal
PROOF OMITTED

LEMMA MsgNotLost == Next /\ TypeOK =>
        \A m \in msgs, b1 \in Ballot, p1 \in Participant, v1 \in Value:
                       /\ m.from = p1
                       /\ m.state[p1].maxBal = b1
                       /\ m.state[p1].maxVBal = b1
                       /\ m.state[p1].maxVVal = v1
                       => m \in msgs'
PROOF OMITTED

LEMMA VotedOnce ==
        MsgInv => \A a1, a2 \in Participant, b \in Ballot, v1, v2 \in Value:
                VotedForIn(a1, b, v1) /\ VotedForIn(a2, b, v2) => (v1 = v2)
PROOF OMITTED

LEMMA SafeAtStable == Inv /\ Next /\ TypeOK' =>
                            \A v \in Value, b \in Ballot:
                               SafeAt(b, v) => SafeAt(b, v)'
PROOF OMITTED

LEMMA PrepareMsgInv == ASSUME NEW p \in Participant, NEW b \in Ballot, Prepare(p, b), Inv, TypeOK'
                        PROVE MsgInv'
PROOF OBVIOUS

(*
For checking Liveness
WF(A): if A ever becomes enabled, then an A step will eventually occur-even
if A remains enabled for only a fraction of a nanosecond and is never again
enabled.
Liveness in TPaxos: like paxos, there should be a single-leader to prapre
and accept.
*)

LConstrain == /\ \E p \in Participant:
                /\ MaxBallot \in Bals(p)
                /\ WF_vars(Prepare(p, MaxBallot))
                /\ \A v \in Value: WF_vars(Accept(p, MaxBallot, v))
                /\ \E Q \in Quorum:
                    /\ p \in Q
                    /\ \A q \in Q: WF_vars(OnMessage(q))

LSpec == Spec /\ LConstrain

Liveness == <>(chosen # {})
=============================================================================
\* Modification History
\* Last modified Thu Oct 29 15:28:07 CST 2020 by stary
\* Last modified Wed Oct 14 16:39:25 CST 2020 by pure_
\* Last modified Fri Oct 09 14:33:01 CST 2020 by admin
\* Created Thu Jun 25 14:23:28 CST 2020 by admin