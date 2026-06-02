------------------------------ MODULE TPaxosWithProof_VotedInv --------------------------------
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
EXTENDS Integers, FiniteSets, TLAPS
-----------------------------------------------------------------------------
Max(m, n) == IF m > n THEN m ELSE n
Injective(f) == \A a, b \in DOMAIN f: (a # b) => (f[a] # f[b])
-----------------------------------------------------------------------------
CONSTANTS
    Participant,  \* the set of partipants
    Value         \* the set of possible input values for Participant to propose

None == CHOOSE b : b \notin Value

LEMMA NoneNotAValue == None \notin Value
  PROOF OMITTED

NP == Cardinality(Participant) \* number of p \in Participants

Quorum == {Q \in SUBSET Participant : Cardinality(Q) * 2 >= NP + 1}
ASSUME QuorumAssumption ==
    /\ \A Q \in Quorum : Q \subseteq Participant
    /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

Ballot == Nat
AllBallot == Ballot \cup {-1}
AllValue == Value \cup {None}
MaxBallot == Cardinality(Ballot) - 1

PIndex == CHOOSE f \in [Participant -> 1 .. NP] : Injective(f)
Bals(p) == {b \in Ballot : b % NP = PIndex[p] - 1} \* allocate ballots for each p \in Participant
-----------------------------------------------------------------------------
State == [maxBal: Ballot \cup {-1},
         maxVBal: Ballot \cup {-1}, maxVVal: Value \cup {None}]

InitState == [maxBal |-> -1, maxVBal |-> -1, maxVVal |-> None]
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
-----------------------------------------------------------------------------
VARIABLES
    state,  \* state[p][q]: the state of q \in Participant from the view of p \in Participant
    msgs    \* the set of messages that have been sent

vars == <<state, msgs>>

TypeOK ==
    /\ state \in [Participant -> [Participant -> State]]
\*    /\ \A p \in Participant: state[p] \in [Participant -> State]
\*    /\ \A p \in Participant, q \in Participant:
\*            /\ state[p][q].maxBal \in AllBallot
\*            /\ state[p][q].maxVBal \in AllBallot
\*            /\ state[p][q].maxVVal \in AllValue
    /\ msgs \subseteq Message

Send(m) == msgs' = msgs \cup {m}
-----------------------------------------------------------------------------
Init ==
    /\ state = [p \in Participant |-> [q \in Participant |-> InitState]]
    /\ msgs = {}
(*
p \in Participant starts the prepare phase by issuing a ballot b \in Ballot.
*)
Prepare(p, b) ==
    /\ b \in Bals(p)
    /\ state[p][p].maxBal < b
    /\ state' = [state EXCEPT ![p][p].maxBal = b]
    /\ Send([from |-> p, to |-> Participant \ {p}, state |-> state'[p]])
(*
q \in Participant updates its own state state[q] according to the actual state
pp of p \in Participant extracted from a message m \in Message it receives.
This is called by OnMessage(q).
Note: pp is m.state[p]; it may not be equal to state[p][p] at the time
UpdateState is called.
*)
UpdateState(q, p, pp) ==
    LET maxB == Max(state[q][q].maxBal, pp.maxBal)
        maxBV == IF (maxB <= pp.maxVBal)
                    THEN pp.maxVBal
                    ELSE state[q][q].maxVBal
        maxVV == IF (maxB <= pp.maxVBal)
                    THEN pp.maxVVal
                    ELSE state[q][q].maxVVal
       new_state_qq == [maxBal |-> maxB,
                        maxVBal |-> maxBV,
                        maxVVal |-> maxVV]
       new_state_qp == [maxBal |->  Max(state[q][p].maxBal, pp.maxBal),
                        maxVBal |-> Max(state[q][p].maxVBal, pp.maxVBal),
                        maxVVal |-> (IF (state[q][p].maxVBal =< pp.maxVBal)
                                        THEN pp.maxVVal
                                        ELSE state[q][p].maxVVal)]
    IN  state' =
          [state EXCEPT
              ![q] = [ state[q] EXCEPT
                          ![q] = new_state_qq,
                          ![p] = new_state_qp
                      ]
           ]
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
OnMessage(q) ==
    \E m \in msgs :
        /\ q \in m.to
        /\ LET p == m.from
           IN  UpdateState(q, p, m.state[p])
        /\ LET qm == [from |-> m.from, to |-> m.to \ {q}, state |-> m.state] \*remove q from to
               nm == [from |-> q, to |-> {m.from}, state |-> state'[q]] \*new message to reply
           IN  IF \/ m.state[q].maxBal < state'[q][q].maxBal
                  \/ m.state[q].maxVBal < state'[q][q].maxVBal
                 THEN msgs' = msgs \cup {nm}
                 ELSE UNCHANGED msgs
\*               THEN msgs' = (msgs \ {m}) \cup {qm, nm}
\*               ELSE msgs' = (msgs \ {m}) \cup {qm}
(*
p \in Participant starts the accept phase by issuing the ballot b \in Ballot
with value v \in Value.
*)
Accept(p, b, v) ==
    /\ b \in Bals(p)
    /\ ~ \E m \in msgs: m.state[m.from].maxBal = b /\ m.state[m.from].maxVBal = b
    /\ state[p][p].maxBal = b \*corresponding the first conjunction in Voting
    /\ state[p][p].maxVBal # b \* correspongding the second conjunction in Voting
    /\ \E Q \in Quorum :
       /\ \A q \in Q : state[p][q].maxBal = b
       \* pick the value from the quorum
       /\ \/ \A q \in Q : state[p][q].maxVBal = -1 \* free to pick its own value
\*          \/ \E q \in Q : \* v is the value with the highest maxVBal in the quorum
\*                /\ state[p][q].maxVVal = v
          \/ \E c \in 0..(b-1):
              /\ \A r \in Q: state[p][r].maxVBal =< c
              /\ \E r \in Q: /\ state[p][r].maxVBal = c
                             /\ state[p][r].maxVVal = v
\*                /\ \A r \in Q : state[p][q].maxVBal >= state[p][r].maxVBal
    \*choose the value from all the local state
\*    /\ \/ \A q \in Participant : state[p][q].maxVBal = -1 \* free to pick its own value
\*       \/ \E q \in Participant : \* v is the value with the highest maxVBal
\*            /\ state[p][q].maxVVal = v
\*            /\ \A r \in Participant: state[p][q].maxVBal >= state[p][r].maxVBal
\*    /\ state' = [state EXCEPT ![p][p].maxVBal = b,
\*                              ![p][p].maxVVal = v]
    /\ state' = [state EXCEPT ![p] = [state[p] EXCEPT
                                        ![p] = [state[p][p] EXCEPT !.maxVBal = b,
                                                                   !.maxVVal = v]]]
    /\ Send([from |-> p, to |-> Participant \ {p}, state |-> state'[p]])
---------------------------------------------------------------------------
Next == \E p \in Participant : \/ OnMessage(p)
                               \/ \E b \in Ballot : \/ Prepare(p, b)
                                                    \/ \E v \in Value : Accept(p, b, v)
Spec == Init /\ [][Next]_vars
---------------------------------------------------------------------------
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

---------------------------------------------------------------------------
WontVoteIn(a, b) == /\ \A v \in Value: ~ VotedForIn(a, b, v)
                    /\ state[a][a].maxBal > b

SafeAt(b, v) ==
        \A c \in 0..(b-1):
            \E Q \in Quorum:
                \A a \in Q: VotedForIn(a, c, v) \/ WontVoteIn(a, c)

---------------------------------------------------------------------------
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
--------------------------------------------------------------------------
LEMMA VotedInv ==
        MsgInv /\ TypeOK =>
            \A a \in Participant, b \in Ballot, v \in Value:
                VotedForIn(a, b, v) => SafeAt(b, v)
PROOF OBVIOUS

=============================================================================