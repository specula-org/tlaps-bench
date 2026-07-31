--------------------------------- MODULE Ben_or83 ------------------------------------
(*
 * This is a TLA+ specification of the Ben-Or's solution to the Byzantine consensus
 * problem. The algorithm is described in the paper:
 *
 * M. Ben-Or. Another advantage of free choice (extended abstract). PODC 1983.
 *
 * The algorithm is probabilistic. We focus on safety and, therefore, abstract
 * probabilities with non-determinism.
 *
 * Igor Konnov, 2024
 *)
EXTENDS FiniteSets, Integers, typedefs

\* The set of values to choose from
VALUES == { 0, 1 }

CONSTANTS
    \* The total number of replicas.
    \* @type: Int;
    N,
    \* An upper bound on the number of faulty replicas.
    \* @type: Int;
    T,
    \* The actual number of faulty replicas (unknown to the replicas).
    \* @type: Int;
    F,
    \* The set of the correct (honest) replicas.
    \* @type: Set(REPLICA);
    CORRECT,
    \* The set of the Byzantine (faulty) replicas.
    \* @type: Set(REPLICA);
    FAULTY,
    \* The set of rounds, which we bound for model checking.
    \* @type: Set(Int);
    ROUNDS

ALL == CORRECT \union FAULTY
NO_DECISION == -1

ASSUME N > 5 * T /\ Cardinality(CORRECT) = N - F /\ Cardinality(FAULTY) = F
ASSUME 1 \in ROUNDS
ASSUME NO_DECISION \notin VALUES

VARIABLES
  \* The current value by a replica, called $x_P$ in the paper.
  \* @type: REPLICA -> Int;
  value,
  \* The decision by a replica, where -1 means no decision.
  \* @type: REPLICA -> Int;
  decision,
  \* The round number of a replica, called $r$ in the paper.
  \* @type: REPLICA -> Int;
  round,
  \* The replica step: S1, S2, S3.
  \* @type: REPLICA -> STEP;
  step,
  \* Type-1 messages sent by the correct and faulty replicas, mapped by rounds.
  \* @type: Int -> Set($msgOne);
  msgs1,
  \* Type-2 messages sent by the correct and faulty replicas, mapped by rounds.
  \* @type: Int -> Set($msgTwo);
  msgs2

\* @type: Set($msgOne) => Set(REPLICA);
Senders1(m1s) ==
  \* Filter the set of ALL, as it has fixed size, in contrast to m1s.
  \* This is especially important, when we call Cardinality on the result.
  { id \in ALL: \E m \in m1s: m.src = id }

\* @type: Set($msgTwo) => Set(REPLICA);
Senders2(m2s) ==
  \* Filter the set of ALL, as it has fixed size, in contrast to m2s.
  \* This is especially important, when we call Cardinality on the result.
  { id \in ALL:
    \E m \in m2s: (IsD2(m) /\ AsD2(m).src = id) \/ (IsQ2(m) /\ AsQ2(m).src = id) }

Init ==
  \* non-deterministically choose the initial values
  /\ value \in [ CORRECT -> VALUES ]
  /\ decision = [ r \in CORRECT |-> NO_DECISION ]
  /\ round = [ r \in CORRECT |-> 1 ]
  /\ step = [ r \in CORRECT |-> S1 ]
  /\ msgs1 = [ r \in ROUNDS |-> {}]
  /\ msgs2 = [ r \in ROUNDS |-> {}]

InitWithFaults ==
  \* non-deterministically choose the initial values
  /\ value \in [ CORRECT -> VALUES ]
  /\ decision = [ r \in CORRECT |-> NO_DECISION ]
  /\ round = [ r \in CORRECT |-> 1 ]
  /\ step = [ r \in CORRECT |-> S1 ]
  \* non-deterministically initialize the messages with faults
  /\ \E F1 \in SUBSET [ src: FAULTY, r: ROUNDS, v: VALUES ]:
        msgs1 = [ r \in ROUNDS |-> { m \in F1: m.r = r } ]
  /\ \E F1D \in SUBSET [ src: FAULTY, r: ROUNDS, v: VALUES ],
        F1Q \in SUBSET [ src: FAULTY, r: ROUNDS ]:
        msgs2 = [ r \in ROUNDS |->
            { D2(mm.src, r, mm.v): mm \in { m \in F1D: m.r = r } }
                \union { Q2(mm.src, r): mm \in { m \in F1Q: m.r = r } }
        ]

\* @type: REPLICA => Bool;
Step1(id) ==
  Step1::
  LET r == round[id] IN
  /\ step[id] = S1
  \* "send the message (1, r, x_P) to all the processes"
  /\ msgs1' = [msgs1 EXCEPT ![r] = @ \union { M1(id, r, value[id]) }]
  /\ step' = [step EXCEPT ![id] = S2]
  /\ UNCHANGED << value, decision, round, msgs2 >>

Step2(id) ==
  Step2::
  LET r == round[id] IN
  /\ step[id] = S2
  /\ \E received \in SUBSET msgs1[r]:
     \* "wait till messages of type (1, r, *) are received from N - T processes"
     /\ Cardinality(Senders1(received)) >= N - T
     /\ LET Weights == [ v \in VALUES |->
          Cardinality(Senders1({ m \in received: m.v = v })) ]
        IN
        \/ \E v \in VALUES: 
          \* "if more than (N + T)/2 messages have the same value v..."
          /\ 2 * Weights[v] > N + T
          \* "...then send the message (2, r, v, D) to all processes"
          /\ msgs2' = [msgs2 EXCEPT ![r] = @ \union { D2(id, r, v) }]
        \//\ \A v \in VALUES: 2 * Weights[v] <= N + T
          \* "Else send the message (2, r, ?) to all processes"
          /\ msgs2' = [msgs2 EXCEPT ![r] = @ \union { Q2(id, r) }]
  /\ step' = [ step EXCEPT ![id] = S3 ]
  /\ UNCHANGED << value, decision, round, msgs1 >>

Step3(id) ==
  Step3::
  LET r == round[id] IN
  /\ step[id] = S3
  /\ \E received \in SUBSET msgs2[r]:
    \* "Wait till messages of type (2, r, *) arrive from N - T processes"
    /\ Cardinality(Senders2(received)) = N - T
    /\ LET Weights == [ v \in VALUES |->
             Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = v })) ]
       IN
       \/ \E v \in VALUES: 
          \* "(a) If there are at least T+1 D-messages (2, r, v, D),
          \* then set x_P to v"
          /\ Weights[v] >= T + 1
          /\ value' = [value EXCEPT ![id] = v]
          \* "(b) If there are more than (N + T)/2 D-messages..."
          /\ IF 2 * Weights[v] > N + T
             \* "...then decide v"
             THEN decision' = [decision EXCEPT ![id] = v]
             ELSE decision' = decision
       \/ /\ \A v \in VALUES: Weights[v] < T + 1
          /\ \E next_v \in VALUES:
             \* "(c) Else set x_P = 1 or 0 each with probability 1/2."
             \* We replace probabilites with non-determinism.
             /\ value' = [value EXCEPT ![id] = next_v]
             /\ decision' = decision
    \* the condition below is to bound the number of rounds for model checking
    /\ r + 1 \in ROUNDS
    \* "Set r := r + 1 and go to step 1"
    /\ round' = [ round EXCEPT ![id] = r + 1 ]
    /\ step' = [ step EXCEPT ![id] = S1 ]
    /\ UNCHANGED << msgs1, msgs2 >>

FaultyD2Records(r) == [ src: FAULTY, r: { r }, v: VALUES ]
FaultyQ2Records(r) == [ src: FAULTY, r: { r } ]

FaultyStep ==
    \* the faulty replicas collectively inject messages for a single round
    Faulty::
    /\ \E r \in ROUNDS:
        /\ \E F1 \in SUBSET [ src: FAULTY, r: { r }, v: VALUES ]:
            msgs1' = [ msgs1 EXCEPT ![r] = @ \union F1 ]
        /\ \E F2D \in SUBSET FaultyD2Records(r):
             \E F2Q \in SUBSET FaultyQ2Records(r):
                msgs2' = [ msgs2 EXCEPT ![r] =
                    @ \union { D2(mm.src, r, mm.v): mm \in F2D }
                      \union { Q2(mm.src, r): mm \in F2Q } ]
    /\ UNCHANGED << value, decision, round, step >>

CorrectStep ==
  \E id \in CORRECT:
    \/ Step1(id)
    \/ Step2(id)
    \/ Step3(id)

Next ==
  \/ CorrectStep
  \/ FaultyStep

\****************** INVARIANTS *****************************

\* No two correct replicas decide on different values
AgreementInv ==
    \A id1, id2 \in CORRECT:
        \/ decision[id1] = NO_DECISION
        \/ decision[id2] = NO_DECISION
        \/ decision[id1] = decision[id2]

\* Once a correct replica decides, it never changes its decision
FinalityInv ==
    \A id \in CORRECT:
        \/ decision[id] = NO_DECISION
        \/ \/ decision'[id] /= NO_DECISION
           \/ decision'[id] = decision[id]

\****************** EXAMPLES   *****************************

\* An example of a replica that has made a decision
DecisionEx ==
    ~(\E id \in CORRECT: decision[id] /= NO_DECISION)

\* An example of all correct replicas having made a decision
AllDecisionEx ==
    ~(\A id \in CORRECT: decision[id] /= NO_DECISION)

\* simple view
View == <<
    { value[id]: id \in CORRECT },
    { decision[id]: id \in CORRECT },
    { round[id]: id \in CORRECT },
    { step[id]: id \in CORRECT }
>>

\* Count the number of replicas that map to a value.
\* @type: (REPLICA -> a) => (a -> Int);
CountImg(f) ==
    LET V == {f[id]: id \in CORRECT} IN
    [ v \in V |-> Cardinality({ id \in CORRECT: f[id] = v })]

PreciseView == <<
    CountImg(value),
    CountImg(decision),
    CountImg(round),
    CountImg(step)
>>
======================================================================================
