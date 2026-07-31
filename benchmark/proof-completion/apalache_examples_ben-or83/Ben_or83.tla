--------------------------------- MODULE Ben_or83 ------------------------------------

EXTENDS FiniteSets, Integers, typedefs

VALUES == { 0, 1 }

CONSTANTS

    N,

    T,

    F,

    CORRECT,

    FAULTY,

    ROUNDS

ALL == CORRECT \union FAULTY
NO_DECISION == -1

ASSUME N > 5 * T /\ Cardinality(CORRECT) = N - F /\ Cardinality(FAULTY) = F
ASSUME 1 \in ROUNDS
ASSUME NO_DECISION \notin VALUES

VARIABLES

  value,

  decision,

  round,

  step,

  msgs1,

  msgs2

Senders1(m1s) ==

  { id \in ALL: \E m \in m1s: m.src = id }

Senders2(m2s) ==

  { id \in ALL:
    \E m \in m2s: (IsD2(m) /\ AsD2(m).src = id) \/ (IsQ2(m) /\ AsQ2(m).src = id) }

Init ==
  
  /\ value \in [ CORRECT -> VALUES ]
  /\ decision = [ r \in CORRECT |-> NO_DECISION ]
  /\ round = [ r \in CORRECT |-> 1 ]
  /\ step = [ r \in CORRECT |-> S1 ]
  /\ msgs1 = [ r \in ROUNDS |-> {}]
  /\ msgs2 = [ r \in ROUNDS |-> {}]

InitWithFaults ==
  
  /\ value \in [ CORRECT -> VALUES ]
  /\ decision = [ r \in CORRECT |-> NO_DECISION ]
  /\ round = [ r \in CORRECT |-> 1 ]
  /\ step = [ r \in CORRECT |-> S1 ]
  
  /\ \E F1 \in SUBSET [ src: FAULTY, r: ROUNDS, v: VALUES ]:
        msgs1 = [ r \in ROUNDS |-> { m \in F1: m.r = r } ]
  /\ \E F1D \in SUBSET [ src: FAULTY, r: ROUNDS, v: VALUES ],
        F1Q \in SUBSET [ src: FAULTY, r: ROUNDS ]:
        msgs2 = [ r \in ROUNDS |->
            { D2(mm.src, r, mm.v): mm \in { m \in F1D: m.r = r } }
                \union { Q2(mm.src, r): mm \in { m \in F1Q: m.r = r } }
        ]

Step1(id) ==
  Step1::
  LET r == round[id] IN
  /\ step[id] = S1
  
  /\ msgs1' = [msgs1 EXCEPT ![r] = @ \union { M1(id, r, value[id]) }]
  /\ step' = [step EXCEPT ![id] = S2]
  /\ UNCHANGED << value, decision, round, msgs2 >>

Step2(id) ==
  Step2::
  LET r == round[id] IN
  /\ step[id] = S2
  /\ \E received \in SUBSET msgs1[r]:
     
     /\ Cardinality(Senders1(received)) >= N - T
     /\ LET Weights == [ v \in VALUES |->
          Cardinality(Senders1({ m \in received: m.v = v })) ]
        IN
        \/ \E v \in VALUES: 
          
          /\ 2 * Weights[v] > N + T
          
          /\ msgs2' = [msgs2 EXCEPT ![r] = @ \union { D2(id, r, v) }]
        \//\ \A v \in VALUES: 2 * Weights[v] <= N + T
          
          /\ msgs2' = [msgs2 EXCEPT ![r] = @ \union { Q2(id, r) }]
  /\ step' = [ step EXCEPT ![id] = S3 ]
  /\ UNCHANGED << value, decision, round, msgs1 >>

Step3(id) ==
  Step3::
  LET r == round[id] IN
  /\ step[id] = S3
  /\ \E received \in SUBSET msgs2[r]:
    
    /\ Cardinality(Senders2(received)) = N - T
    /\ LET Weights == [ v \in VALUES |->
             Cardinality(Senders2({ m \in received: IsD2(m) /\ AsD2(m).v = v })) ]
       IN
       \/ \E v \in VALUES: 

          /\ Weights[v] >= T + 1
          /\ value' = [value EXCEPT ![id] = v]
          
          /\ IF 2 * Weights[v] > N + T
             
             THEN decision' = [decision EXCEPT ![id] = v]
             ELSE decision' = decision
       \/ /\ \A v \in VALUES: Weights[v] < T + 1
          /\ \E next_v \in VALUES:

             /\ value' = [value EXCEPT ![id] = next_v]
             /\ decision' = decision
    
    /\ r + 1 \in ROUNDS
    
    /\ round' = [ round EXCEPT ![id] = r + 1 ]
    /\ step' = [ step EXCEPT ![id] = S1 ]
    /\ UNCHANGED << msgs1, msgs2 >>

FaultyD2Records(r) == [ src: FAULTY, r: { r }, v: VALUES ]
FaultyQ2Records(r) == [ src: FAULTY, r: { r } ]

FaultyStep ==
    
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

AgreementInv ==
    \A id1, id2 \in CORRECT:
        \/ decision[id1] = NO_DECISION
        \/ decision[id2] = NO_DECISION
        \/ decision[id1] = decision[id2]

FinalityInv ==
    \A id \in CORRECT:
        \/ decision[id] = NO_DECISION
        \/ \/ decision'[id] /= NO_DECISION
           \/ decision'[id] = decision[id]

DecisionEx ==
    ~(\E id \in CORRECT: decision[id] /= NO_DECISION)

AllDecisionEx ==
    ~(\A id \in CORRECT: decision[id] /= NO_DECISION)

View == <<
    { value[id]: id \in CORRECT },
    { decision[id]: id \in CORRECT },
    { round[id]: id \in CORRECT },
    { step[id]: id \in CORRECT }
>>

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
