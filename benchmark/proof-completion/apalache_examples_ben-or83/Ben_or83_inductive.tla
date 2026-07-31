-------------------------- MODULE Ben_or83_inductive ------------------------------

EXTENDS FiniteSets, Integers, typedefs, Ben_or83

TypeOK ==
  /\ value \in [ CORRECT -> VALUES ]
  /\ decision \in [ CORRECT -> VALUES \union { NO_DECISION } ]
  /\ round \in [ CORRECT -> ROUNDS ]
  /\ step \in [ CORRECT -> { S1, S2, S3 } ]
  /\ \E A1 \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ]:
        msgs1 = [ r \in ROUNDS |-> { m \in A1: m.r = r } ]
  /\ \E A1D \in SUBSET [ src: ALL, r: ROUNDS, v: VALUES ],
          A1Q \in SUBSET [ src: ALL, r: ROUNDS ]:
        msgs2 = [ r \in ROUNDS |->
            { D2(mm.src, r, mm.v): mm \in { m \in A1D: m.r = r } }
                \union { Q2(mm.src, r): mm \in { m \in A1Q: m.r = r } }
        ]

ExistsQuorum2(r, v) ==
  \E Q \in SUBSET ALL:
    \E Qv \in SUBSET Q:
      LET cardQv == Cardinality(Qv) IN
      /\ Qv \subseteq Senders2({ m \in msgs2[r]: IsD2(m) /\ AsD2(m).v = v })
      /\ Q \subseteq Senders2(msgs2[r])
      /\ Cardinality(Q) = N - T
      /\ cardQv >= T + 1
      /\ 2 * cardQv > N + T

ExistsQuorum2LessRam(r, v) ==
  LET nv == Cardinality({ m \in msgs2[r]: IsD2(m) /\ AsD2(m).v = v })
      n == Cardinality(msgs2[r])
  IN
  /\ n >= N - T
  /\ nv >= T + 1
  /\ 2 * nv > N + T

Lemma1_DecisionRequiresQuorumAll_Slow ==
  Lemma1 ::
  \A id \in CORRECT:
    decision[id] /= NO_DECISION =>
        \E r \in ROUNDS:
        /\ r <= round[id]
        /\ ExistsQuorum2(r, decision[id])

Lemma1_DecisionRequiresLastQuorum ==
  Lemma1b ::
  \A id \in CORRECT:
    \/ decision[id] = NO_DECISION
    \/ round[id] > 1 /\ ExistsQuorum2(round[id] - 1, decision[id])

Lemma1_DecisionRequiresLastQuorumLessRam ==
  Lemma1c ::
  \A id \in CORRECT:
    \/ decision[id] = NO_DECISION
    \/ round[id] > 1 /\ ExistsQuorum2LessRam(round[id] - 1, decision[id])

Lemma2_NoEquivocation1ByCorrect ==
  Lemma2 ::
  \A r \in ROUNDS:
    \A m1, m2 \in msgs1[r]:
      (m1.src \in CORRECT /\ m1.src = m2.src) => (m1.v = m2.v)

Lemma3_NoEquivocation2ByCorrect ==
  Lemma3 ::
  \A r \in ROUNDS:
    \A m1, m2 \in msgs2[r]:
      /\ IsD2(m1) /\ IsD2(m2) /\ AsD2(m1).src = AsD2(m2).src =>
        (AsD2(m1).src \in CORRECT => AsD2(m1).v = AsD2(m2).v)
      /\ IsQ2(m1) /\ IsD2(m2) /\ AsQ2(m1).src = AsD2(m2).src =>
        AsQ2(m1).src \in FAULTY

Lemma4_MessagesNotFromFuture ==
  Lemma4 ::
  \A r \in ROUNDS:
    /\ \A m \in msgs1[r]:
      m.src \in CORRECT =>
        /\ step[m.src] /= S1 => (m.r <= round[m.src])
        /\ step[m.src] = S1 => (m.r < round[m.src])
    /\ \A m \in msgs2[r]:
      LET src == IF IsD2(m) THEN AsD2(m).src ELSE AsQ2(m).src IN
      LET mr == IF IsD2(m) THEN AsD2(m).r ELSE AsQ2(m).r IN
      src \in CORRECT =>
        /\ step[src] = S3 => (mr <= round[src])
        /\ step[src] /= S3 => (mr < round[src])

Lemma5_RoundNeedsSentMessages ==
  Lemma5 ::
  \A id \in CORRECT:
    LET myStep == step[id]
        myRound == round[id]
    IN
    \A r \in ROUNDS:
      
      /\ r < myRound \/ (r = myRound /\ myStep /= S1)
        => \E m \in msgs1[r]: m.src = id
      /\ r < myRound
        => \E m \in msgs2[r]: AsD2(m).src = id \/ AsQ2(m).src = id
      
      /\ (r = myRound /\ myStep = S3)
        => \E m \in msgs2[r]:
            AsD2(m).src = id \/ AsQ2(m).src = id

Lemma6_DecisionDefinesValue ==
  Lemma6 ::
  \A id \in CORRECT:
    decision[id] /= NO_DECISION => value[id] = decision[id]
    
Lemma7_D2RequiresQuorum ==
  Lemma7 ::
  LET ExistsQuorum1(r, v) ==
    LET Sv == { m \in msgs1[r]: m.v = v } IN
    2 * Cardinality(Senders1(Sv)) > N + T
  IN
  \A r \in ROUNDS:
    \A v \in VALUES:
      (\E m \in msgs2[r]: IsD2(m) /\ AsD2(m).v = v /\ AsD2(m).src \in CORRECT)
        => ExistsQuorum1(r, v)

Lemma8_Q2RequiresNoQuorum ==
  Lemma8 ::
  LET RoundsWithQ2 ==
    { r \in ROUNDS:
      \E m \in msgs2[r]: IsQ2(m) /\ AsQ2(m).src \in CORRECT }
  IN
  \A r \in RoundsWithQ2:
    
    \E Q \in SUBSET ALL:
      /\ Cardinality(Q) >= N - T
      /\ Q \subseteq Senders1(msgs1[r])
      /\ \A v \in VALUES:
        LET Sv == Senders1({ m \in msgs1[r]:
            m.v = v /\ m.src \in Q /\ m.src \in CORRECT })
        IN
        2 * Cardinality(Sv) <= N

Lemma8_Q2RequiresNoQuorumFaster ==
  Lemma8a ::
  LET RoundsWithQ2 ==
    { r \in ROUNDS:
      \E m \in msgs2[r]: IsQ2(m) /\ AsQ2(m).src \in CORRECT }
  IN
  \A r \in RoundsWithQ2:
    
    LET n0 == Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 0 ] \in msgs1[r] })
        n1 == Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 1 ] \in msgs1[r] })
        
        nf == Cardinality({ id \in FAULTY: id \in { m.src: m \in msgs1[r] } })
    IN
    \E x0, x1 \in 0..N:
      /\ x0 <= n0 /\ x1 <= n1
      /\ x0 + x1 + nf >= N - T
      /\ 2 * x0 <= N + T
      /\ 2 * x1 <= N + T

SupportedValues(r) ==
  LET ExistsSupport(v) ==
    LET Sv == Senders2({ m \in msgs2[r]: IsD2(m) /\ AsD2(m).v = v }) IN
    LET Others == Senders2({ m \in msgs2[r]: IsQ2(m) \/ AsD2(m).v /= v }) IN
    /\ Cardinality(Senders2(msgs2[r])) >= N - T
    /\ Cardinality(Sv) >= T + 1
    /\ Cardinality(Others) < N - 2 * T
  IN
  { v \in VALUES: ExistsSupport(v) }

Lemma9_RoundsConnection ==
  Lemma9 ::
  \A r \in ROUNDS:
    r + 1 \in ROUNDS =>
      
      LET Supported == SupportedValues(r) IN
      \/ Supported = {} 
      \/ \E v \in Supported:
           \A m \in msgs1[r + 1]:
             (m.src \in CORRECT => m.v = v)

Lemma13_ValueLock ==
  Lemma13 ::
  LET supported == [ r \in ROUNDS |-> SupportedValues(r) ] IN
  \A id \in CORRECT, v \in VALUES:
    \/ round[id] = 1
    \/ /\ round[id] > 1
       /\ LET S == supported[round[id] - 1] IN
          \/ S = {}
          \/ value[id] \in S

Lemma10_M1RequiresQuorum ==
  Lemma10 ::
  LET RoundsWithM1 ==
      { r \in ROUNDS \ { 1 }: \E m \in msgs1[r]: m.src \in CORRECT }
  IN

  \A r \in RoundsWithM1:
    Cardinality(Senders2(msgs2[r - 1])) >= N - T

Lemma11_ValueOnQuorum ==
  Lemma11 ::
  \A id \in CORRECT:
    LET r == round[id] IN
    r > 1 =>
      \/ \E Q \in SUBSET ALL:
        LET v == value[id] IN
        LET Qv == Senders2({
          m \in msgs2[r - 1]:
            IsD2(m) /\ AsD2(m).v = v  /\ AsD2(m).src \in Q })
        IN
        /\ Q \subseteq Senders2(msgs2[r - 1])
        /\ 2 * Cardinality(Qv) > N + T
      \/ \E Q \in SUBSET ALL:
        /\ Cardinality(Q) = N - T
        /\ Q \subseteq Senders2(msgs2[r - 1])
        /\ \A v \in VALUES:

           LET DinQ ==
             Senders2({ m \in msgs2[r - 1]:
               IsD2(m) /\ AsD2(m).v = v /\ AsD2(m).src \in Q })
           IN
           2 * Cardinality(DinQ) <= N + T

Lemma11_ValueOnQuorumLessRam ==
  Lemma11a ::
  \A id \in CORRECT:
    LET r == round[id] IN
    r > 1 =>
      \/ LET v == value[id]
             Qv == Senders2({ m \in msgs2[r - 1]: IsD2(m) /\ AsD2(m).v = v })
         IN
         2 * Cardinality(Qv) > N + T
      \/ LET n0 == Cardinality({ m \in msgs2[r - 1]: IsD2(m) /\ AsD2(m).v = 0 })
             n1 == Cardinality({ m \in msgs2[r - 1]: IsD2(m) /\ AsD2(m).v = 1 })
             nq == Cardinality({ m \in msgs2[r - 1]: IsQ2(m) })
         IN
         \E x0, x1 \in 0..N:
           /\ x0 <= n0 /\ x1 <= n1
           /\ x0 + x1 + nq >= N - T
           /\ 2 * x0 <= N + T
           /\ 2 * x1 <= N + T

Lemma12_CannotJumpRoundsWithoutQuorum ==
  Lemma12 ::
  \A r \in ROUNDS:
    r + 1 \in ROUNDS =>

      LET nextRoundReached ==
        \E id \in CORRECT:
          round[id] = r + 1 /\ step[id] = S1
      IN
      nextRoundReached =>
        Cardinality(Senders2(msgs2[r])) >= N - T

IndInv ==
  /\ Lemma2_NoEquivocation1ByCorrect
  /\ Lemma3_NoEquivocation2ByCorrect
  /\ Lemma4_MessagesNotFromFuture
  /\ Lemma5_RoundNeedsSentMessages
  /\ Lemma6_DecisionDefinesValue
  /\ Lemma7_D2RequiresQuorum
  /\ Lemma8_Q2RequiresNoQuorumFaster
  /\ Lemma9_RoundsConnection
  /\ Lemma10_M1RequiresQuorum
  /\ Lemma11_ValueOnQuorumLessRam
  /\ Lemma12_CannotJumpRoundsWithoutQuorum
  /\ Lemma13_ValueLock
  
  /\ Lemma1_DecisionRequiresLastQuorumLessRam

IndInit ==
  /\ TypeOK
  /\ IndInv

======================================================================================
