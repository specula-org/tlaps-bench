-------------------------- MODULE Ben_or83_inductive ------------------------------
(*
 * Inductive constructions for proving safety of AgreementInv for bounded parameters.
 *
 * Igor Konnov, August 2024
 *
 * To make sure that we have constructed an inductive invariant, we have to check:
 *
 * 1. That IndInit => AgreementInv:
 *
 * $ apalache-mc check --init=IndInit --inv=AgreementInv --length=0 MC_n6t1f0_inductive.tla
 *
 * On my computer, it finished in 10 min 13 sec using 5.3G of RAM.
 *
 * 2. That InitWithFaults => IndInv:
 *
 * $ apalache-mc check --init=InitWithFaults --inv=IndInv --length=0 MC_n6t1f0_inductive.tla
 *
 * 3. That IndInit /\ Next => IndInv' (running all jobs in parallel):
 *
 * $ seq 0 12 | parallel --delay 1 -j 13 \
 *   apalache-mc check --length=1 --inv=IndInv --init=IndInit \
 *   --tuning-options='search.invariantFilter=1-\>'state{} --out-dir=out/{} MC_n6t1f0_inductive.tla
 *
 * Do the same for MC_n6t1f1_inductive.tla instead of MC_n6t1f0_inductive.tla.
 *
 * Timeline:
 *
 * - 2.5h to come up with Lemmas 1-9 for the fault-free case
 * - 2.5h to fix Lemma8_Q2RequiresNoQuorum
 * - 20 min to fix Lemma5_RoundNeedsSentMessages
 * - 1h to fix Lemma9_RoundsConnection by introducing Lemma10_M1RequiresQuorum
 * - 45 min to add Lemma11_ValueOnQuorum
 * - A single lemma requires about 40G of RAM!
 * - 10 min to add Lemma12_CannotJumpRoundsWithoutQuorum
 * - 5 min to fix Lemma12_CannotJumpRoundsWithoutQuorum
 * - A single lemma requires 4-8G of RAM?
 * - 25 min to fix Lemma1 by introducing Lemma1_DecisionRequiresLastQuorum
 * - 15 min to fix Lemma11_ValueOnQuorum
 * - 1.5h to fix Lemma9_RoundsConnection (2 * T + 1)
 * - Using 'simulate' to debug the lemmas
 * - 5 min to add Lemma13_ValueLock
 * - 1.5h to fix Lemma9_RoundsConnection and Lemma13_ValueLock
 * - 2h to add Lemma8_Q2RequiresNoQuorumFaster
 *
 * -------- checking the inductive step for MC_n6t1f1_inductive.tla -----
 * - 15 min to fix Lemma2_NoEquivocation1ByCorrect, Lemma3_NoEquivocation2ByCorrect, Lemma4_MessagesNotFromFuture
 * - 1h to fix Lemma9_RoundsConnection
 * - 30 min to fix Lemma13_ValueLock
 * - 20 min to fix Lemma9_RoundsConnection, Lemma1_DecisionRequiresLastQuorum
 *
 * -------- speeding up and reducing RAM consumption -----
 * - 3h to speed up Lemma8_Q2RequiresNoQuorum
 * - 30 min to reduce RAM consumption in Lemma11_ValueOnQuorum
 * - 20 min to reduce RAM consumption in Lemma1_DecisionRequiresLastQuorum
 *)
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

\*********** AUXILIARY DEFINITIONS ***********/

\* this definition is memory-hungry, see ExistsQuorum2LessRam
ExistsQuorum2(r, v) ==
  \E Q \in SUBSET ALL:
    \E Qv \in SUBSET Q:
      LET cardQv == Cardinality(Qv) IN
      /\ Qv \subseteq Senders2({ m \in msgs2[r]: IsD2(m) /\ AsD2(m).v = v })
      /\ Q \subseteq Senders2(msgs2[r])
      /\ Cardinality(Q) = N - T
      /\ cardQv >= T + 1
      /\ 2 * cardQv > N + T

\* a more memory-efficient version of ExistsQuorum2
ExistsQuorum2LessRam(r, v) ==
  LET nv == Cardinality({ m \in msgs2[r]: IsD2(m) /\ AsD2(m).v = v })
      n == Cardinality(msgs2[r])
  IN
  /\ n >= N - T
  /\ nv >= T + 1
  /\ 2 * nv > N + T

\*********** LEMMAS THAT CONSTITUTE THE INDUCTIVE INVARIANT ***********/

\* although Lemma1 is the most natural one, it is quite slow
Lemma1_DecisionRequiresQuorumAll_Slow ==
  Lemma1 ::
  \A id \in CORRECT:
    decision[id] /= NO_DECISION =>
        \E r \in ROUNDS:
        /\ r <= round[id]
        /\ ExistsQuorum2(r, decision[id])

\* This is a faster version of Lemma 1.
\* Still, this lemma is rather slow, >21h.
\* Moreover, it requires >40G of RAM.
\* See Lemma1_DecisionRequiresLastQuorumLessRam.
Lemma1_DecisionRequiresLastQuorum ==
  Lemma1b ::
  \A id \in CORRECT:
    \/ decision[id] = NO_DECISION
    \/ round[id] > 1 /\ ExistsQuorum2(round[id] - 1, decision[id])

\* This version reduces the RAM consumption from 40G to 7G.
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
      \* this part takes a lot of time to check, >21h
      /\ r < myRound \/ (r = myRound /\ myStep /= S1)
        => \E m \in msgs1[r]: m.src = id
      /\ r < myRound
        => \E m \in msgs2[r]: AsD2(m).src = id \/ AsQ2(m).src = id
      \* this part takes >24h
      /\ (r = myRound /\ myStep = S3)
        => \E m \in msgs2[r]:
            AsD2(m).src = id \/ AsQ2(m).src = id

\* This lemma takes >24h.
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
    \* follows from Step2
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
    \* follows from Step2
    LET n0 == Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 0 ] \in msgs1[r] })
        n1 == Cardinality({ id \in CORRECT: [ src |-> id, r |-> r, v |-> 1 ] \in msgs1[r] })
        \* we wrap the map in a filter to constrain the set bound
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
      \* find the values that could go over T + 1 in every quorum of msgs2[r]
      LET Supported == SupportedValues(r) IN
      \/ Supported = {} \* no constraints on values
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
  \* for all rounds greater than 1,
  \* a correct replica needs N - T messages of type 2 to send a message of type 1
  \A r \in RoundsWithM1:
    Cardinality(Senders2(msgs2[r - 1])) >= N - T

\* this lemma leads to RAM explosion of 27G, see Lemma11_ValueOnQuorumLessRam
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
           \* there was a way to select N - T replicas
           \* that did not shows us over (N + T) / 2 messages for every value
           LET DinQ ==
             Senders2({ m \in msgs2[r - 1]:
               IsD2(m) /\ AsD2(m).v = v /\ AsD2(m).src \in Q })
           IN
           2 * Cardinality(DinQ) <= N + T

\* Using cardinalities and arithmetics instead of quorum sets.
\* This reduced RAM consumption from 27G to 7G.
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
      \* if there is a correct replica in S1 of round r + 1 right now,
      \* then there were at least N - T messages of type 2 in round r
      LET nextRoundReached ==
        \E id \in CORRECT:
          round[id] = r + 1 /\ step[id] = S1
      IN
      nextRoundReached =>
        Cardinality(Senders2(msgs2[r])) >= N - T

\******** THE INDUCTIVE INVARIANT ***********/
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
  \* this lemma is rather slow
  /\ Lemma1_DecisionRequiresLastQuorumLessRam

\******** THE INDUCTIVE INVARIANT + THE SHAPE INVARIANT ***********/
IndInit ==
  /\ TypeOK
  /\ IndInv

======================================================================================