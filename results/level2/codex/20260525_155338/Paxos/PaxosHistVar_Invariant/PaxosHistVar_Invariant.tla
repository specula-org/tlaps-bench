------------------------------- MODULE PaxosHistVar_Invariant --------------------------

EXTENDS Integers, TLAPS, NaturalsInduction

CONSTANTS Acceptors, Values, Quorums

ASSUME QuorumAssumption == 
          /\ Quorums \subseteq SUBSET Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

Ballots == Nat

VARIABLES sent

vars == <<sent>>

Send(m) == sent' = sent \cup {m}

None == CHOOSE v : v \notin Values

Init == sent = {}

Phase1a(b) == Send([type |-> "1a", bal |-> b])

last_voted(a) == LET 2bs == {m \in sent: m.type = "2b" /\ m.acc = a}
                 IN IF 2bs # {} THEN {m \in 2bs: \A m2 \in 2bs: m.bal >= m2.bal}
                    ELSE {[bal |-> -1, val |-> None]}

Phase1b(a) ==
  \E m \in sent, r \in last_voted(a):
     /\ m.type = "1a"
     /\ \A m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.acc = a => m.bal > m2.bal
     /\ Send([type |-> "1b", bal |-> m.bal,
              maxVBal |-> r.bal, maxVal |-> r.val, acc |-> a])

Phase2a(b) ==
  /\ ~ \E m \in sent : (m.type = "2a") /\ (m.bal = b) 
  /\ \E v \in Values, Q \in Quorums, S \in SUBSET {m \in sent : m.type = "1b" /\ m.bal = b}:
       /\ \A a \in Q : \E m \in S : m.acc = a
       /\ \/ \A m \in S : m.maxVBal = -1
          \/ \E c \in 0..(b-1) : 
               /\ \A m \in S : m.maxVBal =< c
               /\ \E m \in S : /\ m.maxVBal = c
                               /\ m.maxVal = v
       /\ Send([type |-> "2a", bal |-> b, val |-> v])

Phase2b(a) == 
  \E m \in sent :
    /\ m.type = "2a" 
    /\ \A m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.acc = a => m.bal >= m2.bal
    /\ Send([type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a])

Next == \/ \E b \in Ballots : Phase1a(b) \/ Phase2a(b)
        \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a) 

Spec == Init /\ [][Next]_vars
-----------------------------------------------------------------------------

VotedForIn(a, v, b) == \E m \in sent : /\ m.type = "2b"
                                       /\ m.val  = v
                                       /\ m.bal  = b
                                       /\ m.acc  = a

-----------------------------------------------------------------------------

Messages ==      [type : {"1a"}, bal : Ballots]
            \cup [type : {"1b"}, bal : Ballots, maxVBal : Ballots \cup {-1},
                    maxVal : Values \cup {None}, acc : Acceptors]
            \cup [type : {"2a"}, bal : Ballots, val : Values]
            \cup [type : {"2b"}, bal : Ballots, val : Values, acc : Acceptors]

TypeOK == sent \in SUBSET Messages

WontVoteIn(a, b) == /\ \A v \in Values : ~ VotedForIn(a, v, b)
                    /\ \E m \in sent: m.type \in {"1b", "2b"} /\ m.acc = a /\ m.bal > b

SafeAt(v, b) == 
  \A b2 \in 0..(b-1) :
    \E Q \in Quorums :
      \A a \in Q : VotedForIn(a, v, b2) \/ WontVoteIn(a, b2)

MsgInv ==
  \A m \in sent : 
    /\ m.type = "1b" => /\ VotedForIn(m.acc, m.maxVal, m.maxVBal) \/ m.maxVBal = -1
                        /\ \A b \in m.maxVBal+1..m.bal-1: ~\E v \in Values: VotedForIn(m.acc, v, b)
    /\ m.type = "2a" => /\ SafeAt(m.val, m.bal)
                        /\ \A m2 \in sent : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
    /\ m.type = "2b" => \E m2 \in sent : /\ m2.type = "2a"
                                         /\ m2.bal  = m.bal
                                         /\ m2.val  = m.val

Inv == TypeOK /\ MsgInv

-----------------------------------------------------------------------------

VotedForInS(S, a, v, b) == \E m \in S : /\ m.type = "2b"
                                             /\ m.val  = v
                                             /\ m.bal  = b
                                             /\ m.acc  = a

WontVoteInS(S, a, b) ==
  /\ \A v \in Values : ~ VotedForInS(S, a, v, b)
  /\ \E m \in S: m.type \in {"1b", "2b"}
                /\ m.acc = a
                /\ m.bal > b

SafeAtS(S, v, b) ==
  \A b2 \in 0..(b-1) :
    \E Q \in Quorums :
      \A a \in Q : VotedForInS(S, a, v, b2) \/ WontVoteInS(S, a, b2)

MsgInvFor(S, m) ==
    /\ m.type = "1b" => /\ VotedForInS(S, m.acc, m.maxVal, m.maxVBal)
                           \/ m.maxVBal = -1
                         /\ \A b \in m.maxVBal+1..m.bal-1:
                              ~\E v \in Values: VotedForInS(S, m.acc, v, b)
    /\ m.type = "2a" => /\ SafeAtS(S, m.val, m.bal)
                         /\ \A m2 \in S : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
    /\ m.type = "2b" => \E m2 \in S : /\ m2.type = "2a"
                                      /\ m2.bal  = m.bal
                                      /\ m2.val  = m.val

MsgInvS(S) == \A m \in S : MsgInvFor(S, m)

TypeOKS(S) == S \in SUBSET Messages

StateInv(S) == TypeOKS(S) /\ MsgInvS(S)

LEMMA InvIsStateInv == Inv <=> StateInv(sent)
PROOF
  BY SMT DEF Inv, TypeOK, MsgInv, StateInv, TypeOKS, MsgInvS, MsgInvFor,
             VotedForIn, VotedForInS, WontVoteIn, WontVoteInS, SafeAt, SafeAtS,
             Messages, Ballots

LEMMA InvPrimeIsStateInv == Inv' <=> StateInv(sent')
PROOF
  BY SMT DEF Inv, TypeOK, MsgInv, StateInv, TypeOKS, MsgInvS, MsgInvFor,
             VotedForIn, VotedForInS, WontVoteIn, WontVoteInS, SafeAt, SafeAtS,
             Messages, Ballots

LEMMA Add1aStateInv == \A S : \A b \in Ballots :
  StateInv(S) => StateInv(S \cup {[type |-> "1a", bal |-> b]})
PROOF
  <1>1. SUFFICES ASSUME NEW S, NEW b \in Ballots, StateInv(S)
          PROVE StateInv(S \cup {[type |-> "1a", bal |-> b]})
    OBVIOUS
  <1>2. DEFINE mm == [type |-> "1a", bal |-> b]
  <1>3. TypeOKS(S \cup {mm})
    BY <1>1 DEF StateInv, TypeOKS, Messages, Ballots
  <1>4. MsgInvS(S \cup {mm})
  PROOF
    <2>1. SUFFICES ASSUME NEW m \in S \cup {mm}
            PROVE MsgInvFor(S \cup {mm}, m)
      BY DEF MsgInvS
    <2>2. CASE m \in S
      BY <1>1, <2>2 DEF StateInv, MsgInvS, MsgInvFor,
                          VotedForInS, WontVoteInS, SafeAtS
    <2>3. CASE m = mm
      BY <2>3 DEF mm, MsgInvFor
    <2>4. QED
      BY <2>2, <2>3, SMT
  <1>5. QED
    BY <1>3, <1>4 DEF StateInv

LEMMA Add1bStateInv ==
  \A S, a, b, mb, mv :
    /\ StateInv(S)
    /\ a \in Acceptors
    /\ b \in Ballots
    /\ mb \in Ballots \cup {-1}
    /\ mv \in Values \cup {None}
    /\ (VotedForInS(S, a, mv, mb) \/ mb = -1)
    /\ \A c \in mb+1..b-1 : ~\E v \in Values : VotedForInS(S, a, v, c)
    => StateInv(S \cup {[type |-> "1b", bal |-> b,
                          maxVBal |-> mb, maxVal |-> mv, acc |-> a]})
PROOF
  <1>1. SUFFICES ASSUME NEW S, NEW a, NEW b, NEW mb, NEW mv,
                          StateInv(S),
                          a \in Acceptors,
                          b \in Ballots,
                          mb \in Ballots \cup {-1},
                          mv \in Values \cup {None},
                          VotedForInS(S, a, mv, mb) \/ mb = -1,
                          \A c \in mb+1..b-1 :
                            ~\E v \in Values : VotedForInS(S, a, v, c)
          PROVE StateInv(S \cup {[type |-> "1b", bal |-> b,
                                  maxVBal |-> mb, maxVal |-> mv, acc |-> a]})
    OBVIOUS
  <1>2. DEFINE mm == [type |-> "1b", bal |-> b,
                       maxVBal |-> mb, maxVal |-> mv, acc |-> a]
  <1>3. TypeOKS(S \cup {mm})
    BY <1>1 DEF StateInv, TypeOKS, Messages, Ballots, mm
  <1>4. MsgInvS(S \cup {mm})
  PROOF
    <2>1. SUFFICES ASSUME NEW m \in S \cup {mm}
            PROVE MsgInvFor(S \cup {mm}, m)
      BY DEF MsgInvS
    <2>2. CASE m \in S
    PROOF
      <3>1. CASE m.type = "1b"
        BY <1>1, <2>2, <3>1, SMTT(20)
           DEF StateInv, MsgInvS, MsgInvFor,
               VotedForInS, WontVoteInS, SafeAtS, mm
      <3>2. CASE m.type = "2a"
        BY <1>1, <2>2, <3>2, SMTT(20)
           DEF StateInv, MsgInvS, MsgInvFor,
               VotedForInS, WontVoteInS, SafeAtS, mm
      <3>3. CASE m.type = "2b"
        BY <1>1, <2>2, <3>3
           DEF StateInv, MsgInvS, MsgInvFor, VotedForInS, mm
      <3>4. CASE m.type # "1b" /\ m.type # "2a" /\ m.type # "2b"
        BY <3>4 DEF MsgInvFor
      <3>5. QED
        BY <3>1, <3>2, <3>3, <3>4
    <2>3. CASE m = mm
      BY <1>1, <2>3 DEF mm, MsgInvFor, VotedForInS, WontVoteInS, SafeAtS
    <2>4. QED
      BY <2>2, <2>3, SMT
  <1>5. QED
    BY <1>3, <1>4 DEF StateInv

LEMMA LastVotedGood ==
  \A a, r, b :
    TypeOK /\ r \in last_voted(a) =>
      /\ r.bal \in Ballots \cup {-1}
      /\ r.val \in Values \cup {None}
      /\ (VotedForIn(a, r.val, r.bal) \/ r.bal = -1)
      /\ \A c \in r.bal+1..b-1 :
           ~\E v \in Values : VotedForIn(a, v, c)
PROOF
  BY SMTT(20) DEF TypeOK, Messages, last_voted, VotedForIn, Ballots

LEMMA OneBInvAdd2b ==
  \A S, aa, bb, vv, m :
    /\ MsgInvFor(S, m)
    /\ TypeOKS(S)
    /\ m \in S
    /\ m.type = "1b"
    /\ aa \in Acceptors
    /\ bb \in Ballots
    /\ vv \in Values
    /\ \A m2 \in S : m2.type \in {"1b", "2b"} /\ m2.acc = aa => bb >= m2.bal
    => MsgInvFor(S \cup {[type |-> "2b", bal |-> bb, val |-> vv, acc |-> aa]}, m)
PROOF
  BY SMTT(20) DEF MsgInvFor, VotedForInS, WontVoteInS, SafeAtS,
                  TypeOKS, Messages, Ballots

LEMMA WontAdd2bPreserve ==
  \A S, aa, bb, vv, a, b :
    /\ WontVoteInS(S, a, b)
    /\ ~(a = aa /\ b = bb)
    => WontVoteInS(S \cup {[type |-> "2b", bal |-> bb, val |-> vv, acc |-> aa]}, a, b)
PROOF
  BY SMT DEF WontVoteInS, VotedForInS

LEMMA NoWontAt2bBal ==
  \A S, aa, bb :
    /\ TypeOKS(S)
    /\ bb \in Ballots
    /\ (\A m2 \in S : m2.type \in {"1b", "2b"} /\ m2.acc = aa => bb >= m2.bal)
    => ~WontVoteInS(S, aa, bb)
PROOF
  BY SMTT(20) DEF WontVoteInS, VotedForInS, TypeOKS, Messages, Ballots

LEMMA SafeAtAdd2bPreserve ==
  \A S, aa, bb, vv, v, b :
    /\ SafeAtS(S, v, b)
    /\ TypeOKS(S)
    /\ bb \in Ballots
    /\ \A m2 \in S : m2.type \in {"1b", "2b"} /\ m2.acc = aa => bb >= m2.bal
    => SafeAtS(S \cup {[type |-> "2b", bal |-> bb, val |-> vv, acc |-> aa]}, v, b)
PROOF
  <1>1. SUFFICES ASSUME NEW S, NEW aa, NEW bb, NEW vv, NEW v, NEW b,
                          SafeAtS(S, v, b),
                          TypeOKS(S),
                          bb \in Ballots,
                          \A m2 \in S : m2.type \in {"1b", "2b"} /\ m2.acc = aa
                                          => bb >= m2.bal
          PROVE SafeAtS(S \cup {[type |-> "2b", bal |-> bb, val |-> vv, acc |-> aa]}, v, b)
    OBVIOUS
  <1>2. DEFINE SS == S \cup {[type |-> "2b", bal |-> bb, val |-> vv, acc |-> aa]}
  <1>3. SUFFICES ASSUME NEW b2 \in 0..b-1
          PROVE \E Q \in Quorums :
                  \A a \in Q : VotedForInS(SS, a, v, b2) \/ WontVoteInS(SS, a, b2)
    BY DEF SafeAtS
  <1>4. PICK Q \in Quorums :
          \A a \in Q : VotedForInS(S, a, v, b2) \/ WontVoteInS(S, a, b2)
    BY <1>1, <1>3 DEF SafeAtS
  <1>5. \A a \in Q : VotedForInS(SS, a, v, b2) \/ WontVoteInS(SS, a, b2)
  PROOF
    <2>1. SUFFICES ASSUME NEW a \in Q
            PROVE VotedForInS(SS, a, v, b2) \/ WontVoteInS(SS, a, b2)
      OBVIOUS
    <2>2. VotedForInS(S, a, v, b2) \/ WontVoteInS(S, a, b2)
      BY <1>4, <2>1
    <2>3. CASE VotedForInS(S, a, v, b2)
      BY <2>3 DEF SS, VotedForInS
    <2>4. CASE WontVoteInS(S, a, b2)
    PROOF
      <3>1. CASE a = aa /\ b2 = bb
        BY <1>1, <2>4, <3>1, NoWontAt2bBal
      <3>2. CASE ~(a = aa /\ b2 = bb)
        BY <2>4, <3>2, WontAdd2bPreserve DEF SS
      <3>3. QED
        BY <3>1, <3>2
    <2>5. QED
      BY <2>2, <2>3, <2>4
  <1>6. QED
    BY <1>4, <1>5

LEMMA TwoAInvAdd2b ==
  \A S, aa, bb, vv, m :
    /\ MsgInvFor(S, m)
    /\ TypeOKS(S)
    /\ m \in S
    /\ m.type = "2a"
    /\ aa \in Acceptors
    /\ bb \in Ballots
    /\ vv \in Values
    /\ \A m2 \in S : m2.type \in {"1b", "2b"} /\ m2.acc = aa => bb >= m2.bal
    => MsgInvFor(S \cup {[type |-> "2b", bal |-> bb, val |-> vv, acc |-> aa]}, m)
PROOF
  <1>1. SUFFICES ASSUME NEW S, NEW aa, NEW bb, NEW vv, NEW m,
                          MsgInvFor(S, m),
                          TypeOKS(S),
                          m \in S,
                          m.type = "2a",
                          aa \in Acceptors,
                          bb \in Ballots,
                          vv \in Values,
                          \A m2 \in S : m2.type \in {"1b", "2b"} /\ m2.acc = aa
                                          => bb >= m2.bal
          PROVE MsgInvFor(S \cup {[type |-> "2b", bal |-> bb, val |-> vv, acc |-> aa]}, m)
    OBVIOUS
  <1>2. DEFINE mm == [type |-> "2b", bal |-> bb, val |-> vv, acc |-> aa]
          SS == S \cup {mm}
  <1>3. SafeAtS(S, m.val, m.bal)
    BY <1>1 DEF MsgInvFor
  <1>4. SafeAtS(SS, m.val, m.bal)
    BY <1>1, <1>3, SafeAtAdd2bPreserve DEF SS, mm
  <1>5. \A m2 \in SS : (m2.type = "2a" /\ m2.bal = m.bal) => m2 = m
  PROOF
    <2>1. SUFFICES ASSUME NEW m2 \in SS,
                            m2.type = "2a" /\ m2.bal = m.bal
            PROVE m2 = m
      OBVIOUS
    <2>2. CASE m2 \in S
      BY <1>1, <2>1, <2>2 DEF MsgInvFor
    <2>3. CASE m2 = mm
      BY <2>1, <2>3 DEF mm
    <2>4. QED
      BY <2>1, <2>2, <2>3, SMT DEF SS
  <1>6. QED
    BY <1>1, <1>4, <1>5 DEF MsgInvFor, SS, mm

LEMMA Add2bStateInv ==
  \A S, a, b, v :
    /\ StateInv(S)
    /\ a \in Acceptors
    /\ b \in Ballots
    /\ v \in Values
    /\ \E m2 \in S : /\ m2.type = "2a"
                      /\ m2.bal = b
                      /\ m2.val = v
    /\ \A m2 \in S : m2.type \in {"1b", "2b"} /\ m2.acc = a => b >= m2.bal
    => StateInv(S \cup {[type |-> "2b", bal |-> b, val |-> v, acc |-> a]})
PROOF
  <1>1. SUFFICES ASSUME NEW S, NEW a, NEW b, NEW v,
                          StateInv(S),
                          a \in Acceptors,
                          b \in Ballots,
                          v \in Values,
                          \E m2 \in S : /\ m2.type = "2a"
                                         /\ m2.bal = b
                                         /\ m2.val = v,
                          \A m2 \in S : m2.type \in {"1b", "2b"} /\ m2.acc = a
                                          => b >= m2.bal
          PROVE StateInv(S \cup {[type |-> "2b", bal |-> b, val |-> v, acc |-> a]})
    OBVIOUS
  <1>2. DEFINE mm == [type |-> "2b", bal |-> b, val |-> v, acc |-> a]
  <1>3. TypeOKS(S \cup {mm})
    BY <1>1 DEF StateInv, TypeOKS, Messages, Ballots, mm
  <1>4. MsgInvS(S \cup {mm})
  PROOF
    <2>1. SUFFICES ASSUME NEW m \in S \cup {mm}
            PROVE MsgInvFor(S \cup {mm}, m)
      BY DEF MsgInvS
    <2>2. CASE m \in S
    PROOF
      <3>1. CASE m.type = "1b"
        BY <1>1, <2>2, <3>1, OneBInvAdd2b
           DEF StateInv, MsgInvS, mm
      <3>2. CASE m.type = "2a"
        BY <1>1, <2>2, <3>2, TwoAInvAdd2b
           DEF StateInv, MsgInvS, mm
      <3>3. CASE m.type = "2b"
        BY <1>1, <2>2, <3>3
           DEF StateInv, MsgInvS, MsgInvFor, VotedForInS, mm
      <3>4. CASE m.type # "1b" /\ m.type # "2a" /\ m.type # "2b"
        BY <3>4 DEF MsgInvFor
      <3>5. QED
        BY <3>1, <3>2, <3>3, <3>4
    <2>3. CASE m = mm
      BY <1>1, <2>3 DEF mm, MsgInvFor, VotedForInS
    <2>4. QED
      BY <2>2, <2>3, SMT
  <1>5. QED
    BY <1>3, <1>4 DEF StateInv

LEMMA SafeAtAdd2aPreserve ==
  \A S, b, v, vv, bb :
    SafeAtS(S, vv, bb) =>
      SafeAtS(S \cup {[type |-> "2a", bal |-> b, val |-> v]}, vv, bb)
PROOF
  BY SMT DEF SafeAtS, VotedForInS, WontVoteInS

LEMMA OneBImpliesWont ==
  \A S, m, b2 :
    /\ StateInv(S)
    /\ m \in S
    /\ m.type = "1b"
    /\ b2 \in m.maxVBal+1..m.bal-1
    => WontVoteInS(S, m.acc, b2)
PROOF
  BY SMTT(20) DEF StateInv, TypeOKS, MsgInvS, MsgInvFor,
                  VotedForInS, WontVoteInS, Messages, Ballots

LEMMA VoteImpliesSafeAt ==
  \A S, a, v, b :
    StateInv(S) /\ VotedForInS(S, a, v, b) => SafeAtS(S, v, b)
PROOF
  BY SMTT(20) DEF StateInv, TypeOKS, MsgInvS, MsgInvFor,
                  VotedForInS, SafeAtS, Messages, Ballots

LEMMA VoteValueUnique ==
  \A S, a1, a2, v1, v2, b :
    /\ StateInv(S)
    /\ VotedForInS(S, a1, v1, b)
    /\ VotedForInS(S, a2, v2, b)
    => v1 = v2
PROOF
  BY SMTT(20) DEF StateInv, TypeOKS, MsgInvS, MsgInvFor,
                  VotedForInS, Messages, Ballots

LEMMA InGapEq ==
  \A mb, c, b, b2 :
    /\ mb \in Ballots \cup {-1}
    /\ c \in 0..b-1
    /\ b2 \in 0..b-1
    /\ b2 = c
    /\ mb < c
    => b2 \in mb+1..b-1
PROOF
  BY SMTT(20), SimpleArithmetic DEF Ballots

LEMMA InGapGt ==
  \A mb, c, b, b2 :
    /\ mb \in Ballots \cup {-1}
    /\ c \in 0..b-1
    /\ b2 \in 0..b-1
    /\ b2 > c
    /\ mb =< c
    => b2 \in mb+1..b-1
PROOF
  BY SMTT(20), SimpleArithmetic DEF Ballots

LEMMA Add2aStateInv ==
  \A S, b, v :
    /\ StateInv(S)
    /\ b \in Ballots
    /\ v \in Values
    /\ SafeAtS(S, v, b)
    /\ ~\E m \in S : m.type = "2a" /\ m.bal = b
    => StateInv(S \cup {[type |-> "2a", bal |-> b, val |-> v]})
PROOF
  <1>1. SUFFICES ASSUME NEW S, NEW b, NEW v,
                          StateInv(S),
                          b \in Ballots,
                          v \in Values,
                          SafeAtS(S, v, b),
                          ~\E m \in S : m.type = "2a" /\ m.bal = b
          PROVE StateInv(S \cup {[type |-> "2a", bal |-> b, val |-> v]})
    OBVIOUS
  <1>2. DEFINE mm == [type |-> "2a", bal |-> b, val |-> v]
  <1>3. TypeOKS(S \cup {mm})
    BY <1>1 DEF StateInv, TypeOKS, Messages, Ballots, mm
  <1>4. MsgInvS(S \cup {mm})
  PROOF
    <2>1. SUFFICES ASSUME NEW m \in S \cup {mm}
            PROVE MsgInvFor(S \cup {mm}, m)
      BY DEF MsgInvS
    <2>2. CASE m \in S
      BY <1>1, <2>2, SMTT(20)
         DEF StateInv, MsgInvS, MsgInvFor,
             VotedForInS, WontVoteInS, SafeAtS, mm
    <2>3. CASE m = mm
    PROOF
      <3>1. SafeAtS(S \cup {mm}, v, b)
        BY <1>1, SafeAtAdd2aPreserve DEF mm
      <3>2. \A m2 \in S \cup {mm} : (m2.type = "2a" /\ m2.bal = b) => m2 = mm
        BY <1>1 DEF mm
      <3>3. QED
        BY <2>3, <3>1, <3>2 DEF mm, MsgInvFor
    <2>4. QED
      BY <2>2, <2>3, SMT
  <1>5. QED
    BY <1>3, <1>4 DEF StateInv

LEMMA Phase2aSafe ==
  \A S, b, v, Q, R :
    /\ StateInv(S)
    /\ b \in Ballots
    /\ v \in Values
    /\ Q \in Quorums
    /\ R \in SUBSET {m \in S : m.type = "1b" /\ m.bal = b}
    /\ \A a \in Q : \E m \in R : m.acc = a
    /\ \/ \A m \in R : m.maxVBal = -1
       \/ \E c \in 0..b-1 :
            /\ \A m \in R : m.maxVBal =< c
            /\ \E m \in R : /\ m.maxVBal = c
                            /\ m.maxVal = v
    => SafeAtS(S, v, b)
PROOF
  <1>1. SUFFICES ASSUME NEW S, NEW b, NEW v, NEW Q, NEW R,
                          StateInv(S),
                          b \in Ballots,
                          v \in Values,
                          Q \in Quorums,
                          R \in SUBSET {m \in S : m.type = "1b" /\ m.bal = b},
                          \A a \in Q : \E m \in R : m.acc = a,
                          \/ \A m \in R : m.maxVBal = -1
                          \/ \E c \in 0..b-1 :
                               /\ \A m \in R : m.maxVBal =< c
                               /\ \E m \in R : /\ m.maxVBal = c
                                               /\ m.maxVal = v
          PROVE SafeAtS(S, v, b)
    OBVIOUS
  <1>2. SUFFICES ASSUME NEW b2 \in 0..b-1
          PROVE \E QQ \in Quorums :
                  \A a \in QQ : VotedForInS(S, a, v, b2) \/ WontVoteInS(S, a, b2)
    BY DEF SafeAtS
  <1>3. CASE \A m \in R : m.maxVBal = -1
  PROOF
    <2>1. \A a \in Q : WontVoteInS(S, a, b2)
    PROOF
      <3>1. SUFFICES ASSUME NEW a \in Q
              PROVE WontVoteInS(S, a, b2)
        OBVIOUS
      <3>2. PICK m \in R : m.acc = a
        BY <1>1, <3>1
      <3>3. /\ m \in S
             /\ m.type = "1b"
             /\ m.bal = b
             /\ m.maxVBal = -1
        BY <1>1, <1>3, <3>2
      <3>4. b2 \in m.maxVBal+1..m.bal-1
        BY <1>2, <3>3, SMT
      <3>5. QED
        BY <1>1, <3>2, <3>3, <3>4, OneBImpliesWont
    <2>2. QED
      BY <1>1, <2>1
  <1>4. CASE \E c \in 0..b-1 :
                 /\ \A m \in R : m.maxVBal =< c
                 /\ \E m \in R : /\ m.maxVBal = c
                                 /\ m.maxVal = v
  PROOF
    <2>1. PICK c \in 0..b-1 :
             /\ \A m \in R : m.maxVBal =< c
             /\ \E m \in R : /\ m.maxVBal = c
                             /\ m.maxVal = v
      BY <1>4
    <2>2. PICK mx \in R : /\ mx.maxVBal = c
                           /\ mx.maxVal = v
      BY <2>1
    <2>3. VotedForInS(S, mx.acc, v, c)
      BY <1>1, <2>1, <2>2, SMT
         DEF StateInv, MsgInvS, MsgInvFor
    <2>4. SafeAtS(S, v, c)
      BY <1>1, <2>3, VoteImpliesSafeAt
    <2>5. CASE b2 < c
    PROOF
      <3>1. b2 \in 0..c-1
        BY <1>2, <2>1, <2>5, SMT
      <3>2. QED
        BY <2>4, <3>1 DEF SafeAtS
    <2>6. CASE b2 = c
    PROOF
      <3>1. \A a \in Q : VotedForInS(S, a, v, b2) \/ WontVoteInS(S, a, b2)
      PROOF
        <4>1. SUFFICES ASSUME NEW a \in Q
                PROVE VotedForInS(S, a, v, b2) \/ WontVoteInS(S, a, b2)
          OBVIOUS
        <4>2. PICK m \in R : m.acc = a
          BY <1>1, <4>1
        <4>3. /\ m \in S
               /\ m.type = "1b"
               /\ m.bal = b
               /\ m.maxVBal =< c
               /\ m.maxVBal \in Ballots \cup {-1}
          BY <1>1, <2>1, <4>2 DEF StateInv, TypeOKS, Messages, Ballots
        <4>4. CASE m.maxVBal < c
        PROOF
          <5>1. b2 \in m.maxVBal+1..m.bal-1
            BY <1>2, <2>1, <2>6, <4>3, <4>4, InGapEq
          <5>2. WontVoteInS(S, a, b2)
            BY <1>1, <4>2, <4>3, <5>1, OneBImpliesWont
          <5>3. QED
            BY <5>2
        <4>5. CASE m.maxVBal = c
        PROOF
          <5>1. VotedForInS(S, a, m.maxVal, c)
            BY <1>1, <4>2, <4>3, <4>5, SMT
               DEF StateInv, MsgInvS, MsgInvFor
          <5>2. m.maxVal = v
            BY <1>1, <2>3, <5>1, VoteValueUnique
          <5>3. VotedForInS(S, a, v, b2)
            BY <2>6, <5>1, <5>2
          <5>4. QED
            BY <5>3
        <4>6. QED
          BY <4>3, <4>4, <4>5, SMT
      <3>2. QED
        BY <1>1, <3>1
    <2>7. CASE b2 > c
    PROOF
      <3>1. \A a \in Q : WontVoteInS(S, a, b2)
      PROOF
        <4>1. SUFFICES ASSUME NEW a \in Q
                PROVE WontVoteInS(S, a, b2)
          OBVIOUS
        <4>2. PICK m \in R : m.acc = a
          BY <1>1, <4>1
        <4>3. /\ m \in S
               /\ m.type = "1b"
               /\ m.bal = b
               /\ m.maxVBal =< c
               /\ m.maxVBal \in Ballots \cup {-1}
          BY <1>1, <2>1, <4>2 DEF StateInv, TypeOKS, Messages, Ballots
        <4>4. b2 \in m.maxVBal+1..m.bal-1
          BY <1>2, <2>1, <2>7, <4>3, InGapGt
        <4>5. QED
          BY <1>1, <4>2, <4>3, <4>4, OneBImpliesWont
      <3>2. QED
        BY <1>1, <3>1
    <2>8. QED
      BY <1>2, <2>1, <2>5, <2>6, <2>7, SMT
  <1>5. QED
    BY <1>1, <1>3, <1>4

-----------------------------------------------------------------------------

LEMMA InitInv == Init => Inv
PROOF
  BY SMT DEF Init, Inv, TypeOK, MsgInv, Messages, VotedForIn, SafeAt, WontVoteIn

LEMMA Phase1aInv == \A b \in Ballots : Inv /\ Phase1a(b) => Inv'
PROOF
  <1>1. SUFFICES ASSUME NEW b \in Ballots, Inv, Phase1a(b)
          PROVE Inv'
    OBVIOUS
  <1>2. StateInv(sent)
    BY <1>1, InvIsStateInv
  <1>3. sent' = sent \cup {[type |-> "1a", bal |-> b]}
    BY <1>1 DEF Phase1a, Send
  <1>4. StateInv(sent \cup {[type |-> "1a", bal |-> b]})
    BY <1>1, <1>2, Add1aStateInv
  <1>5. StateInv(sent')
    BY <1>3, <1>4
  <1>6. QED
    BY <1>5, InvPrimeIsStateInv

LEMMA Phase1bInv == \A a \in Acceptors : Inv /\ Phase1b(a) => Inv'
PROOF
  <1>1. SUFFICES ASSUME NEW a \in Acceptors, Inv, Phase1b(a)
          PROVE Inv'
    OBVIOUS
  <1>2. PICK m \in sent, r \in last_voted(a) :
          /\ m.type = "1a"
          /\ \A m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.acc = a => m.bal > m2.bal
          /\ sent' = sent \cup {[type |-> "1b", bal |-> m.bal,
                                  maxVBal |-> r.bal, maxVal |-> r.val, acc |-> a]}
    BY <1>1 DEF Phase1b, Send
  <1>3. StateInv(sent)
    BY <1>1, InvIsStateInv
  <1>4. TypeOK
    BY <1>1 DEF Inv
  <1>5. m.bal \in Ballots
    BY <1>1, <1>2, <1>4 DEF TypeOK, Messages, Ballots
  <1>6. /\ r.bal \in Ballots \cup {-1}
         /\ r.val \in Values \cup {None}
         /\ (VotedForIn(a, r.val, r.bal) \/ r.bal = -1)
         /\ \A c \in r.bal+1..m.bal-1 :
              ~\E v \in Values : VotedForIn(a, v, c)
    BY <1>2, <1>4, LastVotedGood
  <1>7. /\ r.bal \in Ballots \cup {-1}
         /\ r.val \in Values \cup {None}
         /\ (VotedForInS(sent, a, r.val, r.bal) \/ r.bal = -1)
         /\ \A c \in r.bal+1..m.bal-1 :
              ~\E v \in Values : VotedForInS(sent, a, v, c)
    BY <1>6 DEF VotedForIn, VotedForInS
  <1>8. /\ StateInv(sent)
         /\ a \in Acceptors
         /\ m.bal \in Ballots
         /\ r.bal \in Ballots \cup {-1}
         /\ r.val \in Values \cup {None}
         /\ (VotedForInS(sent, a, r.val, r.bal) \/ r.bal = -1)
         /\ \A c \in r.bal+1..m.bal-1 :
              ~\E v \in Values : VotedForInS(sent, a, v, c)
    BY <1>1, <1>3, <1>5, <1>7
  <1>9. StateInv(sent \cup {[type |-> "1b", bal |-> m.bal,
                              maxVBal |-> r.bal, maxVal |-> r.val, acc |-> a]})
    BY <1>8, Add1bStateInv, SMT
  <1>10. StateInv(sent')
    BY <1>2, <1>9
  <1>11. QED
    BY <1>10, InvPrimeIsStateInv

LEMMA Phase2aInv == \A b \in Ballots : Inv /\ Phase2a(b) => Inv'
PROOF
  <1>1. SUFFICES ASSUME NEW b \in Ballots, Inv, Phase2a(b)
          PROVE Inv'
    OBVIOUS
  <1>2. PICK v \in Values, Q \in Quorums,
              R \in SUBSET {m \in sent : m.type = "1b" /\ m.bal = b} :
          /\ \A a \in Q : \E m \in R : m.acc = a
          /\ \/ \A m \in R : m.maxVBal = -1
             \/ \E c \in 0..b-1 :
                  /\ \A m \in R : m.maxVBal =< c
                  /\ \E m \in R : /\ m.maxVBal = c
                                  /\ m.maxVal = v
          /\ sent' = sent \cup {[type |-> "2a", bal |-> b, val |-> v]}
          /\ ~\E m \in sent : m.type = "2a" /\ m.bal = b
    BY <1>1 DEF Phase2a, Send
  <1>3. StateInv(sent)
    BY <1>1, InvIsStateInv
  <1>4. SafeAtS(sent, v, b)
    BY <1>1, <1>2, <1>3, Phase2aSafe
  <1>5. StateInv(sent \cup {[type |-> "2a", bal |-> b, val |-> v]})
    BY <1>1, <1>2, <1>3, <1>4, Add2aStateInv
  <1>6. StateInv(sent')
    BY <1>2, <1>5
  <1>7. QED
    BY <1>6, InvPrimeIsStateInv

LEMMA Phase2bInv == \A a \in Acceptors : Inv /\ Phase2b(a) => Inv'
PROOF
  <1>1. SUFFICES ASSUME NEW a \in Acceptors, Inv, Phase2b(a)
          PROVE Inv'
    OBVIOUS
  <1>2. PICK m \in sent :
          /\ m.type = "2a"
          /\ \A m2 \in sent: m2.type \in {"1b", "2b"} /\ m2.acc = a => m.bal >= m2.bal
          /\ sent' = sent \cup {[type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a]}
    BY <1>1 DEF Phase2b, Send
  <1>3. StateInv(sent)
    BY <1>1, InvIsStateInv
  <1>4. TypeOK
    BY <1>1 DEF Inv
  <1>5. /\ m.bal \in Ballots
         /\ m.val \in Values
    BY <1>2, <1>4 DEF TypeOK, Messages, Ballots
  <1>6. \E m2 \in sent : /\ m2.type = "2a"
                           /\ m2.bal = m.bal
                           /\ m2.val = m.val
    BY <1>2
  <1>7. StateInv(sent \cup {[type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a]})
    BY <1>1, <1>2, <1>3, <1>5, <1>6, Add2bStateInv, SMT
  <1>8. StateInv(sent')
    BY <1>2, <1>7
  <1>9. QED
    BY <1>8, InvPrimeIsStateInv

LEMMA NextInv == Inv /\ Next => Inv'
PROOF
  BY Phase1aInv, Phase1bInv, Phase2aInv, Phase2bInv
     DEF Next, Ballots

LEMMA StepInv == Inv /\ [Next]_vars => Inv'
PROOF
  BY NextInv, SMT DEF Inv, TypeOK, MsgInv, VotedForIn, SafeAt, WontVoteIn, vars

-----------------------------------------------------------------------------

THEOREM Invariant == Spec => []Inv
PROOF
  BY InitInv, StepInv, PTL DEF Spec

=============================================================================
