------------------------------- MODULE Paxos_Refinement -------------------------------

EXTENDS Integers, TLAPS, TLC
-----------------------------------------------------------------------------
CONSTANTS Acceptors, Values, Quorums

ASSUME QuorumAssumption == 
          /\ Quorums \subseteq SUBSET Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}                 

Ballots == Nat

None == CHOOSE v : v \notin Values

-----------------------------------------------------------------------------
VARIABLES msgs,    
          maxBal,  
          maxVBal, 
          maxVal   

vars == <<msgs, maxBal, maxVBal, maxVal>>

Send(m) == msgs' = msgs \cup {m}
-----------------------------------------------------------------------------
Init == /\ msgs = {}
        /\ maxVBal = [a \in Acceptors |-> -1]
        /\ maxBal  = [a \in Acceptors |-> -1]
        /\ maxVal  = [a \in Acceptors |-> None]

Phase1a(b) == /\ ~ \E m \in msgs : (m.type = "1a") /\ (m.bal = b)
              /\ Send([type |-> "1a", bal |-> b])
              /\ UNCHANGED <<maxVBal, maxBal, maxVal>>
              
Phase1b(a) == 
  \E m \in msgs : 
     /\ m.type = "1a"
     /\ m.bal > maxBal[a]
     /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
     /\ Send([type |-> "1b", bal |-> m.bal, 
           maxVBal |-> maxVBal[a], maxVal |-> maxVal[a], acc |-> a])
     /\ UNCHANGED <<maxVBal, maxVal>>
        
Phase2a(b) ==
  /\ ~ \E m \in msgs : (m.type = "2a") /\ (m.bal = b) 
  /\ \E v \in Values :
       /\ \E Q \in Quorums :
            \E S \in SUBSET {m \in msgs : (m.type = "1b") /\ (m.bal = b)} :
               /\ \A a \in Q : \E m \in S : m.acc = a
               /\ \/ \A m \in S : m.maxVBal = -1
                  \/ \E c \in 0..(b-1) : 
                        /\ \A m \in S : m.maxVBal =< c
                        /\ \E m \in S : /\ m.maxVBal = c
                                        /\ m.maxVal = v
       /\ Send([type |-> "2a", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

Phase2b(a) == 
  \E m \in msgs :
    /\ m.type = "2a" 
    /\ m.bal >= maxBal[a]
    /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
    /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
    /\ maxVal' = [maxVal EXCEPT ![a] = m.val]
    /\ Send([type |-> "2b", bal |-> m.bal, val |-> m.val, acc |-> a])
-----------------------------------------------------------------------------
Next == \/ \E b \in Ballots : Phase1a(b) \/ Phase2a(b)
        \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a) 

Spec == Init /\ [][Next]_vars       
-----------------------------------------------------------------------------
VotedForIn(a, v, b) == \E m \in msgs : /\ m.type = "2b"
                                       /\ m.val  = v
                                       /\ m.bal  = b
                                       /\ m.acc  = a

ChosenIn(v, b) == \E Q \in Quorums :
                     \A a \in Q : VotedForIn(a, v, b)

Chosen(v) == \E b \in Ballots : ChosenIn(v, b)

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------

NI == INSTANCE NaturalsInduction

Is1a(m) == m.type = "1a"
Is1b(m) == m.type = "1b"
Is2a(m) == m.type = "2a"
Is2b(m) == m.type = "2b"

MsgTypeOK ==
  \A m \in msgs :
    \/ /\ Is1a(m)
       /\ m.bal \in Ballots
    \/ /\ Is1b(m)
       /\ m.bal \in Ballots
       /\ m.acc \in Acceptors
    \/ /\ Is2a(m)
       /\ m.bal \in Ballots
       /\ m.val \in Values
    \/ /\ Is2b(m)
       /\ m.bal \in Ballots
       /\ m.val \in Values
       /\ m.acc \in Acceptors

MaxTypeOK ==
  /\ maxBal \in [Acceptors -> ({-1} \cup Ballots)]
  /\ maxVBal \in [Acceptors -> ({-1} \cup Ballots)]
  /\ maxVal \in [Acceptors -> (Values \cup {None})]

SafeMsg(v, b) ==
  \E Q \in Quorums :
    \E S \in SUBSET {m \in msgs : /\ Is1b(m) /\ m.bal = b} :
      /\ \A a \in Q : \E m \in S : m.acc = a
      /\ \/ \A m \in S : m.maxVBal = -1
         \/ \E c \in 0..(b-1) :
              /\ \A m \in S : m.maxVBal =< c
              /\ \E m \in S : /\ m.maxVBal = c
                              /\ m.maxVal = v

SafeAt(v, b) ==
  \A c \in 0..(b-1) :
    \A w \in Values : ChosenIn(w, c) => w = v

One2a ==
  \A m1, m2 \in msgs :
    (/\ Is2a(m1)
     /\ Is2a(m2)
     /\ m1.bal = m2.bal)
    => (m1.val = m2.val)

VoteInv ==
  \A m \in msgs :
    Is2b(m) =>
      \E n \in msgs : /\ Is2a(n)
                      /\ n.bal = m.bal
                      /\ n.val = m.val

SafeMsgInv ==
  \A m \in msgs :
    Is2a(m) => SafeMsg(m.val, m.bal)

MaxBalInv ==
  \A a \in Acceptors :
    \A m \in msgs :
      ((Is1b(m) \/ Is2b(m)) /\ m.acc = a)
      => (m.bal <= maxBal[a])

MaxVBalInv ==
  \A a \in Acceptors :
    \A m \in msgs :
      (Is2b(m) /\ m.acc = a)
      => (m.bal <= maxVBal[a])

MaxValInv ==
  \A a \in Acceptors :
    maxVBal[a] = -1 \/ VotedForIn(a, maxVal[a], maxVBal[a])

MaxVBalLeMaxBal ==
  \A a \in Acceptors : maxVBal[a] <= maxBal[a]

PromiseInv ==
  \A r \in msgs :
    Is1b(r) =>
      /\ (r.maxVBal = -1 \/ VotedForIn(r.acc, r.maxVal, r.maxVBal))
      /\ \A m \in msgs :
           (/\ Is2b(m)
            /\ m.acc = r.acc
            /\ m.bal < r.bal)
           => (m.bal <= r.maxVBal)

IndInv ==
  /\ MsgTypeOK
  /\ MaxTypeOK
  /\ One2a
  /\ VoteInv
  /\ SafeMsgInv
  /\ MaxBalInv
  /\ MaxVBalInv
  /\ MaxValInv
  /\ PromiseInv

THEOREM InitImpliesIndInv == Init => IndInv
PROOF
  BY SMT DEF Init, IndInv, MsgTypeOK, MaxTypeOK, One2a, VoteInv,
             SafeMsgInv, MaxBalInv, MaxVBalInv, MaxValInv,
             PromiseInv, VotedForIn

MsgsMonotone == msgs \subseteq msgs'

THEOREM SendImpliesMsgsMonotone ==
  \A m : Send(m) => MsgsMonotone
PROOF
  BY SMT DEF Send, MsgsMonotone

THEOREM NextImpliesMsgsMonotone ==
  [Next]_vars => MsgsMonotone
PROOF
  BY SMT DEF Next, Phase1a, Phase1b, Phase2a, Phase2b, Send,
             MsgsMonotone, vars

SafeMsgMonotone ==
  \A v, b : SafeMsg(v, b) => SafeMsg(v, b)'

THEOREM MsgsMonotoneImpliesSafeMsgMonotone ==
  MsgsMonotone => SafeMsgMonotone
PROOF
  BY SMT DEF MsgsMonotone, SafeMsgMonotone, SafeMsg, Is1b

THEOREM ExceptApply ==
  \A S, T, f, i, e, j :
    /\ f \in [S -> T]
    /\ i \in S
    /\ j \in S
    => [f EXCEPT ![i] = e][j] = IF j = i THEN e ELSE f[j]
PROOF
  BY SMT

THEOREM Add2aPreservesSafeMsgInv ==
  \A b, v :
    /\ SafeMsgInv
    /\ SafeMsg(v, b)
    /\ SafeMsgMonotone
    /\ msgs' = msgs \cup {[type |-> "2a", bal |-> b, val |-> v]}
    => SafeMsgInv'
PROOF
  BY SMTT(30) DEF SafeMsgInv, SafeMsgMonotone, Is2a

THEOREM Phase1aPreservesIndInv ==
  IndInv /\ (\E b \in Ballots : Phase1a(b)) => IndInv'
PROOF
<1>1. ASSUME IndInv, \E b \in Ballots : Phase1a(b)
      PROVE  IndInv'
  <2>1. MsgTypeOK'
    BY <1>1, SMTT(30) DEF IndInv, MsgTypeOK, Phase1a, Send,
                          Is1a, Is1b, Is2a, Is2b, Ballots
  <2>2. MaxTypeOK'
    BY <1>1, SMTT(30) DEF IndInv, MaxTypeOK, Phase1a, Send, Ballots
  <2>3. One2a'
    BY <1>1, SMTT(30) DEF IndInv, One2a, Phase1a, Send, Is2a
  <2>4. VoteInv'
    BY <1>1, SMTT(30) DEF IndInv, VoteInv, Phase1a, Send, Is2a, Is2b
  <2>5. SafeMsgInv'
    BY <1>1, SendImpliesMsgsMonotone, MsgsMonotoneImpliesSafeMsgMonotone,
       SMTT(30) DEF IndInv, SafeMsgInv, Phase1a, Send, Is2a,
                    SafeMsgMonotone, MsgsMonotone
  <2>6. MaxBalInv'
    BY <1>1, SMTT(30) DEF IndInv, MaxBalInv, Phase1a, Send, Is1b, Is2b
  <2>7. MaxVBalInv'
    BY <1>1, SMTT(30) DEF IndInv, MaxVBalInv, Phase1a, Send, Is2b
  <2>8. MaxValInv'
    BY <1>1, SMTT(30) DEF IndInv, MaxValInv, Phase1a, Send, VotedForIn
  <2>9. PromiseInv'
    BY <1>1, SMTT(30) DEF IndInv, PromiseInv, Phase1a, Send,
                          Is1b, Is2b, VotedForIn
  <2>10. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8,
       <2>9 DEF IndInv
<1>2. QED
  BY <1>1

THEOREM Phase1bPreservesIndInv ==
  IndInv /\ (\E a \in Acceptors : Phase1b(a)) => IndInv'
PROOF
<1>1. ASSUME IndInv, \E a \in Acceptors : Phase1b(a)
      PROVE  IndInv'
  <2>1. MsgTypeOK'
    BY <1>1, SMTT(30) DEF IndInv, MsgTypeOK, Phase1b, Send,
                          Is1a, Is1b, Is2a, Is2b, Ballots
  <2>2. MaxTypeOK'
    BY <1>1, SMTT(30) DEF IndInv, MsgTypeOK, MaxTypeOK, Phase1b, Send,
                          Is1a, Is1b, Is2a, Is2b, Ballots
  <2>3. One2a'
    BY <1>1, SMTT(30) DEF IndInv, One2a, Phase1b, Send, Is2a
  <2>4. VoteInv'
    BY <1>1, SMTT(30) DEF IndInv, VoteInv, Phase1b, Send, Is2a, Is2b
  <2>5. SafeMsgInv'
    BY <1>1, SendImpliesMsgsMonotone, MsgsMonotoneImpliesSafeMsgMonotone,
       SMTT(30) DEF IndInv, SafeMsgInv, Phase1b, Send, Is2a,
                    SafeMsgMonotone, MsgsMonotone
  <2>6. MaxBalInv'
  PROOF
    <3>1. PICK aa \in Acceptors : Phase1b(aa)
      BY <1>1
    <3>2. QED
      BY <1>1, <3>1, SMTT(30) DEF IndInv, MsgTypeOK, MaxTypeOK,
                                      MaxBalInv, Phase1b, Send,
                                      Is1a, Is1b, Is2a, Is2b, Ballots
  <2>7. MaxVBalInv'
    BY <1>1, SMTT(30) DEF IndInv, MaxVBalInv, Phase1b, Send, Is2b
  <2>8. MaxValInv'
    BY <1>1, SMTT(30) DEF IndInv, MaxValInv, Phase1b, Send, VotedForIn
  <2>9. PromiseInv'
    BY <1>1, SMTT(30) DEF IndInv, PromiseInv, MaxVBalInv, MaxValInv,
                          Phase1b, Send, Is1a, Is1b, Is2b, VotedForIn
  <2>10. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8,
       <2>9 DEF IndInv
<1>2. QED
  BY <1>1

THEOREM Phase2aPreservesIndInv ==
  IndInv /\ (\E b \in Ballots : Phase2a(b)) => IndInv'
PROOF
<1>1. ASSUME IndInv, \E b \in Ballots : Phase2a(b)
      PROVE  IndInv'
  <2>1. MsgTypeOK'
    BY <1>1, SMTT(30) DEF IndInv, MsgTypeOK, Phase2a, Send,
                          Is1a, Is1b, Is2a, Is2b, Ballots
  <2>2. MaxTypeOK'
    BY <1>1, SMTT(30) DEF IndInv, MaxTypeOK, Phase2a, Send
  <2>3. One2a'
    BY <1>1, SMTT(30) DEF IndInv, One2a, Phase2a, Send, Is2a
  <2>4. VoteInv'
    BY <1>1, SMTT(30) DEF IndInv, VoteInv, Phase2a, Send, Is2a, Is2b
  <2>5. SafeMsgInv'
  PROOF
    <3>1. PICK bb \in Ballots : Phase2a(bb)
      BY <1>1
    <3>2. PICK vv \in Values,
                 QQ \in Quorums,
                 SS \in SUBSET {m \in msgs : /\ m.type = "1b" /\ m.bal = bb} :
             /\ \A a \in QQ : \E m \in SS : m.acc = a
             /\ \/ \A m \in SS : m.maxVBal = -1
                \/ \E c \in 0..(bb-1) :
                     /\ \A m \in SS : m.maxVBal =< c
                     /\ \E m \in SS : /\ m.maxVBal = c
                                     /\ m.maxVal = vv
             /\ Send([type |-> "2a", bal |-> bb, val |-> vv])
      BY <3>1 DEF Phase2a
    <3>3. SafeMsg(vv, bb)
      BY <3>2, SMT DEF SafeMsg, Is1b
    <3>4. SafeMsgMonotone
      BY <3>2, SendImpliesMsgsMonotone, MsgsMonotoneImpliesSafeMsgMonotone,
         SMT DEF Send, MsgsMonotone
    <3>5. msgs' = msgs \cup {[type |-> "2a", bal |-> bb, val |-> vv]}
      BY <3>2 DEF Send
    <3>6. QED
      BY <1>1, <3>3, <3>4, <3>5, Add2aPreservesSafeMsgInv,
         SMT DEF IndInv
  <2>6. MaxBalInv'
    BY <1>1, SMTT(30) DEF IndInv, MaxBalInv, Phase2a, Send, Is1b, Is2b
  <2>7. MaxVBalInv'
    BY <1>1, SMTT(30) DEF IndInv, MaxVBalInv, Phase2a, Send, Is2b
  <2>8. MaxValInv'
    BY <1>1, SMTT(30) DEF IndInv, MaxValInv, Phase2a, Send, VotedForIn
  <2>9. PromiseInv'
    BY <1>1, SMTT(30) DEF IndInv, PromiseInv, Phase2a, Send,
                          Is1b, Is2b, VotedForIn
  <2>10. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8,
       <2>9 DEF IndInv
<1>2. QED
  BY <1>1

THEOREM Phase2bPreservesIndInv ==
  IndInv /\ (\E a \in Acceptors : Phase2b(a)) => IndInv'
PROOF
<1>1. ASSUME IndInv, \E a \in Acceptors : Phase2b(a)
      PROVE  IndInv'
  <2>1. MsgTypeOK'
    BY <1>1, SMTT(30) DEF IndInv, MsgTypeOK, Phase2b, Send,
                          Is1a, Is1b, Is2a, Is2b, Ballots
  <2>2. MaxTypeOK'
    BY <1>1, SMTT(30) DEF IndInv, MsgTypeOK, MaxTypeOK, Phase2b, Send,
                          Is1a, Is1b, Is2a, Is2b, Ballots
  <2>3. One2a'
    BY <1>1, SMTT(30) DEF IndInv, One2a, Phase2b, Send, Is2a
  <2>4. VoteInv'
    BY <1>1, SMTT(30) DEF IndInv, VoteInv, Phase2b, Send, Is2a, Is2b
  <2>5. SafeMsgInv'
    BY <1>1, SendImpliesMsgsMonotone, MsgsMonotoneImpliesSafeMsgMonotone,
       SMTT(30) DEF IndInv, SafeMsgInv, Phase2b, Send, Is2a,
                    SafeMsgMonotone, MsgsMonotone
  <2>6. MaxBalInv'
  PROOF
    <3>1. PICK aa \in Acceptors : Phase2b(aa)
      BY <1>1
    <3>2. PICK mm \in msgs :
             /\ mm.type = "2a"
             /\ mm.bal >= maxBal[aa]
             /\ maxVBal' = [maxVBal EXCEPT ![aa] = mm.bal]
             /\ maxBal' = [maxBal EXCEPT ![aa] = mm.bal]
             /\ maxVal' = [maxVal EXCEPT ![aa] = mm.val]
             /\ Send([type |-> "2b", bal |-> mm.bal, val |-> mm.val, acc |-> aa])
      BY <3>1 DEF Phase2b
    <3>3. \A x \in Acceptors :
             maxBal'[x] = IF x = aa THEN mm.bal ELSE maxBal[x]
      BY <1>1, <3>1, <3>2, SMT DEF IndInv, MaxTypeOK
    <3>4. msgs' = msgs \cup {[type |-> "2b", bal |-> mm.bal, val |-> mm.val, acc |-> aa]}
      BY <3>2 DEF Send
    <3>5. QED
      BY <1>1, <3>1, <3>2, <3>3, <3>4, ExceptApply, SimplifyAndSolve
         DEF IndInv, MaxTypeOK,
                                      MaxBalInv, Phase2b, Send,
                                      Is1b, Is2b
  <2>7. MaxVBalInv'
  PROOF
    <3>1. PICK aa \in Acceptors : Phase2b(aa)
      BY <1>1
    <3>2. PICK mm \in msgs :
             /\ mm.type = "2a"
             /\ mm.bal >= maxBal[aa]
             /\ maxVBal' = [maxVBal EXCEPT ![aa] = mm.bal]
             /\ maxBal' = [maxBal EXCEPT ![aa] = mm.bal]
             /\ maxVal' = [maxVal EXCEPT ![aa] = mm.val]
             /\ Send([type |-> "2b", bal |-> mm.bal, val |-> mm.val, acc |-> aa])
      BY <3>1 DEF Phase2b
    <3>3. QED
      BY <1>1, <3>1, <3>2, ExceptApply, SimplifyAndSolve
         DEF IndInv, MaxTypeOK,
                                      MaxBalInv, MaxVBalInv, Phase2b, Send,
                                      Is1b, Is2b
  <2>8. MaxValInv'
  PROOF
    <3>1. PICK aa \in Acceptors : Phase2b(aa)
      BY <1>1
    <3>2. PICK mm \in msgs :
             /\ mm.type = "2a"
             /\ mm.bal >= maxBal[aa]
             /\ maxVBal' = [maxVBal EXCEPT ![aa] = mm.bal]
             /\ maxBal' = [maxBal EXCEPT ![aa] = mm.bal]
             /\ maxVal' = [maxVal EXCEPT ![aa] = mm.val]
             /\ Send([type |-> "2b", bal |-> mm.bal, val |-> mm.val, acc |-> aa])
      BY <3>1 DEF Phase2b
    <3>3. QED
      BY <1>1, <3>1, <3>2, ExceptApply, SimplifyAndSolve
         DEF IndInv, MaxTypeOK,
                                      MaxValInv, Phase2b, Send,
                                      Is2a, Is2b, VotedForIn
  <2>9. PromiseInv'
  PROOF
    <3>1. PICK aa \in Acceptors : Phase2b(aa)
      BY <1>1
    <3>2. PICK mm \in msgs :
             /\ mm.type = "2a"
             /\ mm.bal >= maxBal[aa]
             /\ maxVBal' = [maxVBal EXCEPT ![aa] = mm.bal]
             /\ maxBal' = [maxBal EXCEPT ![aa] = mm.bal]
             /\ maxVal' = [maxVal EXCEPT ![aa] = mm.val]
             /\ Send([type |-> "2b", bal |-> mm.bal, val |-> mm.val, acc |-> aa])
      BY <3>1 DEF Phase2b
    <3>3. QED
      BY <1>1, <3>1, <3>2, ExceptApply, SimplifyAndSolve
         DEF IndInv, MaxTypeOK,
                                      MaxBalInv, PromiseInv, Phase2b, Send,
                                      Is1b, Is2b, VotedForIn
  <2>10. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6, <2>7, <2>8,
       <2>9 DEF IndInv
<1>2. QED
  BY <1>1

THEOREM NextPreservesIndInv ==
  IndInv /\ [Next]_vars => IndInv'
PROOF
  BY Phase1aPreservesIndInv, Phase1bPreservesIndInv,
     Phase2aPreservesIndInv, Phase2bPreservesIndInv, SMT
     DEF Next, vars, IndInv

SafeMsgStep(v, n) ==
  /\ v \in Values
  /\ n \in Ballots
  /\ SafeMsg(v, n)
  /\ \A k \in 0..(n-1) :
       \A vv \in Values : SafeMsg(vv, k) => SafeAt(vv, k)
  => SafeAt(v, n)

THEOREM SafeMsgStepLemma ==
  IndInv => \A n \in Ballots : \A v \in Values : SafeMsgStep(v, n)
PROOF
  BY SMTT(60) DEF SafeMsgStep, SafeMsg, SafeAt, ChosenIn, VotedForIn,
                 IndInv, MsgTypeOK, One2a, VoteInv, PromiseInv,
                 SafeMsgInv, Is1b, Is2a, Is2b

THEOREM SafeMsgImpliesSafeAt ==
  IndInv => \A n \in Ballots : \A v \in Values : SafeMsg(v, n) => SafeAt(v, n)
PROOF
<1>1. ASSUME IndInv
      PROVE  \A n \in Ballots : \A v \in Values : SafeMsg(v, n) => SafeAt(v, n)
  <2> DEFINE P(n) == \A v \in Values : SafeMsg(v, n) => SafeAt(v, n)
  <2>1. \A n \in Nat : (\A k \in 0..(n-1) : P(k)) => P(n)
    BY <1>1, SafeMsgStepLemma DEF P, SafeMsgStep, Ballots
  <2>2. \A n \in Nat : P(n)
    BY <2>1, NI!GeneralNatInduction
  <2>3. QED
    BY <2>2 DEF P, Ballots
<1>2. QED
  BY <1>1

THEOREM ChosenInImpliesSafeMsg ==
  \A v, b :
    IndInv /\ ChosenIn(v, b) =>
      /\ b \in Ballots
      /\ v \in Values
      /\ SafeMsg(v, b)
PROOF
  BY SMTT(30) DEF IndInv, MsgTypeOK, VoteInv, SafeMsgInv, One2a,
                 ChosenIn, VotedForIn, QuorumAssumption,
                 Is2a, Is2b

THEOREM SameBallotAgreement ==
  \A v, w, b :
    IndInv /\ ChosenIn(v, b) /\ ChosenIn(w, b) => v = w
PROOF
  BY ChosenInImpliesSafeMsg, SMTT(30)
     DEF IndInv, One2a, VoteInv, ChosenIn, VotedForIn,
         Is2a, Is2b, QuorumAssumption

THEOREM ChosenInAgreement ==
  \A v, w, b, c :
    IndInv /\ ChosenIn(v, b) /\ ChosenIn(w, c) => v = w
PROOF
  BY SafeMsgImpliesSafeAt, ChosenInImpliesSafeMsg, SameBallotAgreement,
     SMTT(60) DEF SafeAt, Ballots

THEOREM ChosenAgreement ==
  \A v, w : IndInv /\ Chosen(v) /\ Chosen(w) => v = w
PROOF
  BY ChosenInAgreement DEF Chosen

THEOREM SpecImpliesAlwaysIndInv == Spec => []IndInv
PROOF
  BY InitImpliesIndInv, NextPreservesIndInv, PTL DEF Spec

-----------------------------------------------------------------------------
chosenBar == {v \in Values : Chosen(v)}

C == INSTANCE Consensus WITH chosen <- chosenBar

THEOREM ChosenMonotone ==
  MsgsMonotone => chosenBar \subseteq chosenBar'
PROOF
  BY SMT DEF MsgsMonotone, chosenBar, Chosen, ChosenIn, VotedForIn

AtMostOneChosenBar ==
  \A v, w \in chosenBar : v = w

THEOREM IndInvImpliesAtMostOneChosenBar ==
  IndInv => AtMostOneChosenBar
PROOF
  BY ChosenAgreement DEF AtMostOneChosenBar, chosenBar

THEOREM ChosenBarEmptyOrSingleton ==
  IndInv => (chosenBar = {} \/ \E v \in Values : chosenBar = {v})
PROOF
  BY IndInvImpliesAtMostOneChosenBar, IsaWithSetExtensionality
     DEF AtMostOneChosenBar, chosenBar

THEOREM InitImpliesCInit == Init => C!Init
PROOF
  BY SMT DEF Init, C!Init, chosenBar, Chosen, ChosenIn, VotedForIn

THEOREM AbsStep ==
  IndInv /\ IndInv' /\ [Next]_vars => [C!Next]_{chosenBar}
PROOF
  BY NextImpliesMsgsMonotone, ChosenMonotone, ChosenBarEmptyOrSingleton,
     IndInvImpliesAtMostOneChosenBar, IsaWithSetExtensionality, SMTT(30)
     DEF C!Next, chosenBar, AtMostOneChosenBar

THEOREM Refinement == Spec => C!Spec
PROOF
  BY SpecImpliesAlwaysIndInv, InitImpliesCInit, AbsStep, PTL
     DEF Spec, C!Spec
=============================================================================
