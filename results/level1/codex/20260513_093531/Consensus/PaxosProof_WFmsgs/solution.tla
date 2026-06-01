---- MODULE PaxosProof_WFmsgs ----
EXTENDS Integers, NaturalsInduction, TLAPS
(* ---- Content from module Sets ---- *)
  \** NB: Module NaturalsInduction comes from the TLAPS library, usually
  \** installed in /usr/local/lib/tlaps. Make sure this is in your Toolbox
  \** search path, see Preferences/TLA+ Preferences.

IsBijection(f, S, T) == /\ f \in [S -> T]
                        /\ \A x, y \in S : (x # y) => (f[x] # f[y])
                        /\ \A y \in T : \E x \in S : f[x] = y


IsFiniteSet(S) == \E n \in Nat : \E f : IsBijection(f, 1..n, S)

(****************************************************************************)
(* Finite sets and cardinality are defined in the TLA+ standard module      *)
(* FiniteSets, but this is not yet natively supported by TLAPS. For the     *)
(* time being, we use the following axiom for defining set cardinality.     *)
(****************************************************************************)
\* Cardinality(S) == CHOOSE n : (n \in Nat) /\ \E f : IsBijection(f, 1..n, S)

CONSTANT Cardinality(_)
AXIOM CardinalityAxiom ==
         \A S : IsFiniteSet(S) =>
           \A n : (n = Cardinality(S)) <=>
                    (n \in Nat) /\ \E f : IsBijection(f, 1..n, S)
-----------------------------------------------------------------------------

THEOREM CardinalityInNat == \A S : IsFiniteSet(S) => Cardinality(S) \in Nat
  PROOF OMITTED

------------------------------------------------------------------

THEOREM CardinalityZero ==
           /\ IsFiniteSet({})
           /\ Cardinality({}) = 0
           /\ \A S : IsFiniteSet(S) /\ (Cardinality(S)=0) => (S = {})
  PROOF OMITTED

THEOREM CardinalityPlusOne ==
    ASSUME NEW S, IsFiniteSet(S),
           NEW x, x \notin S
    PROVE  /\ IsFiniteSet(S \cup {x})
           /\ Cardinality(S \cup {x}) = Cardinality(S) + 1
  PROOF OMITTED

------------------------------------------------------------------

THEOREM CardinalityOne == \A m : /\ IsFiniteSet({m})
                                 /\ Cardinality({m}) = 1
  PROOF OMITTED

THEOREM CardinalityTwo == \A m, p : m # p => 
                              /\ IsFiniteSet({m,p})
                              /\ Cardinality({m,p}) = 2
  PROOF OMITTED

THEOREM IntervalCardinality ==  
  ASSUME NEW a \in Nat, NEW b \in Nat 
  PROVE  /\ IsFiniteSet(a..b)
         /\ Cardinality(a..b) = IF a > b THEN 0 ELSE b-a+1
  PROOF OMITTED

------------------------------------------------------------------

THEOREM CardinalityOneConverse ==
   ASSUME NEW S, IsFiniteSet(S), Cardinality(S) = 1
   PROVE  \E m : S = {m}
  PROOF OMITTED

-----------------------------------------------------------------------------

THEOREM IsBijectionInverse ==
  ASSUME NEW f, NEW S, NEW T, 
         IsBijection(f, S, T) 
  PROVE  \E g : IsBijection(g, T, S)
  PROOF OMITTED

THEOREM IsBijectionTransitive ==
  ASSUME NEW f1, NEW f2, NEW S, NEW T, NEW U, 
           IsBijection(f1, S, U),
           IsBijection(f2, U, T) 
  PROVE  \E g : IsBijection(g, S, T)
  PROOF OMITTED

THEOREM IsBijectionCardinality ==
  \A f, S, T : /\ IsFiniteSet(S)
               /\ IsFiniteSet(T)
               => (IsBijection(f, S, T) <=> Cardinality(S) = Cardinality(T))

LEMMA CardinalitySetMinus ==
      ASSUME NEW S, IsFiniteSet(S),
             NEW x \in S
      PROVE /\ IsFiniteSet(S \ {x})
            /\ Cardinality(S \ {x}) = Cardinality(S) - 1
  PROOF OMITTED

THEOREM FiniteSubset ==
  ASSUME NEW S, NEW TT, IsFiniteSet(TT), S \subseteq TT
  PROVE  /\ IsFiniteSet(S)
         /\ Cardinality(S) \leq Cardinality(TT)
  PROOF OMITTED

-------------------------------------------------------

THEOREM CardinalityUnion ==
          \A S, T : IsFiniteSet(S) /\ IsFiniteSet(T) =>
                      /\ IsFiniteSet(S \cup T)
                      /\ IsFiniteSet(S \cap T)
                      /\ Cardinality(S \cup T) =
                              Cardinality(S) + Cardinality(T)
                              - Cardinality(S \cap T)  

-----------------------------------------------------------------------------

THEOREM PigeonHole ==
            \A S, T : /\ IsFiniteSet(S)
                      /\ IsFiniteSet(T)
                      /\ Cardinality(T) < Cardinality(S)
                      => \A f \in [S -> T] :
                           \E x, y \in S : x # y /\ f[x] = f[y]
  PROOF OMITTED

-------------------------------------------------------

THEOREM \A S, T , f :  /\ IsFiniteSet(S)
                       /\ f \in [S -> T]
                       /\ \A y \in T : \E x \in S : y = f[x]
                       => /\ IsFiniteSet(T)
                          /\ Cardinality(T) \leq Cardinality(S)
PROOF OMITTED

THEOREM ProductFinite ==
     \A S, T : IsFiniteSet(S) /\ IsFiniteSet(T) => IsFiniteSet(S \X T)
PROOF OMITTED

THEOREM SubsetsFinite == \A S : IsFiniteSet(S) => IsFiniteSet(SUBSET S)
PROOF OMITTED

(* ---- Content from module PaxosTuple ---- *)
-----------------------------------------------------------------------------
CONSTANT Value, Acceptor, Quorum

ASSUME QuorumAssumption == /\ \A Q \in Quorum : Q \subseteq Acceptor
                           /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}
Ballot ==  Nat
None == CHOOSE v : v \notin Ballot
-----------------------------------------------------------------------------
Message ==
       {"1a"} \X Ballot
  \cup {"1b"} \X Acceptor \X Ballot \X (Ballot \cup {-1}) \X (Value \cup {None})
  \cup {"2a"} \X Ballot \X Value
  \cup {"2b"} \X Acceptor \X Ballot \X Value
-----------------------------------------------------------------------------
VARIABLE maxBal,
         maxVBal, \* <<maxVBal[a], maxVal[a]>>: the vote with the largest ballot number cast by a;
         maxVal,  \* it is <<-1, None>> if a has not cast any vote.
         msgs

Send(m) == msgs' = msgs \cup {m}

vars == <<maxBal, maxVBal, maxVal, msgs>>

TypeOK == /\ maxBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
          /\ maxVal \in [Acceptor -> Value \cup {None}]
          /\ msgs \subseteq Message
-----------------------------------------------------------------------------
Init == /\ maxBal = [a \in Acceptor |-> -1]
        /\ maxVBal = [a \in Acceptor |-> -1]
        /\ maxVal = [a \in Acceptor |-> None]
        /\ msgs = {}

Phase1a(b) == /\ Send(<<"1a", b>>)
              /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

Phase1b(a) == /\ \E m \in msgs :
                  /\ m[1] = "1a"
                  /\ m[2] > maxBal[a]
                  /\ maxBal' = [maxBal EXCEPT ![a] = m[2]]
                  /\ Send(<<"1b", a, m[2], maxVBal[a], maxVal[a]>>)
              /\ UNCHANGED <<maxVBal, maxVal>>

Phase2a(b, v) ==
  /\ ~ \E m \in msgs : m[1] = "2a" /\ m[3] = b
  /\ \E Q \in Quorum :
        LET Q1b == {m \in msgs : /\ m[1] = "1b"
                                 /\ m[2] \in Q
                                 /\ m[3] = b}
            Q1bv == {m \in Q1b : m[4] \geq 0}
        IN  /\ \A a \in Q : \E m \in Q1b : m[2] = a
            /\ \/ Q1bv = {}
               \/ \E m \in Q1bv :
                    /\ m[5] = v
                    /\ \A mm \in Q1bv : m[4] \geq mm[4]
  /\ Send(<<"2a", b, v>>)
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

Phase2b(a) == \E m \in msgs : /\ m[1] = "2a"
                              /\ m[2] \geq maxBal[a]
                              /\ maxBal' = [maxBal EXCEPT ![a] = m[2]]
                              /\ maxVBal' = [maxVBal EXCEPT ![a] = m[2]]
                              /\ maxVal' = [maxVal EXCEPT ![a] = m[3]]
                              /\ Send(<<"2b", a, m[2], m[3]>>)
----------------------------------------------------------------------------
Next == \/ \E b \in Ballot : \/ Phase1a(b)
                             \/ \E v \in Value : Phase2a(b, v)
        \/ \E a \in Acceptor : Phase1b(a) \/ Phase2b(a)

Spec == Init /\ [][Next]_vars
----------------------------------------------------------------------------
votes == [a \in Acceptor |->
           {<<m[3], m[4]>> : m \in {mm \in msgs: /\ mm[1] = "2b"
                                                 /\ mm[2] = a }}]
V == INSTANCE Voting

THEOREM Spec => V!Spec


WellFormedMessages == \A m \in msgs :
    /\ m[1] = "1a" => m[2] \in Ballot
    /\ m[1] = "1b" => /\ m[2] \in Acceptor
                      /\ m[3] \in Ballot
                      /\ m[4] \in Ballot \union {-1}
                      /\ m[5] \in Value \union {None}
    /\ m[1] = "2a" => m[2] \in Ballot /\ m[3] \in Value
    /\ m[1] = "2b" => m[2] \in Acceptor /\ m[3] \in Ballot /\ m[4] \in Value
-----------------------------------------------------------------------------
THEOREM WFmsgs == TypeOK => WellFormedMessages
PROOF
  <1>1. ASSUME TypeOK
        PROVE WellFormedMessages
    <2>1. msgs \subseteq Message BY <1>1 DEF TypeOK
    <2>2. SUFFICES ASSUME NEW m \in msgs
                     PROVE  /\ m[1] = "1a" => m[2] \in Ballot
                            /\ m[1] = "1b" => /\ m[2] \in Acceptor
                                                /\ m[3] \in Ballot
                                                /\ m[4] \in Ballot \union {-1}
                                                /\ m[5] \in Value \union {None}
                            /\ m[1] = "2a" => m[2] \in Ballot /\ m[3] \in Value
                            /\ m[1] = "2b" => m[2] \in Acceptor /\ m[3] \in Ballot /\ m[4] \in Value
      BY DEF WellFormedMessages
    <2>3. m \in Message BY <2>1, <2>2
    <2>4. CASE m[1] = "1a"
      <3>1. m \in {"1a"} \X Ballot BY <2>3, <2>4 DEF Message
      <3>2. m[2] \in Ballot BY <3>1
      <3>3. QED BY <2>4, <3>2
    <2>5. CASE m[1] = "1b"
      <3>1. m \in {"1b"} \X Acceptor \X Ballot \X (Ballot \cup {-1}) \X (Value \cup {None})
        BY <2>3, <2>5 DEF Message
      <3>2. /\ m[2] \in Acceptor
             /\ m[3] \in Ballot
             /\ m[4] \in Ballot \union {-1}
             /\ m[5] \in Value \union {None}
        BY <3>1
      <3>3. QED BY <2>5, <3>2
    <2>6. CASE m[1] = "2a"
      <3>1. m \in {"2a"} \X Ballot \X Value BY <2>3, <2>6 DEF Message
      <3>2. m[2] \in Ballot /\ m[3] \in Value BY <3>1
      <3>3. QED BY <2>6, <3>2
    <2>7. CASE m[1] = "2b"
      <3>1. m \in {"2b"} \X Acceptor \X Ballot \X Value BY <2>3, <2>7 DEF Message
      <3>2. m[2] \in Acceptor /\ m[3] \in Ballot /\ m[4] \in Value BY <3>1
      <3>3. QED BY <2>7, <3>2
    <2>8. QED BY <2>4, <2>5, <2>6, <2>7
  <1>2. QED BY <1>1

========================================
