-------------------------- MODULE SequencesTheorems_AppendProperties -------------------------

EXTENDS Integers, Sequences, TLAPS

AXIOM SeqDef == \A S : Seq(S) = UNION {[1..n -> S] : n \in Nat}

AXIOM LenDef == \A S : \A seq \in Seq(S) :
                     /\ Len(seq) \in Nat
                     /\ DOMAIN seq = 1..Len(seq)

AXIOM HeadDef == \A s : Head(s) = s[1]
AXIOM TailDef == \A s : Tail(s) = [i \in 1..(Len(s)-1) |-> s[i+1]]

AXIOM SubSeqDef ==
        \A s, m, n : SubSeq(s, m, n) = [i \in 1..(1+n-m) |-> s[i+m-1]]

------------------------------------------------------------------

LEMMA SeqInSeqS ==
  ASSUME NEW S, NEW seq \in Seq(S)
  PROVE  /\ Len(seq) \in Nat
         /\ DOMAIN seq = 1..Len(seq)
         /\ seq \in [1..Len(seq) -> S]
<1>1. Len(seq) \in Nat /\ DOMAIN seq = 1..Len(seq)
  BY LenDef
<1>2. seq \in UNION {[1..k -> S] : k \in Nat}
  BY SeqDef
<1>3. PICK k \in Nat : seq \in [1..k -> S]
  BY <1>2
<1>4. DOMAIN seq = 1..k
  BY <1>3
<1>5. 1..k = 1..Len(seq)
  BY <1>1, <1>4
<1>6. seq \in [1..Len(seq) -> S]
  BY <1>3, <1>5
<1>. QED  BY <1>1, <1>6

------------------------------------------------------------------

LEMMA SingletonProps ==
  ASSUME NEW S, NEW elt \in S
  PROVE  /\ <<elt>> \in Seq(S)
         /\ Len(<<elt>>) = 1
         /\ <<elt>>[1] = elt
<1>1. <<elt>> = [i \in 1..1 |-> elt]
  OBVIOUS
<1>2. <<elt>> \in [1..1 -> S]
  BY <1>1
<1>3. <<elt>> \in Seq(S)
  <2>1. <<elt>> \in [1..1 -> S]
    BY <1>2
  <2>2. \E n \in Nat : <<elt>> \in [1..n -> S]
    BY <2>1
  <2>. QED  BY <2>2, SeqDef
<1>4. Len(<<elt>>) \in Nat /\ DOMAIN <<elt>> = 1..Len(<<elt>>)
  BY <1>3, LenDef
<1>5. DOMAIN <<elt>> = 1..1
  BY <1>1
<1>6. 1..Len(<<elt>>) = 1..1
  BY <1>4, <1>5
<1>7. Len(<<elt>>) = 1
  BY <1>4, <1>6
<1>8. <<elt>>[1] = elt
  BY <1>1
<1>. QED  BY <1>3, <1>7, <1>8

------------------------------------------------------------------

------------------------------------------------------------------

-----------------------------------------------------------------------------

THEOREM AppendProperties ==
          \A S :
            \A seq \in Seq(S), elt \in S :
                /\ Append(seq, elt) \in Seq(S)
                /\ Len(Append(seq, elt)) = Len(seq)+1
                /\ \A i \in 1.. Len(seq) : Append(seq, elt)[i] = seq[i]
                /\ Append(seq, elt)[Len(seq)+1] = elt
<1>. SUFFICES ASSUME NEW S, NEW seq \in Seq(S), NEW elt \in S
              PROVE  /\ Append(seq, elt) \in Seq(S)
                     /\ Len(Append(seq, elt)) = Len(seq)+1
                     /\ \A i \in 1.. Len(seq) : Append(seq, elt)[i] = seq[i]
                     /\ Append(seq, elt)[Len(seq)+1] = elt
  OBVIOUS
<1>1. /\ Len(seq) \in Nat
      /\ DOMAIN seq = 1..Len(seq)
      /\ seq \in [1..Len(seq) -> S]
  BY SeqInSeqS
<1>2. /\ <<elt>> \in Seq(S)
      /\ Len(<<elt>>) = 1
      /\ <<elt>>[1] = elt
  BY SingletonProps
<1>. DEFINE n == Len(seq)
<1>. DEFINE app == [j \in 1..(n + 1) |-> IF j \leq n THEN seq[j] ELSE <<elt>>[j - n]]
<1>3. Append(seq, elt) = app
  BY <1>2 DEF Append, \o
<1>4. ASSUME NEW j \in 1..(n+1)
      PROVE  app[j] \in S
  <2>1. app[j] = (IF j \leq n THEN seq[j] ELSE <<elt>>[j - n])
    OBVIOUS
  <2>2. CASE j \leq n
    <3>1. j \in 1..n
      BY <2>2, <1>1
    <3>2. seq[j] \in S
      BY <3>1, <1>1
    <3>. QED  BY <2>1, <2>2, <3>2
  <2>3. CASE ~(j \leq n)
    <3>1. j = n+1
      BY <2>3, <1>1
    <3>2. j - n = 1
      BY <3>1, <1>1
    <3>3. <<elt>>[j-n] = elt
      BY <3>2, <1>2
    <3>. QED  BY <2>1, <2>3, <3>3
  <2>. QED  BY <2>2, <2>3
<1>5. app \in [1..(n+1) -> S]
  BY <1>4
<1>6. (n+1) \in Nat
  BY <1>1
<1>7. app \in Seq(S)
  <2>1. \E k \in Nat : app \in [1..k -> S]
    BY <1>5, <1>6
  <2>. QED  BY <2>1, SeqDef
<1>8. DOMAIN app = 1..(n+1)
  OBVIOUS
<1>9. Len(app) = n+1
  <2>1. DOMAIN app = 1..Len(app) /\ Len(app) \in Nat
    BY <1>7, LenDef
  <2>2. 1..Len(app) = 1..(n+1)
    BY <1>8, <2>1
  <2>. QED  BY <2>1, <2>2, <1>6
<1>10. Append(seq, elt) \in Seq(S)
  BY <1>3, <1>7
<1>11. Len(Append(seq, elt)) = Len(seq)+1
  BY <1>3, <1>9
<1>12. \A i \in 1..Len(seq) : Append(seq, elt)[i] = seq[i]
  <2>. SUFFICES ASSUME NEW i \in 1..Len(seq)
                PROVE  Append(seq, elt)[i] = seq[i]
    OBVIOUS
  <2>1. i \in 1..(n+1) /\ i \leq n
    BY <1>1
  <2>2. app[i] = seq[i]
    BY <2>1
  <2>. QED  BY <1>3, <2>2
<1>13. Append(seq, elt)[Len(seq)+1] = elt
  <2>1. (n+1) \in 1..(n+1) /\ ~((n+1) \leq n)
    BY <1>1
  <2>2. app[n+1] = <<elt>>[(n+1) - n]
    BY <2>1
  <2>3. (n+1)-n = 1
    BY <1>1
  <2>4. <<elt>>[(n+1)-n] = elt
    BY <2>3, <1>2
  <2>. QED  BY <1>3, <2>2, <2>4
<1>. QED  BY <1>10, <1>11, <1>12, <1>13

-----------------------------------------------------------------------------

=============================================================================
