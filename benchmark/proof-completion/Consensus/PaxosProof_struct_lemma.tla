-----------------MODULE PaxosProof_struct_lemma-------------------
EXTENDS TLAPS, PaxosTuple

WellFormedMessages == \A m \in msgs :
    /\ m[1] = "1a" => m[2] \in Ballot
    /\ m[1] = "1b" => /\ m[2] \in Acceptor
                      /\ m[3] \in Ballot
                      /\ m[4] \in Ballot \union {-1}
                      /\ m[5] \in Value \union {None}
    /\ m[1] = "2a" => m[2] \in Ballot /\ m[3] \in Value
    /\ m[1] = "2b" => m[2] \in Acceptor /\ m[3] \in Ballot /\ m[4] \in Value
THEOREM WFmsgs == TypeOK => WellFormedMessages
PROOF OMITTED

THEOREM typing == Spec => []TypeOK
PROOF OMITTED
StructOK1 == \A a \in Acceptor : IF maxVBal[a] = -1
                                 THEN maxVal[a] = None
                                 ELSE <<maxVBal[a], maxVal[a]>> \in votes[a]

THEOREM Spec => []StructOK1
PROOF OMITTED
StructOK2 == \A m \in msgs :
   (m[1] = "1b") => /\ maxBal[m[2]] >= m[3]
                    /\ (m[4] >= 0) => <<m[4],m[5]>> \in votes[m[2]]

StructOK3 == \A m \in msgs : m[1] = "2a" => /\ \E Q \in Quorum : V!ShowsSafeAt(Q,m[2],m[3])
                                            /\ \A mm \in msgs : /\ mm[1] = "2a"
                                                                /\ mm[2] = m[2]
                                                                => mm[3] = m[3]

StructOK4 == \A m \in msgs : m[1] = "2b" => /\ \E mo \in msgs : /\ mo[1] = "2a"
                                                                /\ mo[2] = m[3]
                                                                /\ mo[3] = m[4]
                                            /\ maxBal[m[2]] >= m[3]
                                            /\ maxVBal[m[2]] >= m[3]

StructOK5 == \A m \in msgs : m[1] = "1b" => \A d \in Ballot : m[4] < d /\ d < m[3] =>
                                            \A v \in Value : ~ <<d,v>> \in votes[m[2]]

StructOK == /\ TypeOK 
            /\ StructOK1 
            /\ StructOK2 
\*            /\ StructOK3 
            /\ StructOK4 
            /\ StructOK5 

THEOREM struct_lemma == Spec => []StructOK
PROOF OBVIOUS

Inv == TypeOK /\ StructOK1 /\ StructOK2 /\ StructOK3 /\ StructOK4 /\ StructOK5

============================================================