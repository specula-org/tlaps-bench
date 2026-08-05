----------------------------- MODULE VoteProof_VT2Defs ------------------------------

EXTENDS VoteProofModel

TypeOK == /\ votes \in [Acceptor -> SUBSET (Ballot \X Value)]
          /\ maxBal \in [Acceptor -> Ballot \cup {-1}]

VInv2 == \A a \in Acceptor, b \in Ballot, v \in Value :
                  VotedFor(a, b, v) => SafeAt(b, v)

VInv3 ==  \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value : 
                VotedFor(a1, b, v1) /\ VotedFor(a2, b, v2) => (v1 = v2)

VInv4 == \A a \in Acceptor, b \in Ballot : 
            maxBal[a] < b => DidNotVoteIn(a, b)

VInv == TypeOK /\ VInv2 /\ VInv3 /\ VInv4

===============================================================================
