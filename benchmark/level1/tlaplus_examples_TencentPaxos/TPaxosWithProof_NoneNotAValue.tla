------------------------------ MODULE TPaxosWithProof_NoneNotAValue --------------------------------
(*
Specification of the consensus protocol in PaxosStore.
See [PaxosStore@VLDB2017](https://www.vldb.org/pvldb/vol10/p1730-lin.pdf)
by Tencent.
In this version (adopted from "PaxosStore.tla"):
- Client-restricted config (Ballot)
- Message types (i.e., "Prepare", "Accept", "ACK") are deleted.
No state flags (such as "Prepare", "Wait-Prepare", "Accept", "Wait-Accept"
are needed.
- Choose value from a quorum in Accept.
*)
EXTENDS Integers, FiniteSets, TLAPS
-----------------------------------------------------------------------------
Max(m, n) == IF m > n THEN m ELSE n
Injective(f) == \A a, b \in DOMAIN f: (a # b) => (f[a] # f[b])
-----------------------------------------------------------------------------
CONSTANTS
    Participant,  \* the set of partipants
    Value         \* the set of possible input values for Participant to propose

None == CHOOSE b : b \notin Value

LEMMA NoneNotAValue == None \notin Value
PROOF OBVIOUS

=============================================================================