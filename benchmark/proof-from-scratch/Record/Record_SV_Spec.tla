------------------------------- MODULE Record_SV_Spec -------------------------------

EXTENDS Record

maxBal == [p \in Participant |-> state[p][p].maxBal]

SV == INSTANCE SimpleVoting

THEOREM Spec => SV!Spec
PROOF OBVIOUS
=============================================================================

