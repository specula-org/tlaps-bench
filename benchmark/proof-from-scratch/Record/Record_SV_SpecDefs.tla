------------------------------- MODULE Record_SV_SpecDefs -------------------------------

EXTENDS RecordModel

maxBal == [p \in Participant |-> state[p][p].maxBal]

SV == INSTANCE SimpleVoting

=============================================================================

