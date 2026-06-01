----------------------------- MODULE VoteProof_Liveness ------------------------------

EXTENDS AuxLiveness, TLAPS

-----------------------------------------------------------------------------

THEOREM Liveness == LiveSpec => C!LiveSpec
PROOF
  <1>. SUFFICES AuxLive
    BY DEF AuxLive
  <1>. QED BY AuxLive

===============================================================================
