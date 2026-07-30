---- MODULE tcp_proof_IndInvStutter ----
EXTENDS tcp_proof_IndInvStutterScaffold
LEMMA IndInvStutter == IndInv /\ UNCHANGED vars => IndInv'
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
