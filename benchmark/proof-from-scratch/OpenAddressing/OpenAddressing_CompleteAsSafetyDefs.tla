

-------------------------- MODULE OpenAddressing_CompleteAsSafetyDefs --------------------------
EXTENDS OpenAddressingModel

CompleteAsSafety == \A self \in ProcSet: pc[self] = "Done" => (history = fps)

=============================================================================
