------------------------------ MODULE FlashWithMutex_MemDataCorrect ------------------------------

EXTENDS FlashWithMutex

Spec == Init /\ [][Next]_vars

MemDataProp ==
    ~Dir.Dirty => MemData = CurrData
THEOREM MemDataCorrect == Spec => []MemDataProp
PROOF OBVIOUS

=============================================================================
