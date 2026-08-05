------------------------------ MODULE FlashWithMutex_MemDataCorrectDefs ------------------------------

EXTENDS FlashWithMutexModel

Spec == Init /\ [][Next]_vars

MemDataProp ==
    ~Dir.Dirty => MemData = CurrData

=============================================================================
