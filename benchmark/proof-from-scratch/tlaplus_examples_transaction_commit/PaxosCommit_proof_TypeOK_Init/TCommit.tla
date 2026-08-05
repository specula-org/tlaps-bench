------------------------------- MODULE TCommit ------------------------------
CONSTANT RM       
VARIABLE rmState  
-----------------------------------------------------------------------------

canCommit == \A rm \in RM : rmState[rm] \in {"prepared", "committed"}

notCommitted == \A rm \in RM : rmState[rm] # "committed" 

-----------------------------------------------------------------------------

Decide(rm)  == \/ /\ rmState[rm] = "prepared"
                  /\ canCommit
                  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
               \/ /\ rmState[rm] \in {"working", "prepared"}
                  /\ notCommitted
                  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]

-----------------------------------------------------------------------------

-----------------------------------------------------------------------------

=============================================================================
