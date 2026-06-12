-------------------------- MODULE ivy_examples_split_queue_2_new_Liveness --------------------------
EXTENDS IvySplitQueue2New

WorkCompletion ==
  \A x \in Nat : begun[x] ~> done[x]

THEOREM Liveness == Spec => WorkCompletion
PROOF OBVIOUS

===========================================================================================
