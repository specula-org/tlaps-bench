---------------------------- MODULE BinarySearch_resultCorrect ----------------------------

EXTENDS BinarySearch

resultCorrect == 
   (pc = "Done") => IF \E i \in 1..Len(seq) : seq[i] = val
                     THEN seq[result] = val
                     ELSE result = 0 

THEOREM Spec => []resultCorrect
PROOF OBVIOUS
=============================================================================
