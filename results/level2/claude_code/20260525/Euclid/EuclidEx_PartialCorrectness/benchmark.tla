------------------------------ MODULE EuclidEx_PartialCorrectness ------------------------------
EXTENDS GCD, TLAPS
-----------------------------------------------------------------------------
CONSTANTS M, N
ASSUME MNPosInt == 
    /\ M \in Nat \ {0}
    /\ N \in Nat \ {0}
(*******************************************************************
--algorithm Euclid {
  variables x = M, y = N ;
  { while (x # y) { if (x < y) { y := y - x }
                    else       { x := x - y }
                  };
  }
}
 *******************************************************************)
\* BEGIN TRANSLATION
VARIABLES x, y, pc

vars == << x, y, pc >>

Init == (* Global variables *)
        /\ x = M
        /\ y = N
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ IF x # y
               THEN /\ IF x < y
                          THEN /\ y' = y - x
                               /\ x' = x
                          ELSE /\ x' = x - y
                               /\ y' = y
                    /\ pc' = "Lbl_1"
               ELSE /\ pc' = "Done"
                    /\ UNCHANGED << x, y >>

Next == Lbl_1 \* Allow infinite stuttering to prevent deadlock on termination.
           \/ (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
-----------------------------------------------------------------------------
PartialCorrectness ==
    (pc = "Done") => (x = y) /\ (x = GCD(M, N))

TypeOK == 
    /\ x \in Nat \ {0}
    /\ y \in Nat \ {0}

Inv == 
    /\ TypeOK
    /\ GCD(x, y) = GCD(M, N)
    /\ (pc = "Done") => (x = y)
-----------------------------------------------------------------------------
THEOREM Spec => []PartialCorrectness
PROOF OBVIOUS
=============================================================================
\* Modification History
\* Last modified Tue Jul 16 09:46:10 CST 2019 by hengxin
\* Created Mon Jul 15 16:59:12 CST 2019 by hengxin