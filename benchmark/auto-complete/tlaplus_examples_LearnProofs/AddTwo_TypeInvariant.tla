------------------------------ MODULE AddTwo_TypeInvariant --------------------------------
(***************************************************************************)
(* Defines a very simple algorithm that continually increments a variable  *)
(* by 2. We try to prove that this variable is always divisible by 2.      *)
(* This was created as an exercise in learning the absolute basics of the  *)
(* proof language.                                                         *)
(***************************************************************************)

EXTENDS AddTwo

(****************************************************************************
--algorithm Increase {
  variable x = 0; {
    while (TRUE) {
      x := x + 2
    }
  }
}
****************************************************************************)
\* BEGIN TRANSLATION (chksum(pcal) = "b4b07666" /\ chksum(tla) = "8adfa002")

\* END TRANSLATION 

TypeOK == x \in Nat

THEOREM TypeInvariant == Spec => []TypeOK
PROOF OBVIOUS

a|b == \E c \in Nat : a*c = b

Even == 2|x

=============================================================================

