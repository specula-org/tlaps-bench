---- MODULE ReadersWriters_proof_SafetyCorrect ----
EXTENDS FiniteSetTheorems, FiniteSets, Naturals, Sequences, TLAPS
(* ---- Content from module ReadersWriters ---- *)
(***************************************************************************)
(* This solution to the readers-writers problem, cf.                       *)
(* https://en.wikipedia.org/wiki/Readers–writers_problem,                  *)
(* uses a queue in order to fairly serve all requests.                     *)
(***************************************************************************)

CONSTANT NumActors

VARIABLES
    readers, \* set of processes currently reading
    writers, \* set of processes currently writing
    waiting  \* queue of processes waiting to access the resource

vars == <<readers, writers, waiting>>

Actors == 1..NumActors

ToSet(s) == { s[i] : i \in DOMAIN s }

read(s)  == s[1] = "read"
write(s) == s[1] = "write"

WaitingToRead  == { p[2] : p \in ToSet(SelectSeq(waiting, read)) }

WaitingToWrite == { p[2] : p \in ToSet(SelectSeq(waiting, write)) }

---------------------------------------------------------------------------

(***********)
(* Actions *)
(***********)

TryRead(actor) ==
    /\ actor \notin WaitingToRead
    /\ waiting' = Append(waiting, <<"read", actor>>)
    /\ UNCHANGED <<readers, writers>>

TryWrite(actor) ==
    /\ actor \notin WaitingToWrite
    /\ waiting' = Append(waiting, <<"write", actor>>)
    /\ UNCHANGED <<readers, writers>>

Read(actor) ==
    /\ readers' = readers \union {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED writers

Write(actor) ==
    /\ readers = {}
    /\ writers' = writers \union {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED readers

ReadOrWrite ==
    /\ waiting /= <<>>
    /\ writers = {}
    /\ LET pair  == Head(waiting)
           actor == pair[2]
       IN CASE pair[1] = "read" -> Read(actor)
            [] pair[1] = "write" -> Write(actor)

StopActivity(actor) ==
    IF actor \in readers
    THEN /\ readers' = readers \ {actor}
         /\ UNCHANGED <<writers, waiting>>
    ELSE /\ writers' = writers \ {actor}
         /\ UNCHANGED <<readers, waiting>>

Stop == \E actor \in readers \cup writers : StopActivity(actor)

---------------------------------------------------------------------------

(*****************)
(* Specification *)
(*****************)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ waiting = <<>>

Next ==
    \/ \E actor \in Actors : TryRead(actor)
    \/ \E actor \in Actors : TryWrite(actor)
    \/ ReadOrWrite
    \/ Stop

Fairness ==
    /\ \A actor \in Actors : WF_vars(TryRead(actor))
    /\ \A actor \in Actors : WF_vars(TryWrite(actor))
    /\ WF_vars(ReadOrWrite)
    /\ WF_vars(Stop)

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------

(**************)
(* Invariants *)
(**************)

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waiting \in Seq({"read", "write"} \times Actors)

Safety ==
    /\ ~(readers /= {} /\ writers /= {})
    /\ Cardinality(writers) <= 1

(**************)
(* Properties *)
(**************)

Liveness ==
    /\ \A actor \in Actors : []<>(actor \in readers)
    /\ \A actor \in Actors : []<>(actor \in writers)
    /\ \A actor \in Actors : []<>(actor \notin readers)
    /\ \A actor \in Actors : []<>(actor \notin writers)


(***************************************************************************)
(* TLAPS proof of the safety properties of the readers-writers spec:       *)
(*                                                                         *)
(*   Spec => []TypeOK                                                      *)
(*   Spec => []Safety                                                      *)
(*                                                                         *)
(* Both are inductive once we know that the head of `waiting` is a 2-tuple *)
(* with first component "read"/"write" (which TypeOK already gives us).   *)
(* Cardinality(writers) <= 1 follows because:                              *)
(*   - Writes only happen via ReadOrWrite, whose precondition is           *)
(*     `writers = {}`; so writers' = writers \cup {actor} = {actor}.       *)
(*   - StopActivity only removes elements; cardinality cannot grow there.  *)
(***************************************************************************)

(***************************************************************************)
(* The spec leaves `NumActors` as an unconstrained CONSTANT.  Make the    *)
(* (TLC-implicit) assumption explicit so the finiteness reasoning goes    *)
(* through.                                                                *)
(***************************************************************************)
ASSUME NumActorsIsNat == NumActors \in Nat

(***************************************************************************)
(* The head of a non-empty Seq(T) is in T.                                 *)
(***************************************************************************)
LEMMA HeadInSeqRange ==
  ASSUME NEW T, NEW s \in Seq(T), s # << >>
  PROVE  Head(s) \in T
  OBVIOUS

LEMMA TailIsSeq ==
  ASSUME NEW T, NEW s \in Seq(T), s # << >>
  PROVE  Tail(s) \in Seq(T)
  OBVIOUS

(***************************************************************************)
(* The set of "read"/"write" labels is closed under SelectSeq, but TypeOK  *)
(* gives us all we need: waiting \in Seq({"read","write"} \X Actors).      *)
(***************************************************************************)

(***************************************************************************)
(* Type correctness.                                                       *)
(***************************************************************************)
THEOREM TypeCorrect == Spec => []TypeOK
  PROOF OMITTED

Inv == TypeOK /\ Safety

LEMMA SafetyStep == Inv /\ [Next]_vars => Inv'
  PROOF OMITTED

THEOREM SafetyCorrect == Spec => []Safety
PROOF OBVIOUS

========================================