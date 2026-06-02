------------------------ MODULE Termination ------------------------

(**************************************************************************************)
(* Distributed termination detection of a message-driven computation.  A              *)
(* set of processes exchange messages.  Initialy there is one message in              *)
(* the network.  A process can receive a messages and send 0, 1, or more              *)
(* messages as a response in a single atomic step.  A daemon visits                   *)
(* arbitrary nodes one by one, each time noting how many messages the node            *)
(* has sent to each other node, and how many it has received from each                *)
(* other node.  When the daemon sees that all numbers match, it declares              *)
(* that the system has terminated.                                                    *)
(*                                                                                    *)
(* This is the algorithm described in Section 4 of: Kumar, Devendra.  A               *)
(* class of termination detection algorithms for distributed computations.            *)
(* International Conference on Foundations of Software Technology and                 *)
(* Theoretical Computer Science.  Springer, Berlin, Heidelberg, 1985.                 *)
(*                                                                                    *)
(* The algorithm can also be found in : Mattern, Friedemann.  Algorithms              *)
(* for distributed termination detection.  Distributed computing 2.3                  *)
(* (1987): 161-175.  In this paper, the algorithm is called the Channel               *)
(* Counting Algorithm and is described in Section 7.                                  *)
(*                                                                                    *)
(* The original, operational proof is a little mind-bending (the principle            *)
(* is illustrated in Figure 8, Section 6, of Algorithms for distributed               *)
(* termination detection.)                                                            *)
(**************************************************************************************)

EXTENDS Integers

CONSTANT P

VARIABLES
    \* s[<<p,q>>] is the number of messages sent on channel <<p,q>>, i.e. by p to q as counted by p:
    s,
    \* r[<<p,q>>] is the number of messages received on channel <<p,q>>, i.e. by q from p as counted by q
    r,
    \* ds[<<p,q>>] is the number of messages sent by p to q as recorded by the daemon in its last visit to p:
    ds,
    \* dr[<<p,q>>] is the number of messages received by q from p as recorded by the daemon in its last visit to q:
    dr,
    \* visited is the set of processes that the daemon visited so far:
    visited,
    \* terminated is set to TRUE when the daemon terminates
    terminated

\* The number of messages in flight from p to q:
NumPending(p, q) ==
    s[<<p,q>>] - r[<<p,q>>]

(***************************************************************************)
(* The correstness property: when the daemon terminates, there are no      *)
(* messages in flight (i.e.  the distributed computation is finished):     *)
(***************************************************************************)
Safety == terminated => \A p,q \in P : NumPending(p,q) = 0

TypeOK ==
  /\  s \in [P\times P -> Int]
  /\  \A pq \in P\times P : s[pq] >= 0
  /\  r \in [P\times P -> Int]
  /\  \A pq \in P\times P : r[pq] >= 0
  /\  ds \in [P\times P -> Int]
  /\  \A pq \in P\times P : ds[pq] >= 0
  /\  dr \in [P\times P -> Int]
  /\  \A pq \in P\times P : dr[pq] >= 0
  /\  visited \in SUBSET P
  /\  terminated \in BOOLEAN

(**************************************************************************************)
(* Initially, no messages have been received and the daemon has not started           *)
(* visiting any nodes.  However, one process has sent a message (otherwise nothing    *)
(* happens).                                                                          *)
(**************************************************************************************)

Init ==
    /\ s \in [P\times P -> Int]
    /\ \E pq \in P\times P :
        /\ s[pq] = 1
        /\ \A rs \in P\times P : rs # pq => s[rs] = 0
    /\ r = [pq \in P\times P |-> 0] \* no message received so far
    \* Daemon state:
    /\ ds = [pq \in P\times P |-> 0]
    /\ dr = [pq \in P\times P |-> 0]
    /\ visited = {}
    /\ terminated = FALSE

(***************************************************************************)
(* Receive a message and, in response, pick a set Q of processes and send  *)
(* one new message to each.                                                *)
(***************************************************************************)
process(self) ==
  /\ \E p \in P \ {self} : \* receive a message from p
      /\ NumPending(p,self) > 0
      /\ r' = [r EXCEPT ![<<p,self>>] =  @ + 1]
  /\ \E Q \in SUBSET (P \ {self}): \* send messages to set Q
     /\ s' = [t \in P\times P |->
          IF t[1] = self /\ t[2] \in Q THEN s[t]+1 ELSE s[t]]
  /\ UNCHANGED << ds, dr, visited, terminated >>

(***************************************************************************)
(* While the daemon has not visited all processes, or it has but there is  *)
(* a pair whose message counts, as recorded by the daemon, do not match,   *)
(* visit a new process                                                     *)
(***************************************************************************)
Consistent(Q) ==
  \A p,q \in Q : ds[<<p,q>>] = dr[<<p,q>>]
daemon ==
        /\ IF visited # P \/ \neg Consistent(P)
              THEN /\ \E p \in P: \* pick a process p to visit
                        /\ ds' = [t \in P\times P |-> IF t[1] = p THEN s[t] ELSE ds[t]]
                        /\ dr' = [t \in P\times P |-> IF t[2] = p THEN r[t] ELSE dr[t]]
                        /\ visited' = (visited \union {p})
                        /\ UNCHANGED terminated
              ELSE /\ terminated' = TRUE \* declare termination
                   /\ UNCHANGED << ds, dr, visited >>
        /\ UNCHANGED << s, r >>

Next == daemon \/ (\E p \in P : process(p))

vars == << s, r, ds, dr, visited, terminated >>
Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Canary invariants                                                       *)
(***************************************************************************)
Canary1 == \neg terminated

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

\* A process cannot receive more than has been sent to it:
Inv1 == \A p,q \in P : r[<<p,q>>] <= s[<<p,q>>]
Inv1_ == TypeOK /\ Inv1

(***************************************************************************)
(* If a set Q of visited nodes is consistent and a member of Q has         *)
(* received or sent more than what the daemon saw, then a message from     *)
(* outside Q that the daemon has not seen has been received:               *)
(***************************************************************************)
Stale(Q) ==
  \E p \in Q, q \in P :
    \/ r[<<q,p>>] # dr[<<q,p>>]
    \/ s[<<p,q>>] # ds[<<p,q>>]
Inv2 == \A Q \in SUBSET visited : Consistent(Q) /\ Stale(Q) => \E p \in Q, q \in P \ Q : r[<<q,p>>] > dr[<<q,p>>]
Inv2_ == TypeOK /\ Inv1 /\ Inv2

Inv3 ==
  terminated => visited = P /\ Consistent(P)
Inv3_ == TypeOK /\ Inv3

(***************************************************************************)
(* We check that Inv2 and Inv3 imply Safety by using Safety_precondition   *)
(* as init predicate and checking that Safety holds in the initial state.  *)
(***************************************************************************)
Safety_ == TypeOK /\ Inv2 /\ Inv3

=============================================================================
