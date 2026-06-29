---------------------------- MODULE AbstractRaft_SameTermSameLog ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS
    Server,
    Value,
    Quorum

Term == Nat
Index == Nat \ {0}

ASSUME QuorumAssumption ==

    /\ Quorum \in SUBSET (SUBSET Server)
    /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

    /\ \/ \E s \in Server : Server = {s}
       \/ \A s \in Server : \E Q \in Quorum : s \notin Q

VARIABLES
    role,
    term,
    ballots,
    entries,
    commitIndex

vars == <<role, term, ballots, entries, commitIndex>>

Entry == [val: Value, trm: Term]
Ballot == Server \X Term

lastEntryTerm(es) ==
    IF es = << >> THEN 0 ELSE es[Len(es)].trm

TypeOK ==
    /\ role \in [Server -> {"leader", "follower", "candidate"}]
    /\ term \in [Server -> Term]
    /\ ballots \in [Server -> SUBSET Ballot]
    /\ entries \in [Server -> Seq(Entry)]
    /\ commitIndex \in [Server -> Index \union {0}]
    /\ \A s \in Server : commitIndex[s] <= Len(entries[s])

Min(m,n) == IF m <= n THEN m ELSE n
Max(m,n) == IF m <= n THEN n ELSE m

BackedByQuorum(s,t) ==
    \E Q \in Quorum : \A srv \in Q : <<s,t>> \in ballots[srv]

InLog(s,i,e) ==
  /\ i \in 1 .. Len(entries[s])
  /\ entries[s][i] = e

QuorumContainsEntry(i, e) ==
    \E Q \in Quorum : \A srv \in Q : InLog(srv, i, e)

-----------------------------------------------------------------------------

Init ==
    /\ role = [s \in Server |-> "follower"]
    /\ term = [s \in Server |-> 0]
    /\ ballots = [s \in Server |-> {}]
    /\ entries = [s \in Server |-> << >>]
    /\ commitIndex = [s \in Server |-> 0]

Timeout(s) ==
    /\ role[s] \in {"follower", "candidate"}
    /\ role' = [role EXCEPT ![s] = "candidate"]
    /\ \E t \in Term :
          /\ t > term[s] /\ term' = [term EXCEPT ![s] = t]
          /\ ballots' = [ballots EXCEPT ![s] = @ \union {<<s,t>>}]
    /\ UNCHANGED <<entries, commitIndex>>

Vote(s) == \E cdt \in Server \ {s} :
    /\ LET ct == term[cdt]
       IN  /\ term[s] < ct
           /\ \A b \in ballots[s] : b[2] < ct
           /\ \/ lastEntryTerm(entries[s]) < lastEntryTerm(entries[cdt])
              \/ /\ lastEntryTerm(entries[s]) = lastEntryTerm(entries[cdt])
                 /\ Len(entries[s]) <= Len(entries[cdt])
           /\ role' = [role EXCEPT ![s] = "follower"]
           /\ term' = [term EXCEPT ![s] = ct]
           /\ ballots' = [ballots EXCEPT ![s] = @ \union {<<cdt, ct>>}]
           /\ UNCHANGED <<entries, commitIndex>>

ElectLeader(s) ==
    /\ role[s] = "candidate"
    /\ BackedByQuorum(s, term[s])
    /\ role' = [role EXCEPT ![s] = "leader"]
    /\ UNCHANGED <<entries, commitIndex, term, ballots>>

UpdateTerm(s) == \E srv \in Server :
    /\ term[srv] > term[s]
    /\ role' = [role EXCEPT ![s] = "follower"]
    /\ term' = [term EXCEPT ![s] = term[srv]]
    /\ UNCHANGED <<entries, commitIndex, ballots>>

AppendEntry(s) ==
    /\ role[s] = "leader"
    /\ \E v \in Value :
          LET entry == [val |-> v, trm |-> term[s]]
          IN  /\ entries' = [entries EXCEPT ![s] = Append(@, entry)]
    /\ UNCHANGED <<commitIndex, role, term, ballots>>

LearnEntry(s) ==
    /\ role[s] = "follower"
    /\ \E ldr \in Server :
          /\ BackedByQuorum(ldr, term[s])
          /\ \E n \in 1 .. Min(Len(entries[s])+1, Len(entries[ldr])) :
                /\ n \in 1 .. Len(entries[s]) =>
                       entries[s][n].trm # entries[ldr][n].trm
                /\ n-1 \in 1 .. Len(entries[s]) =>
                       entries[s][n-1].trm = entries[ldr][n-1].trm
                /\ entries' = [entries EXCEPT ![s] =
                      Append(SubSeq(entries[s], 1, n-1), entries[ldr][n])]

                /\ commitIndex' = [commitIndex EXCEPT ![s] = Min(@, n-1)]

                /\ term' = [term EXCEPT ![s] = Max(entries[ldr][n].trm, term[s])]
    /\ UNCHANGED <<ballots, role>>

LeaderCommit(ldr) ==
    /\ role[ldr] = "leader"
    /\ \E n \in commitIndex[ldr]+1 .. Len(entries[ldr]) :
          /\ entries[ldr][n].trm = term[ldr]
          /\ \E Q \in Quorum : \A s \in Q :
                /\ InLog(s, n, entries[ldr][n])
                /\ term[s] = term[ldr]
          /\ commitIndex' = [commitIndex EXCEPT ![ldr] = n]
    /\ UNCHANGED <<entries, role, term, ballots>>

GossipCommit(s) ==
    /\ \E srv \in Server : \E n \in commitIndex[s]+1 .. commitIndex[srv] :
          /\ role[s] = "follower"
          /\ term[s] <= term[srv]
          /\ n \in 1 .. Len(entries[s])
          /\ entries[s][n].trm = entries[srv][n].trm
          /\ term' = [term EXCEPT ![s] = term[srv]]
          /\ commitIndex' = [commitIndex EXCEPT ![s] = n]
    /\ UNCHANGED <<entries, role, ballots>>

Next == \E s \in Server :
    \/ Timeout(s)
    \/ Vote(s)
    \/ ElectLeader(s)
    \/ UpdateTerm(s)
    \/ AppendEntry(s)
    \/ LearnEntry(s)
    \/ LeaderCommit(s)
    \/ GossipCommit(s)

Spec == Init /\ [][Next]_vars

SameTermSameLog ==
    \A s1, s2 \in Server : \A i \in 1 .. Min(Len(entries[s1]), Len(entries[s2])) :
       entries[s1][i].trm = entries[s2][i].trm =>
       \A j \in 1 .. i : entries[s1][j] = entries[s2][j]

THEOREM Spec => []SameTermSameLog
PROOF OBVIOUS
==============================================================================
