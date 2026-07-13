# Dataset breakdown

Every task presents one stated theorem whose proof body is replaced by
`PROOF OBVIOUS`; see the [README](../README.md) for the two task types and the
per-source summary.

Each row is a benchmark **example** — one directory under `benchmark/<mode>/`,
i.e. one coherent protocol or example. A protocol whose proof is split across
several TLA+ modules stays a single row. The example name links to its upstream
location; two have none (`AbstractRaft` was contributed directly and
`GermanProtocol` could not be located upstream).

`–` marks a mode with no task for that example: a source with no human proofs
yields no proof-completion task, and an example whose only proven theorems are
*unnamed* (so they cannot be referenced as scaffolding) is likewise
proof-from-scratch only.

This file is generated; regenerate it with `python3 scripts/dataset_table.py`.

| Example | Source | Proof completion | Proof from scratch | Total |
|---|---|--:|--:|--:|
| AbstractRaft | AbstractRaft | – | 4 | 4 |
| [hybrid_reliable_broadcast_cisa](https://github.com/kenmcmil/ivy/blob/master/examples/liveness/hybrid_reliable_broadcast_cisa.ivy) | Ivy liveness | – | 3 | 3 |
| [alternating_bit_protocol](https://github.com/kenmcmil/ivy/blob/master/examples/liveness/alternating_bit_protocol.ivy) | Ivy liveness | – | 2 | 2 |
| [ticket](https://github.com/kenmcmil/ivy/blob/master/examples/liveness/ticket.ivy) | Ivy liveness | – | 2 | 2 |
| [ticket_nested](https://github.com/kenmcmil/ivy/blob/master/examples/liveness/ticket_nested.ivy) | Ivy liveness | – | 2 | 2 |
| [tlb](https://github.com/kenmcmil/ivy/blob/master/examples/liveness/tlb.ivy) | Ivy liveness | – | 2 | 2 |
| [split_queue_2_new](https://github.com/kenmcmil/ivy/blob/master/examples/liveness/split_queue_2_new.ivy) | Ivy liveness | – | 1 | 1 |
| [OpenAddressing](https://github.com/lemmy/Examples/tree/mku-OA/specifications/TLC) | OpenAddressing | 1 | 5 | 6 |
| [Consensus](https://github.com/tlaplus/tlapm/tree/main/examples_draft/consensus) | TLAPS distribution examples | 25 | 10 | 35 |
| [Data](https://github.com/tlaplus/tlapm/tree/main/zenon/regression/examples/data) | TLAPS distribution examples | 15 | 9 | 24 |
| [Cantor](https://github.com/tlaplus/tlapm/tree/main/examples/cantor) | TLAPS distribution examples | 11 | 10 | 21 |
| [Paxos](https://github.com/hengxin/tlaps-examples/tree/master/Paxos) | TLAPS distribution examples | 13 | 6 | 19 |
| [Allocator](https://github.com/tlaplus/tlapm/blob/main/examples/Allocator.tla) | TLAPS distribution examples | 10 | 4 | 14 |
| [BubbleSort](https://github.com/tlaplus/tlapm/blob/main/examples/BubbleSort.tla) | TLAPS distribution examples | 8 | 3 | 11 |
| [Euclid](https://github.com/hengxin/tlaps-examples/tree/master/Euclid) | TLAPS distribution examples | 6 | 5 | 11 |
| [AtomicBakery](https://github.com/hengxin/tlaps-examples/tree/master/AtomicBakery) | TLAPS distribution examples | 8 | 2 | 10 |
| [SimpleMutex](https://github.com/tlaplus/tlapm/blob/main/examples/SimpleMutex.tla) | TLAPS distribution examples | 5 | 2 | 7 |
| [EWD840](https://github.com/tlaplus/tlapm/blob/main/examples/EWD840.tla) | TLAPS distribution examples | 2 | 1 | 3 |
| [Peterson](https://github.com/tlaplus/tlapm/blob/main/examples/Peterson.tla) | TLAPS distribution examples | – | 2 | 2 |
| [Bakery](https://github.com/tlaplus/tlapm/blob/main/examples/Bakery.tla) | TLAPS distribution examples | – | 1 | 1 |
| [Record](https://github.com/hengxin/tlaps-examples/tree/master/Record) | TLAPS distribution examples | – | 1 | 1 |
| [SumAndMax](https://github.com/tlaplus/tlapm/blob/main/examples/SumAndMax.tla) | TLAPS distribution examples | – | 1 | 1 |
| [ZooKeeper](https://github.com/Disalg-ICS-NJU/zookeeper-tla-spec/blob/main/high-level-spec/Zab.tla) | ZooKeeper (Remix) | – | 9 | 9 |
| [ZooKeeper_LowLevel](https://github.com/Disalg-ICS-NJU/zookeeper-tla-spec/tree/main/low-level-spec/zk-3.7) | ZooKeeper (Remix) | – | 9 | 9 |
| [etcd_raft](https://github.com/specula-org/Specula/blob/main/skills/spec_generation/examples/etcdraft.tla) | etcd (Specula) | – | 8 | 8 |
| [ewd998](https://github.com/tlaplus/Examples/tree/master/specifications/ewd998) | tlaplus/Examples | 52 | 7 | 59 |
| [byzpaxos](https://github.com/tlaplus/Examples/tree/master/specifications/byzpaxos) | tlaplus/Examples | 41 | 11 | 52 |
| [lamport_mutex](https://github.com/tlaplus/Examples/tree/master/specifications/lamport_mutex) | tlaplus/Examples | 20 | 2 | 22 |
| [TencentPaxos](https://github.com/tlaplus/Examples/tree/master/specifications/TencentPaxos) | tlaplus/Examples | 19 | 2 | 21 |
| [LoopInvariance](https://github.com/tlaplus/Examples/tree/master/specifications/LoopInvariance) | tlaplus/Examples | 17 | 3 | 20 |
| [allocator](https://github.com/tlaplus/Examples/tree/master/specifications/allocator) | tlaplus/Examples | 14 | 5 | 19 |
| [ewd687a](https://github.com/tlaplus/Examples/tree/master/specifications/ewd687a) | tlaplus/Examples | 16 | 3 | 19 |
| [ewd840](https://github.com/tlaplus/Examples/tree/master/specifications/ewd840) | tlaplus/Examples | 14 | 5 | 19 |
| [tcp](https://github.com/tlaplus/Examples/tree/master/specifications/tcp) | tlaplus/Examples | 16 | 3 | 19 |
| [bcastByz](https://github.com/tlaplus/Examples/tree/master/specifications/bcastByz) | tlaplus/Examples | 13 | 5 | 18 |
| [FiniteMonotonic](https://github.com/tlaplus/Examples/tree/master/specifications/FiniteMonotonic) | tlaplus/Examples | 14 | 3 | 17 |
| [TeachingConcurrency](https://github.com/tlaplus/Examples/tree/master/specifications/TeachingConcurrency) | tlaplus/Examples | 8 | 8 | 16 |
| [barriers](https://github.com/tlaplus/Examples/tree/master/specifications/barriers) | tlaplus/Examples | 11 | 5 | 16 |
| [transaction_commit](https://github.com/tlaplus/Examples/tree/master/specifications/transaction_commit) | tlaplus/Examples | 12 | 4 | 16 |
| [PaxosHowToWinATuringAward](https://github.com/tlaplus/Examples/tree/master/specifications/PaxosHowToWinATuringAward) | tlaplus/Examples | 9 | 6 | 15 |
| [locks_auxiliary_vars](https://github.com/tlaplus/Examples/tree/master/specifications/locks_auxiliary_vars) | tlaplus/Examples | 9 | 5 | 14 |
| [BlockingQueue](https://github.com/lemmy/BlockingQueue) | tlaplus/Examples | 8 | 5 | 13 |
| [LearnProofs](https://github.com/tlaplus/Examples/tree/master/specifications/LearnProofs) | tlaplus/Examples | 5 | 6 | 11 |
| [MultiCarElevator](https://github.com/tlaplus/Examples/tree/master/specifications/MultiCarElevator) | tlaplus/Examples | 9 | 2 | 11 |
| [CigaretteSmokers](https://github.com/tlaplus/Examples/tree/master/specifications/CigaretteSmokers) | tlaplus/Examples | 8 | 2 | 10 |
| [MisraReachability](https://github.com/tlaplus/Examples/tree/master/specifications/MisraReachability) | tlaplus/Examples | 8 | 2 | 10 |
| [Majority](https://github.com/tlaplus/Examples/tree/master/specifications/Majority) | tlaplus/Examples | 9 | – | 9 |
| [glowingRaccoon](https://github.com/tlaplus/Examples/tree/master/specifications/glowingRaccoon) | tlaplus/Examples | 6 | 3 | 9 |
| [Paxos](https://github.com/tlaplus/Examples/tree/master/specifications/Paxos) | tlaplus/Examples | 3 | 4 | 7 |
| [Bakery-Boulangerie](https://github.com/tlaplus/Examples/tree/master/specifications/Bakery-Boulangerie) | tlaplus/Examples | 2 | 4 | 6 |
| [ReadersWriters](https://github.com/tlaplus/Examples/tree/master/specifications/ReadersWriters) | tlaplus/Examples | 3 | 2 | 5 |
| [SpecifyingSystems_Composing](https://github.com/tlaplus/Examples/tree/master/specifications/SpecifyingSystems/Composing) | tlaplus/Examples | 4 | 1 | 5 |
| [Termination](https://github.com/tlaplus/Examples/tree/master/specifications/Termination) | tlaplus/Examples | 4 | 1 | 5 |
| [SpecifyingSystems_AsynchronousInterface](https://github.com/tlaplus/Examples/tree/master/specifications/SpecifyingSystems/AsynchronousInterface) | tlaplus/Examples | 2 | 2 | 4 |
| [DieHard](https://github.com/tlaplus/Examples/tree/master/specifications/DieHard) | tlaplus/Examples | 2 | 1 | 3 |
| [SpecifyingSystems_CachingMemory](https://github.com/tlaplus/Examples/tree/master/specifications/SpecifyingSystems/CachingMemory) | tlaplus/Examples | 2 | 1 | 3 |
| [SpecifyingSystems_FIFO](https://github.com/tlaplus/Examples/tree/master/specifications/SpecifyingSystems/FIFO) | tlaplus/Examples | 2 | 1 | 3 |
| [SpecifyingSystems_Liveness](https://github.com/tlaplus/Examples/tree/master/specifications/SpecifyingSystems/Liveness) | tlaplus/Examples | 3 | – | 3 |
| [SpecifyingSystems_RealTime](https://github.com/tlaplus/Examples/tree/master/specifications/SpecifyingSystems/RealTime) | tlaplus/Examples | 3 | – | 3 |
| [TwoPhase](https://github.com/tlaplus/Examples/tree/master/specifications/TwoPhase) | tlaplus/Examples | 1 | 2 | 3 |
| [spanning](https://github.com/tlaplus/Examples/tree/master/specifications/spanning) | tlaplus/Examples | 2 | 1 | 3 |
| [sums_even](https://github.com/tlaplus/Examples/tree/master/specifications/sums_even) | tlaplus/Examples | 1 | 2 | 3 |
| [CoffeeCan](https://github.com/tlaplus/Examples/tree/master/specifications/CoffeeCan) | tlaplus/Examples | 1 | 1 | 2 |
| [KeyValueStore](https://github.com/tlaplus/Examples/tree/master/specifications/KeyValueStore) | tlaplus/Examples | 1 | 1 | 2 |
| [MissionariesAndCannibals](https://github.com/tlaplus/Examples/tree/master/specifications/MissionariesAndCannibals) | tlaplus/Examples | 1 | 1 | 2 |
| [SpanningTree](https://github.com/tlaplus/Examples/tree/master/specifications/SpanningTree) | tlaplus/Examples | 1 | 1 | 2 |
| [SpecifyingSystems_TLC](https://github.com/tlaplus/Examples/tree/master/specifications/SpecifyingSystems/TLC) | tlaplus/Examples | 1 | 1 | 2 |
| [byihive](https://github.com/tlaplus/Examples/tree/master/specifications/byihive) | tlaplus/Examples | 1 | 1 | 2 |
| GermanProtocol | tlaplus/Examples | – | 1 | 1 |
| [SpecifyingSystems_HourClock](https://github.com/tlaplus/Examples/tree/master/specifications/SpecifyingSystems/HourClock) | tlaplus/Examples | 1 | – | 1 |
| [two_thread_mutex](https://github.com/anvil-verifier/anvil/blob/main/src/tla_demo.rs) | two_thread_mutex (Anvil) | – | 1 | 1 |

**Total: 71 examples — 483 proof-completion + 231 proof-from-scratch = 714 tasks.**
