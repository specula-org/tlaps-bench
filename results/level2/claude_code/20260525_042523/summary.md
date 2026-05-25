# Claude Code (Opus 4.7, --effort max) — L2 clean-72 consolidated

Consolidated authoritative result over 72 clean benchmarks.
Each benchmark takes the run where it first PASSed (original full run, else a max-effort rerun). Failures in the original run were session-limit
artifacts, not capability; every one passes on a clean max-effort rerun.

- **PASS: 72/72 = 100.0%**
- Total tokens: 118,883,457 in / 3,521,238 out

## Provenance

- `20260523_075338`: 61
- `20260524_190959_maxeff_last4`: 4
- `20260524_134005_maxeff_3of9`: 3
- `20260524_150053_maxeff_2more`: 2
- `20260524_084759_maxeffort_retry`: 2

## Per-benchmark

| Benchmark | Verdict | Time (s) | in tok | source run |
|---|---|--:|--:|---|
| Allocator/Allocator_InitMutex.tla | PASS | 39 | 142,538 | 20260523_075338 |
| Allocator/Allocator_InitTypeInvariant.tla | PASS | 42 | 143,783 | 20260523_075338 |
| Allocator/Allocator_NextMutex.tla | PASS | 101 | 214,934 | 20260523_075338 |
| Allocator/Allocator_NextTypeInvariant.tla | PASS | 62 | 199,810 | 20260523_075338 |
| AtomicBakery/AtomicBakeryWithoutSMT_Safety.tla | PASS | 855 | 1,656,395 | 20260523_075338 |
| AtomicBakery/AtomicBakery_MutualExclusion.tla | PASS | 658 | 941,136 | 20260523_075338 |
| Bakery/Bakery_MutualExclusion.tla | PASS | 2574 | 10,112,001 | 20260524_150053_maxeff_2more |
| BubbleSort/BubbleSort_IsPermOfExchange.tla | PASS | 153 | 265,533 | 20260523_075338 |
| BubbleSort/BubbleSort_IsPermOfTransitive.tla | PASS | 110 | 234,289 | 20260523_075338 |
| BubbleSort/BubbleSort_line202.tla | PASS | 1112 | 2,735,311 | 20260524_084759_maxeffort_retry |
| ByzantinePaxos/BPConProof_line4176.tla | PASS | 127 | 558,657 | 20260523_075338 |
| ByzantinePaxos/PConProof_NextDef.tla | PASS | 74 | 258,869 | 20260523_075338 |
| ByzantinePaxos/VoteProof_GeneralNatInduction.tla | PASS | 386 | 724,321 | 20260523_075338 |
| ByzantinePaxos/VoteProof_InitImpliesInv.tla | PASS | 62 | 266,925 | 20260523_075338 |
| ByzantinePaxos/VoteProof_VInv1.tla | PASS | 59 | 335,626 | 20260523_075338 |
| ByzantinePaxos/VoteProof_VT1.tla | PASS | 1681 | 7,343,797 | 20260524_084759_maxeffort_retry |
| Cantor/Cantor10_NoSetContainsAllValues.tla | PASS | 52 | 159,937 | 20260523_075338 |
| Cantor/Cantor1_cantor.tla | PASS | 57 | 168,346 | 20260523_075338 |
| Cantor/Cantor2_cantor.tla | PASS | 56 | 166,369 | 20260523_075338 |
| Cantor/Cantor3_cantor.tla | PASS | 38 | 152,439 | 20260523_075338 |
| Cantor/Cantor4_cantor.tla | PASS | 46 | 133,391 | 20260523_075338 |
| Cantor/Cantor5_cantor.tla | PASS | 61 | 141,595 | 20260523_075338 |
| Cantor/Cantor6_cantor.tla | PASS | 83 | 151,156 | 20260523_075338 |
| Cantor/Cantor7_cantor.tla | PASS | 56 | 139,803 | 20260523_075338 |
| Cantor/Cantor8_Cantor.tla | PASS | 66 | 173,603 | 20260523_075338 |
| Cantor/Cantor9_Cantor.tla | PASS | 175 | 334,132 | 20260523_075338 |
| Consensus/Consensus_Invariance.tla | PASS | 66 | 205,892 | 20260523_075338 |
| Consensus/PaxosProof_OtherMessage.tla | PASS | 81 | 207,661 | 20260523_075338 |
| Consensus/PaxosProof_StructOK1.tla | PASS | 377 | 420,237 | 20260523_075338 |
| Consensus/PaxosProof_line130.tla | PASS | 936 | 2,437,822 | 20260523_075338 |
| Consensus/PaxosProof_line91.tla | PASS | 2144 | 7,096,369 | 20260524_190959_maxeff_last4 |
| Consensus/Voting_AllSafeAtZero.tla | PASS | 63 | 209,355 | 20260523_075338 |
| Consensus/Voting_ChoosableThm.tla | PASS | 44 | 133,324 | 20260523_075338 |
| Consensus/Voting_Consistent.tla | PASS | 2301 | 3,807,961 | 20260524_134005_maxeff_3of9 |
| Consensus/Voting_Invariant.tla | PASS | 987 | 1,547,240 | 20260523_075338 |
| Consensus/Voting_QuorumNonEmpty.tla | PASS | 36 | 129,403 | 20260523_075338 |
| Consensus/Voting_Refinement.tla | PASS | 1742 | 7,436,768 | 20260524_190959_maxeff_last4 |
| Data/GraphTheorem_line62.tla | PASS | 518 | 528,609 | 20260523_075338 |
| Data/SequencesTheorems_AppendDef.tla | PASS | 214 | 441,233 | 20260523_075338 |
| Data/SequencesTheorems_AppendProperties.tla | PASS | 189 | 397,495 | 20260523_075338 |
| Data/SequencesTheorems_ConcatProperties.tla | PASS | 308 | 812,818 | 20260523_075338 |
| Data/SequencesTheorems_ElementOfSeq.tla | PASS | 59 | 164,735 | 20260523_075338 |
| Data/SequencesTheorems_HeadAndTailOfSeq.tla | PASS | 199 | 311,243 | 20260523_075338 |
| Data/SequencesTheorems_InitialSubSeq.tla | PASS | 114 | 185,848 | 20260523_075338 |
| Data/SequencesTheorems_RemoveSeq.tla | PASS | 91 | 195,627 | 20260523_075338 |
| Data/Sets_CardinalityOneConverse.tla | PASS | 64 | 153,813 | 20260523_075338 |
| Data/Sets_CardinalityTwo.tla | PASS | 109 | 219,536 | 20260523_075338 |
| Data/Sets_FiniteSubset.tla | PASS | 387 | 870,679 | 20260523_075338 |
| Data/Sets_IntervalCardinality.tla | PASS | 105 | 184,402 | 20260523_075338 |
| Data/Sets_IsBijectionInverse.tla | PASS | 87 | 161,070 | 20260523_075338 |
| Data/Sets_IsBijectionTransitive.tla | PASS | 57 | 130,179 | 20260523_075338 |
| Data/Sets_PigeonHole.tla | PASS | 710 | 1,487,617 | 20260523_075338 |
| EWD840/EWD840_TerminationDetection.tla | PASS | 893 | 1,294,821 | 20260523_075338 |
| Euclid/EuclidEx_PartialCorrectness.tla | PASS | 251 | 280,252 | 20260523_075338 |
| Euclid/Euclid_Correctness.tla | PASS | 156 | 200,584 | 20260523_075338 |
| Euclid/GCD_GCD1.tla | PASS | 232 | 435,906 | 20260523_075338 |
| Euclid/GCD_GCD2.tla | PASS | 51 | 145,196 | 20260523_075338 |
| Euclid/GCD_GCD3.tla | PASS | 171 | 374,432 | 20260523_075338 |
| Paxos/Consensus_Inv.tla | PASS | 809 | 2,347,617 | 20260523_075338 |
| Paxos/PaxosHistVar_Consistent.tla | PASS | 2537 | 6,002,574 | 20260524_190959_maxeff_last4 |
| Paxos/PaxosHistVar_Invariant.tla | PASS | 2400 | 1,773,304 | 20260523_075338 |
| Paxos/Paxos_Consistent.tla | PASS | 3136 | 6,448,771 | 20260524_190959_maxeff_last4 |
| Paxos/Paxos_Invariant.tla | PASS | 2278 | 8,511,111 | 20260524_134005_maxeff_3of9 |
| Paxos/Paxos_Refinement.tla | PASS | 6063 | 8,375,060 | 20260524_150053_maxeff_2more |
| Peterson/Peterson_Liveness.tla | PASS | 4276 | 22,664,891 | 20260524_134005_maxeff_3of9 |
| Peterson/Peterson_MutualExclusion.tla | PASS | 65 | 157,336 | 20260523_075338 |
| Record/Record_SV_Spec.tla | PASS | 115 | 297,639 | 20260523_075338 |
| SimpleMutex/SimpleMutex_Safety.tla | PASS | 66 | 164,975 | 20260523_075338 |
| SimpleMutex/SimpleMutex_line140.tla | PASS | 47 | 202,070 | 20260523_075338 |
| SumAndMax/SumAndMax_Correctness.tla | PASS | 289 | 643,139 | 20260523_075338 |
| TeachingConcurrency/Simple_AtLeastOneYWhenDone.tla | PASS | 462 | 610,841 | 20260523_075338 |
| Two-Phase/TwoPhase_Implementation.tla | PASS | 124 | 221,306 | 20260523_075338 |
