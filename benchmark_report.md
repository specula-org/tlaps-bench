# TLAPS Benchmark Validation Report

**Generated**: 2026-05-12 20:47:33

## Summary

| Metric | Count |
|--------|-------|
| Total benchmarks | 190 |
| ✅ Passed | 165 |
| ❌ Failed | 12 |
| ⚠️ Cheating detected | 13 |
| 🔍 No proof found | 0 |
| 💥 Error | 0 |
| ⏱️ Total verification time | 1411.6s |
| 📝 Total baseline proof lines | 4456 |

## Results by Module

### Allocator (10/10 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `AllocateMutex` | `Allocator/Allocator.tla` | ✅ PASS | 70 | 0.5s |  |
| `AllocateTypeInvariant` | `Allocator/Allocator.tla` | ✅ PASS | 1 | 0.2s |  |
| `InitMutex` | `Allocator/Allocator.tla` | ✅ PASS | 1 | 0.2s |  |
| `InitTypeInvariant` | `Allocator/Allocator.tla` | ✅ PASS | 1 | 0.2s |  |
| `NextMutex` | `Allocator/Allocator.tla` | ✅ PASS | 1 | 0.2s |  |
| `NextTypeInvariant` | `Allocator/Allocator.tla` | ✅ PASS | 15 | 0.2s |  |
| `RequestMutexBis` | `Allocator/Allocator.tla` | ✅ PASS | 1 | 0.2s |  |
| `RequestTypeInvariant` | `Allocator/Allocator.tla` | ✅ PASS | 1 | 0.2s |  |
| `ReturnMutex` | `Allocator/Allocator.tla` | ✅ PASS | 19 | 0.2s |  |
| `ReturnTypeInvariant` | `Allocator/Allocator.tla` | ✅ PASS | 1 | 0.2s |  |

### AtomicBakery (8/8 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `AfterPrime` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ✅ PASS | 1 | 0.5s |  |
| `GGIrreflexive` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ✅ PASS | 15 | 0.5s |  |
| `InductiveInvariant` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ✅ PASS | 256 | 20.3s |  |
| `InitImpliesTypeOK` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ✅ PASS | 15 | 0.5s |  |
| `InitInv` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ✅ PASS | 1 | 0.5s |  |
| `InvExclusion` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ✅ PASS | 1 | 0.5s |  |
| `Safety` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ✅ PASS | 5 | 0.5s |  |
| `TypeOKInvariant` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ✅ PASS | 50 | 1.9s |  |

### BubbleSort (7/8 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `CompositionAssociative` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 1 | 0.2s |  |
| `CompositionOfPerms` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 1 | 5.3s |  |
| `ExchangeAPerm` | `BubbleSort/BubbleSort.tla` | ❌ FAIL | 1 | 5.2s | 1/2 obligations failed |
| `IdAPerm` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 1 | 0.2s |  |
| `IdIdentity` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 1 | 0.2s |  |
| `IsPermOfExchange` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 8 | 5.4s |  |
| `IsPermOfReflexive` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 1 | 0.2s |  |
| `IsPermOfTransitive` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 14 | 5.6s |  |

### ByzantinePaxos (31/38 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `BMessageLemma` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 8 | 0.3s |  |
| `EnabledDef` | `ByzantinePaxos/Consensus.tla` | ⚠️ CHEATING | 7 | 5.3s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `FiniteMsgsLemma` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 12 | 89.0s |  |
| `GeneralNatInduction` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 31 | 5.4s |  |
| `InductiveInvariance` | `ByzantinePaxos/Consensus.tla` | ✅ PASS | 15 | 5.3s |  |
| `InductiveInvariance` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 312 | 11.1s |  |
| `InitImpliesInv` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 13 | 0.4s |  |
| `Invariance` | `ByzantinePaxos/Consensus.tla` | ⚠️ CHEATING | 11 | 0.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `KnowsSafeAtDef` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 2 | 93.5s |  |
| `LiveSpecEquals` | `ByzantinePaxos/Consensus.tla` | ⚠️ CHEATING | 7 | 0.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `Liveness` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 364 | 23.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `MaxBallotLemma1` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 22 | 0.6s |  |
| `MaxBallotLemma2` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 96 | 2.3s |  |
| `MaxBallotProp` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 15 | 0.5s |  |
| `MsgsLemma` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 308 | 180.0s | Timeout |
| `MsgsTypeLemma` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 19 | 87.6s |  |
| `MsgsTypeLemmaPrime` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 19 | 87.5s |  |
| `NextDef` | `ByzantinePaxos/PConProof.tla` | ✅ PASS | 8 | 0.3s |  |
| `NextDef` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 7 | 0.3s |  |
| `NextDef` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 9 | 6.3s |  |
| `OnePlusFinite` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 1 | 5.2s |  |
| `PMaxBalLemma3` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 29 | 90.5s |  |
| `PNextDef` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 6 | 86.1s |  |
| `PmaxBalLemma1` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 10 | 0.3s |  |
| `PmaxBalLemma2` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 11 | 5.3s |  |
| `PmaxBalLemma4` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 32 | 93.2s |  |
| `PmaxBalLemma5` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 34 | 91.1s |  |
| `QuorumNonEmpty` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 1 | 0.2s |  |
| `QuorumTheorem` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 16 | 0.4s |  |
| `SafeAtProp` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 48 | 10.8s |  |
| `SafeLemma` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 142 | 7.0s |  |
| `VT0` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 71 | 6.1s |  |
| `VT0Prime` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 71 | 6.2s |  |
| `VT1` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 35 | 0.7s |  |
| `VT1Prime` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 35 | 0.8s |  |
| `VT2` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 6 | 0.3s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `VT3` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 103 | 8.1s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `VT4` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 75 | 6.0s |  |

### Cantor (11/11 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `Cantor` | `Cantor/Cantor10.tla` | ✅ PASS | 6 | 0.2s |  |
| `Cantor` | `Cantor/Cantor8.tla` | ✅ PASS | 15 | 0.2s |  |
| `Cantor` | `Cantor/Cantor9.tla` | ✅ PASS | 11 | 5.2s |  |
| `NoSetContainsAllValues` | `Cantor/Cantor10.tla` | ✅ PASS | 13 | 5.2s |  |
| `cantor` | `Cantor/Cantor5.tla` | ✅ PASS | 5 | 0.2s |  |
| `cantor` | `Cantor/Cantor6.tla` | ✅ PASS | 4 | 0.2s |  |
| `cantor` | `Cantor/Cantor7.tla` | ✅ PASS | 6 | 0.2s |  |
| `cantor` | `Cantor/Cantor1.tla` | ✅ PASS | 7 | 5.3s |  |
| `cantor` | `Cantor/Cantor2.tla` | ✅ PASS | 19 | 5.2s |  |
| `cantor` | `Cantor/Cantor3.tla` | ✅ PASS | 20 | 5.2s |  |
| `cantor` | `Cantor/Cantor4.tla` | ✅ PASS | 14 | 5.2s |  |

### Consensus (44/50 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `AllSafeAtZero` | `Consensus/Voting.tla` | ✅ PASS | 1 | 0.2s |  |
| `CardinalityInNat` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.2s |  |
| `CardinalityInNat` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.2s |  |
| `CardinalityInNat` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.2s |  |
| `CardinalityOne` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.4s |  |
| `CardinalityOne` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.4s |  |
| `CardinalityOne` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.4s |  |
| `CardinalityOneConverse` | `Consensus/Sets.tla` | ✅ PASS | 6 | 5.3s |  |
| `CardinalityOneConverse` | `Consensus/Sets.tla` | ✅ PASS | 6 | 5.3s |  |
| `CardinalityOneConverse` | `Consensus/Sets.tla` | ✅ PASS | 6 | 5.3s |  |
| `CardinalityPlusOne` | `Consensus/Sets.tla` | ✅ PASS | 8 | 0.4s |  |
| `CardinalityPlusOne` | `Consensus/Sets.tla` | ✅ PASS | 8 | 0.4s |  |
| `CardinalityPlusOne` | `Consensus/Sets.tla` | ✅ PASS | 8 | 0.4s |  |
| `CardinalitySetMinus` | `Consensus/Sets.tla` | ⚠️ CHEATING | 41 | 0.6s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `CardinalitySetMinus` | `Consensus/Sets.tla` | ⚠️ CHEATING | 41 | 0.6s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `CardinalitySetMinus` | `Consensus/Sets.tla` | ⚠️ CHEATING | 41 | 0.6s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `CardinalityTwo` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.4s |  |
| `CardinalityTwo` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.4s |  |
| `CardinalityTwo` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.4s |  |
| `CardinalityZero` | `Consensus/Sets.tla` | ✅ PASS | 13 | 0.3s |  |
| `CardinalityZero` | `Consensus/Sets.tla` | ✅ PASS | 13 | 0.3s |  |
| `CardinalityZero` | `Consensus/Sets.tla` | ✅ PASS | 13 | 0.3s |  |
| `ChoosableThm` | `Consensus/Voting.tla` | ✅ PASS | 1 | 0.2s |  |
| `Consistent` | `Consensus/Voting.tla` | ✅ PASS | 9 | 0.3s |  |
| `FiniteSubset` | `Consensus/Sets.tla` | ✅ PASS | 65 | 0.8s |  |
| `FiniteSubset` | `Consensus/Sets.tla` | ✅ PASS | 65 | 0.8s |  |
| `FiniteSubset` | `Consensus/Sets.tla` | ✅ PASS | 65 | 0.8s |  |
| `IntervalCardinality` | `Consensus/Sets.tla` | ✅ PASS | 14 | 0.6s |  |
| `IntervalCardinality` | `Consensus/Sets.tla` | ✅ PASS | 14 | 0.6s |  |
| `IntervalCardinality` | `Consensus/Sets.tla` | ✅ PASS | 14 | 0.6s |  |
| `Invariance` | `Consensus/Consensus.tla` | ✅ PASS | 6 | 0.3s |  |
| `Invariant` | `Consensus/Voting.tla` | ✅ PASS | 82 | 11.7s |  |
| `IsBijectionInverse` | `Consensus/Sets.tla` | ✅ PASS | 3 | 0.2s |  |
| `IsBijectionInverse` | `Consensus/Sets.tla` | ✅ PASS | 3 | 0.2s |  |
| `IsBijectionInverse` | `Consensus/Sets.tla` | ✅ PASS | 3 | 0.2s |  |
| `IsBijectionTransitive` | `Consensus/Sets.tla` | ✅ PASS | 7 | 0.2s |  |
| `IsBijectionTransitive` | `Consensus/Sets.tla` | ✅ PASS | 7 | 0.2s |  |
| `IsBijectionTransitive` | `Consensus/Sets.tla` | ✅ PASS | 7 | 0.2s |  |
| `OneVoteThm` | `Consensus/Voting.tla` | ✅ PASS | 1 | 0.2s |  |
| `OtherMessage` | `Consensus/PaxosProof.tla` | ❌ FAIL | 1 | 6.8s | 1/19 obligations failed |
| `PigeonHole` | `Consensus/Sets.tla` | ✅ PASS | 47 | 0.8s |  |
| `PigeonHole` | `Consensus/Sets.tla` | ✅ PASS | 47 | 0.8s |  |
| `PigeonHole` | `Consensus/Sets.tla` | ✅ PASS | 47 | 0.8s |  |
| `QuorumNonEmpty` | `Consensus/Voting.tla` | ✅ PASS | 1 | 0.2s |  |
| `Refinement` | `Consensus/Voting.tla` | ✅ PASS | 21 | 1.1s |  |
| `ShowsSafety` | `Consensus/Voting.tla` | ✅ PASS | 3 | 2.1s |  |
| `VotesSafeImpliesConsistency` | `Consensus/Voting.tla` | ✅ PASS | 18 | 0.3s |  |
| `WFmsgs` | `Consensus/PaxosProof.tla` | ✅ PASS | 1 | 1.1s |  |
| `struct_lemma` | `Consensus/PaxosProof.tla` | ⚠️ CHEATING | 7 | 6.8s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `typing` | `Consensus/PaxosProof.tla` | ⚠️ CHEATING | 8 | 1.4s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |

### Data (33/37 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `AppendDef` | `Data/SequencesTheorems.tla` | ❌ FAIL | 1 | 5.2s | 1/2 obligations failed |
| `AppendProperties` | `Data/SequencesTheorems.tla` | ✅ PASS | 1 | 0.2s |  |
| `AtLeastTwo` | `Data/GraphTheorem.tla` | ✅ PASS | 1 | 0.2s |  |
| `CardinalityInNat` | `Data/Sets.tla` | ✅ PASS | 1 | 0.2s |  |
| `CardinalityInNat` | `Data/Sets.tla` | ✅ PASS | 1 | 0.2s |  |
| `CardinalityOne` | `Data/Sets.tla` | ✅ PASS | 1 | 0.4s |  |
| `CardinalityOne` | `Data/Sets.tla` | ✅ PASS | 1 | 0.4s |  |
| `CardinalityOneConverse` | `Data/Sets.tla` | ✅ PASS | 6 | 5.3s |  |
| `CardinalityOneConverse` | `Data/Sets.tla` | ✅ PASS | 6 | 5.3s |  |
| `CardinalityPlusOne` | `Data/Sets.tla` | ✅ PASS | 8 | 0.4s |  |
| `CardinalityPlusOne` | `Data/Sets.tla` | ✅ PASS | 8 | 0.4s |  |
| `CardinalitySetMinus` | `Data/Sets.tla` | ⚠️ CHEATING | 41 | 0.6s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `CardinalitySetMinus` | `Data/Sets.tla` | ⚠️ CHEATING | 41 | 0.6s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `CardinalityTwo` | `Data/Sets.tla` | ✅ PASS | 1 | 0.4s |  |
| `CardinalityTwo` | `Data/Sets.tla` | ✅ PASS | 1 | 0.4s |  |
| `CardinalityZero` | `Data/Sets.tla` | ✅ PASS | 13 | 0.3s |  |
| `CardinalityZero` | `Data/Sets.tla` | ✅ PASS | 13 | 0.3s |  |
| `ConcatDef` | `Data/SequencesTheorems.tla` | ❌ FAIL | 1 | 5.2s | 1/2 obligations failed |
| `ConcatProperties` | `Data/SequencesTheorems.tla` | ✅ PASS | 1 | 0.2s |  |
| `EdgesAxiom` | `Data/GraphTheorem.tla` | ✅ PASS | 1 | 0.4s |  |
| `ElementOfSeq` | `Data/SequencesTheorems.tla` | ✅ PASS | 1 | 0.2s |  |
| `EmptySeq` | `Data/SequencesTheorems.tla` | ✅ PASS | 1 | 0.2s |  |
| `FiniteSubset` | `Data/Sets.tla` | ✅ PASS | 65 | 0.8s |  |
| `FiniteSubset` | `Data/Sets.tla` | ✅ PASS | 65 | 0.8s |  |
| `HeadAndTailOfSeq` | `Data/SequencesTheorems.tla` | ✅ PASS | 9 | 0.2s |  |
| `InitialSubSeq` | `Data/SequencesTheorems.tla` | ✅ PASS | 16 | 1.1s |  |
| `IntervalCardinality` | `Data/Sets.tla` | ✅ PASS | 13 | 0.6s |  |
| `IntervalCardinality` | `Data/Sets.tla` | ✅ PASS | 13 | 0.6s |  |
| `IsBijectionInverse` | `Data/Sets.tla` | ✅ PASS | 3 | 0.2s |  |
| `IsBijectionInverse` | `Data/Sets.tla` | ✅ PASS | 3 | 0.2s |  |
| `IsBijectionTransitive` | `Data/Sets.tla` | ✅ PASS | 7 | 0.2s |  |
| `IsBijectionTransitive` | `Data/Sets.tla` | ✅ PASS | 7 | 0.2s |  |
| `LenAxiom` | `Data/SequencesTheorems.tla` | ✅ PASS | 1 | 0.2s |  |
| `LenDomain` | `Data/SequencesTheorems.tla` | ✅ PASS | 1 | 0.2s |  |
| `PigeonHole` | `Data/Sets.tla` | ✅ PASS | 47 | 0.8s |  |
| `PigeonHole` | `Data/Sets.tla` | ✅ PASS | 47 | 0.8s |  |
| `RemoveSeq` | `Data/SequencesTheorems.tla` | ✅ PASS | 17 | 0.3s |  |

### EWD840 (1/2 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `Inv_implies_Termination` | `EWD840/EWD840.tla` | ✅ PASS | 9 | 1.7s |  |
| `TypeOK_inv` | `EWD840/EWD840.tla` | ❌ FAIL | 7 | 45.4s | 1/8 obligations failed |

### Euclid (5/6 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `Correctness` | `Euclid/Euclid-TLAPS-Example/Euclid.tla` | ✅ PASS | 8 | 0.2s |  |
| `GCD1` | `Euclid/Euclid-Hyperbook/GCD.tla` | ✅ PASS | 9 | 0.2s |  |
| `GCD2` | `Euclid/Euclid-Hyperbook/GCD.tla` | ✅ PASS | 1 | 0.2s |  |
| `GCD3` | `Euclid/Euclid-Hyperbook/GCD.tla` | ❌ FAIL | 9 | 5.5s | 1/3 obligations failed |
| `InitProperty` | `Euclid/Euclid-TLAPS-Example/Euclid.tla` | ✅ PASS | 1 | 0.2s |  |
| `NextProperty` | `Euclid/Euclid-TLAPS-Example/Euclid.tla` | ✅ PASS | 20 | 0.3s |  |

### Paxos (9/13 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `Consistent` | `Paxos/PaxosHistVar.tla` | ✅ PASS | 25 | 0.5s |  |
| `Consistent` | `Paxos/Paxos.tla` | ✅ PASS | 25 | 0.4s |  |
| `Invariant` | `Paxos/PaxosHistVar.tla` | ❌ FAIL | 126 | 23.7s | 1/109 obligations failed |
| `Invariant` | `Paxos/Paxos.tla` | ❌ FAIL | 184 | 45.8s | 2/161 obligations failed |
| `NoneNotAValue` | `Paxos/Paxos.tla` | ✅ PASS | 1 | 0.2s |  |
| `QuorumNonEmpty` | `Paxos/Paxos.tla` | ✅ PASS | 1 | 0.2s |  |
| `Refinement` | `Paxos/Paxos.tla` | ❌ FAIL | 16 | 16.3s | 1/19 obligations failed |
| `SafeAtStable` | `Paxos/Paxos.tla` | ✅ PASS | 49 | 5.7s |  |
| `SafeAtStable` | `Paxos/PaxosHistVar.tla` | ❌ FAIL | 39 | 60.5s | 2/45 obligations failed |
| `VotedInv` | `Paxos/PaxosHistVar.tla` | ✅ PASS | 1 | 0.2s |  |
| `VotedInv` | `Paxos/Paxos.tla` | ✅ PASS | 1 | 0.2s |  |
| `VotedOnce` | `Paxos/PaxosHistVar.tla` | ✅ PASS | 1 | 0.2s |  |
| `VotedOnce` | `Paxos/Paxos.tla` | ✅ PASS | 1 | 0.2s |  |

### SimpleMutex (4/5 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `Initialization` | `SimpleMutex/SimpleMutex.tla` | ✅ PASS | 1 | 0.2s |  |
| `Invariance` | `SimpleMutex/SimpleMutex.tla` | ❌ FAIL | 38 | 5.6s | 1/39 obligations failed |
| `Mutex` | `SimpleMutex/SimpleMutex.tla` | ✅ PASS | 1 | 0.2s |  |
| `Safety` | `SimpleMutex/SimpleMutex.tla` | ✅ PASS | 1 | 0.2s |  |
| `TLAInvariance` | `SimpleMutex/SimpleMutex.tla` | ✅ PASS | 1 | 0.2s |  |

### Two-Phase (2/2 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `Implementation` | `Two-Phase/TwoPhase.tla` | ✅ PASS | 14 | 0.3s |  |
| `Mod2` | `Two-Phase/TwoPhase.tla` | ✅ PASS | 7 | 0.2s |  |

## Cheating Detection Details

### `benchmark/ByzantinePaxos/Consensus_EnabledDef.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/ByzantinePaxos/Consensus_Invariance.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/ByzantinePaxos/Consensus_LiveSpecEquals.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/ByzantinePaxos/VoteProof_Liveness.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/ByzantinePaxos/VoteProof_VT2.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/ByzantinePaxos/VoteProof_VT3.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/Consensus/Consensus_CardinalitySetMinus.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/Consensus/PaxosProof_CardinalitySetMinus.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/Consensus/Sets_CardinalitySetMinus.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/Consensus/PaxosProof_struct_lemma.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/Consensus/PaxosProof_typing.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/Data/GraphTheorem_CardinalitySetMinus.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/Data/Sets_CardinalitySetMinus.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

## Failed Verification Details

### `benchmark/BubbleSort/BubbleSort_ExchangeAPerm.tla`

```
[INFO]: All 0 obligation proved.
[ERROR]: Could not prove or check:
[ERROR]: 1/2 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/ByzantinePaxos/BPConProof_MsgsLemma.tla`


### `benchmark/Consensus/PaxosProof_OtherMessage.tla`

```
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
[ERROR]: Could not prove or check:
[ERROR]: 1/19 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Data/SequencesTheorems_AppendDef.tla`

```
[INFO]: All 0 obligation proved.
[ERROR]: Could not prove or check:
[ERROR]: 1/2 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Data/SequencesTheorems_ConcatDef.tla`

```
[INFO]: All 0 obligation proved.
[ERROR]: Could not prove or check:
[ERROR]: 1/2 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/EWD840/EWD840_TypeOK_inv.tla`

```
[INFO]: All 0 obligation proved.
[ERROR]: Could not prove or check:
[ERROR]: 1/8 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Euclid/GCD_GCD3.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/3 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Paxos/PaxosHistVar_Invariant.tla`

```
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
[ERROR]: Could not prove or check:
[ERROR]: 1/109 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Paxos/Paxos_Invariant.tla`

```
[INFO]: All 0 obligation proved.
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: 2/161 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Paxos/Paxos_Refinement.tla`

```
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
[ERROR]: Could not prove or check:
[ERROR]: 1/19 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Paxos/PaxosHistVar_SafeAtStable.tla`

```
[INFO]: All 0 obligation proved.
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: 2/45 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/SimpleMutex/SimpleMutex_Invariance.tla`

```
[INFO]: All 0 obligation proved.
[ERROR]: Could not prove or check:
[ERROR]: 1/39 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```
