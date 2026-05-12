# TLAPS Benchmark Validation Report

**Generated**: 2026-05-12 20:14:42

## Summary

| Metric | Count |
|--------|-------|
| Total benchmarks | 190 |
| ✅ Passed | 165 |
| ❌ Failed | 12 |
| ⚠️ Cheating detected | 13 |
| 🔍 No proof found | 0 |
| 💥 Error | 0 |
| ⏱️ Total verification time | 1482.4s |
| 📝 Total baseline proof lines | 4456 |

## Results by Module

### Allocator (10/10 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `AllocateMutex` | `Allocator/Allocator.tla` | ✅ PASS | 70 | 0.8s |  |
| `AllocateTypeInvariant` | `Allocator/Allocator.tla` | ✅ PASS | 1 | 0.3s |  |
| `InitMutex` | `Allocator/Allocator.tla` | ✅ PASS | 1 | 0.3s |  |
| `InitTypeInvariant` | `Allocator/Allocator.tla` | ✅ PASS | 1 | 0.3s |  |
| `NextMutex` | `Allocator/Allocator.tla` | ✅ PASS | 1 | 0.3s |  |
| `NextTypeInvariant` | `Allocator/Allocator.tla` | ✅ PASS | 15 | 0.4s |  |
| `RequestMutexBis` | `Allocator/Allocator.tla` | ✅ PASS | 1 | 0.3s |  |
| `RequestTypeInvariant` | `Allocator/Allocator.tla` | ✅ PASS | 1 | 0.3s |  |
| `ReturnMutex` | `Allocator/Allocator.tla` | ✅ PASS | 19 | 0.4s |  |
| `ReturnTypeInvariant` | `Allocator/Allocator.tla` | ✅ PASS | 1 | 0.3s |  |

### AtomicBakery (8/8 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `AfterPrime` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ✅ PASS | 1 | 0.9s |  |
| `GGIrreflexive` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ✅ PASS | 15 | 1.0s |  |
| `InductiveInvariant` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ✅ PASS | 256 | 23.5s |  |
| `InitImpliesTypeOK` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ✅ PASS | 15 | 0.9s |  |
| `InitInv` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ✅ PASS | 1 | 0.8s |  |
| `InvExclusion` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ✅ PASS | 1 | 0.9s |  |
| `Safety` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ✅ PASS | 5 | 0.9s |  |
| `TypeOKInvariant` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ✅ PASS | 50 | 3.7s |  |

### BubbleSort (7/8 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `CompositionAssociative` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 1 | 0.3s |  |
| `CompositionOfPerms` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 1 | 5.5s |  |
| `ExchangeAPerm` | `BubbleSort/BubbleSort.tla` | ❌ FAIL | 1 | 5.3s | 1/2 obligations failed |
| `IdAPerm` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 1 | 0.3s |  |
| `IdIdentity` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 1 | 0.3s |  |
| `IsPermOfExchange` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 8 | 5.6s |  |
| `IsPermOfReflexive` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 1 | 0.3s |  |
| `IsPermOfTransitive` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 14 | 5.9s |  |

### ByzantinePaxos (31/38 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `BMessageLemma` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 8 | 0.5s |  |
| `EnabledDef` | `ByzantinePaxos/Consensus.tla` | ⚠️ CHEATING | 7 | 5.5s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `FiniteMsgsLemma` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 12 | 91.0s |  |
| `GeneralNatInduction` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 31 | 5.9s |  |
| `InductiveInvariance` | `ByzantinePaxos/Consensus.tla` | ✅ PASS | 15 | 5.5s |  |
| `InductiveInvariance` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 312 | 13.6s |  |
| `InitImpliesInv` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 13 | 0.8s |  |
| `Invariance` | `ByzantinePaxos/Consensus.tla` | ⚠️ CHEATING | 11 | 0.4s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `KnowsSafeAtDef` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 2 | 93.8s |  |
| `LiveSpecEquals` | `ByzantinePaxos/Consensus.tla` | ⚠️ CHEATING | 7 | 0.4s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `Liveness` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 364 | 27.0s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `MaxBallotLemma1` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 22 | 1.1s |  |
| `MaxBallotLemma2` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 96 | 4.4s |  |
| `MaxBallotProp` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 15 | 1.1s |  |
| `MsgsLemma` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 308 | 120.0s | Timeout |
| `MsgsTypeLemma` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 19 | 90.3s |  |
| `MsgsTypeLemmaPrime` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 19 | 89.6s |  |
| `NextDef` | `ByzantinePaxos/PConProof.tla` | ✅ PASS | 8 | 0.6s |  |
| `NextDef` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 7 | 0.8s |  |
| `NextDef` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 9 | 7.4s |  |
| `OnePlusFinite` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 1 | 5.4s |  |
| `PMaxBalLemma3` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 29 | 93.0s |  |
| `PNextDef` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 6 | 89.2s |  |
| `PmaxBalLemma1` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 10 | 0.6s |  |
| `PmaxBalLemma2` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 11 | 5.5s |  |
| `PmaxBalLemma4` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 32 | 99.0s |  |
| `PmaxBalLemma5` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 34 | 93.5s |  |
| `QuorumNonEmpty` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 1 | 0.3s |  |
| `QuorumTheorem` | `ByzantinePaxos/BPConProof.tla` | ✅ PASS | 16 | 0.9s |  |
| `SafeAtProp` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 48 | 11.5s |  |
| `SafeLemma` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 142 | 9.0s |  |
| `VT0` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 71 | 7.2s |  |
| `VT0Prime` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 71 | 7.7s |  |
| `VT1` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 35 | 1.4s |  |
| `VT1Prime` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 35 | 1.5s |  |
| `VT2` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 6 | 0.5s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `VT3` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 103 | 10.7s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `VT4` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 75 | 6.6s |  |

### Cantor (11/11 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `Cantor` | `Cantor/Cantor10.tla` | ✅ PASS | 6 | 0.3s |  |
| `Cantor` | `Cantor/Cantor8.tla` | ✅ PASS | 15 | 0.4s |  |
| `Cantor` | `Cantor/Cantor9.tla` | ✅ PASS | 11 | 5.4s |  |
| `NoSetContainsAllValues` | `Cantor/Cantor10.tla` | ✅ PASS | 13 | 5.4s |  |
| `cantor` | `Cantor/Cantor7.tla` | ✅ PASS | 6 | 0.3s |  |
| `cantor` | `Cantor/Cantor6.tla` | ✅ PASS | 4 | 0.3s |  |
| `cantor` | `Cantor/Cantor5.tla` | ✅ PASS | 5 | 0.4s |  |
| `cantor` | `Cantor/Cantor2.tla` | ✅ PASS | 19 | 5.4s |  |
| `cantor` | `Cantor/Cantor1.tla` | ✅ PASS | 7 | 5.4s |  |
| `cantor` | `Cantor/Cantor3.tla` | ✅ PASS | 20 | 5.4s |  |
| `cantor` | `Cantor/Cantor4.tla` | ✅ PASS | 14 | 5.4s |  |

### Consensus (44/50 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `AllSafeAtZero` | `Consensus/Voting.tla` | ✅ PASS | 1 | 0.4s |  |
| `CardinalityInNat` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.3s |  |
| `CardinalityInNat` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.6s |  |
| `CardinalityInNat` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.5s |  |
| `CardinalityOne` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.8s |  |
| `CardinalityOne` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.9s |  |
| `CardinalityOne` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.9s |  |
| `CardinalityOneConverse` | `Consensus/Sets.tla` | ✅ PASS | 6 | 5.5s |  |
| `CardinalityOneConverse` | `Consensus/Sets.tla` | ✅ PASS | 6 | 5.7s |  |
| `CardinalityOneConverse` | `Consensus/Sets.tla` | ✅ PASS | 6 | 5.6s |  |
| `CardinalityPlusOne` | `Consensus/Sets.tla` | ✅ PASS | 8 | 0.8s |  |
| `CardinalityPlusOne` | `Consensus/Sets.tla` | ✅ PASS | 8 | 0.9s |  |
| `CardinalityPlusOne` | `Consensus/Sets.tla` | ✅ PASS | 8 | 0.9s |  |
| `CardinalitySetMinus` | `Consensus/Sets.tla` | ⚠️ CHEATING | 41 | 1.1s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `CardinalitySetMinus` | `Consensus/Sets.tla` | ⚠️ CHEATING | 41 | 1.4s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `CardinalitySetMinus` | `Consensus/Sets.tla` | ⚠️ CHEATING | 41 | 1.4s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `CardinalityTwo` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.9s |  |
| `CardinalityTwo` | `Consensus/Sets.tla` | ✅ PASS | 1 | 1.0s |  |
| `CardinalityTwo` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.8s |  |
| `CardinalityZero` | `Consensus/Sets.tla` | ✅ PASS | 13 | 0.7s |  |
| `CardinalityZero` | `Consensus/Sets.tla` | ✅ PASS | 13 | 0.8s |  |
| `CardinalityZero` | `Consensus/Sets.tla` | ✅ PASS | 13 | 0.6s |  |
| `ChoosableThm` | `Consensus/Voting.tla` | ✅ PASS | 1 | 0.5s |  |
| `Consistent` | `Consensus/Voting.tla` | ✅ PASS | 9 | 0.6s |  |
| `FiniteSubset` | `Consensus/Sets.tla` | ✅ PASS | 65 | 1.9s |  |
| `FiniteSubset` | `Consensus/Sets.tla` | ✅ PASS | 65 | 2.1s |  |
| `FiniteSubset` | `Consensus/Sets.tla` | ✅ PASS | 65 | 1.9s |  |
| `IntervalCardinality` | `Consensus/Sets.tla` | ✅ PASS | 14 | 1.4s |  |
| `IntervalCardinality` | `Consensus/Sets.tla` | ✅ PASS | 14 | 1.5s |  |
| `IntervalCardinality` | `Consensus/Sets.tla` | ✅ PASS | 14 | 1.4s |  |
| `Invariance` | `Consensus/Consensus.tla` | ✅ PASS | 6 | 0.7s |  |
| `Invariant` | `Consensus/Voting.tla` | ✅ PASS | 82 | 13.3s |  |
| `IsBijectionInverse` | `Consensus/Sets.tla` | ✅ PASS | 3 | 0.6s |  |
| `IsBijectionInverse` | `Consensus/Sets.tla` | ✅ PASS | 3 | 0.6s |  |
| `IsBijectionInverse` | `Consensus/Sets.tla` | ✅ PASS | 3 | 0.6s |  |
| `IsBijectionTransitive` | `Consensus/Sets.tla` | ✅ PASS | 7 | 0.6s |  |
| `IsBijectionTransitive` | `Consensus/Sets.tla` | ✅ PASS | 7 | 0.7s |  |
| `IsBijectionTransitive` | `Consensus/Sets.tla` | ✅ PASS | 7 | 0.6s |  |
| `OneVoteThm` | `Consensus/Voting.tla` | ✅ PASS | 1 | 0.6s |  |
| `OtherMessage` | `Consensus/PaxosProof.tla` | ❌ FAIL | 1 | 8.6s | 1/19 obligations failed |
| `PigeonHole` | `Consensus/Sets.tla` | ✅ PASS | 47 | 1.8s |  |
| `PigeonHole` | `Consensus/Sets.tla` | ✅ PASS | 47 | 1.9s |  |
| `PigeonHole` | `Consensus/Sets.tla` | ✅ PASS | 47 | 1.8s |  |
| `QuorumNonEmpty` | `Consensus/Voting.tla` | ✅ PASS | 1 | 0.4s |  |
| `Refinement` | `Consensus/Voting.tla` | ✅ PASS | 21 | 2.5s |  |
| `ShowsSafety` | `Consensus/Voting.tla` | ✅ PASS | 3 | 4.3s |  |
| `VotesSafeImpliesConsistency` | `Consensus/Voting.tla` | ✅ PASS | 18 | 0.9s |  |
| `WFmsgs` | `Consensus/PaxosProof.tla` | ✅ PASS | 1 | 2.3s |  |
| `struct_lemma` | `Consensus/PaxosProof.tla` | ⚠️ CHEATING | 7 | 8.7s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `typing` | `Consensus/PaxosProof.tla` | ⚠️ CHEATING | 8 | 2.8s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |

### Data (33/37 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `AppendDef` | `Data/SequencesTheorems.tla` | ❌ FAIL | 1 | 5.5s | 1/2 obligations failed |
| `AppendProperties` | `Data/SequencesTheorems.tla` | ✅ PASS | 1 | 0.5s |  |
| `AtLeastTwo` | `Data/GraphTheorem.tla` | ✅ PASS | 1 | 0.7s |  |
| `CardinalityInNat` | `Data/Sets.tla` | ✅ PASS | 1 | 0.6s |  |
| `CardinalityInNat` | `Data/Sets.tla` | ✅ PASS | 1 | 0.6s |  |
| `CardinalityOne` | `Data/Sets.tla` | ✅ PASS | 1 | 0.9s |  |
| `CardinalityOne` | `Data/Sets.tla` | ✅ PASS | 1 | 1.0s |  |
| `CardinalityOneConverse` | `Data/Sets.tla` | ✅ PASS | 6 | 5.8s |  |
| `CardinalityOneConverse` | `Data/Sets.tla` | ✅ PASS | 6 | 5.8s |  |
| `CardinalityPlusOne` | `Data/Sets.tla` | ✅ PASS | 8 | 1.1s |  |
| `CardinalityPlusOne` | `Data/Sets.tla` | ✅ PASS | 8 | 1.0s |  |
| `CardinalitySetMinus` | `Data/Sets.tla` | ⚠️ CHEATING | 41 | 1.6s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `CardinalitySetMinus` | `Data/Sets.tla` | ⚠️ CHEATING | 41 | 1.6s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `CardinalityTwo` | `Data/Sets.tla` | ✅ PASS | 1 | 1.1s |  |
| `CardinalityTwo` | `Data/Sets.tla` | ✅ PASS | 1 | 1.1s |  |
| `CardinalityZero` | `Data/Sets.tla` | ✅ PASS | 13 | 0.7s |  |
| `CardinalityZero` | `Data/Sets.tla` | ✅ PASS | 13 | 0.8s |  |
| `ConcatDef` | `Data/SequencesTheorems.tla` | ❌ FAIL | 1 | 5.5s | 1/2 obligations failed |
| `ConcatProperties` | `Data/SequencesTheorems.tla` | ✅ PASS | 1 | 0.5s |  |
| `EdgesAxiom` | `Data/GraphTheorem.tla` | ✅ PASS | 1 | 1.2s |  |
| `ElementOfSeq` | `Data/SequencesTheorems.tla` | ✅ PASS | 1 | 0.5s |  |
| `EmptySeq` | `Data/SequencesTheorems.tla` | ✅ PASS | 1 | 0.5s |  |
| `FiniteSubset` | `Data/Sets.tla` | ✅ PASS | 65 | 2.2s |  |
| `FiniteSubset` | `Data/Sets.tla` | ✅ PASS | 65 | 2.1s |  |
| `HeadAndTailOfSeq` | `Data/SequencesTheorems.tla` | ✅ PASS | 9 | 0.7s |  |
| `InitialSubSeq` | `Data/SequencesTheorems.tla` | ✅ PASS | 16 | 2.5s |  |
| `IntervalCardinality` | `Data/Sets.tla` | ✅ PASS | 13 | 1.5s |  |
| `IntervalCardinality` | `Data/Sets.tla` | ✅ PASS | 13 | 1.4s |  |
| `IsBijectionInverse` | `Data/Sets.tla` | ✅ PASS | 3 | 0.6s |  |
| `IsBijectionInverse` | `Data/Sets.tla` | ✅ PASS | 3 | 0.8s |  |
| `IsBijectionTransitive` | `Data/Sets.tla` | ✅ PASS | 7 | 0.7s |  |
| `IsBijectionTransitive` | `Data/Sets.tla` | ✅ PASS | 7 | 0.8s |  |
| `LenAxiom` | `Data/SequencesTheorems.tla` | ✅ PASS | 1 | 0.5s |  |
| `LenDomain` | `Data/SequencesTheorems.tla` | ✅ PASS | 1 | 0.5s |  |
| `PigeonHole` | `Data/Sets.tla` | ✅ PASS | 47 | 1.9s |  |
| `PigeonHole` | `Data/Sets.tla` | ✅ PASS | 47 | 1.7s |  |
| `RemoveSeq` | `Data/SequencesTheorems.tla` | ✅ PASS | 17 | 0.8s |  |

### EWD840 (1/2 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `Inv_implies_Termination` | `EWD840/EWD840.tla` | ✅ PASS | 9 | 3.6s |  |
| `TypeOK_inv` | `EWD840/EWD840.tla` | ❌ FAIL | 7 | 46.0s | 1/8 obligations failed |

### Euclid (5/6 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `Correctness` | `Euclid/Euclid-TLAPS-Example/Euclid.tla` | ✅ PASS | 8 | 0.7s |  |
| `GCD1` | `Euclid/Euclid-Hyperbook/GCD.tla` | ✅ PASS | 9 | 0.5s |  |
| `GCD2` | `Euclid/Euclid-Hyperbook/GCD.tla` | ✅ PASS | 1 | 0.6s |  |
| `GCD3` | `Euclid/Euclid-Hyperbook/GCD.tla` | ❌ FAIL | 9 | 5.8s | 1/3 obligations failed |
| `InitProperty` | `Euclid/Euclid-TLAPS-Example/Euclid.tla` | ✅ PASS | 1 | 0.5s |  |
| `NextProperty` | `Euclid/Euclid-TLAPS-Example/Euclid.tla` | ✅ PASS | 20 | 0.8s |  |

### Paxos (9/13 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `Consistent` | `Paxos/PaxosHistVar.tla` | ✅ PASS | 25 | 1.4s |  |
| `Consistent` | `Paxos/Paxos.tla` | ✅ PASS | 25 | 1.2s |  |
| `Invariant` | `Paxos/PaxosHistVar.tla` | ❌ FAIL | 126 | 25.4s | 1/109 obligations failed |
| `Invariant` | `Paxos/Paxos.tla` | ❌ FAIL | 184 | 46.7s | 2/161 obligations failed |
| `NoneNotAValue` | `Paxos/Paxos.tla` | ✅ PASS | 1 | 0.5s |  |
| `QuorumNonEmpty` | `Paxos/Paxos.tla` | ✅ PASS | 1 | 0.5s |  |
| `Refinement` | `Paxos/Paxos.tla` | ❌ FAIL | 16 | 17.0s | 1/19 obligations failed |
| `SafeAtStable` | `Paxos/Paxos.tla` | ✅ PASS | 49 | 6.2s |  |
| `SafeAtStable` | `Paxos/PaxosHistVar.tla` | ❌ FAIL | 39 | 61.3s | 2/45 obligations failed |
| `VotedInv` | `Paxos/PaxosHistVar.tla` | ✅ PASS | 1 | 0.7s |  |
| `VotedInv` | `Paxos/Paxos.tla` | ✅ PASS | 1 | 0.6s |  |
| `VotedOnce` | `Paxos/PaxosHistVar.tla` | ✅ PASS | 1 | 0.8s |  |
| `VotedOnce` | `Paxos/Paxos.tla` | ✅ PASS | 1 | 0.5s |  |

### SimpleMutex (4/5 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `Initialization` | `SimpleMutex/SimpleMutex.tla` | ✅ PASS | 1 | 0.6s |  |
| `Invariance` | `SimpleMutex/SimpleMutex.tla` | ❌ FAIL | 38 | 6.2s | 1/39 obligations failed |
| `Mutex` | `SimpleMutex/SimpleMutex.tla` | ✅ PASS | 1 | 0.4s |  |
| `Safety` | `SimpleMutex/SimpleMutex.tla` | ✅ PASS | 1 | 0.4s |  |
| `TLAInvariance` | `SimpleMutex/SimpleMutex.tla` | ✅ PASS | 1 | 0.6s |  |

### Two-Phase (2/2 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `Implementation` | `Two-Phase/TwoPhase.tla` | ✅ PASS | 14 | 0.5s |  |
| `Mod2` | `Two-Phase/TwoPhase.tla` | ✅ PASS | 7 | 0.5s |  |

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
