# TLAPS Benchmark Validation Report

**Generated**: 2026-05-12 17:35:39

## Summary

| Metric | Count |
|--------|-------|
| Total benchmarks | 259 |
| ✅ Passed | 171 |
| ❌ Failed | 56 |
| ⚠️ Cheating detected | 32 |
| 🔍 No proof found | 0 |
| 💥 Error | 0 |
| ⏱️ Total verification time | 512.8s |
| 📝 Total baseline proof lines | 7473 |

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
| `AfterPrime` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ✅ PASS | 1 | 0.4s |  |
| `GGIrreflexive` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ✅ PASS | 15 | 0.4s |  |
| `InductiveInvariant` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ✅ PASS | 256 | 20.5s |  |
| `InitImpliesTypeOK` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ✅ PASS | 15 | 0.4s |  |
| `InitInv` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ✅ PASS | 1 | 0.4s |  |
| `InvExclusion` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ✅ PASS | 1 | 0.4s |  |
| `Safety` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ✅ PASS | 5 | 0.5s |  |
| `TypeOKInvariant` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ✅ PASS | 50 | 1.7s |  |

### BubbleSort (7/8 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `CompositionAssociative` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 1 | 0.2s |  |
| `CompositionOfPerms` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 1 | 5.3s |  |
| `ExchangeAPerm` | `BubbleSort/BubbleSort.tla` | ❌ FAIL | 1 | 5.2s | 1/2 obligations failed |
| `IdAPerm` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 1 | 0.2s |  |
| `IdIdentity` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 1 | 0.2s |  |
| `IsPermOfExchange` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 8 | 5.3s |  |
| `IsPermOfReflexive` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 1 | 0.2s |  |
| `IsPermOfTransitive` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 14 | 5.5s |  |

### ByzantinePaxos (28/84 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `BMessageLemma` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 8 | 0.1s |  |
| `EnabledDef` | `ByzantinePaxos/Consensus.tla` | ⚠️ CHEATING | 7 | 5.3s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `EnabledDef` | `ByzantinePaxos/Consensus.tla` | ⚠️ CHEATING | 7 | 5.3s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `EnabledDef` | `ByzantinePaxos/Consensus.tla` | ⚠️ CHEATING | 7 | 5.3s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `EnabledDef` | `ByzantinePaxos/Consensus.tla` | ⚠️ CHEATING | 7 | 5.3s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `EventuallyAlwaysForall` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 39 | 0.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `EventuallyAlwaysForall` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 39 | 0.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `EventuallyAlwaysForall` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 39 | 0.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `FiniteMsgsLemma` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 52 | 0.1s |  |
| `GeneralNatInduction` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 31 | 5.5s |  |
| `GeneralNatInduction` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 31 | 5.5s |  |
| `GeneralNatInduction` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 31 | 5.5s |  |
| `InductiveInvariance` | `ByzantinePaxos/Consensus.tla` | ❌ FAIL | 15 | 0.5s | 1/5 obligations failed |
| `InductiveInvariance` | `ByzantinePaxos/Consensus.tla` | ✅ PASS | 15 | 5.3s |  |
| `InductiveInvariance` | `ByzantinePaxos/Consensus.tla` | ✅ PASS | 15 | 5.3s |  |
| `InductiveInvariance` | `ByzantinePaxos/Consensus.tla` | ❌ FAIL | 15 | 0.5s | 1/5 obligations failed |
| `InductiveInvariance` | `ByzantinePaxos/Consensus.tla` | ✅ PASS | 15 | 5.3s |  |
| `InductiveInvariance` | `ByzantinePaxos/VoteProof.tla` | ❌ FAIL | 312 | 0.2s |  |
| `InductiveInvariance` | `ByzantinePaxos/VoteProof.tla` | ❌ FAIL | 312 | 0.5s | 1/5 obligations failed |
| `InitImpliesInv` | `ByzantinePaxos/VoteProof.tla` | ❌ FAIL | 13 | 0.6s | 1/15 obligations failed |
| `InitImpliesInv` | `ByzantinePaxos/VoteProof.tla` | ❌ FAIL | 13 | 0.6s | 1/15 obligations failed |
| `InitImpliesInv` | `ByzantinePaxos/VoteProof.tla` | ❌ FAIL | 13 | 0.6s | 1/15 obligations failed |
| `Invariance` | `ByzantinePaxos/Consensus.tla` | ⚠️ CHEATING | 11 | 0.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `Invariance` | `Consensus/Consensus.tla` | ❌ FAIL | 6 | 0.2s |  |
| `Invariance` | `ByzantinePaxos/Consensus.tla` | ⚠️ CHEATING | 11 | 0.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `Invariance` | `ByzantinePaxos/Consensus.tla` | ⚠️ CHEATING | 11 | 0.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `KnowsSafeAtDef` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 2 | 0.1s |  |
| `LiveSpecEquals` | `ByzantinePaxos/Consensus.tla` | ⚠️ CHEATING | 7 | 0.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `LiveSpecEquals` | `ByzantinePaxos/Consensus.tla` | ⚠️ CHEATING | 7 | 0.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `LiveSpecEquals` | `ByzantinePaxos/Consensus.tla` | ⚠️ CHEATING | 7 | 0.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `LiveSpecEquals` | `ByzantinePaxos/Consensus.tla` | ⚠️ CHEATING | 7 | 0.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `Liveness` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 364 | 0.1s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `Liveness` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 364 | 0.1s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `Liveness` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 364 | 0.1s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `MaxBallotLemma1` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 22 | 0.1s |  |
| `MaxBallotLemma2` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 97 | 0.1s |  |
| `MaxBallotProp` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 15 | 0.1s |  |
| `MsgsLemma` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 308 | 0.1s |  |
| `MsgsTypeLemma` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 19 | 0.1s |  |
| `MsgsTypeLemmaPrime` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 19 | 0.1s |  |
| `NextDef` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 9 | 0.2s |  |
| `NextDef` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 9 | 0.1s |  |
| `NextDef` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 9 | 0.1s |  |
| `NextDef` | `ByzantinePaxos/PConProof.tla` | ❌ FAIL | 8 | 0.2s |  |
| `NextDef` | `ByzantinePaxos/PConProof.tla` | ❌ FAIL | 8 | 0.1s |  |
| `NextDef` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 7 | 0.4s |  |
| `OnePlusFinite` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 13 | 0.1s |  |
| `PMaxBalLemma3` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 29 | 0.1s |  |
| `PNextDef` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 6 | 0.1s |  |
| `PmaxBalLemma1` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 10 | 0.1s |  |
| `PmaxBalLemma2` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 11 | 0.1s |  |
| `PmaxBalLemma4` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 32 | 0.1s |  |
| `PmaxBalLemma5` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 34 | 0.1s |  |
| `QuorumNonEmpty` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 1 | 0.2s |  |
| `QuorumNonEmpty` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 1 | 0.2s |  |
| `QuorumNonEmpty` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 1 | 0.2s |  |
| `QuorumTheorem` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 38 | 0.1s |  |
| `SafeAtProp` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 48 | 10.9s |  |
| `SafeAtProp` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 48 | 10.9s |  |
| `SafeAtProp` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 48 | 10.9s |  |
| `SafeLemma` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 142 | 7.5s |  |
| `SafeLemma` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 142 | 7.3s |  |
| `SafeLemma` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 142 | 7.4s |  |
| `VT0` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 71 | 6.3s |  |
| `VT0` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 71 | 6.3s |  |
| `VT0` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 71 | 6.3s |  |
| `VT0Prime` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 71 | 6.5s |  |
| `VT0Prime` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 71 | 6.4s |  |
| `VT0Prime` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 71 | 6.5s |  |
| `VT1` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 35 | 0.8s |  |
| `VT1` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 35 | 0.8s |  |
| `VT1` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 35 | 0.8s |  |
| `VT1Prime` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 35 | 0.9s |  |
| `VT1Prime` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 35 | 1.0s |  |
| `VT1Prime` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 35 | 0.9s |  |
| `VT2` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 6 | 0.5s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `VT2` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 6 | 0.5s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `VT2` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 6 | 0.5s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `VT3` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 103 | 0.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `VT3` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 103 | 0.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `VT3` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 103 | 0.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `VT4` | `ByzantinePaxos/VoteProof.tla` | ❌ FAIL | 75 | 0.2s |  |
| `VT4` | `ByzantinePaxos/VoteProof.tla` | ❌ FAIL | 75 | 0.2s |  |
| `VT4` | `ByzantinePaxos/VoteProof.tla` | ❌ FAIL | 75 | 0.2s |  |

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
| `cantor` | `Cantor/Cantor1.tla` | ✅ PASS | 7 | 5.2s |  |
| `cantor` | `Cantor/Cantor2.tla` | ✅ PASS | 19 | 5.2s |  |
| `cantor` | `Cantor/Cantor3.tla` | ✅ PASS | 20 | 5.2s |  |
| `cantor` | `Cantor/Cantor4.tla` | ✅ PASS | 14 | 5.2s |  |

### Consensus (63/73 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `AllSafeAtZero` | `Consensus/Voting.tla` | ✅ PASS | 1 | 0.3s |  |
| `AllSafeAtZero` | `Consensus/Voting.tla` | ✅ PASS | 1 | 0.2s |  |
| `CardinalityInNat` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.2s |  |
| `CardinalityInNat` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.2s |  |
| `CardinalityInNat` | `Data/Sets.tla` | ✅ PASS | 1 | 0.2s |  |
| `CardinalityInNat` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.2s |  |
| `CardinalityOne` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.3s |  |
| `CardinalityOne` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.4s |  |
| `CardinalityOne` | `Data/Sets.tla` | ✅ PASS | 1 | 0.3s |  |
| `CardinalityOne` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.4s |  |
| `CardinalityOneConverse` | `Consensus/Sets.tla` | ✅ PASS | 6 | 5.3s |  |
| `CardinalityOneConverse` | `Consensus/Sets.tla` | ✅ PASS | 6 | 5.3s |  |
| `CardinalityOneConverse` | `Data/Sets.tla` | ✅ PASS | 6 | 5.3s |  |
| `CardinalityOneConverse` | `Consensus/Sets.tla` | ✅ PASS | 6 | 5.3s |  |
| `CardinalityPlusOne` | `Consensus/Sets.tla` | ✅ PASS | 8 | 0.4s |  |
| `CardinalityPlusOne` | `Consensus/Sets.tla` | ✅ PASS | 8 | 1.7s |  |
| `CardinalityPlusOne` | `Data/Sets.tla` | ✅ PASS | 8 | 0.4s |  |
| `CardinalityPlusOne` | `Consensus/Sets.tla` | ✅ PASS | 8 | 1.8s |  |
| `CardinalitySetMinus` | `Consensus/Sets.tla` | ⚠️ CHEATING | 41 | 0.6s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `CardinalitySetMinus` | `Consensus/Sets.tla` | ⚠️ CHEATING | 41 | 1.0s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `CardinalitySetMinus` | `Data/Sets.tla` | ⚠️ CHEATING | 41 | 0.6s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `CardinalitySetMinus` | `Consensus/Sets.tla` | ⚠️ CHEATING | 41 | 1.0s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `CardinalityTwo` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.4s |  |
| `CardinalityTwo` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.4s |  |
| `CardinalityTwo` | `Data/Sets.tla` | ✅ PASS | 1 | 0.3s |  |
| `CardinalityTwo` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.4s |  |
| `CardinalityZero` | `Consensus/Sets.tla` | ✅ PASS | 13 | 0.3s |  |
| `CardinalityZero` | `Consensus/Sets.tla` | ✅ PASS | 13 | 0.3s |  |
| `CardinalityZero` | `Data/Sets.tla` | ✅ PASS | 13 | 0.3s |  |
| `CardinalityZero` | `Consensus/Sets.tla` | ✅ PASS | 13 | 0.3s |  |
| `ChoosableThm` | `Consensus/Voting.tla` | ✅ PASS | 1 | 0.2s |  |
| `ChoosableThm` | `Consensus/Voting.tla` | ✅ PASS | 1 | 0.3s |  |
| `Consistent` | `Consensus/Voting.tla` | ✅ PASS | 9 | 0.4s |  |
| `Consistent` | `Consensus/Voting.tla` | ✅ PASS | 9 | 0.4s |  |
| `FiniteSubset` | `Consensus/Sets.tla` | ✅ PASS | 65 | 0.8s |  |
| `FiniteSubset` | `Consensus/Sets.tla` | ✅ PASS | 65 | 0.8s |  |
| `FiniteSubset` | `Data/Sets.tla` | ✅ PASS | 65 | 0.8s |  |
| `FiniteSubset` | `Consensus/Sets.tla` | ✅ PASS | 65 | 0.8s |  |
| `IntervalCardinality` | `Consensus/Sets.tla` | ✅ PASS | 14 | 0.6s |  |
| `IntervalCardinality` | `Consensus/Sets.tla` | ✅ PASS | 14 | 0.4s |  |
| `IntervalCardinality` | `Data/Sets.tla` | ✅ PASS | 13 | 0.5s |  |
| `IntervalCardinality` | `Consensus/Sets.tla` | ✅ PASS | 14 | 0.4s |  |
| `Invariance` | `Consensus/Consensus.tla` | ✅ PASS | 6 | 0.3s |  |
| `Invariance` | `Consensus/Consensus.tla` | ✅ PASS | 6 | 0.3s |  |
| `Invariance` | `Consensus/Consensus.tla` | ✅ PASS | 6 | 0.3s |  |
| `Invariant` | `Consensus/Voting.tla` | ✅ PASS | 82 | 2.5s |  |
| `Invariant` | `Consensus/Voting.tla` | ✅ PASS | 82 | 2.5s |  |
| `IsBijectionInverse` | `Consensus/Sets.tla` | ✅ PASS | 3 | 0.2s |  |
| `IsBijectionInverse` | `Consensus/Sets.tla` | ✅ PASS | 3 | 0.2s |  |
| `IsBijectionInverse` | `Data/Sets.tla` | ✅ PASS | 3 | 0.2s |  |
| `IsBijectionInverse` | `Consensus/Sets.tla` | ✅ PASS | 3 | 0.2s |  |
| `IsBijectionTransitive` | `Consensus/Sets.tla` | ✅ PASS | 7 | 0.2s |  |
| `IsBijectionTransitive` | `Consensus/Sets.tla` | ✅ PASS | 7 | 0.2s |  |
| `IsBijectionTransitive` | `Data/Sets.tla` | ✅ PASS | 7 | 0.2s |  |
| `IsBijectionTransitive` | `Consensus/Sets.tla` | ✅ PASS | 7 | 0.3s |  |
| `OneVoteThm` | `Consensus/Voting.tla` | ✅ PASS | 1 | 0.2s |  |
| `OneVoteThm` | `Consensus/Voting.tla` | ✅ PASS | 1 | 0.3s |  |
| `OtherMessage` | `Consensus/PaxosProof.tla` | ❌ FAIL | 1 | 0.2s |  |
| `PigeonHole` | `Consensus/Sets.tla` | ✅ PASS | 47 | 0.7s |  |
| `PigeonHole` | `Data/Sets.tla` | ✅ PASS | 47 | 0.7s |  |
| `PigeonHole` | `Consensus/Sets.tla` | ✅ PASS | 47 | 5.5s |  |
| `PigeonHole` | `Consensus/Sets.tla` | ✅ PASS | 47 | 5.5s |  |
| `QuorumNonEmpty` | `Consensus/Voting.tla` | ✅ PASS | 1 | 0.2s |  |
| `QuorumNonEmpty` | `Consensus/Voting.tla` | ✅ PASS | 1 | 0.2s |  |
| `Refinement` | `Consensus/Voting.tla` | ❌ FAIL | 21 | 0.2s |  |
| `Refinement` | `Consensus/Voting.tla` | ❌ FAIL | 21 | 0.2s |  |
| `ShowsSafety` | `Consensus/Voting.tla` | ✅ PASS | 3 | 2.1s |  |
| `ShowsSafety` | `Consensus/Voting.tla` | ✅ PASS | 3 | 2.1s |  |
| `VotesSafeImpliesConsistency` | `Consensus/Voting.tla` | ✅ PASS | 18 | 0.5s |  |
| `VotesSafeImpliesConsistency` | `Consensus/Voting.tla` | ✅ PASS | 18 | 0.6s |  |
| `WFmsgs` | `Consensus/PaxosProof.tla` | ❌ FAIL | 1 | 0.2s |  |
| `struct_lemma` | `Consensus/PaxosProof.tla` | ⚠️ CHEATING | 7 | 0.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `typing` | `Consensus/PaxosProof.tla` | ⚠️ CHEATING | 8 | 0.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |

### Data (30/37 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `AppendDef` | `Data/SequencesTheorems.tla` | ❌ FAIL | 1 | 5.2s | 1/2 obligations failed |
| `AppendProperties` | `Data/SequencesTheorems.tla` | ✅ PASS | 1 | 0.2s |  |
| `AtLeastTwo` | `Data/GraphTheorem.tla` | ✅ PASS | 1 | 0.2s |  |
| `CardinalityInNat` | `Data/Sets.tla` | ✅ PASS | 1 | 0.2s |  |
| `CardinalityInNat` | `Data/Sets.tla` | ✅ PASS | 1 | 0.2s |  |
| `CardinalityOne` | `Data/Sets.tla` | ✅ PASS | 1 | 0.3s |  |
| `CardinalityOne` | `Data/Sets.tla` | ✅ PASS | 1 | 0.3s |  |
| `CardinalityOneConverse` | `Data/Sets.tla` | ✅ PASS | 6 | 5.3s |  |
| `CardinalityOneConverse` | `Data/Sets.tla` | ✅ PASS | 6 | 5.3s |  |
| `CardinalityPlusOne` | `Data/Sets.tla` | ✅ PASS | 8 | 0.4s |  |
| `CardinalityPlusOne` | `Data/Sets.tla` | ✅ PASS | 8 | 0.4s |  |
| `CardinalitySetMinus` | `Data/Sets.tla` | ⚠️ CHEATING | 41 | 0.6s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `CardinalitySetMinus` | `Data/Sets.tla` | ⚠️ CHEATING | 41 | 0.6s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `CardinalityTwo` | `Data/Sets.tla` | ✅ PASS | 1 | 0.3s |  |
| `CardinalityTwo` | `Data/Sets.tla` | ✅ PASS | 1 | 0.3s |  |
| `CardinalityZero` | `Data/Sets.tla` | ✅ PASS | 13 | 0.3s |  |
| `CardinalityZero` | `Data/Sets.tla` | ✅ PASS | 13 | 0.3s |  |
| `ConcatDef` | `Data/SequencesTheorems.tla` | ❌ FAIL | 1 | 5.2s | 1/2 obligations failed |
| `ConcatProperties` | `Data/SequencesTheorems.tla` | ✅ PASS | 1 | 0.2s |  |
| `EdgesAxiom` | `Data/GraphTheorem.tla` | ✅ PASS | 1 | 0.4s |  |
| `ElementOfSeq` | `Data/SequencesTheorems.tla` | ✅ PASS | 1 | 0.2s |  |
| `EmptySeq` | `Data/SequencesTheorems.tla` | ✅ PASS | 1 | 0.2s |  |
| `FiniteSubset` | `Data/Sets.tla` | ✅ PASS | 65 | 0.8s |  |
| `FiniteSubset` | `Data/Sets.tla` | ✅ PASS | 65 | 0.8s |  |
| `HeadAndTailOfSeq` | `Data/SequencesTheorems.tla` | ❌ FAIL | 9 | 0.1s |  |
| `InitialSubSeq` | `Data/SequencesTheorems.tla` | ❌ FAIL | 16 | 0.1s |  |
| `IntervalCardinality` | `Data/Sets.tla` | ✅ PASS | 13 | 0.5s |  |
| `IntervalCardinality` | `Data/Sets.tla` | ✅ PASS | 13 | 0.6s |  |
| `IsBijectionInverse` | `Data/Sets.tla` | ✅ PASS | 3 | 0.2s |  |
| `IsBijectionInverse` | `Data/Sets.tla` | ✅ PASS | 3 | 0.2s |  |
| `IsBijectionTransitive` | `Data/Sets.tla` | ✅ PASS | 7 | 0.2s |  |
| `IsBijectionTransitive` | `Data/Sets.tla` | ✅ PASS | 7 | 0.2s |  |
| `LenAxiom` | `Data/SequencesTheorems.tla` | ✅ PASS | 1 | 0.2s |  |
| `LenDomain` | `Data/SequencesTheorems.tla` | ⚠️ CHEATING | 5 | 0.2s | EXTRA_AXIOM: New AXIOM 'TailDef' added — bypasses proof obligation; EXTRA_AXIOM: New AXIOM 'SubSeqDef' added — bypasses proof obligation; EXTRA_AXIOM: New AXIOM 'HeadDef' added — bypasses proof obligation |
| `PigeonHole` | `Data/Sets.tla` | ✅ PASS | 47 | 0.7s |  |
| `PigeonHole` | `Data/Sets.tla` | ✅ PASS | 47 | 0.7s |  |
| `RemoveSeq` | `Data/SequencesTheorems.tla` | ✅ PASS | 17 | 0.3s |  |

### EWD840 (1/2 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `Inv_implies_Termination` | `EWD840/EWD840.tla` | ✅ PASS | 9 | 1.6s |  |
| `TypeOK_inv` | `EWD840/EWD840.tla` | ❌ FAIL | 7 | 45.4s | 1/8 obligations failed |

### Euclid (5/6 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `Correctness` | `Euclid/Euclid-TLAPS-Example/Euclid.tla` | ✅ PASS | 8 | 0.2s |  |
| `GCD1` | `Euclid/Euclid-Hyperbook/GCD.tla` | ✅ PASS | 9 | 0.2s |  |
| `GCD2` | `Euclid/Euclid-Hyperbook/GCD.tla` | ✅ PASS | 1 | 0.2s |  |
| `GCD3` | `Euclid/Euclid-Hyperbook/GCD.tla` | ❌ FAIL | 9 | 5.4s | 1/3 obligations failed |
| `InitProperty` | `Euclid/Euclid-TLAPS-Example/Euclid.tla` | ✅ PASS | 1 | 0.2s |  |
| `NextProperty` | `Euclid/Euclid-TLAPS-Example/Euclid.tla` | ✅ PASS | 20 | 0.3s |  |

### Paxos (3/13 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `Consistent` | `Paxos/PaxosHistVar.tla` | ✅ PASS | 25 | 0.5s |  |
| `Consistent` | `Paxos/Paxos.tla` | ❌ FAIL | 25 | 0.2s |  |
| `Invariant` | `Paxos/Paxos.tla` | ❌ FAIL | 184 | 0.2s |  |
| `Invariant` | `Paxos/PaxosHistVar.tla` | ❌ FAIL | 126 | 22.8s | 1/109 obligations failed |
| `NoneNotAValue` | `Paxos/Paxos.tla` | ❌ FAIL | 1 | 5.4s | 2/15 obligations failed |
| `QuorumNonEmpty` | `Paxos/Paxos.tla` | ❌ FAIL | 1 | 5.4s | 2/15 obligations failed |
| `Refinement` | `Paxos/Paxos.tla` | ❌ FAIL | 16 | 0.2s |  |
| `SafeAtStable` | `Paxos/Paxos.tla` | ❌ FAIL | 49 | 0.2s |  |
| `SafeAtStable` | `Paxos/PaxosHistVar.tla` | ❌ FAIL | 39 | 60.5s | 2/45 obligations failed |
| `VotedInv` | `Paxos/PaxosHistVar.tla` | ✅ PASS | 1 | 0.2s |  |
| `VotedInv` | `Paxos/Paxos.tla` | ❌ FAIL | 1 | 5.4s | 2/14 obligations failed |
| `VotedOnce` | `Paxos/PaxosHistVar.tla` | ✅ PASS | 1 | 0.2s |  |
| `VotedOnce` | `Paxos/Paxos.tla` | ❌ FAIL | 9 | 5.4s | 2/14 obligations failed |

### SimpleMutex (4/5 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `Initialization` | `SimpleMutex/SimpleMutex.tla` | ✅ PASS | 1 | 0.2s |  |
| `Invariance` | `SimpleMutex/SimpleMutex.tla` | ❌ FAIL | 38 | 5.5s | 1/39 obligations failed |
| `Mutex` | `SimpleMutex/SimpleMutex.tla` | ✅ PASS | 1 | 0.2s |  |
| `Safety` | `SimpleMutex/SimpleMutex.tla` | ✅ PASS | 1 | 0.2s |  |
| `TLAInvariance` | `SimpleMutex/SimpleMutex.tla` | ✅ PASS | 1 | 0.2s |  |

### Two-Phase (1/2 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `Implementation` | `Two-Phase/TwoPhase.tla` | ❌ FAIL | 14 | 0.1s |  |
| `Mod2` | `Two-Phase/TwoPhase.tla` | ✅ PASS | 7 | 0.2s |  |

## Cheating Detection Details

### `benchmark/ByzantinePaxos/BPConProof_EnabledDef.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/ByzantinePaxos/Consensus_EnabledDef.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/ByzantinePaxos/PConProof_EnabledDef.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/ByzantinePaxos/VoteProof_EnabledDef.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/ByzantinePaxos/BPConProof_EventuallyAlwaysForall.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/ByzantinePaxos/PConProof_EventuallyAlwaysForall.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/ByzantinePaxos/VoteProof_EventuallyAlwaysForall.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/ByzantinePaxos/BPConProof_Invariance.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/ByzantinePaxos/PConProof_Invariance.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/ByzantinePaxos/VoteProof_Invariance.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/ByzantinePaxos/BPConProof_LiveSpecEquals.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/ByzantinePaxos/Consensus_LiveSpecEquals.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/ByzantinePaxos/PConProof_LiveSpecEquals.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/ByzantinePaxos/VoteProof_LiveSpecEquals.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/ByzantinePaxos/BPConProof_Liveness.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/ByzantinePaxos/PConProof_Liveness.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/ByzantinePaxos/VoteProof_Liveness.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/ByzantinePaxos/BPConProof_VT2.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/ByzantinePaxos/PConProof_VT2.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/ByzantinePaxos/VoteProof_VT2.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/ByzantinePaxos/BPConProof_VT3.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/ByzantinePaxos/PConProof_VT3.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/ByzantinePaxos/VoteProof_VT3.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/Consensus/Consensus_CardinalitySetMinus.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/Consensus/PaxosProof_CardinalitySetMinus.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/Consensus/Sets_CardinalitySetMinus.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/Consensus/Voting_CardinalitySetMinus.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/Consensus/PaxosProof_struct_lemma.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/Consensus/PaxosProof_typing.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/Data/GraphTheorem_CardinalitySetMinus.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/Data/Sets_CardinalitySetMinus.tla`

- **PROOF_OMITTED**: Proof uses PROOF OMITTED to skip obligations

### `benchmark/Data/SequencesTheorems_LenDomain.tla`

- **EXTRA_AXIOM**: New AXIOM 'TailDef' added — bypasses proof obligation
- **EXTRA_AXIOM**: New AXIOM 'SubSeqDef' added — bypasses proof obligation
- **EXTRA_AXIOM**: New AXIOM 'HeadDef' added — bypasses proof obligation

## Failed Verification Details

### `benchmark/BubbleSort/BubbleSort_ExchangeAPerm.tla`

```
[INFO]: All 0 obligation proved.
[ERROR]: Could not prove or check:
[ERROR]: 1/2 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/ByzantinePaxos/BPConProof_BMessageLemma.tla`


### `benchmark/ByzantinePaxos/BPConProof_FiniteMsgsLemma.tla`


### `benchmark/ByzantinePaxos/BPConProof_InductiveInvariance_1.tla`

```
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
[ERROR]: Could not prove or check:
[ERROR]: 1/5 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/ByzantinePaxos/PConProof_InductiveInvariance_1.tla`

```
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
[ERROR]: Could not prove or check:
[ERROR]: 1/5 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/ByzantinePaxos/VoteProof_InductiveInvariance.tla`

```
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
```

### `benchmark/ByzantinePaxos/VoteProof_InductiveInvariance_1.tla`

```
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
[ERROR]: Could not prove or check:
[ERROR]: 1/5 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/ByzantinePaxos/BPConProof_InitImpliesInv.tla`

```
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
[ERROR]: Could not prove or check:
[ERROR]: 1/15 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/ByzantinePaxos/PConProof_InitImpliesInv.tla`

```
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
[ERROR]: Could not prove or check:
[ERROR]: 1/15 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/ByzantinePaxos/VoteProof_InitImpliesInv.tla`

```
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
[ERROR]: Could not prove or check:
[ERROR]: 1/15 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/ByzantinePaxos/Consensus_Invariance.tla`

```
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
```

### `benchmark/ByzantinePaxos/BPConProof_KnowsSafeAtDef.tla`


### `benchmark/ByzantinePaxos/BPConProof_MaxBallotLemma1.tla`


### `benchmark/ByzantinePaxos/BPConProof_MaxBallotLemma2.tla`


### `benchmark/ByzantinePaxos/BPConProof_MaxBallotProp.tla`


### `benchmark/ByzantinePaxos/BPConProof_MsgsLemma.tla`


### `benchmark/ByzantinePaxos/BPConProof_MsgsTypeLemma.tla`


### `benchmark/ByzantinePaxos/BPConProof_MsgsTypeLemmaPrime.tla`


### `benchmark/ByzantinePaxos/BPConProof_NextDef.tla`

```
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
```

### `benchmark/ByzantinePaxos/BPConProof_NextDef_1.tla`


### `benchmark/ByzantinePaxos/BPConProof_NextDef_2.tla`


### `benchmark/ByzantinePaxos/PConProof_NextDef.tla`

```
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
```

### `benchmark/ByzantinePaxos/PConProof_NextDef_1.tla`


### `benchmark/ByzantinePaxos/BPConProof_OnePlusFinite.tla`


### `benchmark/ByzantinePaxos/BPConProof_PMaxBalLemma3.tla`


### `benchmark/ByzantinePaxos/BPConProof_PNextDef.tla`


### `benchmark/ByzantinePaxos/BPConProof_PmaxBalLemma1.tla`


### `benchmark/ByzantinePaxos/BPConProof_PmaxBalLemma2.tla`


### `benchmark/ByzantinePaxos/BPConProof_PmaxBalLemma4.tla`


### `benchmark/ByzantinePaxos/BPConProof_PmaxBalLemma5.tla`


### `benchmark/ByzantinePaxos/BPConProof_QuorumTheorem.tla`


### `benchmark/ByzantinePaxos/BPConProof_VT4.tla`

```
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
```

### `benchmark/ByzantinePaxos/PConProof_VT4.tla`

```
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
```

### `benchmark/ByzantinePaxos/VoteProof_VT4.tla`

```
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
```

### `benchmark/Consensus/PaxosProof_OtherMessage.tla`

```
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
```

### `benchmark/Consensus/PaxosProof_Refinement.tla`

```
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
```

### `benchmark/Consensus/Voting_Refinement.tla`

```
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
```

### `benchmark/Consensus/PaxosProof_WFmsgs.tla`

```
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
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

### `benchmark/Data/SequencesTheorems_HeadAndTailOfSeq.tla`

```
[INFO]: All 0 obligation proved.
```

### `benchmark/Data/SequencesTheorems_InitialSubSeq.tla`

```
[INFO]: All 0 obligation proved.
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

### `benchmark/Paxos/Paxos_Consistent.tla`

```
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
```

### `benchmark/Paxos/Paxos_Invariant.tla`

```
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
```

### `benchmark/Paxos/PaxosHistVar_Invariant.tla`

```
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
[ERROR]: Could not prove or check:
[ERROR]: 1/109 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Paxos/Paxos_NoneNotAValue.tla`

```
[INFO]: All 0 obligation proved.
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: 2/15 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Paxos/Paxos_QuorumNonEmpty.tla`

```
[INFO]: All 0 obligation proved.
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: 2/15 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Paxos/Paxos_Refinement.tla`

```
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
```

### `benchmark/Paxos/Paxos_SafeAtStable.tla`

```
[INFO]: All 0 obligation proved.
[INFO]: All 0 obligation proved.
```

### `benchmark/Paxos/PaxosHistVar_SafeAtStable.tla`

```
[INFO]: All 0 obligation proved.
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: 2/45 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Paxos/Paxos_VotedInv.tla`

```
[INFO]: All 0 obligation proved.
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: 2/14 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Paxos/Paxos_VotedOnce.tla`

```
[INFO]: All 0 obligation proved.
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: 2/14 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/SimpleMutex/SimpleMutex_Invariance.tla`

```
[INFO]: All 0 obligation proved.
[ERROR]: Could not prove or check:
[ERROR]: 1/39 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Two-Phase/TwoPhase_Implementation.tla`

```
[INFO]: All 0 obligation proved.
```
