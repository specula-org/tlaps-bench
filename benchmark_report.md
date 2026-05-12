# TLAPS Benchmark Validation Report

**Generated**: 2026-05-12 17:15:48

## Summary

| Metric | Count |
|--------|-------|
| Total benchmarks | 259 |
| ✅ Passed | 146 |
| ❌ Failed | 81 |
| ⚠️ Cheating detected | 32 |
| 🔍 No proof found | 0 |
| 💥 Error | 0 |
| ⏱️ Total verification time | 889.9s |
| 📝 Total baseline proof lines | 7473 |

## Results by Module

### Allocator (9/10 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `AllocateMutex` | `Allocator/Allocator.tla` | ✅ PASS | 70 | 5.8s |  |
| `AllocateTypeInvariant` | `Allocator/Allocator.tla` | ✅ PASS | 1 | 0.3s |  |
| `InitMutex` | `Allocator/Allocator.tla` | ✅ PASS | 1 | 0.3s |  |
| `InitTypeInvariant` | `Allocator/Allocator.tla` | ✅ PASS | 1 | 0.3s |  |
| `NextMutex` | `Allocator/Allocator.tla` | ❌ FAIL | 1 | 0.2s |  |
| `NextTypeInvariant` | `Allocator/Allocator.tla` | ✅ PASS | 15 | 0.3s |  |
| `RequestMutexBis` | `Allocator/Allocator.tla` | ✅ PASS | 1 | 0.3s |  |
| `RequestTypeInvariant` | `Allocator/Allocator.tla` | ✅ PASS | 1 | 0.3s |  |
| `ReturnMutex` | `Allocator/Allocator.tla` | ✅ PASS | 19 | 0.4s |  |
| `ReturnTypeInvariant` | `Allocator/Allocator.tla` | ✅ PASS | 1 | 0.3s |  |

### AtomicBakery (0/8 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `AfterPrime` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ❌ FAIL | 1 | 30.4s | 6/8 obligations failed |
| `GGIrreflexive` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ❌ FAIL | 15 | 30.4s | 6/30 obligations failed |
| `InductiveInvariant` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ❌ FAIL | 256 | 34.4s | 9/253 obligations failed |
| `InitImpliesTypeOK` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ❌ FAIL | 15 | 30.4s | 6/16 obligations failed |
| `InitInv` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ❌ FAIL | 1 | 30.4s | 6/9 obligations failed |
| `InvExclusion` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ❌ FAIL | 1 | 30.5s | 6/8 obligations failed |
| `Safety` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ❌ FAIL | 5 | 30.6s | 6/14 obligations failed |
| `TypeOKInvariant` | `AtomicBakery/AtomicBakeryWithoutSMT.tla` | ❌ FAIL | 50 | 31.2s | 6/54 obligations failed |

### BubbleSort (8/8 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `CompositionAssociative` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 1 | 0.4s |  |
| `CompositionOfPerms` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 1 | 0.4s |  |
| `ExchangeAPerm` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 1 | 0.3s |  |
| `IdAPerm` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 1 | 0.3s |  |
| `IdIdentity` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 1 | 0.3s |  |
| `IsPermOfExchange` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 8 | 0.4s |  |
| `IsPermOfReflexive` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 1 | 0.3s |  |
| `IsPermOfTransitive` | `BubbleSort/BubbleSort.tla` | ✅ PASS | 14 | 0.4s |  |

### ByzantinePaxos (28/84 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `BMessageLemma` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 8 | 0.2s |  |
| `EnabledDef` | `ByzantinePaxos/Consensus.tla` | ⚠️ CHEATING | 7 | 0.4s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `EnabledDef` | `ByzantinePaxos/Consensus.tla` | ⚠️ CHEATING | 7 | 0.4s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `EnabledDef` | `ByzantinePaxos/Consensus.tla` | ⚠️ CHEATING | 7 | 0.4s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `EnabledDef` | `ByzantinePaxos/Consensus.tla` | ⚠️ CHEATING | 7 | 0.4s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `EventuallyAlwaysForall` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 39 | 0.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `EventuallyAlwaysForall` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 39 | 0.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `EventuallyAlwaysForall` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 39 | 0.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `FiniteMsgsLemma` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 52 | 0.2s |  |
| `GeneralNatInduction` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 31 | 0.6s |  |
| `GeneralNatInduction` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 31 | 0.5s |  |
| `GeneralNatInduction` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 31 | 0.5s |  |
| `InductiveInvariance` | `ByzantinePaxos/Consensus.tla` | ✅ PASS | 15 | 0.4s |  |
| `InductiveInvariance` | `ByzantinePaxos/Consensus.tla` | ❌ FAIL | 15 | 2.3s | 1/5 obligations failed |
| `InductiveInvariance` | `ByzantinePaxos/Consensus.tla` | ✅ PASS | 15 | 0.4s |  |
| `InductiveInvariance` | `ByzantinePaxos/Consensus.tla` | ✅ PASS | 15 | 0.4s |  |
| `InductiveInvariance` | `ByzantinePaxos/Consensus.tla` | ❌ FAIL | 15 | 2.3s | 1/5 obligations failed |
| `InductiveInvariance` | `ByzantinePaxos/VoteProof.tla` | ❌ FAIL | 312 | 0.2s |  |
| `InductiveInvariance` | `ByzantinePaxos/VoteProof.tla` | ❌ FAIL | 312 | 2.3s | 1/5 obligations failed |
| `InitImpliesInv` | `ByzantinePaxos/VoteProof.tla` | ❌ FAIL | 13 | 2.4s | 1/15 obligations failed |
| `InitImpliesInv` | `ByzantinePaxos/VoteProof.tla` | ❌ FAIL | 13 | 2.5s | 1/15 obligations failed |
| `InitImpliesInv` | `ByzantinePaxos/VoteProof.tla` | ❌ FAIL | 13 | 2.5s | 1/15 obligations failed |
| `Invariance` | `ByzantinePaxos/Consensus.tla` | ⚠️ CHEATING | 11 | 0.3s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `Invariance` | `Consensus/Consensus.tla` | ❌ FAIL | 6 | 0.2s |  |
| `Invariance` | `ByzantinePaxos/Consensus.tla` | ⚠️ CHEATING | 11 | 0.3s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `Invariance` | `ByzantinePaxos/Consensus.tla` | ⚠️ CHEATING | 11 | 0.3s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `KnowsSafeAtDef` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 2 | 0.2s |  |
| `LiveSpecEquals` | `ByzantinePaxos/Consensus.tla` | ⚠️ CHEATING | 7 | 0.4s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `LiveSpecEquals` | `ByzantinePaxos/Consensus.tla` | ⚠️ CHEATING | 7 | 0.3s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `LiveSpecEquals` | `ByzantinePaxos/Consensus.tla` | ⚠️ CHEATING | 7 | 0.4s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `LiveSpecEquals` | `ByzantinePaxos/Consensus.tla` | ⚠️ CHEATING | 7 | 0.3s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `Liveness` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 364 | 0.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `Liveness` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 364 | 0.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `Liveness` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 364 | 0.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `MaxBallotLemma1` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 22 | 0.2s |  |
| `MaxBallotLemma2` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 97 | 0.2s |  |
| `MaxBallotProp` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 15 | 0.2s |  |
| `MsgsLemma` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 308 | 0.2s |  |
| `MsgsTypeLemma` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 19 | 0.2s |  |
| `MsgsTypeLemmaPrime` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 19 | 0.2s |  |
| `NextDef` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 9 | 0.2s |  |
| `NextDef` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 9 | 0.2s |  |
| `NextDef` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 9 | 0.2s |  |
| `NextDef` | `ByzantinePaxos/PConProof.tla` | ❌ FAIL | 8 | 0.2s |  |
| `NextDef` | `ByzantinePaxos/PConProof.tla` | ❌ FAIL | 8 | 0.2s |  |
| `NextDef` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 7 | 0.5s |  |
| `OnePlusFinite` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 13 | 0.2s |  |
| `PMaxBalLemma3` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 29 | 0.2s |  |
| `PNextDef` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 6 | 0.2s |  |
| `PmaxBalLemma1` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 10 | 0.2s |  |
| `PmaxBalLemma2` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 11 | 0.2s |  |
| `PmaxBalLemma4` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 32 | 0.2s |  |
| `PmaxBalLemma5` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 34 | 0.2s |  |
| `QuorumNonEmpty` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 1 | 0.4s |  |
| `QuorumNonEmpty` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 1 | 0.4s |  |
| `QuorumNonEmpty` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 1 | 0.3s |  |
| `QuorumTheorem` | `ByzantinePaxos/BPConProof.tla` | ❌ FAIL | 38 | 0.2s |  |
| `SafeAtProp` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 48 | 17.6s |  |
| `SafeAtProp` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 48 | 17.6s |  |
| `SafeAtProp` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 48 | 17.5s |  |
| `SafeLemma` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 142 | 1.8s |  |
| `SafeLemma` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 142 | 1.8s |  |
| `SafeLemma` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 142 | 1.8s |  |
| `VT0` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 71 | 1.1s |  |
| `VT0` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 71 | 1.1s |  |
| `VT0` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 71 | 1.1s |  |
| `VT0Prime` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 71 | 1.2s |  |
| `VT0Prime` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 71 | 1.2s |  |
| `VT0Prime` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 71 | 1.2s |  |
| `VT1` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 35 | 0.7s |  |
| `VT1` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 35 | 0.7s |  |
| `VT1` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 35 | 0.7s |  |
| `VT1Prime` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 35 | 0.8s |  |
| `VT1Prime` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 35 | 0.8s |  |
| `VT1Prime` | `ByzantinePaxos/VoteProof.tla` | ✅ PASS | 35 | 0.8s |  |
| `VT2` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 6 | 2.3s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `VT2` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 6 | 2.3s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `VT2` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 6 | 2.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `VT3` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 103 | 0.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `VT3` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 103 | 0.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `VT3` | `ByzantinePaxos/VoteProof.tla` | ⚠️ CHEATING | 103 | 0.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `VT4` | `ByzantinePaxos/VoteProof.tla` | ❌ FAIL | 75 | 0.2s |  |
| `VT4` | `ByzantinePaxos/VoteProof.tla` | ❌ FAIL | 75 | 0.2s |  |
| `VT4` | `ByzantinePaxos/VoteProof.tla` | ❌ FAIL | 75 | 0.2s |  |

### Cantor (11/11 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `Cantor` | `Cantor/Cantor10.tla` | ✅ PASS | 6 | 0.3s |  |
| `Cantor` | `Cantor/Cantor9.tla` | ✅ PASS | 11 | 0.3s |  |
| `Cantor` | `Cantor/Cantor8.tla` | ✅ PASS | 15 | 0.3s |  |
| `NoSetContainsAllValues` | `Cantor/Cantor10.tla` | ✅ PASS | 13 | 0.3s |  |
| `cantor` | `Cantor/Cantor1.tla` | ✅ PASS | 7 | 0.3s |  |
| `cantor` | `Cantor/Cantor3.tla` | ✅ PASS | 20 | 0.3s |  |
| `cantor` | `Cantor/Cantor2.tla` | ✅ PASS | 19 | 0.3s |  |
| `cantor` | `Cantor/Cantor5.tla` | ✅ PASS | 5 | 0.3s |  |
| `cantor` | `Cantor/Cantor4.tla` | ✅ PASS | 14 | 0.4s |  |
| `cantor` | `Cantor/Cantor7.tla` | ✅ PASS | 6 | 0.3s |  |
| `cantor` | `Cantor/Cantor6.tla` | ✅ PASS | 4 | 0.3s |  |

### Consensus (49/73 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `AllSafeAtZero` | `Consensus/Voting.tla` | ✅ PASS | 1 | 0.4s |  |
| `AllSafeAtZero` | `Consensus/Voting.tla` | ✅ PASS | 1 | 0.4s |  |
| `CardinalityInNat` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.3s |  |
| `CardinalityInNat` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.3s |  |
| `CardinalityInNat` | `Data/Sets.tla` | ✅ PASS | 1 | 0.3s |  |
| `CardinalityInNat` | `Consensus/Sets.tla` | ✅ PASS | 1 | 0.4s |  |
| `CardinalityOne` | `Consensus/Sets.tla` | ✅ PASS | 1 | 2.2s |  |
| `CardinalityOne` | `Consensus/Sets.tla` | ✅ PASS | 1 | 2.3s |  |
| `CardinalityOne` | `Data/Sets.tla` | ✅ PASS | 1 | 2.2s |  |
| `CardinalityOne` | `Consensus/Sets.tla` | ✅ PASS | 1 | 2.4s |  |
| `CardinalityOneConverse` | `Consensus/Sets.tla` | ✅ PASS | 6 | 0.4s |  |
| `CardinalityOneConverse` | `Consensus/Sets.tla` | ✅ PASS | 6 | 0.4s |  |
| `CardinalityOneConverse` | `Data/Sets.tla` | ✅ PASS | 6 | 0.4s |  |
| `CardinalityOneConverse` | `Consensus/Sets.tla` | ✅ PASS | 6 | 0.4s |  |
| `CardinalityPlusOne` | `Consensus/Sets.tla` | ❌ FAIL | 8 | 5.4s | 1/11 obligations failed |
| `CardinalityPlusOne` | `Consensus/Sets.tla` | ❌ FAIL | 8 | 5.4s | 1/11 obligations failed |
| `CardinalityPlusOne` | `Data/Sets.tla` | ❌ FAIL | 8 | 5.4s | 1/11 obligations failed |
| `CardinalityPlusOne` | `Consensus/Sets.tla` | ❌ FAIL | 8 | 5.4s | 1/11 obligations failed |
| `CardinalitySetMinus` | `Consensus/Sets.tla` | ⚠️ CHEATING | 41 | 0.6s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `CardinalitySetMinus` | `Consensus/Sets.tla` | ⚠️ CHEATING | 41 | 0.7s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `CardinalitySetMinus` | `Data/Sets.tla` | ⚠️ CHEATING | 41 | 0.6s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `CardinalitySetMinus` | `Consensus/Sets.tla` | ⚠️ CHEATING | 41 | 0.7s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `CardinalityTwo` | `Consensus/Sets.tla` | ✅ PASS | 1 | 2.2s |  |
| `CardinalityTwo` | `Consensus/Sets.tla` | ✅ PASS | 1 | 2.2s |  |
| `CardinalityTwo` | `Data/Sets.tla` | ✅ PASS | 1 | 2.2s |  |
| `CardinalityTwo` | `Consensus/Sets.tla` | ✅ PASS | 1 | 2.3s |  |
| `CardinalityZero` | `Consensus/Sets.tla` | ✅ PASS | 13 | 0.4s |  |
| `CardinalityZero` | `Consensus/Sets.tla` | ✅ PASS | 13 | 0.4s |  |
| `CardinalityZero` | `Data/Sets.tla` | ✅ PASS | 13 | 0.4s |  |
| `CardinalityZero` | `Consensus/Sets.tla` | ✅ PASS | 13 | 0.4s |  |
| `ChoosableThm` | `Consensus/Voting.tla` | ✅ PASS | 1 | 0.4s |  |
| `ChoosableThm` | `Consensus/Voting.tla` | ✅ PASS | 1 | 0.4s |  |
| `Consistent` | `Consensus/Voting.tla` | ✅ PASS | 9 | 0.4s |  |
| `Consistent` | `Consensus/Voting.tla` | ✅ PASS | 9 | 0.5s |  |
| `FiniteSubset` | `Consensus/Sets.tla` | ❌ FAIL | 65 | 7.6s | 1/52 obligations failed |
| `FiniteSubset` | `Consensus/Sets.tla` | ❌ FAIL | 65 | 7.6s | 1/52 obligations failed |
| `FiniteSubset` | `Data/Sets.tla` | ❌ FAIL | 65 | 7.6s | 1/52 obligations failed |
| `FiniteSubset` | `Consensus/Sets.tla` | ❌ FAIL | 65 | 7.7s | 1/52 obligations failed |
| `IntervalCardinality` | `Consensus/Sets.tla` | ✅ PASS | 14 | 0.5s |  |
| `IntervalCardinality` | `Consensus/Sets.tla` | ✅ PASS | 14 | 0.5s |  |
| `IntervalCardinality` | `Data/Sets.tla` | ✅ PASS | 13 | 0.4s |  |
| `IntervalCardinality` | `Consensus/Sets.tla` | ✅ PASS | 14 | 0.5s |  |
| `Invariance` | `Consensus/Consensus.tla` | ✅ PASS | 6 | 0.4s |  |
| `Invariance` | `Consensus/Consensus.tla` | ✅ PASS | 6 | 0.4s |  |
| `Invariance` | `Consensus/Consensus.tla` | ✅ PASS | 6 | 0.4s |  |
| `Invariant` | `Consensus/Voting.tla` | ❌ FAIL | 82 | 31.7s | 1/73 obligations failed |
| `Invariant` | `Consensus/Voting.tla` | ❌ FAIL | 82 | 31.0s | 1/73 obligations failed |
| `IsBijectionInverse` | `Consensus/Sets.tla` | ✅ PASS | 3 | 0.4s |  |
| `IsBijectionInverse` | `Consensus/Sets.tla` | ✅ PASS | 3 | 0.4s |  |
| `IsBijectionInverse` | `Data/Sets.tla` | ✅ PASS | 3 | 0.3s |  |
| `IsBijectionInverse` | `Consensus/Sets.tla` | ✅ PASS | 3 | 0.4s |  |
| `IsBijectionTransitive` | `Consensus/Sets.tla` | ✅ PASS | 7 | 0.4s |  |
| `IsBijectionTransitive` | `Consensus/Sets.tla` | ✅ PASS | 7 | 0.4s |  |
| `IsBijectionTransitive` | `Data/Sets.tla` | ✅ PASS | 7 | 0.4s |  |
| `IsBijectionTransitive` | `Consensus/Sets.tla` | ✅ PASS | 7 | 0.4s |  |
| `OneVoteThm` | `Consensus/Voting.tla` | ✅ PASS | 1 | 0.4s |  |
| `OneVoteThm` | `Consensus/Voting.tla` | ✅ PASS | 1 | 0.4s |  |
| `OtherMessage` | `Consensus/PaxosProof.tla` | ❌ FAIL | 1 | 0.2s |  |
| `PigeonHole` | `Consensus/Sets.tla` | ✅ PASS | 47 | 7.2s |  |
| `PigeonHole` | `Consensus/Sets.tla` | ✅ PASS | 47 | 7.2s |  |
| `PigeonHole` | `Data/Sets.tla` | ✅ PASS | 47 | 7.2s |  |
| `PigeonHole` | `Consensus/Sets.tla` | ✅ PASS | 47 | 7.2s |  |
| `QuorumNonEmpty` | `Consensus/Voting.tla` | ✅ PASS | 1 | 0.4s |  |
| `QuorumNonEmpty` | `Consensus/Voting.tla` | ✅ PASS | 1 | 0.3s |  |
| `Refinement` | `Consensus/Voting.tla` | ❌ FAIL | 21 | 0.2s |  |
| `Refinement` | `Consensus/Voting.tla` | ❌ FAIL | 21 | 0.2s |  |
| `ShowsSafety` | `Consensus/Voting.tla` | ❌ FAIL | 3 | 5.3s | 1/3 obligations failed |
| `ShowsSafety` | `Consensus/Voting.tla` | ❌ FAIL | 3 | 5.3s | 1/3 obligations failed |
| `VotesSafeImpliesConsistency` | `Consensus/Voting.tla` | ❌ FAIL | 18 | 5.6s | 3/19 obligations failed |
| `VotesSafeImpliesConsistency` | `Consensus/Voting.tla` | ❌ FAIL | 18 | 5.6s | 3/19 obligations failed |
| `WFmsgs` | `Consensus/PaxosProof.tla` | ❌ FAIL | 1 | 0.2s |  |
| `struct_lemma` | `Consensus/PaxosProof.tla` | ⚠️ CHEATING | 7 | 0.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `typing` | `Consensus/PaxosProof.tla` | ⚠️ CHEATING | 8 | 0.2s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |

### Data (25/37 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `AppendDef` | `Data/SequencesTheorems.tla` | ❌ FAIL | 1 | 5.2s | 1/2 obligations failed |
| `AppendProperties` | `Data/SequencesTheorems.tla` | ✅ PASS | 1 | 0.3s |  |
| `AtLeastTwo` | `Data/GraphTheorem.tla` | ❌ FAIL | 1 | 5.2s | 1/4 obligations failed |
| `CardinalityInNat` | `Data/Sets.tla` | ✅ PASS | 1 | 0.3s |  |
| `CardinalityInNat` | `Data/Sets.tla` | ✅ PASS | 1 | 0.3s |  |
| `CardinalityOne` | `Data/Sets.tla` | ✅ PASS | 1 | 2.2s |  |
| `CardinalityOne` | `Data/Sets.tla` | ✅ PASS | 1 | 2.2s |  |
| `CardinalityOneConverse` | `Data/Sets.tla` | ✅ PASS | 6 | 0.4s |  |
| `CardinalityOneConverse` | `Data/Sets.tla` | ✅ PASS | 6 | 0.4s |  |
| `CardinalityPlusOne` | `Data/Sets.tla` | ❌ FAIL | 8 | 5.4s | 1/11 obligations failed |
| `CardinalityPlusOne` | `Data/Sets.tla` | ❌ FAIL | 8 | 5.4s | 1/11 obligations failed |
| `CardinalitySetMinus` | `Data/Sets.tla` | ⚠️ CHEATING | 41 | 0.6s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `CardinalitySetMinus` | `Data/Sets.tla` | ⚠️ CHEATING | 41 | 0.7s | PROOF_OMITTED: Proof uses PROOF OMITTED to skip obligations |
| `CardinalityTwo` | `Data/Sets.tla` | ✅ PASS | 1 | 2.2s |  |
| `CardinalityTwo` | `Data/Sets.tla` | ✅ PASS | 1 | 2.3s |  |
| `CardinalityZero` | `Data/Sets.tla` | ✅ PASS | 13 | 0.4s |  |
| `CardinalityZero` | `Data/Sets.tla` | ✅ PASS | 13 | 0.4s |  |
| `ConcatDef` | `Data/SequencesTheorems.tla` | ✅ PASS | 1 | 0.3s |  |
| `ConcatProperties` | `Data/SequencesTheorems.tla` | ✅ PASS | 1 | 0.3s |  |
| `EdgesAxiom` | `Data/GraphTheorem.tla` | ❌ FAIL | 1 | 30.4s | 1/2 obligations failed |
| `ElementOfSeq` | `Data/SequencesTheorems.tla` | ✅ PASS | 1 | 0.3s |  |
| `EmptySeq` | `Data/SequencesTheorems.tla` | ✅ PASS | 1 | 0.3s |  |
| `FiniteSubset` | `Data/Sets.tla` | ❌ FAIL | 65 | 7.6s | 1/52 obligations failed |
| `FiniteSubset` | `Data/Sets.tla` | ❌ FAIL | 65 | 7.6s | 1/52 obligations failed |
| `HeadAndTailOfSeq` | `Data/SequencesTheorems.tla` | ❌ FAIL | 9 | 0.2s |  |
| `InitialSubSeq` | `Data/SequencesTheorems.tla` | ❌ FAIL | 16 | 0.2s |  |
| `IntervalCardinality` | `Data/Sets.tla` | ✅ PASS | 13 | 0.4s |  |
| `IntervalCardinality` | `Data/Sets.tla` | ✅ PASS | 13 | 0.4s |  |
| `IsBijectionInverse` | `Data/Sets.tla` | ✅ PASS | 3 | 0.4s |  |
| `IsBijectionInverse` | `Data/Sets.tla` | ✅ PASS | 3 | 0.4s |  |
| `IsBijectionTransitive` | `Data/Sets.tla` | ✅ PASS | 7 | 0.4s |  |
| `IsBijectionTransitive` | `Data/Sets.tla` | ✅ PASS | 7 | 0.4s |  |
| `LenAxiom` | `Data/SequencesTheorems.tla` | ✅ PASS | 1 | 0.3s |  |
| `LenDomain` | `Data/SequencesTheorems.tla` | ⚠️ CHEATING | 5 | 0.3s | EXTRA_AXIOM: New AXIOM 'SubSeqDef' added — bypasses proof obligation; EXTRA_AXIOM: New AXIOM 'TailDef' added — bypasses proof obligation; EXTRA_AXIOM: New AXIOM 'HeadDef' added — bypasses proof obligation |
| `PigeonHole` | `Data/Sets.tla` | ✅ PASS | 47 | 7.2s |  |
| `PigeonHole` | `Data/Sets.tla` | ✅ PASS | 47 | 7.1s |  |
| `RemoveSeq` | `Data/SequencesTheorems.tla` | ✅ PASS | 17 | 0.4s |  |

### EWD840 (2/2 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `Inv_implies_Termination` | `EWD840/EWD840.tla` | ✅ PASS | 9 | 0.5s |  |
| `TypeOK_inv` | `EWD840/EWD840.tla` | ✅ PASS | 7 | 0.4s |  |

### Euclid (4/6 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `Correctness` | `Euclid/Euclid-TLAPS-Example/Euclid.tla` | ✅ PASS | 8 | 0.4s |  |
| `GCD1` | `Euclid/Euclid-Hyperbook/GCD.tla` | ❌ FAIL | 9 | 7.6s | 1/6 obligations failed |
| `GCD2` | `Euclid/Euclid-Hyperbook/GCD.tla` | ✅ PASS | 1 | 5.4s |  |
| `GCD3` | `Euclid/Euclid-Hyperbook/GCD.tla` | ❌ FAIL | 9 | 32.3s | 1/3 obligations failed |
| `InitProperty` | `Euclid/Euclid-TLAPS-Example/Euclid.tla` | ✅ PASS | 1 | 0.3s |  |
| `NextProperty` | `Euclid/Euclid-TLAPS-Example/Euclid.tla` | ✅ PASS | 20 | 0.5s |  |

### Paxos (4/13 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `Consistent` | `Paxos/Paxos.tla` | ❌ FAIL | 25 | 0.2s |  |
| `Consistent` | `Paxos/PaxosHistVar.tla` | ❌ FAIL | 25 | 17.4s | 1/26 obligations failed |
| `Invariant` | `Paxos/Paxos.tla` | ❌ FAIL | 184 | 0.2s |  |
| `Invariant` | `Paxos/PaxosHistVar.tla` | ✅ PASS | 126 | 6.8s |  |
| `NoneNotAValue` | `Paxos/Paxos.tla` | ❌ FAIL | 1 | 35.5s | 2/15 obligations failed |
| `QuorumNonEmpty` | `Paxos/Paxos.tla` | ❌ FAIL | 1 | 35.5s | 2/15 obligations failed |
| `Refinement` | `Paxos/Paxos.tla` | ❌ FAIL | 16 | 0.2s |  |
| `SafeAtStable` | `Paxos/PaxosHistVar.tla` | ✅ PASS | 39 | 1.2s |  |
| `SafeAtStable` | `Paxos/Paxos.tla` | ❌ FAIL | 49 | 0.2s |  |
| `VotedInv` | `Paxos/PaxosHistVar.tla` | ✅ PASS | 1 | 0.4s |  |
| `VotedInv` | `Paxos/Paxos.tla` | ❌ FAIL | 1 | 35.5s | 2/14 obligations failed |
| `VotedOnce` | `Paxos/PaxosHistVar.tla` | ✅ PASS | 1 | 0.4s |  |
| `VotedOnce` | `Paxos/Paxos.tla` | ❌ FAIL | 9 | 35.5s | 2/14 obligations failed |

### SimpleMutex (5/5 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `Initialization` | `SimpleMutex/SimpleMutex.tla` | ✅ PASS | 1 | 0.4s |  |
| `Invariance` | `SimpleMutex/SimpleMutex.tla` | ✅ PASS | 38 | 2.6s |  |
| `Mutex` | `SimpleMutex/SimpleMutex.tla` | ✅ PASS | 1 | 0.3s |  |
| `Safety` | `SimpleMutex/SimpleMutex.tla` | ✅ PASS | 1 | 0.3s |  |
| `TLAInvariance` | `SimpleMutex/SimpleMutex.tla` | ✅ PASS | 1 | 0.3s |  |

### Two-Phase (1/2 passed)

| Theorem | Source | Status | Proof Lines | Time | Notes |
|---------|--------|--------|-------------|------|-------|
| `Implementation` | `Two-Phase/TwoPhase.tla` | ❌ FAIL | 14 | 0.2s |  |
| `Mod2` | `Two-Phase/TwoPhase.tla` | ✅ PASS | 7 | 0.3s |  |

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

- **EXTRA_AXIOM**: New AXIOM 'SubSeqDef' added — bypasses proof obligation
- **EXTRA_AXIOM**: New AXIOM 'TailDef' added — bypasses proof obligation
- **EXTRA_AXIOM**: New AXIOM 'HeadDef' added — bypasses proof obligation

## Failed Verification Details

### `benchmark/Allocator/Allocator_NextMutex.tla`


### `benchmark/AtomicBakery/AtomicBakeryWithoutSMT_AfterPrime.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: 6/8 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/AtomicBakery/AtomicBakeryWithoutSMT_GGIrreflexive.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: 6/30 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/AtomicBakery/AtomicBakeryWithoutSMT_InductiveInvariant.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: 9/253 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/AtomicBakery/AtomicBakeryWithoutSMT_InitImpliesTypeOK.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: 6/16 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/AtomicBakery/AtomicBakeryWithoutSMT_InitInv.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: 6/9 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/AtomicBakery/AtomicBakeryWithoutSMT_InvExclusion.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: 6/8 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/AtomicBakery/AtomicBakeryWithoutSMT_Safety.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: 6/14 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/AtomicBakery/AtomicBakeryWithoutSMT_TypeOKInvariant.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: 6/54 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/ByzantinePaxos/BPConProof_BMessageLemma.tla`


### `benchmark/ByzantinePaxos/BPConProof_FiniteMsgsLemma.tla`


### `benchmark/ByzantinePaxos/BPConProof_InductiveInvariance_1.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/5 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/ByzantinePaxos/PConProof_InductiveInvariance_1.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/5 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/ByzantinePaxos/VoteProof_InductiveInvariance.tla`


### `benchmark/ByzantinePaxos/VoteProof_InductiveInvariance_1.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/5 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/ByzantinePaxos/BPConProof_InitImpliesInv.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/15 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/ByzantinePaxos/PConProof_InitImpliesInv.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/15 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/ByzantinePaxos/VoteProof_InitImpliesInv.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/15 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/ByzantinePaxos/Consensus_Invariance.tla`


### `benchmark/ByzantinePaxos/BPConProof_KnowsSafeAtDef.tla`


### `benchmark/ByzantinePaxos/BPConProof_MaxBallotLemma1.tla`


### `benchmark/ByzantinePaxos/BPConProof_MaxBallotLemma2.tla`


### `benchmark/ByzantinePaxos/BPConProof_MaxBallotProp.tla`


### `benchmark/ByzantinePaxos/BPConProof_MsgsLemma.tla`


### `benchmark/ByzantinePaxos/BPConProof_MsgsTypeLemma.tla`


### `benchmark/ByzantinePaxos/BPConProof_MsgsTypeLemmaPrime.tla`


### `benchmark/ByzantinePaxos/BPConProof_NextDef.tla`


### `benchmark/ByzantinePaxos/BPConProof_NextDef_1.tla`


### `benchmark/ByzantinePaxos/BPConProof_NextDef_2.tla`


### `benchmark/ByzantinePaxos/PConProof_NextDef.tla`


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


### `benchmark/ByzantinePaxos/PConProof_VT4.tla`


### `benchmark/ByzantinePaxos/VoteProof_VT4.tla`


### `benchmark/Consensus/Consensus_CardinalityPlusOne.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/11 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Consensus/PaxosProof_CardinalityPlusOne.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/11 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Consensus/Sets_CardinalityPlusOne.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/11 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Consensus/Voting_CardinalityPlusOne.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/11 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Consensus/Consensus_FiniteSubset.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/52 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Consensus/PaxosProof_FiniteSubset.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/52 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Consensus/Sets_FiniteSubset.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/52 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Consensus/Voting_FiniteSubset.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/52 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Consensus/PaxosProof_Invariant.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/73 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Consensus/Voting_Invariant.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/73 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Consensus/PaxosProof_OtherMessage.tla`


### `benchmark/Consensus/PaxosProof_Refinement.tla`


### `benchmark/Consensus/Voting_Refinement.tla`


### `benchmark/Consensus/PaxosProof_ShowsSafety.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/3 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Consensus/Voting_ShowsSafety.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/3 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Consensus/PaxosProof_VotesSafeImpliesConsistency.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: 3/19 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Consensus/Voting_VotesSafeImpliesConsistency.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: 3/19 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Consensus/PaxosProof_WFmsgs.tla`


### `benchmark/Data/SequencesTheorems_AppendDef.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/2 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Data/GraphTheorem_AtLeastTwo.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/4 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Data/GraphTheorem_CardinalityPlusOne.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/11 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Data/Sets_CardinalityPlusOne.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/11 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Data/GraphTheorem_EdgesAxiom.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/2 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Data/GraphTheorem_FiniteSubset.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/52 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Data/Sets_FiniteSubset.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/52 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Data/SequencesTheorems_HeadAndTailOfSeq.tla`


### `benchmark/Data/SequencesTheorems_InitialSubSeq.tla`


### `benchmark/Euclid/GCD_GCD1.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/6 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Euclid/GCD_GCD3.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/3 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Paxos/Paxos_Consistent.tla`


### `benchmark/Paxos/PaxosHistVar_Consistent.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: 1/26 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Paxos/Paxos_Invariant.tla`


### `benchmark/Paxos/Paxos_NoneNotAValue.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: 2/15 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Paxos/Paxos_QuorumNonEmpty.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: 2/15 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Paxos/Paxos_Refinement.tla`


### `benchmark/Paxos/Paxos_SafeAtStable.tla`


### `benchmark/Paxos/Paxos_VotedInv.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: 2/14 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Paxos/Paxos_VotedOnce.tla`

```
[ERROR]: Could not prove or check:
[ERROR]: Could not prove or check:
[ERROR]: 2/14 obligations failed.
 tlapm ending abnormally with Failure("backend errors: there are unproved obligations")
```

### `benchmark/Two-Phase/TwoPhase_Implementation.tla`

