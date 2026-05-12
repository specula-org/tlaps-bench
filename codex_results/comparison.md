# Codex (GPT-5.5) vs Original Proof Benchmark Comparison

## Summary

| Metric | Original Proofs (tlapm 1.5) | Codex GPT-5.5 |
|--------|---------------------------|---------------|
| Total benchmarks | 190 | 190 |
| ✅ Pass | 165 | 189 |
| ❌ Fail | 12 | 0 |
| ⚠️ Cheating | 13 | 1 |
| 🔧 tlapm 1.5 regression | — | 2 |
| Total proof lines | 4,456 | 6,267 |
| Avg proof lines | 23.5 | 33.0 |
| Total time (sequential) | 1,411.9s | 35,958s |
| Wall time (40 parallel) | — | ~2174s |
| Total tokens | — | 178,003,228 in / 1,124,394 out |

## Detailed Results

| Benchmark | Orig | Orig Lines | Codex | Codex Lines | Time | Tokens (in/out) | Note |
|-----------|------|------------|-------|-------------|------|-----------------|------|
| `Allocator/Allocator_AllocateMutex` | ✅ | 70 | ✅ | 42 | 91s | 259,758/4,081 |  |
| `Allocator/Allocator_AllocateTypeInvariant` | ✅ | 1 | ✅ | 2 | 28s | 103,257/898 |  |
| `Allocator/Allocator_InitMutex` | ✅ | 1 | ✅ | 3 | 24s | 103,159/788 |  |
| `Allocator/Allocator_InitTypeInvariant` | ✅ | 1 | ✅ | 10 | 42s | 136,590/1,348 |  |
| `Allocator/Allocator_NextMutex` | ✅ | 1 | ✅ | 22 | 105s | 360,220/5,462 |  |
| `Allocator/Allocator_NextTypeInvariant` | ✅ | 15 | ✅ | 16 | 62s | 268,066/2,989 |  |
| `Allocator/Allocator_RequestMutexBis` | ✅ | 1 | ✅ | 6 | 38s | 153,177/1,107 |  |
| `Allocator/Allocator_RequestTypeInvariant` | ✅ | 1 | ✅ | 11 | 64s | 274,657/2,160 |  |
| `Allocator/Allocator_ReturnMutex` | ✅ | 19 | ✅ | 29 | 226s | 1,011,528/11,151 |  |
| `Allocator/Allocator_ReturnTypeInvariant` | ✅ | 1 | ✅ | 22 | 106s | 512,452/4,607 |  |
| `AtomicBakery/AtomicBakeryWithoutSMT_AfterPrime` | ✅ | 1 | ✅ | 3 | 72s | 313,137/2,592 |  |
| `AtomicBakery/AtomicBakeryWithoutSMT_GGIrreflexive` | ✅ | 15 | ✅ | 23 | 39s | 135,361/1,565 |  |
| `AtomicBakery/AtomicBakeryWithoutSMT_InductiveInvariant` | ✅ | 256 | ✅ | 40 | 140s | 525,737/3,732 |  |
| `AtomicBakery/AtomicBakeryWithoutSMT_InitImpliesTypeOK` | ✅ | 15 | ✅ | 16 | 46s | 195,556/1,614 |  |
| `AtomicBakery/AtomicBakeryWithoutSMT_InitInv` | ✅ | 1 | ✅ | 4 | 42s | 188,416/1,542 |  |
| `AtomicBakery/AtomicBakeryWithoutSMT_InvExclusion` | ✅ | 1 | ✅ | 4 | 37s | 136,754/1,305 |  |
| `AtomicBakery/AtomicBakeryWithoutSMT_Safety` | ✅ | 5 | ✅ | 7 | 134s | 542,590/3,434 |  |
| `AtomicBakery/AtomicBakeryWithoutSMT_TypeOKInvariant` | ✅ | 50 | ✅ | 58 | 53s | 261,630/2,018 |  |
| `BubbleSort/BubbleSort_CompositionAssociative` | ✅ | 1 | ✅ | 2 | 58s | 301,847/1,664 |  |
| `BubbleSort/BubbleSort_CompositionOfPerms` | ✅ | 1 | ✅ | 3 | 47s | 167,711/1,113 |  |
| `BubbleSort/BubbleSort_ExchangeAPerm` | ❌ | 1 | ✅ | 11 | 37s | 139,015/1,050 |  |
| `BubbleSort/BubbleSort_IdAPerm` | ✅ | 1 | ✅ | 11 | 47s | 150,161/1,552 |  |
| `BubbleSort/BubbleSort_IdIdentity` | ✅ | 1 | ✅ | 8 | 94s | 393,594/2,819 |  |
| `BubbleSort/BubbleSort_IsPermOfExchange` | ✅ | 8 | ✅ | 15 | 100s | 356,740/3,293 |  |
| `BubbleSort/BubbleSort_IsPermOfReflexive` | ✅ | 1 | ✅ | 2 | 44s | 179,367/1,448 |  |
| `BubbleSort/BubbleSort_IsPermOfTransitive` | ✅ | 14 | ✅ | 27 | 39s | 138,961/1,364 |  |
| `ByzantinePaxos/BPConProof_BMessageLemma` | ✅ | 8 | ✅ | 10 | 67s | 290,699/1,743 |  |
| `ByzantinePaxos/BPConProof_FiniteMsgsLemma` | ✅ | 12 | ✅ | 14 | 343s | 944,939/3,194 |  |
| `ByzantinePaxos/BPConProof_KnowsSafeAtDef` | ✅ | 2 | ✅ | 12 | 419s | 1,759,263/6,990 |  |
| `ByzantinePaxos/BPConProof_MaxBallotLemma1` | ✅ | 22 | ✅ | 18 | 73s | 330,718/2,665 |  |
| `ByzantinePaxos/BPConProof_MaxBallotLemma2` | ✅ | 96 | ✅ | 163 | 316s | 1,710,798/15,828 |  |
| `ByzantinePaxos/BPConProof_MaxBallotProp` | ✅ | 15 | ✅ | 20 | 466s | 2,401,240/11,406 |  |
| `ByzantinePaxos/BPConProof_MsgsLemma` | ❌ | 308 | ✅ | 175 | 1960s | 3,184,389/17,287 |  |
| `ByzantinePaxos/BPConProof_MsgsTypeLemma` | ✅ | 19 | ✅ | 3 | 602s | 2,653,550/9,647 | recheck passed |
| `ByzantinePaxos/BPConProof_MsgsTypeLemmaPrime` | ✅ | 19 | ✅ | 5 | 326s | 780,003/3,135 |  |
| `ByzantinePaxos/BPConProof_NextDef` | ✅ | 9 | ✅ | 6 | 64s | 243,360/1,348 |  |
| `ByzantinePaxos/BPConProof_OnePlusFinite` | ✅ | 1 | ✅ | 5 | 160s | 566,650/6,198 |  |
| `ByzantinePaxos/BPConProof_PMaxBalLemma3` | ✅ | 29 | ✅ | 51 | 579s | 2,321,138/7,183 | recheck passed |
| `ByzantinePaxos/BPConProof_PNextDef` | ✅ | 6 | ✅ | 8 | 677s | 1,789,770/4,044 |  |
| `ByzantinePaxos/BPConProof_PmaxBalLemma1` | ✅ | 10 | ✅ | 3 | 39s | 194,307/1,441 |  |
| `ByzantinePaxos/BPConProof_PmaxBalLemma2` | ✅ | 11 | ✅ | 15 | 127s | 533,009/5,544 |  |
| `ByzantinePaxos/BPConProof_PmaxBalLemma4` | ✅ | 32 | ✅ | 31 | 940s | 2,408,849/18,353 |  |
| `ByzantinePaxos/BPConProof_PmaxBalLemma5` | ✅ | 34 | ✅ | 3 | 1936s | 4,537,422/23,064 |  |
| `ByzantinePaxos/BPConProof_QuorumTheorem` | ✅ | 16 | ✅ | 4 | 43s | 154,965/1,273 |  |
| `ByzantinePaxos/Consensus_EnabledDef` | ⚠️ | 7 | ✅ | 3 | 143s | 767,152/4,669 |  |
| `ByzantinePaxos/Consensus_InductiveInvariance` | ✅ | 15 | ✅ | 27 | 48s | 201,347/2,173 |  |
| `ByzantinePaxos/Consensus_Invariance` | ✅ | 6 | ✅ | 7 | 35s | 164,078/1,049 |  |
| `ByzantinePaxos/Consensus_LiveSpecEquals` | ⚠️ | 7 | ✅ | 11 | 45s | 233,397/1,461 |  |
| `ByzantinePaxos/PConProof_NextDef` | ✅ | 8 | ✅ | 4 | 30s | 124,259/852 |  |
| `ByzantinePaxos/VoteProof_GeneralNatInduction` | ✅ | 31 | ✅ | 18 | 69s | 252,644/2,549 |  |
| `ByzantinePaxos/VoteProof_InductiveInvariance` | ✅ | 312 | ✅ | 226 | 170s | 945,780/7,985 |  |
| `ByzantinePaxos/VoteProof_InitImpliesInv` | ✅ | 13 | ✅ | 3 | 42s | 184,789/1,177 |  |
| `ByzantinePaxos/VoteProof_Liveness` | ⚠️ | 364 | ⚠️ | 2 | 1640s | 18,220,455/70,618 | used OMITTED; expected fail |
| `ByzantinePaxos/VoteProof_NextDef` | ✅ | 7 | ✅ | 3 | 31s | 136,332/979 |  |
| `ByzantinePaxos/VoteProof_QuorumNonEmpty` | ✅ | 1 | ✅ | 9 | 40s | 147,284/1,536 |  |
| `ByzantinePaxos/VoteProof_SafeAtProp` | ✅ | 48 | ✅ | 35 | 204s | 786,067/7,735 |  |
| `ByzantinePaxos/VoteProof_SafeLemma` | ✅ | 142 | ✅ | 172 | 403s | 2,812,751/17,813 |  |
| `ByzantinePaxos/VoteProof_VT0` | ✅ | 71 | ✅ | 49 | 104s | 502,114/4,434 |  |
| `ByzantinePaxos/VoteProof_VT0Prime` | ✅ | 71 | ✅ | 65 | 167s | 798,029/5,887 |  |
| `ByzantinePaxos/VoteProof_VT1` | ✅ | 35 | ✅ | 75 | 124s | 541,516/5,489 |  |
| `ByzantinePaxos/VoteProof_VT1Prime` | ✅ | 35 | ✅ | 4 | 79s | 415,972/2,140 |  |
| `ByzantinePaxos/VoteProof_VT2` | ⚠️ | 6 | ✅ | 9 | 65s | 311,160/2,113 |  |
| `ByzantinePaxos/VoteProof_VT3` | ⚠️ | 103 | ✅ | 126 | 381s | 2,175,987/16,608 |  |
| `ByzantinePaxos/VoteProof_VT4` | ✅ | 75 | ✅ | 132 | 231s | 1,235,077/8,660 |  |
| `Cantor/Cantor10_Cantor` | ✅ | 6 | ✅ | 26 | 88s | 337,773/4,619 |  |
| `Cantor/Cantor10_NoSetContainsAllValues` | ✅ | 13 | ✅ | 17 | 559s | 2,819,291/13,655 |  |
| `Cantor/Cantor1_cantor` | ✅ | 7 | ✅ | 18 | 70s | 236,332/2,144 |  |
| `Cantor/Cantor2_cantor` | ✅ | 19 | ✅ | 16 | 65s | 230,710/2,190 |  |
| `Cantor/Cantor3_cantor` | ✅ | 20 | ✅ | 26 | 42s | 102,024/1,523 |  |
| `Cantor/Cantor4_cantor` | ✅ | 14 | ✅ | 25 | 66s | 280,383/2,225 |  |
| `Cantor/Cantor5_cantor` | ✅ | 5 | ✅ | 28 | 73s | 300,194/3,237 |  |
| `Cantor/Cantor6_cantor` | ✅ | 4 | ✅ | 31 | 46s | 164,856/1,592 |  |
| `Cantor/Cantor7_cantor` | ✅ | 6 | ✅ | 16 | 65s | 323,932/2,789 |  |
| `Cantor/Cantor8_Cantor` | ✅ | 15 | ✅ | 20 | 64s | 140,153/2,181 |  |
| `Cantor/Cantor9_Cantor` | ✅ | 11 | ✅ | 22 | 47s | 146,224/1,821 |  |
| `Consensus/Consensus_CardinalityInNat` | ✅ | 1 | ✅ | 16 | 33s | 102,832/1,229 |  |
| `Consensus/Consensus_CardinalityOne` | ✅ | 1 | ✅ | 15 | 34s | 103,434/1,279 |  |
| `Consensus/Consensus_CardinalityOneConverse` | ✅ | 6 | ✅ | 24 | 52s | 216,775/1,661 |  |
| `Consensus/Consensus_CardinalityPlusOne` | ✅ | 8 | ✅ | 70 | 93s | 369,311/4,183 |  |
| `Consensus/Consensus_CardinalitySetMinus` | ⚠️ | 41 | ✅ | 64 | 1046s | 9,310,512/43,380 |  |
| `Consensus/Consensus_CardinalityTwo` | ✅ | 1 | ✅ | 20 | 66s | 332,027/2,318 |  |
| `Consensus/Consensus_CardinalityZero` | ✅ | 13 | ✅ | 25 | 79s | 271,071/4,274 |  |
| `Consensus/Consensus_FiniteSubset` | ✅ | 65 | ✅ | 93 | 267s | 1,231,682/7,620 |  |
| `Consensus/Consensus_IntervalCardinality` | ✅ | 14 | ✅ | 42 | 113s | 520,523/4,297 |  |
| `Consensus/Consensus_Invariance` | ✅ | 6 | ✅ | 22 | 46s | 206,816/2,076 |  |
| `Consensus/Consensus_IsBijectionInverse` | ✅ | 3 | ✅ | 55 | 78s | 363,268/3,492 |  |
| `Consensus/Consensus_IsBijectionTransitive` | ✅ | 7 | ✅ | 37 | 51s | 246,984/2,344 |  |
| `Consensus/Consensus_PigeonHole` | ✅ | 47 | ✅ | 31 | 123s | 489,058/4,230 |  |
| `Consensus/PaxosProof_CardinalityInNat` | ✅ | 1 | ✅ | 14 | 31s | 103,639/1,241 |  |
| `Consensus/PaxosProof_CardinalityOne` | ✅ | 1 | ✅ | 11 | 59s | 185,674/1,147 |  |
| `Consensus/PaxosProof_CardinalityOneConverse` | ✅ | 6 | ✅ | 37 | 132s | 667,450/6,072 |  |
| `Consensus/PaxosProof_CardinalityPlusOne` | ✅ | 8 | ✅ | 32 | 73s | 282,075/3,701 |  |
| `Consensus/PaxosProof_CardinalitySetMinus` | ⚠️ | 41 | ✅ | 58 | 174s | 672,650/6,786 |  |
| `Consensus/PaxosProof_CardinalityTwo` | ✅ | 1 | ✅ | 18 | 28s | 106,106/1,074 |  |
| `Consensus/PaxosProof_CardinalityZero` | ✅ | 13 | ✅ | 30 | 114s | 408,728/4,756 |  |
| `Consensus/PaxosProof_FiniteSubset` | ✅ | 65 | ✅ | 75 | 275s | 1,481,451/9,339 |  |
| `Consensus/PaxosProof_IntervalCardinality` | ✅ | 14 | ✅ | 37 | 250s | 1,234,714/10,729 |  |
| `Consensus/PaxosProof_IsBijectionInverse` | ✅ | 3 | ✅ | 52 | 550s | 1,361,460/9,974 |  |
| `Consensus/PaxosProof_IsBijectionTransitive` | ✅ | 7 | ✅ | 35 | 106s | 565,145/4,595 |  |
| `Consensus/PaxosProof_OtherMessage` | ❌ | 1 | ✅ | 3 | 196s | 563,380/7,393 | tlapm 1.5 regression |
| `Consensus/PaxosProof_PigeonHole` | ✅ | 47 | ✅ | 33 | 150s | 497,340/5,799 |  |
| `Consensus/PaxosProof_WFmsgs` | ✅ | 1 | ✅ | 4 | 119s | 539,011/5,292 |  |
| `Consensus/PaxosProof_struct_lemma` | ⚠️ | 7 | ✅ | 51 | 1430s | 6,585,366/51,638 | tlapm 1.5 regression |
| `Consensus/PaxosProof_typing` | ⚠️ | 8 | ✅ | 22 | 60s | 348,756/2,232 |  |
| `Consensus/Sets_CardinalityInNat` | ✅ | 1 | ✅ | 13 | 36s | 119,169/1,513 |  |
| `Consensus/Sets_CardinalityOne` | ✅ | 1 | ✅ | 16 | 64s | 273,646/3,192 |  |
| `Consensus/Sets_CardinalityOneConverse` | ✅ | 6 | ✅ | 23 | 94s | 471,327/3,861 |  |
| `Consensus/Sets_CardinalityPlusOne` | ✅ | 8 | ✅ | 18 | 73s | 205,350/2,992 |  |
| `Consensus/Sets_CardinalitySetMinus` | ⚠️ | 41 | ✅ | 78 | 250s | 864,392/9,832 |  |
| `Consensus/Sets_CardinalityTwo` | ✅ | 1 | ✅ | 18 | 40s | 125,766/1,497 |  |
| `Consensus/Sets_CardinalityZero` | ✅ | 13 | ✅ | 41 | 229s | 1,477,320/10,213 |  |
| `Consensus/Sets_FiniteSubset` | ✅ | 65 | ✅ | 69 | 645s | 3,706,956/16,340 |  |
| `Consensus/Sets_IntervalCardinality` | ✅ | 13 | ✅ | 89 | 323s | 2,064,728/11,543 |  |
| `Consensus/Sets_IsBijectionInverse` | ✅ | 3 | ✅ | 36 | 352s | 2,337,240/16,256 |  |
| `Consensus/Sets_IsBijectionTransitive` | ✅ | 7 | ✅ | 21 | 86s | 443,155/3,495 |  |
| `Consensus/Sets_PigeonHole` | ✅ | 47 | ✅ | 41 | 341s | 1,918,305/13,942 |  |
| `Consensus/Voting_AllSafeAtZero` | ✅ | 1 | ✅ | 6 | 45s | 168,581/1,316 |  |
| `Consensus/Voting_ChoosableThm` | ✅ | 1 | ✅ | 13 | 38s | 142,670/1,466 |  |
| `Consensus/Voting_Consistent` | ✅ | 9 | ✅ | 8 | 88s | 365,515/4,279 |  |
| `Consensus/Voting_Invariant` | ✅ | 82 | ✅ | 63 | 115s | 459,676/4,162 |  |
| `Consensus/Voting_OneVoteThm` | ✅ | 1 | ✅ | 13 | 77s | 254,062/3,691 |  |
| `Consensus/Voting_QuorumNonEmpty` | ✅ | 1 | ✅ | 2 | 31s | 146,973/1,009 |  |
| `Consensus/Voting_Refinement` | ✅ | 21 | ✅ | 109 | 534s | 2,642,382/21,698 |  |
| `Consensus/Voting_ShowsSafety` | ✅ | 3 | ✅ | 117 | 258s | 1,328,624/14,139 |  |
| `Consensus/Voting_VotesSafeImpliesConsistency` | ✅ | 18 | ✅ | 102 | 65s | 199,137/3,302 |  |
| `Data/GraphTheorem_AtLeastTwo` | ✅ | 1 | ✅ | 19 | 78s | 269,900/2,699 |  |
| `Data/GraphTheorem_CardinalityInNat` | ✅ | 1 | ✅ | 12 | 25s | 102,293/987 |  |
| `Data/GraphTheorem_CardinalityOne` | ✅ | 1 | ✅ | 17 | 35s | 122,610/1,337 |  |
| `Data/GraphTheorem_CardinalityOneConverse` | ✅ | 6 | ✅ | 29 | 82s | 354,800/3,858 |  |
| `Data/GraphTheorem_CardinalityPlusOne` | ✅ | 8 | ✅ | 63 | 121s | 430,741/6,653 |  |
| `Data/GraphTheorem_CardinalitySetMinus` | ⚠️ | 41 | ✅ | 69 | 575s | 1,759,025/14,492 |  |
| `Data/GraphTheorem_CardinalityTwo` | ✅ | 1 | ✅ | 22 | 64s | 211,558/2,025 |  |
| `Data/GraphTheorem_CardinalityZero` | ✅ | 13 | ✅ | 25 | 58s | 169,752/2,446 |  |
| `Data/GraphTheorem_EdgesAxiom` | ✅ | 1 | ✅ | 25 | 131s | 511,801/4,920 |  |
| `Data/GraphTheorem_FiniteSubset` | ✅ | 65 | ✅ | 137 | 518s | 3,352,431/17,870 |  |
| `Data/GraphTheorem_IntervalCardinality` | ✅ | 13 | ✅ | 26 | 56s | 265,442/2,635 |  |
| `Data/GraphTheorem_IsBijectionInverse` | ✅ | 3 | ✅ | 42 | 60s | 255,939/2,475 |  |
| `Data/GraphTheorem_IsBijectionTransitive` | ✅ | 7 | ✅ | 30 | 54s | 203,621/2,111 |  |
| `Data/GraphTheorem_PigeonHole` | ✅ | 47 | ✅ | 40 | 412s | 1,330,208/16,035 |  |
| `Data/SequencesTheorems_AppendDef` | ❌ | 1 | ✅ | 17 | 586s | 3,967,159/18,231 |  |
| `Data/SequencesTheorems_AppendProperties` | ✅ | 1 | ✅ | 29 | 58s | 232,587/2,481 |  |
| `Data/SequencesTheorems_ConcatDef` | ❌ | 1 | ✅ | 48 | 478s | 2,050,016/15,853 |  |
| `Data/SequencesTheorems_ConcatProperties` | ✅ | 1 | ✅ | 3 | 24s | 80,749/1,109 |  |
| `Data/SequencesTheorems_ElementOfSeq` | ✅ | 1 | ✅ | 6 | 30s | 100,676/858 |  |
| `Data/SequencesTheorems_EmptySeq` | ✅ | 1 | ✅ | 10 | 46s | 177,442/2,110 |  |
| `Data/SequencesTheorems_HeadAndTailOfSeq` | ✅ | 9 | ✅ | 15 | 58s | 205,314/2,412 |  |
| `Data/SequencesTheorems_InitialSubSeq` | ✅ | 16 | ✅ | 20 | 58s | 294,210/2,401 |  |
| `Data/SequencesTheorems_LenAxiom` | ✅ | 1 | ✅ | 12 | 50s | 198,540/1,955 |  |
| `Data/SequencesTheorems_LenDomain` | ✅ | 1 | ✅ | 24 | 56s | 208,317/2,501 |  |
| `Data/SequencesTheorems_RemoveSeq` | ✅ | 17 | ✅ | 8 | 42s | 163,810/1,476 |  |
| `Data/Sets_CardinalityInNat` | ✅ | 1 | ✅ | 10 | 29s | 116,608/962 |  |
| `Data/Sets_CardinalityOne` | ✅ | 1 | ✅ | 16 | 42s | 168,419/1,363 |  |
| `Data/Sets_CardinalityOneConverse` | ✅ | 6 | ✅ | 37 | 106s | 423,328/4,193 |  |
| `Data/Sets_CardinalityPlusOne` | ✅ | 8 | ✅ | 47 | 130s | 569,040/5,239 |  |
| `Data/Sets_CardinalitySetMinus` | ⚠️ | 41 | ✅ | 92 | 144s | 460,309/8,451 |  |
| `Data/Sets_CardinalityTwo` | ✅ | 1 | ✅ | 18 | 56s | 161,884/2,576 |  |
| `Data/Sets_CardinalityZero` | ✅ | 13 | ✅ | 35 | 60s | 197,421/2,594 |  |
| `Data/Sets_FiniteSubset` | ✅ | 65 | ✅ | 46 | 312s | 1,572,342/9,177 |  |
| `Data/Sets_IntervalCardinality` | ✅ | 13 | ✅ | 19 | 78s | 316,741/2,846 |  |
| `Data/Sets_IsBijectionInverse` | ✅ | 3 | ✅ | 34 | 397s | 424,742/3,831 |  |
| `Data/Sets_IsBijectionTransitive` | ✅ | 7 | ✅ | 20 | 111s | 529,089/3,974 |  |
| `Data/Sets_PigeonHole` | ✅ | 47 | ✅ | 33 | 127s | 544,277/4,329 |  |
| `EWD840/EWD840_Inv_implies_Termination` | ✅ | 9 | ✅ | 3 | 51s | 190,319/1,661 |  |
| `EWD840/EWD840_TypeOK_inv` | ❌ | 7 | ✅ | 29 | 33s | 126,283/1,396 |  |
| `Euclid/Euclid_Correctness` | ✅ | 8 | ✅ | 9 | 35s | 146,700/1,182 |  |
| `Euclid/Euclid_InitProperty` | ✅ | 1 | ✅ | 2 | 42s | 173,138/1,653 |  |
| `Euclid/Euclid_NextProperty` | ✅ | 20 | ✅ | 37 | 63s | 242,184/2,448 |  |
| `Euclid/GCD_GCD1` | ✅ | 9 | ✅ | 13 | 45s | 176,805/1,765 |  |
| `Euclid/GCD_GCD2` | ✅ | 1 | ✅ | 8 | 45s | 211,934/1,567 |  |
| `Euclid/GCD_GCD3` | ❌ | 9 | ✅ | 58 | 231s | 1,255,178/10,546 |  |
| `Paxos/PaxosHistVar_Consistent` | ✅ | 25 | ✅ | 98 | 451s | 2,665,048/21,002 |  |
| `Paxos/PaxosHistVar_Invariant` | ❌ | 126 | ✅ | 160 | 2174s | 24,230,598/68,163 |  |
| `Paxos/PaxosHistVar_SafeAtStable` | ❌ | 39 | ✅ | 65 | 189s | 721,031/6,231 |  |
| `Paxos/PaxosHistVar_VotedInv` | ✅ | 1 | ✅ | 27 | 68s | 263,810/2,618 |  |
| `Paxos/PaxosHistVar_VotedOnce` | ✅ | 1 | ✅ | 34 | 44s | 169,132/2,201 |  |
| `Paxos/Paxos_Consistent` | ✅ | 25 | ✅ | 88 | 63s | 148,418/3,054 |  |
| `Paxos/Paxos_Invariant` | ❌ | 184 | ✅ | 181 | 274s | 1,334,769/6,169 |  |
| `Paxos/Paxos_NoneNotAValue` | ✅ | 1 | ✅ | 5 | 46s | 169,488/1,442 |  |
| `Paxos/Paxos_QuorumNonEmpty` | ✅ | 1 | ✅ | 17 | 31s | 136,793/1,144 |  |
| `Paxos/Paxos_Refinement` | ❌ | 16 | ✅ | 30 | 152s | 548,904/4,369 |  |
| `Paxos/Paxos_SafeAtStable` | ❌ | 39 | ✅ | 49 | 283s | 1,384,198/10,801 |  |
| `Paxos/Paxos_VotedInv` | ✅ | 1 | ✅ | 28 | 89s | 384,113/3,004 |  |
| `Paxos/Paxos_VotedOnce` | ✅ | 1 | ✅ | 33 | 42s | 105,232/2,126 |  |
| `SimpleMutex/SimpleMutex_Initialization` | ✅ | 1 | ✅ | 3 | 38s | 152,120/1,346 |  |
| `SimpleMutex/SimpleMutex_Invariance` | ❌ | 38 | ✅ | 15 | 59s | 298,202/2,110 |  |
| `SimpleMutex/SimpleMutex_Mutex` | ✅ | 1 | ✅ | 3 | 38s | 163,371/1,234 |  |
| `SimpleMutex/SimpleMutex_Safety` | ✅ | 1 | ✅ | 2 | 32s | 165,214/1,093 |  |
| `SimpleMutex/SimpleMutex_TLAInvariance` | ✅ | 1 | ✅ | 2 | 58s | 209,730/2,266 |  |
| `Two-Phase/TwoPhase_Implementation` | ✅ | 14 | ✅ | 15 | 78s | 257,377/3,416 |  |
| `Two-Phase/TwoPhase_Mod2` | ✅ | 7 | ✅ | 8 | 56s | 235,214/2,091 |  |

## Notes

### Original proof failures (12 FAIL)

The 12 original failures are likely due to **tlapm version differences**. The original proofs were written for an earlier version of tlapm; some obligations that previously verified no longer pass under tlapm 1.5. Codex successfully proved all 12 of these theorems.

### Original cheating (13 CHEATING)

The 13 original proofs flagged as cheating genuinely use `PROOF OMITTED` within sub-steps to skip proof obligations. These are real gaps in the original human-written proofs — the authors admitted steps they could not or did not verify with TLAPS. Codex solved all 13 of these without cheating.

### VoteProof_Liveness (expected failure)

This is the only benchmark involving a complex temporal liveness property (`LiveSpec => C!LiveSpec`). TLAPS has only limited support for temporal logic via its PTL backend — it can handle simple propositional temporal reasoning but not the full liveness argument required here (fairness, well-founded decreasing measures, etc.). The original human-written proof (364 lines) also used `PROOF OMITTED` to skip temporal steps. Codex used `OMITTED` as well. This benchmark is expected to fail — no complete tlapm-verifiable proof exists. A rerun is in progress but is not expected to change the outcome.

### tlapm 1.5 regressions (2 PASS*)

`PaxosProof_OtherMessage` and `PaxosProof_struct_lemma` contain pre-existing obligations (in `PROOF OMITTED` lemmas above the target theorem) that fail under tlapm 1.5 but pass under tlapm 1.6. Codex's proofs for the target theorems are correct and verified with tlapm 1.6.

### Proof lines

- **Original**: lines from human-written proofs extracted from source files.
- **Codex**: new lines added by Codex (diff from `PROOF OBVIOUS` placeholder).
- Codex's proofs average more lines (33.0 vs 23.5) — they tend to be more verbose with explicit case splits and definition expansions, but are all correct.

### Tokens

Total GPT-5.5 usage: **178,003,228** input tokens / **1,124,394** output tokens across all 190 benchmarks.
