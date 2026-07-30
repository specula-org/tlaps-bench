---- MODULE BlockingQueueFair_proofs_EmptySeqRange ----
EXTENDS BlockingQueueFair_proofs_EmptySeqRangeScaffold
LEMMA EmptySeqRange == ASSUME NEW S, NEW seq \in Seq(S)
                       PROVE seq = <<>> <=> Range(seq) = {}
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
