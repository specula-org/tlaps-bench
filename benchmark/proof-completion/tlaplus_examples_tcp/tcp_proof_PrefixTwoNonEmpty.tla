---- MODULE tcp_proof_PrefixTwoNonEmpty ----
EXTENDS tcp_proof_PrefixTwoNonEmptyScaffold
LEMMA PrefixTwoNonEmpty ==
  ASSUME NEW T, NEW e1 \in T, NEW e2 \in T, NEW s \in Seq(T),
         IsPrefix(<<e1, e2>>, s)
  PROVE  /\ Len(s) >= 2
         /\ s[1] = e1
         /\ s[2] = e2
\* BEGIN AGENT PROOF
PROOF OBVIOUS
\* END AGENT PROOF
====
