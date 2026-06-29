"""proof-completion — proof completion.

The benchmark file has its last theorem's body replaced with `PROOF OBVIOUS`.
Preceding theorems are admitted with `PROOF OMITTED`. The agent must fill in
only the last proof. The preamble (everything above `PROOF OBVIOUS`) is
expected to be byte-identical to the baseline.
"""

from .base import Mode


class ProofCompletion(Mode):
    name = "proof-completion"
    description = "Proof completion — fill in the last theorem's PROOF OBVIOUS"
