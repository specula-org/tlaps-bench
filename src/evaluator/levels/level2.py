"""Level 2 — proof from scratch.

The benchmark file keeps the model (definitions, constants, variables,
assumptions) and only the target theorem's statement, with `PROOF OBVIOUS`
in place of its body. All other theorems and lemmas are stripped. The agent
must invent the proof structure — including any helper lemmas — from scratch.

Because the agent is allowed to add new lemmas above the target theorem,
the strict L1 preamble-integrity check does not apply at L2.
"""

from .base import Level


class Level2(Level):
    name = "level2"
    level_number = 2
    description = "Proof from scratch — agent invents the proof structure"
