"""Lock ZooKeeper LocalPrimaryOrder to the intended forall-pairs statement.

The Remix/Zab comment is: if a primary broadcasts a before b, a follower that
delivers b also delivers a before b. The old encoding used
``\\E txn1, txn2 \\in txn_set`` plus reflexive TxnEqual, which is true as soon
as the set is nonempty. The shipped formula must quantify over every pair.
"""

from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]

LPO_FILES = (
    REPO_ROOT / "source" / "ZooKeeper" / "Zab.tla",
    REPO_ROOT / "source" / "ZooKeeper_LowLevel" / "ZkV3_7_0.tla",
    REPO_ROOT / "benchmark" / "proof-from-scratch" / "ZooKeeper" / "Zab_LocalPrimaryOrderDefs.tla",
    REPO_ROOT / "benchmark" / "proof-from-scratch" / "ZooKeeper_LowLevel" / "ZkV3_7_0_LocalPrimaryOrderDefs.tla",
)

EXISTS_PAIR = r"\E txn1, txn2 \in txn_set"
FORALL_PAIR = r"\A txn1, txn2 \in txn_set"


def test_local_primary_order_quantifies_over_every_broadcast_pair():
    for path in LPO_FILES:
        text = path.read_text(encoding="utf-8")
        assert "LocalPrimaryOrder ==" in text, path
        assert EXISTS_PAIR not in text, f"{path} still uses existential pair quantification"
        assert FORALL_PAIR in text, f"{path} is missing forall-pairs LocalPrimaryOrder"
