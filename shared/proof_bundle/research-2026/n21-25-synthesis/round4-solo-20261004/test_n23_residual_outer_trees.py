"""One real freshly accepted tree plus rebound mathematical corruptions."""
from pathlib import Path
from copy import deepcopy
import argparse
import gzip
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish
from audit_n23_residual_outer_supplement import fresh_tree
import exact_graph as exact

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tree", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    treepath, output = args.tree.resolve(), args.output.resolve()
    assert treepath.is_relative_to(ROOT) and output.is_relative_to(ROOT) and not output.exists()
    with gzip.open(treepath, "rt", encoding="utf8") as source:
        tree = json.load(source)
    constantspath = HIGH.parent / "evidence/core-reduction/constants/n23.json"
    constants, constantshash = read(constantspath), sha(constantspath)
    group = {"centers": tree["partial_centers"], "faces": tree["faces"], "members": 1}
    result = exact.verify(15, group["centers"], group["faces"], tree["nodes"], constants)
    outcome = dict(result, members=1)
    fresh_tree(group, outcome, tree, tree["groups_sha256"], constantshash, constants)
    rejected = []
    for label, field, value in (
        ("wrong-N", "N", 25), ("wrong-B", "B", 16),
        ("wrong-center-count", "partial_centers", tree["partial_centers"]+1),
        ("changed-face-identity", "faces", tree["faces"][:-1]),
        ("wrong-original-group-bytes", "groups_sha256", "0"*64),
        ("wrong-constants-bytes", "constants_sha256", "0"*64),
        ("wrong-radius-threshold", "radius_upper", "1/4"),
    ):
        changed = deepcopy(tree)
        changed[field] = value
        try:
            fresh_tree(group, outcome, changed, tree["groups_sha256"], constantshash, constants)
        except (AssertionError, IndexError, ValueError, KeyError, TypeError):
            rejected.append(label)
        else:
            raise AssertionError(("bad new tree binding accepted", label))
    for label, field, value in (
        ("wrong-receipt-node-count", "nodes", outcome["nodes"]+1),
        ("wrong-receipt-node-kinds", "counts", {}),
        ("wrong-original-member-count", "members", 2),
    ):
        changed = deepcopy(outcome)
        changed[field] = value
        try:
            fresh_tree(group, changed, tree, tree["groups_sha256"], constantshash, constants)
        except AssertionError:
            rejected.append(label)
        else:
            raise AssertionError(("bad new receipt accepted", label))
    changed = deepcopy(tree)
    changed["nodes"][0] = {"kind": "FRONTIER"}
    try:
        fresh_tree(group, outcome, changed, tree["groups_sha256"], constantshash, constants)
    except AssertionError:
        rejected.append("actual-unpaid-frontier-not-a-positive-proof")
    else:
        raise AssertionError("unfinished mathematical tree accepted")
    changed = deepcopy(tree)
    changed["nodes"].append({"kind": "EMPTY"})
    try:
        fresh_tree(group, outcome, changed, tree["groups_sha256"], constantshash, constants)
    except AssertionError:
        rejected.append("actual-unreachable-extra-node")
    else:
        raise AssertionError("unreachable proof node accepted")
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N23-residual-new-tree-identity-controls-v1",
        "one_actual_strict_tree_freshly_mathematically_replayed": True,
        "negative_controls_rejected": rejected,
        "positive_tree_sha256": sha(treepath), "constants_sha256": constantshash,
        "source_sha256": sha(Path(__file__)),
        "audit_source_sha256": sha(ROOT / "audit_n23_residual_outer_supplement.py"),
        "all_source_type_maps_and_disjoint_payment_merge_still_required": True,
        "global_optimality_proved": False,
    })
    print("N23 new residual tree identity controls PASS:", len(rejected), "rejections", flush=True)


if __name__ == "__main__":
    main()
