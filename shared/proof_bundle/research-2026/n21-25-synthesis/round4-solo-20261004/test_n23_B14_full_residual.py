"""Real current complete type and positive mathematical tree identity controls."""
from pathlib import Path
from copy import deepcopy
from io import StringIO
import argparse
import json

from audit_n23_B14_full_residual import (
    ROOT, HIGH, parent_gate, check_tree, outcomes_for_pending, IndexedOriginal,
    pending_indices, read, publish, sha, exact)
from probe_collar_batches import make

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    for name in ("source", "parent", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    args = ap.parse_args()
    sourcepath, parent, output = (
        getattr(args, name).resolve() for name in ("source", "parent", "output"))
    assert all(path.is_relative_to(ROOT) for path in (sourcepath, parent, output))
    assert not output.exists()
    accepted, catalogpath, _ = parent_gate(parent, sourcepath)
    catalog = IndexedOriginal(catalogpath)
    constants_path = ROOT.parent / "evidence/core-reduction/constants/n23.json"
    constants = read(constants_path)
    current = pending_indices(parent / "PENDING.jsonl", 8277632)
    found = None
    for _ in range(8):
        index = next(current)
        original = catalog.at(index)
        nodes, _ = make(14, 23, original["faces"], constants, 511, route_weak=False)
        if nodes is not None:
            found = index, original, nodes
            break
    assert found is not None, "no real positive full residual fixture found"
    catalog.close()
    index, original, nodes = found
    tree = {
        "N": 23, "B": 14, "full_centers": 23, "index": index,
        "faces": original["faces"], "nodes": nodes,
        "parent_pending_sha256": accepted["pending_sha256"],
        "constants_sha256": sha(constants_path), "radius_upper": constants["radius_upper"],
    }
    result = check_tree(index, original, tree, accepted["pending_sha256"], sha(constants_path), constants)
    assert result["verified"]
    internal = next(mask for mask in original["faces"] if not mask & ((1 << 14)-1))
    cases = []
    for label, field, value in (
        ("wrong-full-N", "N", 24), ("wrong-B", "B", 15),
        ("outer-only-center-count", "full_centers", 22),
        ("wrong-original-source-index", "index", index+1),
        ("omitted-pure-internal-face", "faces", [f for f in original["faces"] if f != internal]),
        ("wrong-parent-residual-binding", "parent_pending_sha256", "f"*64),
        ("wrong-constants-binding", "constants_sha256", "f"*64),
        ("wrong-radius", "radius_upper", "1/4"),
        ("missing-math-nodes", "nodes", []),
        ("LOCAL-not-a-strict-full-type-payment", "nodes", [{"kind": "LOCAL"}]),
    ):
        changed = deepcopy(tree)
        changed[field] = value
        cases.append((label, changed))
    rejected = []
    for label, changed in cases:
        try:
            check_tree(index, original, changed, accepted["pending_sha256"], sha(constants_path), constants)
        except (AssertionError, ValueError, IndexError, KeyError):
            rejected.append(label)
        else:
            raise AssertionError(("invalid actual full-type strict tree accepted", label))
    fixture = [1, 5, 12]
    outcomes = [{"index": value, "status": "pending"} for value in fixture]

    def join(rows=outcomes, indices=fixture, expected=3):
        return list(outcomes_for_pending(iter(indices),
            StringIO("".join(json.dumps(row)+"\n" for row in rows)), expected))

    assert len(join()) == 3
    for label, rows, indices, expected in (
        ("missing-actual-outcome", outcomes[:-1], fixture, 3),
        ("duplicate-actual-outcome", outcomes[:1]+outcomes, fixture, 3),
        ("extra-actual-outcome", outcomes+outcomes[-1:], fixture, 3),
        ("wrong-declared-current-count", outcomes, fixture, 4),
        ("wrong-current-index-matched", outcomes, [1, 6, 12], 3),
    ):
        try:
            join(rows, indices, expected)
        except (AssertionError, ValueError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError(("invalid actual residual partition accepted", label))
    output.mkdir()
    publish(output / "POSITIVE-REAL-FULL-TREE.json", tree)
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N23-B14-actual-full-residual-type-controls-v1",
        "actual_current_pending_complete_type_positive_control": index,
        "all30_real_original_faces_and_pure_internal_face_preserved": True,
        "positive_full_type_tree_mathematically_verified": True,
        "positive_tree_sha256": sha(output / "POSITIVE-REAL-FULL-TREE.json"),
        "negative_controls_rejected": rejected,
        "audit_source_sha256": sha(ROOT / "audit_n23_B14_full_residual.py"),
        "proposal_source_sha256": sha(ROOT / "propose_n23_B14_full_residual.py"),
        "source_sha256": sha(Path(__file__)), "frozen_exact_checker_sha256": sha(HIGH / "exact_graph.py"),
        "global_optimality_proved": False,
    })
    print("N23/B14 actual full residual strict tree/partition controls passed:", len(rejected), flush=True)


if __name__ == "__main__":
    main()
