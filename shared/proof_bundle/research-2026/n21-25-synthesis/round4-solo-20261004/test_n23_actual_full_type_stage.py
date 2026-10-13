"""Actual N23 full-candidate map and tree-identity corruption controls."""
from copy import deepcopy
from pathlib import Path
import argparse

from audit_n23_actual_full_type_stage import (
    ROOT, HIGH, check_bound_tree, check_complete_candidate, read, publish, sha, exact)

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--core", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    corepath, output = args.core.resolve(), args.output.resolve()
    assert corepath.is_relative_to(ROOT) and output.is_relative_to(ROOT) and not output.exists()
    core = read(corepath)
    candidate = sorted(sum(1 << v for v in face) for face in core["all_faces"])
    assert (core["N"], core["B"], len(candidate)) == (23, 15, 29)
    row = {"index": 17, "faces": candidate}
    mapping = {"centers": list(range(23)), "anchors": list(range(15)),
               "orientation": 1, "shift": 0}
    check_complete_candidate(row, mapping, candidate)
    constantspath = HIGH.parent / "evidence/core-reduction/constants/n23.json"
    constants = read(constantspath)
    constantshash, fullhash = sha(constantspath), "functional-full-input-identity"
    tree = {
        "N": 23, "B": 15, "full_centers": 23, "index": 17, "faces": candidate,
        "restored_full_types_sha256": fullhash, "constants_sha256": constantshash,
        "radius_upper": constants["radius_upper"], "nodes": [{"kind": "EMPTY"}],
    }
    check_bound_tree(row, tree, fullhash, constantshash, constants)
    rejected = []
    for label, field, value in (
        ("wrong-order", "N", 25), ("wrong-boundary", "B", 16),
        ("weakened-center-count", "full_centers", 22), ("wrong-source-index", "index", 18),
        ("omitted-internal-full-face", "faces", candidate[:-1]),
        ("wrong-full-input-binding", "restored_full_types_sha256", "altered"),
        ("wrong-constants-binding", "constants_sha256", "altered"),
        ("wrong-radius", "radius_upper", "1/4"),
        ("local-leaf-cannot-pay-strict-type", "nodes", [{"kind": "LOCAL"}]),
        ("empty-tree", "nodes", []),
    ):
        changed = deepcopy(tree)
        changed[field] = value
        try:
            check_bound_tree(row, changed, fullhash, constantshash, constants)
        except (AssertionError, ValueError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError(("bad full tree identity accepted", label))
    for label, field, value in (
        ("candidate-map-center-collision", "centers", list(range(22))+[21]),
        ("candidate-map-anchor-collision", "anchors", [1]+list(range(1, 15))),
        ("candidate-map-wrong-reflection", "orientation", -1),
        ("candidate-map-wrong-shift", "shift", 1),
    ):
        changed = deepcopy(mapping)
        changed[field] = value
        try:
            check_complete_candidate(row, changed, candidate)
        except (AssertionError, ValueError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError(("bad candidate complete map accepted", label))
    inner = next(mask for mask in candidate if not mask & ((1 << 15)-1))
    changedrow = deepcopy(row)
    changedrow["faces"] = [mask for mask in candidate if mask != inner]
    try:
        check_complete_candidate(changedrow, mapping, candidate)
    except AssertionError:
        rejected.append("outer-agreement-with-missing-pure-internal-face")
    else:
        raise AssertionError("outer agreement was mistaken for complete candidate containment")
    # A syntactically matching EMPTY tree is not a proof: the actual known
    # candidate has a nonempty necessary root box. Invoke the real kernel.
    try:
        exact.verify(15, 23, candidate, tree["nodes"], constants)
    except AssertionError:
        rejected.append("fake-empty-tree-on-real-known-attaining-complete-type")
    else:
        raise AssertionError("real attaining complete graph incorrectly strictly excluded")
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N23-actual-full-type-tree-and-candidate-identity-controls-v1",
        "negative_controls_rejected": rejected,
        "real_original_N23_candidate_full_map_positive_control": True,
        "syntactic_fixture_not_counted_as_mathematical_force_proof": True,
        "real_mathematical_empty_leaf_refused": True,
        "core_sha256": sha(corepath), "constants_sha256": constantshash,
        "source_sha256": sha(Path(__file__)),
        "audit_source_sha256": sha(ROOT / "audit_n23_actual_full_type_stage.py"),
        "no_type_payment_or_global_theorem_from_controls": True,
        "global_optimality_proved": False,
    })
    print("Actual N23 full-type tree/map controls passed:", len(rejected), flush=True)


if __name__ == "__main__":
    main()
