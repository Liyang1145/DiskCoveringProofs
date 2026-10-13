"""Fresh theorem acceptance plus exact full-outer transport and bad-proof controls."""
from pathlib import Path
from copy import deepcopy
import argparse
import json
import random
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha
from n25_outer_search import read, publish, bind, unchanged
from linked_filling_library import library_gate, make_index, lookup_exact_outer, validate_exact_outer_map
from linked_general_collar_kernel import replay as replay_branch

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--library", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    args.library, args.output = args.library.resolve(), args.output.resolve()
    assert args.library.is_relative_to(ROOT) and args.output.is_relative_to(ROOT)
    assert not args.output.exists()
    library, files = library_gate(args.library)
    index = make_index(library)
    args.output.mkdir()
    rng = random.Random(251006)
    positives, last = [], None
    for pattern in library["patterns"]:
        B, centers = pattern["B"], pattern["centers"]
        for sign, shift in ((1, 0), (-1, B-1), (1, B//2)):
            internal = list(range(B, 25));rng.shuffle(internal)
            labeling = [(shift+sign*v) % B for v in range(B)]+internal[:centers-B]
            faces = sorted(sum(1 << labeling[v] for v in range(centers) if mask >> v & 1)
                           for mask in pattern["faces"])
            result = lookup_exact_outer(index, 25, B, 25, faces)
            assert result is not None
            accepted_pattern, mapping, checked = result
            assert accepted_pattern["id"] == pattern["id"]
            assert checked["verified"] and checked["exact_complete_outer_face_image_equal"]
            positives.append({
                "source_pattern": pattern["id"], "faces": faces, "map": mapping,
                "fresh_exact_transport_check": checked,
            })
            if last is None:
                last = pattern, mapping, faces
    assert last is not None
    maps_path = args.output / "POSITIVE-TRANSPORTS.json"
    publish(maps_path, {"transports": positives})
    geometry_path = ROOT.parent / "evidence/n25-algebraic-upper-round2/geometry.json"
    geometry = read(geometry_path)
    known_faces = sorted(sum(1 << v for v in face) for face in geometry["faces"] if any(v < 16 for v in face))
    assert lookup_exact_outer(index, 25, 16, 25, known_faces) is None
    rejected = []
    pattern, mapping, faces = last
    for label in ("wrong-N", "wrong-B", "wrong-anchor-offset", "center-collision",
                  "missing-image-face", "extra-outer-face"):
        bad_map, bad_faces = deepcopy(mapping), list(faces)
        target_order, target_B = 25, pattern["B"]
        if label == "wrong-N":
            target_order = 24
        elif label == "wrong-B":
            target_B -= 1
        elif label == "wrong-anchor-offset":
            bad_map["anchors"][0] = (bad_map["anchors"][0]+1) % target_B
        elif label == "center-collision":
            bad_map["centers"][1] = bad_map["centers"][0]
        elif label == "missing-image-face":
            bad_faces.pop()
        else:
            extra = next((1 << a) | (1 << b) | (1 << v)
                         for a in range(target_B) for b in range(a+1, target_B)
                         for v in range(target_B, 25)
                         if ((1 << a) | (1 << b) | (1 << v)) not in bad_faces)
            bad_faces = sorted(bad_faces+[extra])
        try:
            validate_exact_outer_map(pattern, target_order, target_B, 25, bad_faces, bad_map)
        except (AssertionError, IndexError, KeyError):
            rejected.append(label)
        else:
            raise AssertionError(("bad conditional transport accepted", label))
    for label, field, value in (
        ("wrong-library-threshold", "radius_upper_threshold", "1/4"),
        ("wrong-full-order", "full_order", 26),
        ("false-pattern-count", "pattern_count", library["pattern_count"]+1),
    ):
        bad = deepcopy(library)
        bad[field] = value
        path = args.output / (label+".json")
        publish(path, bad)
        try:
            library_gate(path)
        except AssertionError:
            rejected.append(label)
        else:
            raise AssertionError(("bad conditional library accepted", label))
    # Rebind a genuinely incomplete proof and its true replay result. The
    # rejection must be mathematical completeness, not just a stale hash.
    bad = deepcopy(library)
    first = bad["patterns"][0]
    proof_path = ROOT.parents[2] / first["proof_file_relative_to_workspace"]
    payload = read(proof_path)
    leaf = next(node for node in payload["nodes"] if node["kind"] in ("FORCE", "ANGLE", "DEAD"))
    leaf["kind"] = "FRONTIER"
    bad_proof_path = args.output / "true-unpaid-frontier-PROPOSAL.json"
    publish(bad_proof_path, payload)
    constants = read(ROOT.parent / "evidence/core-reduction/constants/n25.json")
    true_report = replay_branch(bad_proof_path, constants)
    assert not true_report["all_full_simple_disk_completions_strictly_paid"]
    first["proof_file_relative_to_workspace"] = bad_proof_path.relative_to(ROOT.parents[2]).as_posix()
    first["proof_sha256"] = sha(bad_proof_path)
    first["fresh_exact_branch_replay"] = true_report
    bind(bad["files_relative_to_workspace"], bad_proof_path)
    bad_library_path = args.output / "true-unpaid-frontier-LIBRARY.json"
    publish(bad_library_path, bad)
    try:
        library_gate(bad_library_path)
    except AssertionError:
        rejected.append("actual-unpaid-frontier-with-rebound-hash-and-truthful-replay")
    else:
        raise AssertionError("an explicitly unpaid frontier became a library theorem")
    for path in (Path(__file__), args.library, maps_path, geometry_path,
                 ROOT / "linked_filling_library.py", ROOT / "LINKED-FILLING-EXACT-COLLAR-TRANSPORT.md"):
        bind(files, path)
    unchanged(files)
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(args.output / "VERIFIED.json", {
        "verified": True, "schema": "strict-linked-family-exact-outer-transport-controls-v1",
        "N": 25, "source_patterns": library["pattern_count"],
        "explicit_transformed_full_outer_maps_checked": len(positives),
        "all_library_branch_trees_fresh_exact_replayed": True,
        "all_successful_maps_extended_bijectively_to_full25_labels": True,
        "known_exact_N25_attaining_outer_graph_not_strictly_matched": True,
        "negative_controls_rejected": rejected,
        "positive_transports_sha256": sha(maps_path), "library_sha256": sha(args.library),
        "files_relative_to_workspace": files, "source_sha256": sha(Path(__file__)),
        "not_a_complete_competitor_family_or_union": True, "global_optimality_proved": False,
    })
    print("Linked family exact-outer transport controls PASS:", len(positives),
          "positive maps;", len(rejected), "rejections; exact attaining graph retained", flush=True)


if __name__ == "__main__":
    main()
