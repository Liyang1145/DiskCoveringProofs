"""Export conditional full-family theorems from independently paid finite rows."""
from pathlib import Path
from fractions import Fraction as F
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from group_catalog import canonical, validate
from linked_general_collar_kernel import replay, start_states
from n25_outer_search import read, publish, bind, unchanged

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--payments", type=Path, required=True)
    ap.add_argument("--controls", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    args.payments, args.controls, args.output = (
        p.resolve() for p in (args.payments, args.controls, args.output))
    assert all(p.is_relative_to(ROOT) for p in (args.payments, args.controls, args.output))
    assert not args.output.exists()
    parent_path, ledger_path = args.payments / "VERIFIED.json", args.payments / "PARTITION.jsonl"
    parent = read(parent_path)
    assert parent["verified"] and parent["schema"] == "independent-finite-origin-slab-closed-filling-supplement-v1"
    assert parent["source_sha256"] == sha(ROOT / "audit_closed_filling_supplements.py")
    assert parent["finite_rows_fully_scanned"] == 100000
    assert parent["all_old_and_new_positive_payments_fresh_replayed_and_source_rows_checked"]
    assert parent["not_a_complete_competitor_family_or_union"]
    assert sha(ledger_path) == parent["partition_sha256"]
    files = dict(parent["files_relative_to_workspace"])
    unchanged(files)
    controls = read(args.controls)
    assert controls["verified"] and controls["schema"] == "linked-general-collar-filling-controls-v1"
    assert controls["all_no_payment_complete_type_sets_equal_to_references"]
    assert controls["known_attaining_candidate_not_strictly_paid"]
    for key, filename in (
        ("kernel_sha256", "linked_general_collar_kernel.py"),
        ("provider_sha256", "general_collar_filling_linked.py"),
        ("source_induction_sha256", "GENERAL-COLLAR-FILLING-SOURCE.md"),
    ):
        assert controls[key] == sha(ROOT / filename)
    unchanged(controls["files_relative_to_workspace"])
    files.update(controls["files_relative_to_workspace"])
    constants_path = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    constants = read(constants_path)
    assert constants["verified"] and constants["N"] == 25
    assert F(constants["radius_upper"]) == F(239146311738101, 10**15)
    patterns, keys, count = [], set(), 0
    with ledger_path.open(encoding="ascii") as stream:
        header = json.loads(next(stream), object_pairs_hook=no_duplicate_keys)
        assert header["N"] == 25 and header["B"] == parent["B"]
        assert header["not_a_complete_competitor_family_or_union"]
        for index, line in enumerate(stream):
            entry = json.loads(line, object_pairs_hook=no_duplicate_keys)
            assert entry["slab_row"] == index
            count += 1
            if entry["status"] != "strict-complete-filling-family":
                continue
            candidates = [ROOT.parents[2] / relative for relative, digest in files.items()
                          if digest == entry["proof_sha256"] and relative.endswith(".json")]
            assert len(candidates) == 1
            proof_path = candidates[0]
            assert sha(proof_path) == entry["proof_sha256"]
            payload = read(proof_path)
            B, centers, faces = parent["B"], entry["centers"], entry["faces"]
            assert (payload["N"], payload["B"], payload["collar_centers"], payload["collar_faces"]) == (
                25, B, centers, faces)
            assert payload["constants_sha256"] == sha(constants_path)
            assert payload["kernel_sha256"] == sha(ROOT / "linked_general_collar_kernel.py")
            code, mapping = canonical(centers, B, faces, 1)
            assert tuple(faces) == code and len(mapping["centers"]) == centers
            validate(centers, B, code, mapping, faces)
            start_states(25, B, centers, faces)
            result = replay(proof_path, constants)
            assert result["all_full_simple_disk_completions_strictly_paid"]
            assert result["pending_complete_leaves"] == result["unsearched_frontier_nodes"] == 0
            key = (B, centers, code)
            assert key not in keys
            keys.add(key)
            patterns.append({
                "id": len(patterns), "full_order": 25, "B": B, "centers": centers, "faces": faces,
                "proof_file_relative_to_workspace": proof_path.relative_to(ROOT.parents[2]).as_posix(),
                "proof_sha256": sha(proof_path), "fresh_exact_branch_replay": result,
                "lower_mode": "no_full_same_order_simple_disk_with_all_rods_at_most_U25",
                "all_center_labels_used_in_outer_graph": True,
                "not_a_standalone_geometric_weak_graph_exclusion": True,
            })
            if len(patterns) % 100 == 0:
                print("Exact-collar linked family theorems independently exported:", len(patterns), flush=True)
    assert count == 100000 and len(patterns) == parent["counts"]["strict-complete-filling-family"] > 0
    for path in (Path(__file__), parent_path, ledger_path, args.controls, constants_path,
                 ROOT / "linked_filling_library.py", ROOT / "linked_general_collar_kernel.py",
                 ROOT / "general_collar_filling.py", ROOT / "general_collar_filling_linked.py",
                 ROOT / "GENERAL-COLLAR-FILLING-SOURCE.md", ROOT / "LINKED-FILLING-EXACT-COLLAR-TRANSPORT.md",
                 HIGH / "exact_graph.py", HIGH / "group_catalog.py"):
        bind(files, path)
    unchanged(files)
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    args.output.mkdir()
    publish(args.output / "LIBRARY.json", {
        "verified": True, "schema": "strict-linked-completion-exact-collar-library-v1",
        "full_order": 25, "patterns": patterns, "pattern_count": len(patterns),
        "radius_upper_threshold": constants["radius_upper"],
        "exact_N_B_and_outer_image_required": True,
        "all_patterns_pay_complete_linked_filling_families": True,
        "full_order_simple_disk_completion_required": True,
        "pattern_source_row_numbers_or_multiplicities_not_theorem_premises": True,
        "all_family_trees_fresh_standard_library_replayed": True,
        "transport_source_sha256": sha(ROOT / "LINKED-FILLING-EXACT-COLLAR-TRANSPORT.md"),
        "files_relative_to_workspace": files, "source_sha256": sha(Path(__file__)),
        "source_finite_payments_sha256": sha(parent_path),
        "not_a_complete_competitor_family_or_union": True, "global_optimality_proved": False,
    })
    print("Conditional linked exact-collar library accepted:", len(patterns),
          "complete family theorems; not a whole boundary family", flush=True)


if __name__ == "__main__":
    main()
