"""Fresh exact payments only for every member of the complete origin residual."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import argparse
import gzip
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
import exact_graph as exact
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish, bind, unchanged
from batch_streamed_collar import identity
from completion_family_gate import validate_outer_payment

assert __debug__


def main():
    ap = argparse.ArgumentParser()
    for name in ("catalog", "refined", "stage", "output"):
        ap.add_argument("--"+name, type=Path, required=True)
    ap.add_argument("--closure", type=Path, action="append", default=[])
    args = ap.parse_args()
    catalog, refined, stage, output = (getattr(args, name).resolve()
                                       for name in ("catalog", "refined", "stage", "output"))
    assert output.is_relative_to(ROOT) and not output.exists()
    refined_report = read(refined / "VERIFIED.json")
    assert refined_report["verified"] and refined_report["schema"] == "complete-collar-actual-cover-origin-refinement-v1"
    assert refined_report["all_complete_parent_residual_rows_partitioned_once"]
    assert refined_report["source_sha256"] == sha(ROOT / "refine_collar_origin.py")
    assert sha(refined / "RESIDUAL.jsonl") == refined_report["refined_residual_sha256"]
    unchanged(refined_report["files_relative_to_workspace"])
    parent, terminal = read(catalog / "SUMMARY.json"), read(catalog / "NATIVE-TERMINAL.json")
    assert parent["verified"] and parent["complete_necessary_outer_collar_overapproximation"]
    assert terminal["native_terminal_observed"] and terminal["actual_exit_code"] == 0
    unchanged(parent["files_relative_to_workspace"])
    groupspath = catalog / "GROUPS.json"
    digest = sha(groupspath)
    assert digest == parent["groups_sha256"] and groupspath.stat().st_size <= 128*1024**2
    data, receipt = read(groupspath), read(stage / "SUMMARY.json")
    N, B, total = data["N"], data["B"], data["group_count"]
    assert N == 25 and (refined_report["N"], refined_report["B"]) == (N, B)
    assert len(data["groups"]) == total == parent["unpaid_weak_graphs"]
    assert data["full_selected_catalog_scanned"] and data["members_are_necessary_weak_graphs_not_full_types"]
    assert receipt["groups_sha256"] == digest and (receipt["N"], receipt["B"]) == (N, B)
    assert receipt["requested_groups_complete"] and receipt["source_sha256"] == sha(HIGH / "probe_groups.py")
    outcomes = {r["group"]: r for r in receipt["outcomes"]}
    assert len(outcomes) == len(receipt["outcomes"]) == total
    assert set(outcomes) == set(range(total))
    assert Counter(r["status"] for r in receipt["outcomes"]) == {
        "excluded": receipt["excluded_groups"], "pending": receipt["pending_groups"]}
    constants_path = HIGH.parent / "evidence/core-reduction/constants/n25.json"
    constants, constantshash = read(constants_path), sha(constants_path)
    assert constants["verified"] and constants["N"] == 25
    closures = {}
    for path in args.closure:
        closure = read(path)
        assert closure["verified"] and closure["schema"] == "single-collar-strict-full-completion-closure-v1"
        assert closure["pending_completions"] == 0 and closure["complete_this_simple_hole_completion_family"]
        assert closure["strictly_excluded"] == closure["full_completion_types"]
        assert closure["radius_threshold"] == constants["radius_upper"]
        assert (closure["N"], closure["B"]) == (N, B)
        assert closure["source_sha256"] == sha(ROOT / "close_strict_collar_family.py")
        unchanged(closure["files_relative_to_workspace"])
        key = tuple(closure["collar_faces"])
        assert key not in closures
        closures[key] = (closure, path.resolve())
    files = {}
    for path in (Path(__file__), groupspath, catalog / "SUMMARY.json", catalog / "NATIVE-TERMINAL.json",
                 stage / "SUMMARY.json", refined / "VERIFIED.json", refined / "RESIDUAL.jsonl",
                 constants_path, HIGH / "exact_graph.py", HIGH / "probe_groups.py",
                 HIGH.parent / "round2-grouped/partial_force_exact.py", ROOT / "completion_family_gate.py"):
        bind(files, path)
    for path in args.closure:
        bind(files, path)
    bindingpath = catalog / data["bindings_file"]
    assert sha(bindingpath) == data["bindings_sha256"]
    bind(files, bindingpath)
    output.mkdir()
    counts = Counter()
    minimum = None
    previous_id, next_binding = -1, 0
    ledgerpath, residualpath = output / "PAYMENTS.jsonl", output / "RESIDUAL.jsonl"
    with (refined / "RESIDUAL.jsonl").open(encoding="ascii") as source, \
            bindingpath.open(encoding="ascii") as bindings, ledgerpath.open("x", encoding="ascii") as ledger, \
            residualpath.open("x", encoding="ascii") as residual:
        header = json.loads(next(source), object_pairs_hook=no_duplicate_keys)
        assert header["schema"] == "complete-collar-origin-refined-residual-v1"
        assert header["source_catalog_sha256"] == digest and (header["N"], header["B"]) == (N, B)
        residual.write(json.dumps({
            "schema": "complete-collar-origin-and-exact-force-residual-v1", "N": N, "B": B,
            "source_catalog_sha256": digest, "parent_refined_report_sha256": sha(refined / "VERIFIED.json"),
            "members_are_weak_graphs_not_full_types": True,
        }, separators=(",", ":"))+"\n")
        for line in source:
            row = json.loads(line, object_pairs_hook=no_duplicate_keys)
            gid, centers, faces = row["id"], row["centers"], row["faces"]
            assert previous_id < gid < total and row == data["groups"][gid]
            assert centers < 25
            previous_id = gid
            while next_binding <= gid:
                binding = json.loads(next(bindings), object_pairs_hook=no_duplicate_keys)
                assert binding["index"] == next_binding
                if next_binding == gid:
                    assert binding == {"index": gid, "group": gid, "map": identity(centers, B)}
                next_binding += 1
            outcome = outcomes[gid]
            if outcome["status"] == "excluded":
                treepath = stage / f"group-{gid:07}.json.gz"
                assert sha(treepath) == outcome["tree_sha256"]
                with gzip.open(treepath, "rt", encoding="utf8") as stream:
                    tree = json.load(stream, object_pairs_hook=no_duplicate_keys)
                assert (tree["N"], tree["B"], tree["partial_centers"], tree["faces"]) == (N, B, centers, faces)
                assert tree["groups_sha256"] == digest and tree["constants_sha256"] == constantshash
                assert tree["radius_upper"] == constants["radius_upper"]
                result = exact.verify(B, centers, faces, tree["nodes"], constants)
                assert result["verified"] and result["nodes"] == outcome["nodes"]
                assert result["counts"] == outcome["counts"] and outcome["members"] == 1
                margin = F(result["minimum_force_margin"])
                assert margin > 0
                minimum = margin if minimum is None else min(minimum, margin)
                bind(files, treepath)
                payment = {"parent_group": gid, "kind": "fresh-standard-library-exact-weak-force",
                           "tree_sha256": sha(treepath), "minimum_force_margin": str(margin)}
            elif tuple(faces) in closures:
                closure, path = closures[tuple(faces)]
                pattern = {"id": gid, "full_order": 25, "B": B, "centers": closure["collar_centers"],
                           "faces": closure["collar_faces"], "holes": closure["holes"],
                           "lower_mode": "no_full_simple_disk_realization_with_all_rods_at_most_U25"}
                validate_outer_payment(pattern, 25, B, faces, identity(centers, B))
                payment = {"parent_group": gid, "kind": "strict-complete-simple-disk-completion-family",
                           "closure_sha256": sha(path), "not_a_geometric_weak_exclusion": True}
            else:
                assert outcome["status"] == "pending"
                payment = None
            if payment is None:
                counts["pending"] += 1
                residual.write(json.dumps(row, separators=(",", ":"))+"\n")
            else:
                counts[payment["kind"]] += 1
                ledger.write(json.dumps(payment, separators=(",", ":"))+"\n")
            if sum(counts.values()) % 500 == 0:
                print("Selected complete residual exact payments:", sum(counts.values()), dict(counts), flush=True)
    assert sum(counts.values()) == refined_report["remaining_weak_graphs"]
    unchanged(files)
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "complete-origin-residual-exact-force-refinement-v1", "N": N, "B": B,
        "every_parent_residual_row_compared_with_complete_catalog_and_identity_map": True,
        "every_accepted_tree_fresh_standard_library_replayed": True,
        "parent_refined_weak_graphs": refined_report["remaining_weak_graphs"],
        "payment_counts": dict(counts), "remaining_weak_graphs": counts["pending"],
        "minimum_force_margin": None if minimum is None else str(minimum),
        "parent_refined_report_sha256": sha(refined / "VERIFIED.json"),
        "parent_catalog_sha256": digest, "whole_proposal_receipt_sha256": sha(stage / "SUMMARY.json"),
        "payments_sha256": sha(ledgerpath), "residual_sha256": sha(residualpath),
        "files_relative_to_workspace": files, "source_sha256": sha(Path(__file__)),
        "all_other_boundary_families_still_required": True, "global_optimality_proved": False,
    })
    print("Complete origin residual fresh exact refinement accepted:", dict(counts), flush=True)


if __name__ == "__main__":
    main()
