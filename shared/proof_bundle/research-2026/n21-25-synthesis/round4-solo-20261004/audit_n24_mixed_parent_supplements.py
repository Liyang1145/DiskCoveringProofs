"""Finished N24/B15 formal parent: real strict families plus own exact core family."""
from pathlib import Path
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish
from audit_small_order_parent_supplements import base_gate, source_identity, supplement
from small_order_collar_lower_pipeline import rows
from prove_n24_core_and_finer_family import audit as replay_mixed

assert __debug__


def mixed_supplement(item, expected):
    family, proofpath, exactpath = (
        Path(item[key]).resolve() for key in ("family", "proof_path", "exact_path"))
    assert all(path.is_relative_to(ROOT) for path in (family, proofpath, exactpath))
    assert item["parent_index"] == expected["parent_index"] == 29688
    assert item["kind"] == "own-N24-complete-family-strict-and-same-root-core"
    collar = read(family / "INPUT-COLLAR.json")
    source_identity(expected, collar, 24, 15)
    exact = read(exactpath)
    assert exact["verified"]
    assert exact["schema"] == "N24-actual-complete-family-finer-strict-plus-own-nonstrict-core-independent-replay-v1"
    assert exact["source_sha256"] == sha(ROOT / "prove_n24_core_and_finer_family.py")
    assert exact["whole_completion_family_paid_strict_or_same_root"]
    assert exact["pending_complete_leaves"] == exact["unsearched_frontier_nodes"] == 0
    assert not exact["whole_family_strictly_closed"]
    assert exact["same_root_nonstrict_complete_leaves"] == 2
    assert exact["new_strict_complete_leaf_payments"] == 11
    assert exact["original_actual_full_family_identity_and_both_refinement_layers_checked"]
    assert exact["core_payments_never_recast_as_strict_U24_exclusions"]
    assert sha(proofpath) == item["proof_sha256"] == exact["proposal_sha256"]
    assert sha(exactpath) == item["exact_sha256"]
    controlpath = Path(item["own_core_controls"]).resolve()
    assert controlpath.is_relative_to(ROOT)
    assert sha(controlpath) == item["own_core_controls_sha256"]
    fresh = replay_mixed(family, controlpath, proofpath)
    assert fresh == exact
    return {
        "parent_index": expected["parent_index"],
        "kind": "own-N24-complete-family-strict-and-same-root-core",
        "proof_sha256": sha(proofpath), "exact_sha256": sha(exactpath),
        "nonstrict_complete_leaves": 2, "new_strict_complete_leaves": 11,
        "not_a_strict_geometric_weak_graph_exclusion": True}


def manifest_gate(manifest, base_report, expected):
    assert (manifest["N"], manifest["B"]) == (24, 15)
    assert manifest["base_report_sha256"] == base_report
    additions = {}
    for item in manifest["additions"]:
        pid = item["parent_index"]
        assert type(pid) is int and pid not in additions
        assert pid in expected
        assert item["kind"] in ("strict-complete-family-refinement",
                                "own-N24-complete-family-strict-and-same-root-core")
        additions[pid] = item
    assert additions
    mixed = [pid for pid, item in additions.items()
             if item["kind"] == "own-N24-complete-family-strict-and-same-root-core"]
    assert mixed == [29688]
    return additions


def main():
    ap = argparse.ArgumentParser()
    for name in ("stage", "lower", "base", "supplements", "controls", "output"):
        ap.add_argument("--"+name, required=True, type=Path)
    args = ap.parse_args()
    stage, lower, base, manifestpath, controlpath, output = (
        getattr(args, key).resolve() for key in ("stage", "lower", "base", "supplements", "controls", "output"))
    assert all(path.is_relative_to(ROOT) for path in (stage, lower, base, manifestpath, controlpath, output))
    assert not output.exists()
    controls = read(controlpath)
    assert controls["verified"] and controls["source_sha256"] == sha(ROOT / "test_n24_mixed_parent_supplements.py")
    assert controls["audit_source_sha256"] == sha(Path(__file__))
    assert controls["actual_mixed_whole_family_mathematics_freshly_replayed"]
    assert len(controls["negative_mixed_parent_controls_rejected"]) == 10
    source, record = base_gate(stage, lower, base)
    assert (source["N"], source["B"]) == (24, 15)
    expected = {}
    with (base / "ACCEPTED/PENDING.jsonl").open(encoding="ascii") as stream:
        previous = -1
        for line in stream:
            item = json.loads(line, object_pairs_hook=no_duplicate_keys)
            pid = item["parent_index"]
            assert type(pid) is int and pid > previous
            previous, expected[pid] = pid, item
    assert len(expected) == record["pending_families"]
    manifest = read(manifestpath)
    additions = manifest_gate(manifest, sha(base / "ACCEPTED/VERIFIED.json"), expected)
    for path, digest in manifest["supplement_origin_records_sha256"].items():
        assert sha(path) == digest
    new, strict, core = {}, 0, 0
    frozen = {str(path): sha(path) for path in (
        Path(__file__), controlpath, manifestpath, base / "ACCEPTED/VERIFIED.json",
        base / "ACCEPTED/PENDING.jsonl", stage / "ACCEPTED/SOURCE-ACCEPTED.json")}
    for pid in sorted(additions):
        item = additions[pid]
        assert Path(item["family"]).resolve() == (
            base / f"batch-{expected[pid]['job']:06}" / f"parent-{pid:07}").resolve()
        if item["kind"] == "strict-complete-family-refinement":
            new[pid] = supplement(item, expected[pid], 24, 15)
            strict += 1
        else:
            new[pid] = mixed_supplement(item, expected[pid])
            core += 1
        exact = read(Path(item["exact_path"]))
        for path, digest in exact["frozen_files"].items():
            assert path not in frozen or frozen[path] == digest
            frozen[path] = digest
        for key in ("proof_path", "exact_path"):
            frozen[item[key]] = sha(Path(item[key]))
        if len(new) % 10 == 0:
            print("N24 B15 actual formal-parent supplemental families freshly replayed",
                  len(new), "/", len(additions), flush=True)
    output.mkdir()
    seen, pending = set(), 0
    with (output / "ADDITIONAL-PAYMENTS.jsonl").open("x", encoding="ascii") as ledger, \
            (output / "PENDING.jsonl").open("x", encoding="ascii") as residual:
        for row in rows(stage, source):
            pid = row["id"]
            if pid not in expected:
                continue
            assert (row["centers"], row["faces"]) == (expected[pid]["centers"], expected[pid]["faces"])
            seen.add(pid)
            if pid in new:
                ledger.write(json.dumps(new[pid], separators=(",", ":"))+"\n")
            else:
                residual.write(json.dumps(expected[pid], separators=(",", ":"))+"\n")
                pending += 1
    assert seen == set(expected) and len(new)+pending == record["pending_families"]
    assert strict+core == len(new) and core == 1
    for path, digest in frozen.items():
        assert sha(path) == digest
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N24-full-parent-own-strict-and-same-root-core-supplement-disjoint-adoption-v1",
        "N": 24, "B": 15, "complete_parent_weak_graphs": record["parent_weak_graphs"],
        "old_strict_weak_graphs": record["old_strict_weak_graphs"],
        "old_strict_complete_families": record["new_strict_complete_families"],
        "new_strict_refined_complete_families": strict,
        "new_own_strict_and_same_root_core_complete_families": core,
        "remaining_pending_families": pending,
        "full_parent_disjoint_partition_complete": (
            record["old_strict_weak_graphs"]+record["new_strict_complete_families"]+strict+core+pending ==
            record["parent_weak_graphs"]),
        "each_new_actual_complete_family_tree_and_true_source_graph_freshly_independently_replayed": True,
        "all_old_mathematics_reused_under_unchanged_full_parent_and_tree_byte_premises": True,
        "all_core_leaf_center_anchor_face_and_witness_rods_bound_to_own_N24_theorem": True,
        "core_remains_nonstrict_same_root_not_strict_upper_exclusion": True,
        "base_report_sha256": sha(base / "ACCEPTED/VERIFIED.json"),
        "source_acceptance_sha256": sha(stage / "ACCEPTED/SOURCE-ACCEPTED.json"),
        "additional_payments_sha256": sha(output / "ADDITIONAL-PAYMENTS.jsonl"),
        "pending_sha256": sha(output / "PENDING.jsonl"), "frozen_files": frozen,
        "source_sha256": sha(Path(__file__)), "whole_parent_family_lower_paid": pending == 0,
        "complete_arbitrary_cover_source_global_synthesis_and_other_families_still_required": True,
        "global_optimality_proved": False})
    print("N24 B15 entire formal parent mixed adoption accepted:", strict, "new strict,",
          core, "own mixed whole family, pending", pending, flush=True)


if __name__ == "__main__":
    main()
