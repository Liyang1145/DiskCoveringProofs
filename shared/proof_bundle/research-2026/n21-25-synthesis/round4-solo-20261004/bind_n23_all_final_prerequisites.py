"""Current all-content binding of complete N23 source/payment/root prerequisites.

Old accepted mathematics is honestly reused. Original archive-only B13 bytes
remain archive-only. No new global claim is made by this integrity collector.
"""
from pathlib import Path
from collections import deque
import argparse
import json
import sys

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
WORK = ROOT.parents[2]
RECOVERED = ROOT.parents[3]
INCOMING = ROOT.parents[4]
DEPENDENCIES = INCOMING.parent / "dependencies"
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish

assert __debug__


def checked_roots():
    paths = [
        ROOT / "n23-three-full-source-interfaces-v2/VERIFIED.json",
        ROOT / "n23-B14-complete-source-and-union-reacceptance-20261005-v1/VERIFIED.json",
        ROOT / "n23-B14-o1-a/VERIFIED.json", ROOT / "n23-B14-o2-a/VERIFIED.json",
        ROOT / "n23-B14-full1/ACCEPTED/VERIFIED.json",
        ROOT / "n23-B14-final1/ACCEPTED/VERIFIED.json",
        ROOT / "n23-B15-final13-actual-full-types-strict-supplement-audit-solo-v1/VERIFIED.json",
        ROOT / "n23-nonstrict-core-fresh-root-upper-local-angle-audit-solo-v1/VERIFIED.json",
        ROOT / "n23-n24-own-family-budget-v1/VERIFIED.json",
        ROOT / "n23-B13-current-all-byte-integrity-v1/VERIFIED.json",
        ROOT / "n23-B13-final-archive-metadata-v1/VERIFIED.json",
    ]
    data = [read(path) for path in paths]
    assert all(record["verified"] for record in data)
    source, b14source, first, second, full, final, b15, core, budget, b13bytes, metadata = data
    assert source["families"] == [[13, 10], [14, 9], [15, 8]]
    assert source["original_catalog_type_counts"] == [1530509, 8277632, 16790546]
    assert b14source["complete_recorded_necessary_family"]
    assert (first["original_catalog_types"], second["original_catalog_types"],
            full["original_catalog_types"]) == (8277632,)*3
    assert first["counts"] == {
        "unchanged-origin-obstruction": 5725962, "new-strict-full-outer-type": 2242453,
        "pending": 125730, "unchanged-strict-pair-type": 183487}
    assert second["parent_report_sha256"] == sha(paths[2])
    assert (second["previous_pending_full_types"], second["pending_full_types"]) == (125730, 65210)
    assert second["counts"] == {"new-strict-full-outer-type": 60520, "pending": 65210}
    assert full["parent_report_sha256"] == sha(paths[3])
    assert full["counts"] == {"strict-complete-type-force": 65206, "pending": 4}
    adoption = final["actual_parent_adoption"]
    assert adoption["parent_report_sha256"] == sha(paths[4])
    assert (adoption["previous_pending_full_types"], adoption["new_strict_types"],
            adoption["pending_full_types"]) == (4, 4, 0)
    assert final["selected_original_proposal_pending_indices"] == [8270950, 8272018, 8272025, 8272028]
    assert sum((5725962, 183487, 2242453, 60520, 65206, 4)) == 8277632
    assert b15["original_catalog_types"] == 16790546 and b15["pending_full_types"] == 0
    assert b15["counts"] == {"strict-complete-type-force": 828, "nonstrict-same-root-core": 1}
    assert b15["every_actual_current_residual_source_index_partitioned_once"]
    assert b15["previous_attaining_core_payment_preserved_nonstrict_not_recast_as_strict"]
    assert core["N"] == 23 and core["B"] == 15
    for field in (
        "root_interval_certificate_freshly_recomputed",
        "same_root_entire_disk_upper_freshly_recomputed",
        "all_local_exact_principal_minors_and_perturbation_gap_recomputed",
        "all_30653_core_angle_nodes_freshly_replayed",
        "whole_core_lower_bound_is_nonstrict_same_root_not_strict_upper_exclusion"):
        assert core[field]
    own = next(record for record in budget["orders"] if record["N"] == 23)
    assert own["necessary_boundary_internal_families"] == [[13, 10], [14, 9], [15, 8]]
    assert own["fresh_root_report_sha256"] == core["fresh_root_report_sha256"]
    assert b13bytes["file_count"] == 670428 and b13bytes["all_original_bound_files_content_checked"]
    assert b13bytes["current_relocated_files_actually_hashed"] == 121357
    assert b13bytes["absent_files_actually_read_and_hashed_from_original_archives"] == 549071
    assert not b13bytes["mismatches"] and metadata["original_absolute_paths_retained_unchanged"]
    hierarchy = read(RECOVERED / "bulk/n23-B13-hierarchy-audit-complete-cross-volume-resume1.json")
    assert hierarchy["verified"] and hierarchy["coverage_partition_complete"]
    assert hierarchy["disjoint_hierarchy_partition_verified"]
    assert (hierarchy["catalog_types"], hierarchy["pending_types"]) == (1530509, 0)
    assert hierarchy["strict_exclusion_types_with_replayed_certificates"] == 1530509
    assert hierarchy["source_sha256"] == sha(HIGH / "audit_composite_hierarchy.py")
    assert hierarchy["original_map_auditor_sha256"] == sha(HIGH / "audit_streamed_hierarchy.py")
    assert hierarchy["composite_union_auditor_sha256"] == sha(HIGH / "certified_receipt_union.py")
    return paths, data, b13bytes


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    rootpaths, rootdata, oldbytes = checked_roots()
    output.mkdir()
    integritydir = ROOT / "n23-B13-current-all-byte-integrity-v1"
    localledger, archiveledger = integritydir / "LOCAL-FILES.jsonl", integritydir / "ARCHIVE-FILES.jsonl"
    assert sha(localledger) == oldbytes["local_ledger_sha256"]
    assert sha(archiveledger) == oldbytes["archive_ledger_sha256"]
    fallback = {}
    with archiveledger.open(encoding="ascii") as stream:
        for line in stream:
            item = json.loads(line, object_pairs_hook=no_duplicate_keys)
            assert item["key"] not in fallback
            fallback[item["key"]] = (item["sha256"], item["archive"])
    assert len(fallback) == 549071
    bindings, origins, reused_archives = {}, {}, {}
    queue, inspected = deque(), set()
    def eligible_report(path):
        return path.name == "VERIFIED.json" or path.name.endswith("-verified.json")
    def add(path, digest=None, origin="bound-proof-premise"):
        path = Path(path).resolve()
        assert path.is_relative_to(INCOMING) or path.is_relative_to(DEPENDENCIES), (
            "proof binding outside explicitly reviewed recovered/incoming/dependency scope", path)
        if digest is None:
            digest = sha(path)
        assert type(digest) is str and len(digest) == 64
        if path in bindings:
            assert bindings[path] == digest, ("conflicting accepted proof byte identities", path)
            return
        if not path.is_file():
            assert path.is_relative_to(WORK) or path.is_relative_to(RECOVERED / "bulk")
            key = ("workspace/"+path.relative_to(WORK).as_posix() if path.is_relative_to(WORK)
                   else "bulk/"+path.relative_to(RECOVERED / "bulk").as_posix())
            assert key in fallback and fallback[key][0] == digest, ("missing original proof byte", path)
            reused_archives[key] = {"sha256": digest, "archive": fallback[key][1]}
            return
        bindings[path], origins[path] = digest, origin
        if eligible_report(path):
            queue.append(path)
    for path in rootpaths:
        add(path, origin="explicit-full-source-or-final-root")
    for path in (
        Path(__file__), localledger, archiveledger,
        ROOT / "N23-N24-COVER-AND-FULL-PEEL-INDUCTION-v1.md",
        ROOT / "N23-SAME-ROOT-CORE-AND-GLOBAL-ASSEMBLY-INTERFACE-v1.md",
        RECOVERED / "bulk/n23-B13-hierarchy-audit-complete-cross-volume-resume1.json",
        ROOT / "n23-B13-final-archive-metadata-v1/N23-B13-CATALOGUE-SNAPSHOT-cross-volume-resume1.json",
        ROOT / "n23-B13-final-archive-metadata-v1/n23-B13-full-disjoint-replayed-union-resume1.json"):
        add(path)
    with localledger.open(encoding="ascii") as stream:
        count = 0
        for line in stream:
            item = json.loads(line, object_pairs_hook=no_duplicate_keys)
            parts = item["key"].split("/")
            assert parts[0] in ("workspace", "bulk") and ".." not in parts
            path = (WORK if parts[0] == "workspace" else RECOVERED / "bulk").joinpath(*parts[1:])
            add(path, item["sha256"], "original-B13-current-local-byte-premise")
            count += 1
        assert count == 121357
    for name, archive in oldbytes["archive_bindings"].items():
        assert Path(name).name == name
        add(INCOMING / name, archive["archive_sha256"], "original-B13-complete-member-verified-archive")
        add(INCOMING / (name+".meta.json"), archive["archive_metadata_sha256"])
    while queue:
        path = queue.popleft()
        if path in inspected:
            continue
        inspected.add(path)
        record = read(path)
        for field in ("frozen_files", "files_relative_to_workspace"):
            values = record.get(field, {})
            assert isinstance(values, dict)
            for name, digest in values.items():
                if field == "files_relative_to_workspace":
                    target = (WORK / name).resolve()
                    assert target.is_relative_to(WORK)
                else:
                    target = Path(name)
                    assert target.is_absolute()
                add(target, digest)
    print("N23 complete premise byte closure collected:", len(bindings), "current files/archives,",
          len(reused_archives), "additional archive-only dependencies;",
          "all old original archive members stay in the bound archives", flush=True)
    failures, count = [], 0
    with (output / "CURRENT-INPUTS.jsonl").open("x", encoding="ascii") as ledger:
        for path in sorted(bindings, key=str):
            expected = bindings[path]
            actual = sha(path)
            if actual != expected:
                failures.append({"path": str(path), "expected": expected, "actual": actual})
            ledger.write(json.dumps({"path": str(path), "sha256": expected, "origin": origins[path]},
                                    separators=(",", ":"))+"\n")
            count += 1
            if count % 5000 == 0:
                print("N23 current complete proof-premise contents rebound", count,
                      "/", len(bindings), "differences", len(failures), flush=True)
    publish(output / "ARCHIVE-ONLY-DEPENDENCIES.json", reused_archives)
    assert sha(localledger) == oldbytes["local_ledger_sha256"]
    assert sha(archiveledger) == oldbytes["archive_ledger_sha256"]
    publish(output / "VERIFIED.json", {
        "verified": not failures, "schema": "N23-complete-three-family-source-lower-root-current-premise-byte-closure-v1",
        "N": 23, "required_boundary_families": [13, 14, 15],
        "all_original_catalog_lower_payment_chains_formally_zero": True,
        "complete_original_catalog_counts": [1530509, 8277632, 16790546],
        "actual_same_root_upper_budget_local_and_core_transport_prerequisites_linked": True,
        "current_files_and_whole_archives_checked": count, "mismatches": failures,
        "all_current_content_bindings_checked": not failures,
        "B13_original_all670428_member_byte_theorem_reused_under_unchanged_full_archive_and_local_hashes": True,
        "additional_archive_only_dependencies": len(reused_archives),
        "accepted_premise_reports_recursively_inspected": len(inspected),
        "current_input_ledger_sha256": sha(output / "CURRENT-INPUTS.jsonl"),
        "archive_only_dependency_ledger_sha256": sha(output / "ARCHIVE-ONLY-DEPENDENCIES.json"),
        "explicit_entry_report_hashes": {str(path): sha(path) for path in rootpaths},
        "old_mathematics_reused_unchanged_not_claimed_new_fresh_all_tree_replay": True,
        "not_a_complete_native_reenumeration_or_Lean_formalization": True,
        "source_sha256": sha(Path(__file__)),
        "written_complete_global_assembly_and_final_freeze_still_required": True,
        "global_optimality_proved": False})
    assert not failures
    print("N23 all full proof prerequisites current byte closure accepted;",
          "written global assembly/final freeze still owed", flush=True)


if __name__ == "__main__":
    main()
