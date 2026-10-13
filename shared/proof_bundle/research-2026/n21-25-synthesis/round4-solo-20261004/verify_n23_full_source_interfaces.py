"""Bind written N23 cover/peeling review to all three actual full sources.

This binds source-level mathematical reasoning and checks actual historical
source entry points. It is not a Lean proof, fresh native enumeration or a
replacement for each full lower-payment chain.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse
import hashlib
import json
import sys
import zipfile

ROOT = Path(__file__).resolve().parent
HIGH = ROOT.parent / "round3-high"
WORK = ROOT.parents[2]
sys.path.insert(0, str(HIGH))
from stream_catalog import sha, no_duplicate_keys
from n25_outer_search import read, publish
from audit_n23_B15_origin_catalog import input_gate

assert __debug__
DEGREE_SHA = "5d88bffdc65eb8e19c92ef3eb8732c0ad9ef5868ea18a186074ff759ed8bb6ca"
B15_BINARY_SHA = "765abf10d2276628e5c6d88ed5061bbe71f8f9fadb5135d30a1f4b507546a90e"


def segment(text, start, stop):
    assert text.count(start) == 1
    first = text.index(start)
    return text[first:text.index(stop, first)].strip()


def source_derivation():
    degree = (HIGH / "peel_degree.cpp").read_text(encoding="utf8")
    assert sha(HIGH / "peel_degree.cpp") == DEGREE_SHA
    result = []
    for name in ("peel_paid_stream_kernel.inc", "peel_search_stage_kernel.inc"):
        text = (HIGH / name).read_text(encoding="utf8")
        assert segment(degree, "bool possible(State const&s){",
                       "\npair<vector<uint32_t>,int> canonical") == segment(
                           text, "bool possible(State const&s){",
                           "\npair<vector<uint32_t>,int> canonical")
        assert segment(degree, "pair<vector<uint32_t>,int> canonical(State const&s){",
                       "\n}\n") == segment(
                           text, "pair<vector<uint32_t>,int> canonical(State const&s){",
                           "\n}\n")
        assert segment(degree, " int pick=pending.size()-1;",
                       "\n}\n\nint main") == segment(
                           text, " int pick=pending.size()-1;",
                           "\n}\n\nint main")
        assert segment(degree, " bool exposed_to_future[MAXN]{};",
                       "\n if(pending.empty())") == segment(
                           text, " bool exposed_to_future[MAXN]{};",
                           "\n if(already_paid(s))")
        assert "faces_needed=2*n-b-2;" in text
        assert "initial.next=b;" in text
        assert "if(possible(initial))visit(initial,{{boundary,n-b}});" in text
        assert "if(limit&&calls>=limit)throw runtime_error(" in text
        result.append({
            "source": name, "source_sha256": sha(HIGH / name),
            "possible_canonical_minimum_degree_and_entire_peeling_body_literally_equal": True,
            "same_full_initial_region_and_exact_face_budget": True})
    return result


def original_snapshot_json(key):
    auditdir = ROOT / "n23-B13-current-all-byte-integrity-v1"
    report = read(auditdir / "VERIFIED.json")
    assert report["verified"] and report["all_original_bound_files_content_checked"]
    assert report["file_count"] == 670428 and not report["mismatches"]
    assert report["original_snapshot_sha256"] == "64578536865f5078df43decda920f9043468f4fc35f1457bdf8cd0af6a8f6f79"
    path = ROOT.parents[3].joinpath(*key.split("/")).resolve()
    assert path.is_relative_to(ROOT.parents[3])
    if path.is_file():
        return read(path), {"key": key, "sha256": sha(path), "current_file": str(path)}
    ledger = auditdir / "ARCHIVE-FILES.jsonl"
    assert sha(ledger) == report["archive_ledger_sha256"]
    with ledger.open(encoding="ascii") as stream:
        for line in stream:
            item = json.loads(line, object_pairs_hook=no_duplicate_keys)
            if item["key"] == key:
                break
        else:
            raise AssertionError("original source metadata absent from current roots and accepted archives")
    archive = ROOT.parents[4] / item["archive"]
    assert item["archive"] in report["archive_bindings"]
    with zipfile.ZipFile(archive) as stream:
        data = stream.read(key)
    assert len(data) == item["bytes"] and hashlib.sha256(data).hexdigest() == item["sha256"]
    return json.loads(data.decode("utf8"), object_pairs_hook=no_duplicate_keys), {
        "key": key, "archive": item["archive"], "sha256": item["sha256"],
        "archive_sha256": report["archive_bindings"][item["archive"]]["archive_sha256"]}


def b15_gate(summary):
    assert (summary["N"], summary["B"], summary["orbits"]) == (23, 15, 16790546)
    assert summary["complete"] and summary["mode"] == "dfs" and summary["canonical_root_degree_pruning"]
    assert summary["calls"] == 7127057454
    assert summary["catalogue_completeness_requires_written_induction"]
    assert summary["source_sha256"] == sha(HIGH / "peel_degree.cpp") == DEGREE_SHA
    assert summary["binary_sha256"] == sha(HIGH / "peel_degree.exe") == B15_BINARY_SHA
    assert summary["stream_validation_source_sha256"] == sha(HIGH / "enumerate_family_streamed.py")
    assert summary["stream_reader_sha256"] == sha(HIGH / "stream_catalog.py")
    assert summary["constants_sha256"] == sha(ROOT.parent / "evidence/core-reduction/constants/n23.json")
    controls = read(HIGH / "evidence/degree-pruning-regressions-resume1/VERIFIED.json")
    assert controls["verified"] and controls["source_sha256"] == DEGREE_SHA
    assert controls["binary_sha256"] == B15_BINARY_SHA and controls["tests"]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", required=True, type=Path)
    args = ap.parse_args()
    output = args.output.resolve()
    assert output.is_relative_to(ROOT) and not output.exists()
    derivation = source_derivation()
    coverproof = ROOT / "N23-N24-COVER-AND-FULL-PEEL-INDUCTION-v1.md"
    coreproof = ROOT / "N23-SAME-ROOT-CORE-AND-GLOBAL-ASSEMBLY-INTERFACE-v1.md"
    assert sha(coverproof) == "8aca653a57a75546a14aa9d51bd013ebf5c2c2047e02c7a350601d81c958cc58"
    assert sha(coreproof) == "bf8419f836d66352a8d7a7ba914e4a00bb35f83730571869bc107a502ba33c4b"
    # These exact immutable manuscripts are mathematical premises reviewed
    # by the author; checking their hashes is not a machine proof of prose.
    b13summary, b13binding = original_snapshot_json(
        "workspace/research-2026/n21-25-synthesis/round3-high/evidence/n23-B13-paid-streamed-resume1/SUMMARY.json")
    assert b13summary["verified"] and b13summary["complete_residual_family_search"]
    assert (b13summary["N"], b13summary["B"], b13summary["residual_orbits"]) == (23, 13, 1530509)
    assert b13summary["calls"] == 694677316 and b13summary["run_count"] == 134
    assert b13summary["pruned_recursive_states_not_orbit_count"] == 0
    assert b13summary["payment_samples_independently_mapped"] == 0
    assert b13summary["all_sorted_run_union_equality_verified"]
    assert b13summary["source_sha256"] == sha(HIGH / "enumerate_paid_family.py")
    for relative, digest in b13summary["files"].items():
        if relative.endswith(("peel_paid_stream.exe", "peel_paid_stream.cpp",
                              "peel_paid_stream_kernel.inc", "paid_stream_storage.inc",
                              "paid_matcher.inc", "peel_degree.cpp")):
            path = (WORK / relative).resolve()
            assert path.is_relative_to(WORK) and sha(path) == digest
    b14path = ROOT / "n23-B14-complete-source-and-union-reacceptance-20261005-v1/VERIFIED.json"
    b14 = read(b14path)
    assert b14["verified"] and b14["complete_recorded_necessary_family"]
    assert (b14["N"], b14["B"], b14["residual_orbits"]) == (23, 14, 8277632)
    for flag in (
        "all_8726_original_launch_dependencies_explicitly_remapped_and_rehashed",
        "original_production_math_library_storage_and_launcher_gates_freshly_checked",
        "full_root_node_limit_zero_dfs_no_seed_no_prefix_checked",
        "historical_actual_native_zero_terminal_phase_and_source_order_checked",
        "all_original_and_layer_inputs_fresh_complete_union_verified",
        "no_paid_pruned_state_in_this_historical_phase"):
        assert b14[flag]
    dataset = ROOT / "n23-B15-original-archive-dataset-20261005-v1"
    _, gap, originalfrozen = input_gate(dataset)
    assert gap > 0
    b15 = read(dataset / "CATALOG/SUMMARY.json")
    b15_gate(b15)
    negatives = []
    from copy import deepcopy
    for field, value in (
        ("N", 24), ("B", 14), ("complete", False), ("mode", "noscreen"),
        ("orbits", 16790545), ("calls", 1), ("source_sha256", "0"*64),
        ("binary_sha256", "0"*64), ("stream_validation_source_sha256", "0"*64),
        ("constants_sha256", "0"*64)):
        bad = deepcopy(b15)
        bad[field] = value
        try:
            b15_gate(bad)
        except (AssertionError, KeyError):
            negatives.append(field)
        else:
            raise AssertionError("incorrect original full source accepted: "+field)
    frozen = dict(originalfrozen)
    for path in (
        Path(__file__), coverproof, coreproof, b14path,
        ROOT / "n23-B13-current-all-byte-integrity-v1/VERIFIED.json",
        ROOT / "n23-B13-final-archive-metadata-v1/VERIFIED.json",
        ROOT / "n23-B13-final-archive-metadata-v1/N23-B13-CATALOGUE-SNAPSHOT-cross-volume-resume1.json",
        ROOT / "n23-n24-own-family-budget-v1/VERIFIED.json",
        ROOT / "n23-nonstrict-core-fresh-root-upper-local-angle-audit-solo-v1/VERIFIED.json",
        HIGH / "peel_degree.cpp", HIGH / "peel_degree.exe",
        HIGH / "peel_paid_stream_kernel.inc", HIGH / "peel_search_stage_kernel.inc",
        HIGH / "enumerate_family_streamed.py",
        HIGH / "evidence/degree-pruning-regressions-resume1/VERIFIED.json"):
        frozen[str(path)] = sha(path)
    for path, digest in frozen.items():
        assert sha(path) == digest
    output.mkdir()
    publish(output / "VERIFIED.json", {
        "verified": True, "schema": "N23-written-cover-induction-bound-to-three-actual-complete-full-sources-v1",
        "N": 23, "families": [[13, 10], [14, 9], [15, 8]],
        "original_catalog_type_counts": [1530509, 8277632, 16790546],
        "mechanical_full_recursive_degree_and_canonical_source_equalities": derivation,
        "b13_original_summary_byte_binding": b13binding,
        "b13_and_b14_actual_zero_paid_prunes_no_hidden_library_skips": True,
        "b15_actual_original_cpp_binary_degree_controls_and_complete_stream_driver_bound": True,
        "written_cover_transport_and_full_induction_are_reviewed_math_premises_not_hash_proofs": True,
        "original_B15_actual_historical_driver_publishes_only_after_success_and_complete_row_scan": True,
        "not_a_new_native_enumeration_or_Lean_machine_check": True,
        "negative_original_source_controls_rejected": negatives, "frozen_files": frozen,
        "source_sha256": sha(Path(__file__)),
        "all_three_lower_chains_and_same_root_global_integrity_adoption_still_required": True,
        "global_optimality_proved": False})
    print("N23 full source and written-cover/peeling interfaces bound for all three families;",
          "final complete-current-chain global adoption still owed", flush=True)


if __name__ == "__main__":
    main()
