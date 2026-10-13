"""Independent whole-content and exact missing-path closure final.

Does not call the importer's gates or claim a new old force/area replay.
"""

import argparse
from copy import deepcopy
import hashlib
import json
import os
from pathlib import Path


def local(text):
    text = str(text).replace("\\", "/")
    if text.startswith("/mnt/") and os.name == "nt":
        return Path(text[5].upper()+":"+text[6:])
    return Path(text)


def norm(text):
    return os.path.normcase(os.path.normpath(str(local(text))))


def sha(path):
    digest = hashlib.sha256()
    with local(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024*1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def read(path):
    return json.loads(local(path).read_text(encoding="utf-8"))


def gate(own):
    if (
        own["schema"] != "N26-qualified-prior-native-byte-and-partition-closure-import-v1"
        or own["verified"] is not True
        or own["all_actual_missing_prior_native_bytes_freshly_content_rehashed"] != 28800
        or own["all_actual_selected_original_native_events_independently_reconstructed"] != 14400
        or own["all_actual_original_stage_partitions_siblings_AND_raw_terminals_reconstructed"] is not True
        or own["all_missing_paths_independently_derived_from_entire38_native_receipts"] is not True
        or own["old_force_area_math_QUALIFIED_reused_NOT_new_entire_geometry_or_force_tree_replay"] is not True
        or own["no_compilation_native_execution_or_historical_receipt_replacement"] is not True
        or own["not_a_latest_current_or_unrestricted_joint_source_acceptance"] is not True
        or own["separate_independent_final_AND_future_actual_latest_current_join_STILL_required"] is not True
        or own["actual_original_U_frontier_unchanged"] != 3922
        or own["actual_original_LOCAL_unchanged"] != "7/800000"
        or own["new_formal_geometric_payments"] != 0 or own["candidate_whole_roots_removed"] != 0
        or any(own[field] is not False for field in (
            "global_lower_bound_proved", "global_optimality_proved", "n27_started"))
        or [row["stage"] for row in own["actual_prior_stages"]]
        != ["n26-force-stage-v"+str(i) for i in range(3, 9)]
        or len(own["actual_invalid_native_byte_launch_AND_partition_controls_rejected"]) != 12
    ):
        raise ValueError("independent native final rejected altered source/import/qualification scope")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    own_path = args.input/"VERIFIED.json"
    own_digest = sha(own_path)
    own = read(own_path)
    gate(own)
    entries, count = {}, 0
    for path, digest in own["all_actual_admitted_input_sha256"].items():
        if norm(path) in entries:
            raise ValueError("native import repeats a dependency through lexical aliases")
        entries[norm(path)] = digest
        if sha(path) != digest:
            raise ValueError("independent native import whole-content mismatch: "+path)
        count += 1
        if count % 500 == 0:
            print(json.dumps({"native_import_dependencies_independently_content_rehashed": count,
                              "new_formal_payments": 0}), flush=True)
    current_path = Path("outputs/n26-current28-six-target-supplemental-current-v1.json").resolve()
    census_path = Path("outputs/n26-exact26-native-dispatch-actual-current-inventory-v1.json").resolve()
    current, census = read(current_path), read(census_path)
    if sha(current_path) != own["actual_proof_time_SIX_current_sha256"]:
        raise ValueError("native final changed actual proof-time parent")
    original = {norm(path): digest for path, digest in current["files"].items()}
    derived, selected_receipts = {}, []
    for row in census["native_receipts"]:
        path = local(row["native_acceptance_path"])
        receipt = read(path)
        if entries.get(norm(path)) != sha(path) or original.get(norm(path)) != sha(path):
            raise ValueError("native final substituted an original native receipt")
        for name, digest in receipt["files"].items():
            target = path.parent/name
            normalized = norm(target)
            if normalized in original:
                if original[normalized] != digest:
                    raise ValueError("native final found disagreement with existing current binding")
            else:
                if normalized in derived and derived[normalized] != digest:
                    raise ValueError("native final found contradictory missing-path commitments")
                derived[normalized] = digest
        if path.parent.name in {"n26-force-stage-v"+str(i) for i in range(3, 9)}:
            selected_receipts.append((path, receipt))
    if (
        len(derived) != 28800 or len(selected_receipts) != 6
        or any(entries.get(path) != digest for path, digest in derived.items())
    ):
        raise ValueError("independent native final did not close exactly the actual missing28800paths")
    events, covered = 0, set()
    caps = [754112, 1555305, 2486507, 3880649]
    for path, receipt in selected_receipts:
        folder = path.parent
        trace = read(folder/"TRACE.json")
        if len(receipt["runs"]) != 2400 or len(trace["events"]) != 2400:
            raise ValueError("native final lost actual selected run/event coverage")
        for index, (run, event) in enumerate(zip(receipt["runs"], trace["events"])):
            if run["event_index"] != index:
                raise ValueError("native final found reordered/repeated native event ownership")
            for name, digest in ((run["result"], run["result_sha256"]),
                                 (run["launch"], run["launch_sha256"])):
                target = norm(folder/name)
                if derived.get(target) != digest or entries.get(target) != digest:
                    raise ValueError("native final did not cover each actual original result/launch")
                covered.add(target)
            data, launch = read(folder/run["result"]), read(folder/run["launch"])
            depth = 1 if event["kind"] == "split" else 0
            if (
                launch["exit_code"] != 0 or launch["event_index"] != index
                or launch["B"] != event["B"] or launch["prefix"] != event["prefix"]
                or launch["depth"] != depth or launch["command"][-1] != "1"
                or launch["command"][-14] != "26"
                or launch["command"][-13] != str(event["B"])
                or launch["command"][-12] != row_path(folder/run["result"])
                or launch["command"][-11] != "10000000"
                or launch["command"][-10:-6] != list(map(str, caps))
                or launch["command"][-6:-3] != ["0", "dfs", "frontier"]
                or launch["command"][-3] != (",".join(map(str, event["prefix"])) if event["prefix"] else "-")
                or launch["command"][-2] != str(depth)
                or data["N"] != 26 or data["B"] != event["B"]
                or data["prefix"] != event["prefix"] or data["frontier_depth"] != depth
                or data["origin_screen"] is not True or data["complete"] is not True
                or data["family_complete"] is not False or data["screen"] is not True
                or data["caps"] != caps or data["scale"] != 10000000
                or data["operation"] != "frontier" or data["mode"] != "dfs"
                or data["global_optimality_proved"] is not False
            ):
                raise ValueError("independent native final found altered original run/source scope")
            events += 1
    if covered != set(derived) or events != 14400:
        raise ValueError("native final has a missing or extra admitted run artifact")
    rejected = []
    for field, value in (
        ("global_lower_bound_proved", True), ("global_optimality_proved", True),
        ("new_formal_geometric_payments", 1),
        ("old_force_area_math_QUALIFIED_reused_NOT_new_entire_geometry_or_force_tree_replay", False),
        ("all_actual_missing_prior_native_bytes_freshly_content_rehashed", 28801),
    ):
        changed = deepcopy(own)
        changed[field] = value
        try:
            gate(changed)
        except ValueError:
            rejected.append(field)
        else:
            raise AssertionError("invalid independent native import scope accepted")
    if sha(own_path) != own_digest:
        raise ValueError("native own acceptance changed during independent final")
    report = {
        "schema": "N26-independent-qualified-prior-native-byte-closure-final-v1",
        "verified": True, "actual_import_acceptance_sha256": own_digest,
        "all_admitted_input_content_independently_rehashed": True,
        "actual_admitted_input_count": count,
        "actual_missing_native_result_launch_paths_independently_closed": len(derived),
        "actual_original_selected_native_events_independently_scope_checked": events,
        "independent_original_receipt_set_and_each_actual_result_launch_coverage_checked": True,
        "old_force_area_mathematics_QUALIFIED_reused_NOT_new_leaf_or_global_replay": True,
        "original_source_partition_reconstruction_is_own_evidence_NOT_claimed_repeated_here": True,
        "independent_false_global_or_import_scope_controls_rejected": rejected,
        "new_formal_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "future_actual_latest_current_AND_unrestricted_joint_admission_STILL_required": True,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "executed_independent_final_sha256": sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report), flush=True)


def row_path(path):
    text = path.resolve().as_posix()
    if os.name == "nt":
        return "/mnt/"+text[0].lower()+text[2:]
    return text


if __name__ == "__main__":
    main()
