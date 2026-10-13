"""Census of native/dispatch variants in the ACTUAL completed SIX inventory.

Read-only inspection of original receipts; this is not acceptance, fresh
whole mathematical replay, global closure or geometric payment.
"""

import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path

from audit_prefix_partition import linux
import verify_conditional_force_stage as binding


CURRENT_SHA = "c85e130c935e68e2275e53fa457c9c4d95d8be5416b128f4307a76061057911b"
FINAL_SHA = "7c2d29f19f310de58d03a2043fae3dde8bcaeb69635843086118a91ab9b6db4e"
DISPATCH = {
    "verify_force_forest.py", "verify_force_stage.py",
    "verify_conditional_force_stage.py", "verify_conditional_force_stage_sparse.py",
    "n26_sparse_stage_controls.py", "audit_force_forest_native.py",
    "audit_force_forest_native_absolute.py",
}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    current_path = Path("outputs/n26-current28-six-target-supplemental-current-v1.json")
    final_path = Path("outputs/n26-current28-six-target-supplemental-independent-final-v1.json")
    if binding.sha(current_path) != CURRENT_SHA or binding.sha(final_path) != FINAL_SHA:
        raise ValueError("native census changed actual proof-time current/final identity")
    current, final = binding.read(current_path), binding.read(final_path)
    if (
        current["Rstar_conditional_frontier_pending_subtrees"] != 5637
        or current["candidate_angle_unresolved_closed_boxes"] != 25
        or final["current_audit_sha256"] != CURRENT_SHA
        or final["all_current_file_digests_rehashed"] is not True
        or final["current_file_digests_rechecked"] != len(current["files"])
        or current["global_optimality_proved"] is not False
    ):
        raise ValueError("native census requires actual completed SIX/current scope")
    variants, native_paths, bindings = defaultdict(lambda: defaultdict(list)), [], {}
    for text, digest in current["files"].items():
        path = binding.local_path(text)
        name = path.name
        if (
            name in DISPATCH or name == "NATIVE-VERIFIED.json"
            or name.startswith("peel") and path.suffix in (".cpp", ".linux")
        ):
            if binding.sha(path) != digest:
                raise ValueError("actual bound native/dispatch bytes changed: "+text)
            bindings[text] = digest
            if name == "NATIVE-VERIFIED.json":
                native_paths.append(path)
            else:
                variants[name][digest].append(text)
    rows, schemas, mechanisms, event_total = [], Counter(), Counter(), 0
    for index, path in enumerate(native_paths):
        native = binding.read(path)
        schemas[native["schema"]] += 1
        trace_path = path.parent/"TRACE.json"
        if not trace_path.exists() or linux(trace_path) not in current["files"]:
            rows.append({
                "native_acceptance_path": linux(path), "schema": native["schema"],
                "has_actual_bound_TRACE": False, "keys": sorted(native),
            })
            continue
        digest = binding.sha(trace_path)
        if current["files"][linux(trace_path)] != digest:
            raise ValueError("actual native trace changed")
        bindings[linux(trace_path)] = digest
        trace = binding.read(trace_path)
        counts = Counter(row["kind"] for row in trace.get("events", []))
        mechanisms.update(counts)
        event_total += sum(counts.values())
        manifests = []
        for name in ("MANIFEST.json", "VERIFIED.json"):
            selected = path.parent/name
            text = linux(selected)
            if text in current["files"]:
                sha = binding.sha(selected)
                if sha != current["files"][text]:
                    raise ValueError("actual native manifest/acceptance changed")
                bindings[text] = sha
                data = binding.read(selected)
                manifests.append({
                    "name": name, "path": text, "schema": data.get("schema"),
                    "verified": data.get("verified"),
                    "kernel_source_sha256": data.get("kernel_source_sha256"),
                    "kernel_binary_sha256": data.get("kernel_binary_sha256"),
                    "executed_checker_file": data.get("executed_checker_file"),
                    "executed_checker_sha256": data.get("executed_checker_sha256"),
                    "actual_trace_sha256": data.get("trace_sha256"),
                    "radius_scope": data.get("radius_scope"),
                })
        rows.append({
            "native_acceptance_path": linux(path), "schema": native["schema"],
            "has_actual_bound_TRACE": True, "actual_bound_trace_path": linux(trace_path),
            "trace_schema": trace.get("schema"), "N": trace.get("N"),
            "radius_scope": trace.get("radius_scope"),
            "native_declared_events_checked": native.get("native_events_checked"),
            "actual_native_run_rows": len(native.get("runs", [])),
            "actual_event_rows": sum(counts.values()), "actual_event_kinds": dict(counts),
            "candidate_full_payment_dispatch_inventory_still_required": True,
            "actual_bound_manifest_AND_acceptance_headers": manifests,
        })
        if (index+1) % 10 == 0:
            print(json.dumps({"actual_native_receipts_inventoried": index+1,
                              "actual_trace_events_inventoried": event_total,
                              "formal_payments": 0}), flush=True)
    if any(binding.sha(path) != digest for path, digest in bindings.items()):
        raise ValueError("native inventory changed during census")
    report = {
        "schema": "N26-exact26-native-dispatch-actual-current-inventory-audit-v1",
        "verified": False, "actual_current_sha256": CURRENT_SHA, "actual_final_sha256": FINAL_SHA,
        "actual_parent_current_file_count": len(current["files"]),
        "native_AND_dispatch_bound_file_variants": {
            name: [{"sha256": digest, "actual_bound_copy_count": len(paths), "actual_paths": paths}
                   for digest, paths in sorted(by_digest.items())]
            for name, by_digest in sorted(variants.items())
        },
        "actual_native_receipt_schema_counts": dict(schemas),
        "actual_native_receipts_inventoried": len(native_paths),
        "actual_native_trace_events_inventoried": event_total,
        "actual_native_trace_payment_kinds_inventoried": dict(mechanisms),
        "native_receipts": rows, "freshly_checked_selected_input_sha256": bindings,
        "all_other273k_parent_files_NOT_falsely_claimed_freshly_rehashed_here": True,
        "inventory_only_NOT_native_event_semantic_or_force_tree_replay": True,
        "no_native_binary_compilation_or_execution_claimed": True,
        "actual_full_native_AND_all_advanced_model_dispatch_source_audit_still_required": True,
        "new_formal_geometric_payments": 0, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "executed_inventory_checker_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "actual_native_receipts_inventoried": len(native_paths),
        "actual_native_trace_events_inventoried": event_total,
        "native_receipt_schemas": dict(schemas), "native_event_kinds": dict(mechanisms),
        "actual_distinct_variants_by_filename": {
            name: len(values) for name, values in sorted(variants.items())},
        "formal_payments": 0, "inventory_NOT_semantic_acceptance": True,
    }), flush=True)


if __name__ == "__main__":
    main()
