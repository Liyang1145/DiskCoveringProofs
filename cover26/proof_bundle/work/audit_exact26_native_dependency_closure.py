"""Audit native receipt dependency closure against actual current bindings.

Reports missing/unequal explicit bindings honestly. No parent receipt or
frozen source is changed, and no acceptance is written.
"""

import argparse
from collections import Counter
import json
import os
from pathlib import Path

from audit_prefix_partition import linux
import inventory_exact26_native_dispatch_interfaces as inventory
import verify_conditional_force_stage as binding


def key(path):
    return os.path.normcase(os.path.normpath(str(binding.local_path(path))))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    census_path = Path("outputs/n26-exact26-native-dispatch-actual-current-inventory-v1.json")
    census = binding.read(census_path)
    current_path = Path("outputs/n26-current28-six-target-supplemental-current-v1.json")
    if binding.sha(current_path) != inventory.CURRENT_SHA:
        raise ValueError("native dependency audit changed the actual current identity")
    current = binding.read(current_path)
    actual, aliases = {}, {}
    for text, digest in current["files"].items():
        normalized = key(text)
        if normalized in actual and actual[normalized] != digest:
            raise ValueError("current bindings disagree through lexical path aliases")
        actual[normalized] = digest
        aliases[normalized] = text
    selected_hashes = {linux(census_path): binding.sha(census_path),
                       linux(current_path): inventory.CURRENT_SHA,
                       linux(Path(__file__)): binding.sha(__file__)}
    native_extensions = Counter()
    all_native_variants = {}
    for text, digest in current["files"].items():
        path = binding.local_path(text)
        if path.suffix in (".cpp", ".linux", ".exe"):
            native_extensions[path.name] += 1
            all_native_variants.setdefault(path.name, {}).setdefault(digest, []).append(text)
    rows, missing, disagreements, unique = [], {}, {}, {}
    for record in census["native_receipts"]:
        path = binding.local_path(record["native_acceptance_path"])
        digest = binding.sha(path)
        if actual.get(key(path)) != digest:
            raise ValueError("census selected an unbound/changed actual native receipt")
        selected_hashes[linux(path)] = digest
        native = binding.read(path)
        if (
            native["schema"] != "N26-force-forest-native-reference-agreement-v1"
            or native["verified_implementation_agreement"] is not True
            or native["geometric_lower_bound_accepted_by_this_report"] is not False
            or native["global_optimality_proved"] is not False
            or len(native["runs"]) != native["native_events_checked"]
        ):
            raise ValueError("native receipt scope/event coverage changed")
        absent, unequal = [], []
        for name, expected in native["files"].items():
            dependency = path.parent/name
            normalized = key(dependency)
            if normalized in unique and unique[normalized] != expected:
                raise ValueError("native source receipts disagree on the same dependency")
            unique[normalized] = expected
            item = {"path": linux(dependency), "expected_sha256": expected,
                    "native_receipt": linux(path)}
            if normalized not in actual:
                absent.append(item)
                missing[normalized] = item
            elif actual[normalized] != expected:
                item["actual_current_sha256"] = actual[normalized]
                unequal.append(item)
                disagreements[normalized] = item
        runs_unlisted = []
        for index, run in enumerate(native["runs"]):
            if (
                run["event_index"] != index
                or native["files"].get(run["result"]) != run["result_sha256"]
                or native["files"].get(run["launch"]) != run["launch_sha256"]
            ):
                runs_unlisted.append(index)
        if runs_unlisted:
            raise ValueError("native receipt omitted/changed a run result or launch dependency")
        rows.append({
            "actual_native_receipt": linux(path), "actual_events": len(native["runs"]),
            "declared_native_dependencies": len(native["files"]),
            "native_dependency_paths_missing_from_actual_current": len(absent),
            "native_dependency_digest_disagreements_with_actual_current": len(unequal),
        })
    if any(binding.sha(path) != digest for path, digest in selected_hashes.items()):
        raise ValueError("native closure audit inputs changed")
    report = {
        "schema": "N26-exact26-native-receipt-current-dependency-closure-audit-v1",
        "verified": False, "actual_current_sha256": inventory.CURRENT_SHA,
        "selected_input_sha256": selected_hashes,
        "all_cpp_linux_exe_names_in_actual_current_not_only_peel_prefix": dict(native_extensions),
        "all_native_code_binary_variants": all_native_variants,
        "actual_native_receipt_count": len(rows),
        "native_receipt_unique_dependency_paths": len(unique),
        "missing_explicit_native_dependency_current_bindings": len(missing),
        "unequal_explicit_native_dependency_current_bindings": len(disagreements),
        "missing_bindings": list(missing.values()),
        "unequal_bindings": list(disagreements.values()),
        "receipt_conservation_rows": rows,
        "native_dependencies_NOT_falsely_claimed_freshly_content_rehashed_here": True,
        "missing_binding_is_NOT_by_itself_a_new_mathematical_counterexample": True,
        "no_old_current_header_or_frozen_evidence_modified": True,
        "complete_native_event_geometry_dispatch_audit_still_required": True,
        "new_formal_geometric_payments": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "actual_native_receipt_count": len(rows),
        "native_receipt_unique_dependency_paths": len(unique),
        "missing_explicit_native_dependency_current_bindings": len(missing),
        "unequal_explicit_native_dependency_current_bindings": len(disagreements),
        "all_cpp_linux_exe_names_in_actual_current": dict(native_extensions),
        "formal_payments": 0,
    }), flush=True)


if __name__ == "__main__":
    main()
