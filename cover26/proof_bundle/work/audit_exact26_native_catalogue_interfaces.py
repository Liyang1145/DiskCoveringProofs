"""Actual bound catalogue/partial native contracts and canonical bijections.

Fresh selected native/canonical semantics, not new force/area/global replay.
"""

import argparse
from collections import Counter, defaultdict
from copy import deepcopy
import json
import os
from pathlib import Path

from audit_prefix_origin import OriginReference
from audit_prefix_partition import check_frontier, linux
import audit_candidate_transport as positive
import n26_force as force
import n26_terminal_canonical as canonical
import verify_conditional_force_stage as binding
import verify_terminal_catalog as catalog


CURRENT_SHA = "c85e130c935e68e2275e53fa457c9c4d95d8be5416b128f4307a76061057911b"
MODULES = (positive, canonical, catalog)


def normalized(path):
    return os.path.normcase(os.path.normpath(str(binding.local_path(path))))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    current_path = Path("outputs/n26-current28-six-target-supplemental-current-v1.json")
    final_path = Path("outputs/n26-current28-six-target-supplemental-independent-final-v1.json")
    if binding.sha(current_path) != CURRENT_SHA:
        raise ValueError("native catalogue audit changed actual proof-time current")
    current, final = binding.read(current_path), binding.read(final_path)
    if (
        final["current_audit_sha256"] != CURRENT_SHA
        or final["all_current_file_digests_rehashed"] is not True
        or final["current_file_digests_rechecked"] != len(current["files"])
        or current["global_optimality_proved"] is not False
    ):
        raise ValueError("native catalogue audit lacks actual completed current/final identity")
    actual = {normalized(path): digest for path, digest in current["files"].items()}
    checked = {linux(current_path): CURRENT_SHA, linux(final_path): binding.sha(final_path)}
    missing = {}
    def load(path, expected=None):
        path = binding.local_path(path)
        digest = binding.sha(path)
        original = actual.get(normalized(path))
        if expected is None:
            expected = original
        if expected is None or digest != expected or (original is not None and original != digest):
            raise ValueError("native catalogue source/data hash not committed: "+str(path))
        if original is None:
            missing[linux(path)] = digest
        checked[linux(path)] = digest
        return binding.read(path)
    variants = {}
    for module in MODULES:
        name = Path(module.__file__).name
        copies = [(path, digest) for path, digest in current["files"].items()
                  if binding.local_path(path).name == name]
        if not copies:
            raise ValueError("actual native source interface has no bound implementation: "+name)
        inspected = binding.sha(module.__file__)
        if any(digest != inspected or binding.sha(path) != digest for path, digest in copies):
            raise ValueError("native source uses an uninspected/changed implementation variant")
        variants[name] = {"actual_bound_copies_rehashed": len(copies), "one_inspected_digest": inspected}
        checked.update(copies)
    groups = defaultdict(list)
    for path, digest in current["files"].items():
        if binding.local_path(path).name == "NATIVE-RUNS.json":
            data = load(path, digest)
            if not isinstance(data, list) or not data:
                raise ValueError("bound native run list is empty or malformed")
            groups[digest].append(binding.local_path(path))
    original_contracts, aliases, found, tables = [], [], Counter(), []
    first_catalog = None
    for digest, paths in groups.items():
        candidates = []
        for path in paths:
            folder = path.parent
            manifest_path = folder/"MANIFEST.json"
            if not manifest_path.exists() or normalized(manifest_path) not in actual:
                continue
            manifest = load(manifest_path)
            runs = load(path, digest)
            first = runs[0]
            launch_path = folder/first["launch"]
            if not launch_path.exists():
                continue
            launch = load(launch_path, first["launch_sha256"])
            command = launch["command"]
            if len(command) < 14:
                raise ValueError("bound native command has no complete explicit argument tail")
            # A copied NATIVE-RUNS list is DATA, not an execution at its copy
            # location. The checksummed launch names the actual output owner.
            if normalized(command[-12]) == normalized(folder/first["result"]):
                candidates.append((folder, manifest, runs))
        if len(candidates) != 1:
            raise ValueError("native run-list digest lacks a unique actual execution owner: "+
                             json.dumps({"digest": digest, "paths": list(map(str, paths)),
                                         "actual_owners": [str(item[0]) for item in candidates]}))
        folder, manifest, runs = candidates[0]
        aliases.append({"actual_native_run_list_sha256": digest,
                        "actual_execution_owner": linux(folder),
                        "all_bound_equal_byte_run_list_paths": list(map(linux, paths))})
        schema = manifest["schema"]
        found[schema] += 1
        if schema == "N26-selected-terminal-catalogue-input-bindings-v1":
            stage = binding.local_path(manifest["source_stage"])
            accepted = load(stage/"VERIFIED.json", manifest["source_acceptance_sha256"])
            if accepted["verified"] is not True or accepted["global_optimality_proved"] is not False:
                raise ValueError("native terminal catalogue source acceptance scope changed")
            source_acceptance = load(folder/"SOURCE-ACCEPTANCE.json", manifest["source_acceptance_sha256"])
            if source_acceptance != accepted:
                raise ValueError("native terminal catalogue copied a different original source acceptance")
            frontier = load(folder/"SOURCE-FRONTIER.json", accepted["files"]["FRONTIER.json"])
            trace = load(folder/"SOURCE-TRACE.json", accepted["files"]["TRACE.json"])
            candidate = load(folder/"CANDIDATE-PATH.json", manifest["copied_files"]["CANDIDATE-PATH.json"])
            for run in runs:
                for field in ("result", "launch"):
                    load(folder/run[field], run[field+"_sha256"])
            table = catalog.reconstruct(folder, stage, accepted, frontier, trace, candidate, runs)
            own = load(folder/"VERIFIED.json")
            stored = load(folder/"CATALOG.json", own["files"]["CATALOG.json"])
            if (
                stored != table or own["schema"] != "N26-accepted-selected-terminal-canonical-catalogue-v1"
                or own["verified"] is not True or own["global_optimality_proved"] is not False
                or own["selected_terminal_paths"] != table["selected_terminal_paths"]
            ):
                raise ValueError("actual terminal catalogue/full face bijections did not reconstruct")
            for name, expected in (("peel_prefix_origin.cpp", catalog.CPP_SHA),
                                   ("peel_prefix_origin.linux", catalog.BINARY_SHA)):
                path = stage/name
                if binding.sha(path) != expected:
                    raise ValueError("native catalogue used a different original kernel")
                checked[linux(path)] = expected
                if normalized(path) not in actual:
                    missing[linux(path)] = expected
            original_contracts.append({
                "actual_folder": linux(folder), "contract": schema,
                "original_terminal_paths_freshly_reconstructed": table["selected_terminal_paths"],
                "canonical_types": table["distinct_selected_canonical_types"],
                "candidate_type_paths_retained": table["selected_candidate_type_paths"],
                "all_full_vertex_face_bijections_checked": True,
                "all_native_solve_runs_and_source_terminal_partition_checked": True,
            })
            tables.append(table)
            if first_catalog is None:
                first_catalog = (folder, stage, accepted, frontier, trace, candidate, runs, table)
        elif schema == "N26-current-partial-prefix-energy-overlay-bindings-v1":
            source = load(folder/"SOURCE-FRONTIER.json")
            stage = binding.local_path(manifest["source_stage"])
            selected = manifest["selected_source_indices"]
            if len(runs) != len(selected) or len(set(selected)) != len(selected):
                raise ValueError("partial native run/source coverage changed")
            refs = {b: OriginReference(26, b, "dfs", caps=force.CAPS, scale=force.D)
                    for b in (14, 15, 16, 17)}
            for index, (source_index, run) in enumerate(zip(selected, runs)):
                row = source["pending_states"][source_index]
                b, prefix = row["B"], tuple(row["prefix"])
                if (
                    row["terminal"] or run["index"] != index or run["source_index"] != source_index
                    or run["B"] != b or run["prefix"] != list(prefix)
                ):
                    raise ValueError("partial native evidence paid a terminal or changed original prefix")
                state = refs[b].resolve(prefix)
                if {"B": b, **refs[b].entry(prefix, state, refs[b].children(state))} != row:
                    raise ValueError("partial native actual original source state did not reconstruct")
                launch = load(folder/run["launch"], run["launch_sha256"])
                native = load(folder/run["result"], run["result_sha256"])
                command = ["/lib64/ld-linux-x86-64.so.2", linux(stage/"peel_prefix_origin.linux"),
                           "26", str(b), linux(folder/run["result"]), str(force.D),
                           *map(str, force.CAPS), "0", "dfs", "frontier",
                           ",".join(map(str, prefix)), "0", "1"]
                if launch["command"] != command or launch["exit_code"] != 0 or native["origin_screen"] is not True:
                    raise ValueError("partial native launch changed actual source/model scope")
                check_frontier(native, refs[b], prefix, 0)
            original_contracts.append({
                "actual_folder": linux(folder), "contract": schema,
                "actual_nonterminal_native_prefixes_reconstructed": len(runs),
                "old_partial_energy_math_QUALIFIED_reused_NOT_freshly_replayed_here": True,
            })
        else:
            raise ValueError("uninspected actual native run-list contract: "+schema)
        print(json.dumps({"actual_original_native_contracts_reconstructed": len(original_contracts),
                          "bound_equal_byte_aliases_identified": len(paths),
                          "latest_contract": schema, "formal_payments": 0}), flush=True)
    # Actual candidate transport positive control: no native re-execution.
    folder = Path("outputs/n26-candidate-transport-control-v1").resolve()
    path_data = load(folder/"CANDIDATE-PATH.json")
    launch = load(folder/"NATIVE-LAUNCH.json")
    native = load(folder/"NATIVE-FINAL.json")
    root_folder = Path("outputs/n26-same-root-cover-v2").resolve()
    system = load(root_folder/"SYSTEM.json")
    target = {frozenset(face) for face in system["all_faces"]}
    prefix, mapping, states = positive.target_path(target)
    if (
        path_data["prefix"] != list(prefix) or path_data["states"] != states
        or {int(k): v for k, v in path_data["native_to_exact_candidate_labels"].items()} != mapping
    ):
        raise ValueError("actual known-cover transport did not preserve every original source face/path")
    command = ["/lib64/ld-linux-x86-64.so.2",
               linux(Path("work/prefix-origin-v1/peel_prefix_origin.linux")),
               "26", "16", linux(folder/"NATIVE-FINAL.json"), str(force.D),
               *map(str, force.CAPS), "0", "dfs", "frontier",
               ",".join(map(str, prefix)), "0", "1"]
    if launch["command"] != command or launch["exit_code"] != 0 or native["origin_screen"] is not True:
        raise ValueError("known-cover native positive-control launch changed")
    check_frontier(native, OriginReference(26, 16, "dfs", caps=force.CAPS, scale=force.D), prefix, 0)
    rejected = []
    folder, stage, accepted, frontier, trace, candidate, runs, table = first_catalog
    def reject(name, action):
        try:
            action()
        except (ValueError, KeyError, IndexError, TypeError):
            rejected.append(name)
        else:
            raise AssertionError("invalid actual native catalogue accepted: "+name)
    reject("missing-original-native-terminal",
           lambda: catalog.reconstruct(folder, stage, accepted, frontier, trace, candidate, runs[:-1]))
    bad = deepcopy(trace)
    next(paths for paths in bad["terminal_pending_prefixes"].values() if paths).pop()
    reject("source-terminal-omitted",
           lambda: catalog.reconstruct(folder, stage, accepted, frontier, bad, candidate, runs))
    bad = deepcopy(runs)
    bad[0]["prefix"] = bad[0]["prefix"][:-1]
    reject("terminal-native-owner-replaced-by-ancestor",
           lambda: catalog.reconstruct(folder, stage, accepted, frontier, trace, candidate, bad))
    row = table["rows"][0]
    bad = deepcopy(row["canonical"]["canonical_bijections"][0])
    bad["vertex_to_canonical"][1] = bad["vertex_to_canonical"][0]
    reject("nonbijective-full-vertex-map", lambda: canonical.check_bijection(
        26, row["B"], row["faces"], row["canonical"]["faces"], bad))
    bad_faces = row["canonical"]["faces"][:]
    bad_faces[0] ^= 1 << 25
    reject("changed-full-face-image", lambda: canonical.check_bijection(
        26, row["B"], row["faces"], bad_faces, row["canonical"]["canonical_bijections"][0]))
    if any(binding.sha(path) != digest for path, digest in checked.items()):
        raise ValueError("actual native catalogue input changed during semantic audit")
    report = {
        "schema": "N26-actual-native-catalogue-partial-and-positive-source-interface-audit-v1",
        "verified": False, "actual_proof_time_current_sha256": CURRENT_SHA,
        "all_bound_native_run_list_files_inventoried": sum(map(len, groups.values())),
        "distinct_actual_native_run_list_execution_contracts": len(groups),
        "actual_contract_schema_counts": dict(found),
        "actual_bound_module_versions": variants,
        "equal_byte_copies_are_bound_DATA_not_distinct_native_executions": aliases,
        "actual_original_native_contracts": original_contracts,
        "all_historical_terminal_paths_freshly_reconstructed": sum(
            table["selected_terminal_paths"] for table in tables),
        "known_cover_all34faces_original26vertex_transport_and_native_frontier_checked": True,
        "known_cover_positive_control_is_NOT_unrestricted_screen_soundness_proof": True,
        "actual_invalid_terminal_ownership_and_full_bijection_controls_rejected": rejected,
        "all_selected_checked_input_sha256": checked,
        "newly_detected_selected_dependency_paths_not_explicit_in_current": missing,
        "old_force_area_partial_energy_math_NOT_falsely_claimed_replayed_here": True,
        "advanced_candidate_model_gauge_box_AND_unrestricted_joint_admission_still_required": True,
        "new_formal_geometric_payments": 0, "candidate_whole_roots_removed": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
        "executed_audit_sha256": binding.sha(__file__),
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as stream:
        stream.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("equal_byte_copies_are_bound_DATA_not_distinct_native_executions",
                                     "actual_original_native_contracts", "all_selected_checked_input_sha256",
                                     "newly_detected_selected_dependency_paths_not_explicit_in_current")}),
          flush=True)


if __name__ == "__main__":
    main()
