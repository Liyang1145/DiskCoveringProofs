"""Exact successive enumeration on a certified radius<=Rstar source partition.

The native U screen and U force/area payments are conservative sufficient
exclusions. They do not make inherited Rstar exclusions unconditional at U.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import sys

import audit_prefix_origin as origin
import audit_prefix_partition as combinatorics
import n26_force as force
import n26_force_angles as angles
import verify_force_forest as forest
import verify_force_stage as base
import verify_multislope_area as area
import verify_partial_area_closures as partial


SCOPE = "at-most-same-root-Rstar-not-original-U"


def local_path(text):
    text = str(text).replace("\\", "/")
    if sys.platform == "win32" and text.startswith("/mnt/"):
        return Path(text[5].upper() + ":" + text[6:])
    if sys.platform != "win32" and len(text) > 2 and text[1] == ":":
        return Path("/mnt/" + text[0].lower() + text[2:])
    return Path(text)


def sha(path):
    return hashlib.sha256(local_path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(local_path(path).read_text(encoding="utf-8"))


def bound(folder):
    report = read(folder / "VERIFIED.json")
    if not report["verified"] or report["global_optimality_proved"]:
        raise ValueError("conditional stage source is not accepted")
    inventory = [folder / "VERIFIED.json"]
    for name, digest in {**report["files"], **report.get("additional_files", {})}.items():
        path = folder / name
        if sha(path) != digest:
            raise ValueError("conditional stage source byte changed: " + name)
        inventory.append(path)
    for text, digest in report.get("source_files", {}).items():
        if sha(text) != digest:
            raise ValueError("conditional stage historical dependency byte changed")
        inventory.append(local_path(text))
    return report, inventory


def scope_gate(manifest, accepted, source, basis):
    families = accepted.get("families", accepted.get("conditional_frontier_families"))
    if (manifest["schema"] != "N26-successive-radius-conditional-stage-input-bindings-v1"
            or manifest["radius_scope"] != SCOPE or accepted["radius_scope"] != SCOPE
            or source["radius_scope"] != SCOPE
            or source["families"] != families
            or F(manifest["screen_radius_threshold"]) != force.U
            or F(manifest["radius_upper"]) != F(accepted["radius_upper"])
            or F(manifest["radius_upper"]) != F(basis["radius_upper"])
            or F(basis["radius_upper"]) != F(basis["r_strict_interval"][1])
            or not 0 < F(basis["radius_upper"]) < force.U
            or not basis["same_root_continuous_entire_disk_cover_replayed"]
            or manifest["inherited_source_is_unconditional_at_U"] is not False):
        raise ValueError("conditional source was promoted to U, changed radius, or lost families")


def input_gate(folder, area_folder):
    manifest = read(folder / "MANIFEST.json")
    for name, digest in manifest["copied_files"].items():
        if sha(folder / name) != digest:
            raise ValueError("conditional stage sealed input changed")
    if (manifest["kernel_source_sha256"] != base.KERNEL_SOURCE
            or manifest["kernel_binary_sha256"] != base.KERNEL_BINARY
            or sha(folder / "TRACE.json") != manifest["trace_sha256"]):
        raise ValueError("conditional stage native kernel or trace changed")
    source, accepted = read(folder / "SOURCE-FRONTIER.json"), read(folder / "SOURCE-ACCEPTANCE.json")
    source_folder = local_path(manifest["source_acceptance_original_path"]).parent
    actual, inventory = bound(source_folder)
    published_source = local_path(manifest["source_published_replay"])
    if (actual != accepted or read(published_source) != accepted
            or sha(published_source) != manifest["source_published_replay_sha256"]
            or sha(folder / "SOURCE-ACCEPTANCE.json") != manifest["source_acceptance_sha256"]
            or sha(folder / "SOURCE-FRONTIER.json") != manifest["source_frontier_sha256"]
            or accepted["files"][manifest["source_acceptance_key"]] != manifest["source_frontier_sha256"]
            or sha(local_path(manifest["source_frontier_original_path"])) != manifest["source_frontier_sha256"]):
        raise ValueError("conditional starting partition lacks a bound actual published acceptance")
    inventory.extend([published_source, local_path(manifest["source_frontier_original_path"])])
    basis_folder = local_path(manifest["radius_basis"])
    basis, paths = bound(basis_folder)
    inventory.extend(paths)
    basis_replay = local_path(manifest["radius_basis_published_replay"])
    if (read(basis_replay) != basis
            or sha(basis_folder / "VERIFIED.json") != manifest["radius_basis_acceptance_sha256"]
            or read(folder / "RADIUS-BASIS-ACCEPTANCE.json") != basis
            or sha(folder / "CANDIDATE-PATH.json") != basis["files"]["CATALOG-SOURCE/CANDIDATE-PATH.json"]):
        raise ValueError("conditional stage radius basis or candidate positive control changed")
    inventory.append(basis_replay)
    scope_gate(manifest, accepted, source, basis)
    area_accepted, paths = bound(area_folder)
    inventory.extend(paths)
    if sha(area_folder / "VERIFIED.json") != manifest["area_acceptance_sha256"]:
        raise ValueError("conditional area source changed")
    for name in ("verify_degree_area.py", "verify_multislope_area.py", "exact_arcs.py"):
        if sha(folder / name) != area_accepted["files"][name]:
            raise ValueError("conditional stage imported different area arithmetic")
    for module in (base, force, angles, partial, forest, area, area.base, origin, combinatorics):
        name = Path(module.__file__).name
        if sha(module.__file__) != manifest["copied_files"][name]:
            raise ValueError("conditional stage executed arithmetic different from sealed base: " + name)
    old, multi = read(area_folder / "CERTIFICATE.json"), read(area_folder / "MULTISLOPE-CERTIFICATE.json")
    area.parameter_gate(multi)
    native = read(folder / "NATIVE-VERIFIED.json")
    if not native["verified_implementation_agreement"]:
        raise ValueError("conditional native agreement absent")
    for name, digest in native["files"].items():
        if sha(folder / name) != digest:
            raise ValueError("conditional native sibling evidence changed")
    trace = read(folder / "TRACE.json")
    if (trace["schema"] != "N26-successive-radius-conditional-stage-trace-v1"
            or trace["N"] != 26 or trace["radius_scope"] != SCOPE
            or F(trace["radius_threshold"]) != force.U
            or trace["full_catalog_complete"] or trace["global_optimality_proved"]):
        raise ValueError("conditional stage trace overclaims its domain")
    return manifest, source, accepted, basis, old, multi, native, trace, inventory


def replay(folder, source, old, multi, native, trace, arcs, radius, candidate):
    frontier, ledger, margins = base.replay_trace(folder, source, old, multi, native, trace, arcs)
    owners = [row for row in frontier["pending_states"] if row["B"] == 16
              and candidate["prefix"][:len(row["prefix"])] == row["prefix"]]
    if (len(owners) != 1 or owners[0]["prefix"] != candidate["prefix"]
            or owners[0]["faces"] != candidate["states"][-1]["faces"]
            or not owners[0]["terminal"]
            or candidate["prefix"] not in trace["terminal_pending_prefixes"]["16"]):
        raise ValueError("conditional stage lost the known exact candidate complete terminal")
    frontier.update({
        "schema": "N26-successive-radius-conditional-force-angular-frontier-v1",
        "radius_scope": SCOPE, "radius_upper": str(radius), "screen_radius_threshold": str(force.U),
        "inherited_source_is_unconditional_at_U": False,
        "known_candidate_unique_complete_terminal": candidate["prefix"],
        "original_U_frontier_rewritten": False})
    return frontier, ledger, margins


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--area-bundle", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    manifest, source, accepted, basis, old, multi, native, trace, inventory = input_gate(args.input, args.area_bundle)
    digests = {combinatorics.linux(path): sha(path) for path in inventory}
    candidate, radius = read(args.input / "CANDIDATE-PATH.json"), F(manifest["radius_upper"])
    arcs = force.load_trig(args.input)[0]
    frontier, ledger, margins = replay(args.input, source, old, multi, native, trace, arcs, radius, candidate)
    controls = base.regular_ring_controls(arcs)
    negatives = []

    def reject(label, call):
        try:
            call()
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("invalid conditional stage accepted: " + label)

    bad = deepcopy(manifest)
    bad["radius_scope"] = "unconditional-original-U"
    reject("conditional-frontier-promoted-to-unconditional-U", lambda: scope_gate(bad, accepted, source, basis))
    bad = deepcopy(manifest)
    bad["radius_upper"] = str(force.U)
    reject("same-root-radius-endpoint-replaced-by-screen-threshold", lambda: scope_gate(bad, accepted, source, basis))
    bad_source = deepcopy(source)
    bad_source["families"][0]["pending_subtrees"] += 1
    reject("conditional-source-family-changed", lambda: scope_gate(manifest, accepted, bad_source, basis))
    bad = deepcopy(trace)
    bad["pending_prefixes"]["14"].pop()
    reject("lost-conditional-pending-sibling",
           lambda: replay(args.input, source, old, multi, native, bad, arcs, radius, candidate))
    bad_native = deepcopy(native)
    bad_native["runs"].pop()
    reject("missing-conditional-native-event",
           lambda: replay(args.input, source, old, multi, bad_native, trace, arcs, radius, candidate))
    bad = deepcopy(trace)
    next(row for row in bad["events"] if row["kind"] == "split")["all_child_count"] += 1
    reject("changed-conditional-complete-sibling-count",
           lambda: replay(args.input, source, old, multi, native, bad, arcs, radius, candidate))
    first = next(row for row in trace["events"] if row["kind"] == "force_tree")
    ref = origin.OriginReference(26, first["B"], "dfs", caps=force.CAPS, scale=force.D)
    state = ref.resolve(tuple(first["prefix"]))
    spec = {"N": 26, "B": first["B"], "next": state.next_vertex, "faces": list(state.faces)}
    bad_nodes = deepcopy(first["nodes"])
    split = next(row for row in bad_nodes if row["kind"] == "SPLIT")
    split["children"][1] = split["children"][0]
    reject("conditional-angular-closed-half-lost", lambda: angles.verify_angular_tree(spec, bad_nodes, arcs))
    bad_nodes = deepcopy(first["nodes"])
    bad_nodes.append({"kind": "EMPTY"})
    reject("conditional-angular-hidden-node", lambda: angles.verify_angular_tree(spec, bad_nodes, arcs))
    bad_candidate = deepcopy(candidate)
    bad_candidate["prefix"] = bad_candidate["prefix"][:-1]
    reject("candidate-full-terminal-replaced-by-ancestor",
           lambda: replay(args.input, source, old, multi, native, trace, arcs, radius, bad_candidate))
    for name, value in (("FRONTIER.json", frontier), ("LOWER-LEDGER.json", ledger)):
        area.base.publish_or_match(args.input / name, value)
    kinds = {kind: sum(row[kind] for row in frontier["families"]) for kind in base.KINDS}
    files = ["MANIFEST.json", "TRACE.json", "NATIVE-VERIFIED.json", "FRONTIER.json", "LOWER-LEDGER.json",
             *manifest["copied_files"]]
    report = {
        "schema": "N26-successive-radius-conditional-force-angular-stage-acceptance-v1",
        "verified": True, "radius_scope": SCOPE, "radius_upper": str(radius),
        "r_strict_interval": basis["r_strict_interval"], "screen_radius_threshold": str(force.U),
        "source_acceptance_sha256": manifest["source_acceptance_sha256"],
        "radius_basis_acceptance_sha256": manifest["radius_basis_acceptance_sha256"],
        "source_conditional_pending_subtrees": len(source["pending_states"]),
        "native_events_independently_replayed": len(trace["events"]), "event_counts": kinds,
        "new_strict_radius_conditional_whole_transport_subtrees_excluded":
            kinds["force"] + kinds["force_tree"] + kinds["area"],
        "new_combinatorially_empty_subtrees": kinds["empty"],
        "complete_angle_tree_nodes": sum(row["nodes"] for row in ledger if row["kind"] == "force_tree"),
        "all_incoming_angle_boxes_covered": True,
        "minimum_strict_force_margin_above_conservative_U": str(min(margins)) if margins else None,
        "U_force_area_and_screen_bounds_used_only_as_sufficient_conditions_on_Rstar_source": True,
        "inherited_source_is_unconditional_at_U": False,
        "feasible_regular_ring_regression_controls": controls,
        "families": frontier["families"],
        "pending_cover_transport_subtrees": len(frontier["pending_states"]),
        "conditional_frontier_pending_subtrees": len(frontier["pending_states"]),
        "known_candidate_unique_complete_34_face_terminal": candidate["prefix"],
        "older_forests_and_original_native_queues_preserved": True,
        "original_U_frontier_nodes_removed_by_this_conditional_bundle": 0,
        "unrestricted_reduction_final_joint_acceptance": False, "formal_machine_geometry_proof": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "n27_started": False,
        "negative_controls_rejected": negatives,
        "files": {name: sha(args.input / name) for name in dict.fromkeys(files)},
        "source_files": digests, "executed_checker_sha256": sha(__file__)}
    if report["executed_checker_sha256"] != report["files"]["verify_conditional_force_stage.py"]:
        raise ValueError("conditional stage executed a different sealed checker")
    for text, digest in digests.items():
        if sha(text) != digest:
            raise ValueError("conditional stage historical source changed during replay")
    for name, digest in manifest["copied_files"].items():
        if sha(args.input / name) != digest:
            raise ValueError("conditional stage sealed input changed during replay")
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key not in ("files", "source_files")}, indent=2), flush=True)


if __name__ == "__main__":
    main()
