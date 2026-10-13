"""Exact current-frontier continuation with complete angular tree leaf support."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_origin import OriginReference
from audit_prefix_partition import check_frontier, linux
from n26_force import CAPS, D, U, angular_domain, force_check, load_trig, rootbox
from n26_force_angles import verify_angular_tree
from verify_partial_area_closures import partial_bound
from verify_force_forest import KERNEL_BINARY, KERNEL_SOURCE, regular_ring_controls
import verify_multislope_area as area


FAMILIES = (14, 15, 16, 17)
KINDS = ("split", "force", "force_tree", "area", "empty", "terminal")


def input_gate(folder, area_folder):
    manifest = json.loads((folder / "MANIFEST.json").read_text())
    for name, digest in manifest["copied_files"].items():
        if area.base.sha(folder / name) != digest:
            raise ValueError("stage input changed")
    if (manifest["kernel_source_sha256"] != KERNEL_SOURCE
            or manifest["kernel_binary_sha256"] != KERNEL_BINARY
            or area.base.sha(folder / "TRACE.json") != manifest["trace_sha256"]):
        raise ValueError("changed native kernel or trace")
    source = json.loads((folder / "SOURCE-FRONTIER.json").read_text())
    accepted = json.loads((folder / "SOURCE-ACCEPTANCE.json").read_text())
    if (not accepted["verified"] or accepted["global_optimality_proved"]
            or area.base.sha(folder / "SOURCE-ACCEPTANCE.json") != manifest["source_acceptance_sha256"]
            or area.base.sha(folder / "SOURCE-FRONTIER.json") != manifest["source_frontier_sha256"]
            or accepted["files"][manifest["source_acceptance_key"]] != manifest["source_frontier_sha256"]
            or source["families"] != accepted["families"]):
        raise ValueError("starting accepted frontier is not bound")
    area_accepted = json.loads((area_folder / "VERIFIED.json").read_text())
    if (not area_accepted["verified"] or area_accepted["global_optimality_proved"]
            or area.base.sha(area_folder / "VERIFIED.json") != manifest["area_acceptance_sha256"]):
        raise ValueError("area coefficients not accepted")
    for name, digest in area_accepted["files"].items():
        if area.base.sha(area_folder / name) != digest:
            raise ValueError("accepted area dependency changed")
    for name in ("verify_degree_area.py", "verify_multislope_area.py", "exact_arcs.py"):
        if area.base.sha(folder / name) != area_accepted["files"][name]:
            raise ValueError("stage imports different exact area arithmetic")
    old = json.loads((area_folder / "CERTIFICATE.json").read_text())
    multi = json.loads((area_folder / "MULTISLOPE-CERTIFICATE.json").read_text())
    area.parameter_gate(multi)
    native = json.loads((folder / "NATIVE-VERIFIED.json").read_text())
    if not native["verified_implementation_agreement"]:
        raise ValueError("native agreement absent")
    for name, digest in native["files"].items():
        if area.base.sha(folder / name) != digest:
            raise ValueError("native evidence changed")
    trace = json.loads((folder / "TRACE.json").read_text())
    if (trace["N"] != 26 or F(trace["radius_threshold"]) != U
            or trace["full_catalog_complete"] or trace["global_optimality_proved"]):
        raise ValueError("stage scope overclaimed")
    return manifest, source, old, multi, native, trace


def replay_trace(folder, source, old, multi, native, trace, arcs):
    refs = {b: OriginReference(26, b, "dfs", caps=CAPS, scale=D) for b in FAMILIES}
    pending, terminal = {b: {} for b in FAMILIES}, {b: set() for b in FAMILIES}
    for row in source["pending_states"]:
        b, p = row["B"], tuple(row["prefix"])
        state = refs[b].resolve(p)
        if refs[b].entry(p, state, refs[b].children(state)) != {k: v for k, v in row.items() if k != "B"}:
            raise ValueError("stage source state changed")
        if any(p[:len(q)] == q or q[:len(p)] == p for q in pending[b]):
            raise ValueError("stage source prefix overlaps")
        pending[b][p] = state
    if len(native["runs"]) != len(trace["events"]) or native["native_events_checked"] != len(trace["events"]):
        raise ValueError("native event coverage incomplete")
    counts = {b: dict.fromkeys(KINDS, 0) for b in FAMILIES}
    ledger, margins = [], []
    for index, (event, run) in enumerate(zip(trace["events"], native["runs"])):
        b, p, kind = event["B"], tuple(event["prefix"]), event["kind"]
        if b not in FAMILIES or p not in pending[b] or p in terminal[b] or run["event_index"] != index:
            raise ValueError("event processed twice or not in pending partition")
        state, ref = pending[b][p], refs[b]
        children = ref.children(state)
        depth = 1 if kind == "split" else 0
        result_path, launch_path = folder / run["result"], folder / run["launch"]
        if (result_path.name != f"native-{index:05d}.json"
                or launch_path.name != f"native-{index:05d}-launch.json"
                or area.base.sha(result_path) != run["result_sha256"]
                or area.base.sha(launch_path) != run["launch_sha256"]):
            raise ValueError("native event bindings changed")
        launch = json.loads(launch_path.read_text())
        tail = ["26", str(b), linux(result_path), str(D), *map(str, CAPS), "0", "dfs",
                "frontier", ",".join(map(str, p)) if p else "-", str(depth), "1"]
        if launch["exit_code"] != 0 or launch["command"][-14:] != tail:
            raise ValueError("wrong native event invocation")
        data = json.loads(result_path.read_text())
        if not data["origin_screen"]:
            raise ValueError("native origin condition absent")
        check_frontier(data, ref, p, depth)
        if kind in ("force", "force_tree"):
            spec = {"N": 26, "B": b, "next": state.next_vertex, "faces": list(state.faces)}
            if kind == "force":
                lower, upper = rootbox(angular_domain(spec))
                result = force_check(spec, lower, upper, event["cert"], arcs)
                margin = F(result["strict_margin_above_U"])
                if margin <= 0:
                    raise ValueError("nonpositive stage force margin")
            else:
                result = verify_angular_tree(spec, event["nodes"], arcs)
                margin = F(result["minimum_strict_force_margin"])
            margins.append(margin)
            ledger.append({"B": b, "prefix": list(p), "kind": kind, **result})
            pending[b].pop(p)
        elif kind == "area":
            if event["cert"]["B"] != b or event["cert"]["prefix"] != list(p):
                raise ValueError("wrong stage area case")
            bound = partial_bound(event["cert"], state, old, multi)
            if bound >= 0:
                raise ValueError("nonnegative stage area margin")
            ledger.append({"B": b, "prefix": list(p), "kind": kind, "area_dual_upper": str(bound)})
            pending[b].pop(p)
        elif kind == "empty":
            if not state.pending or children:
                raise ValueError("false stage empty subtree")
            pending[b].pop(p)
        elif kind == "split":
            if not children or event["all_child_count"] != len(children):
                raise ValueError("stage split omitted an immediate sibling")
            pending[b].pop(p)
            for k, child in enumerate(children):
                q = p + (k,)
                if q in pending[b]:
                    raise ValueError("stage replacement overlaps")
                pending[b][q] = ref.normalize(child)
        elif kind == "terminal":
            if state.pending or state.next_vertex != 26:
                raise ValueError("false stage terminal")
            area.base.degrees(b, list(state.faces))
            terminal[b].add(p)
        else:
            raise ValueError("unknown stage event kind")
        counts[b][kind] += 1
    for b in FAMILIES:
        if (trace["pending_prefixes"][str(b)] != [list(p) for p in sorted(pending[b])]
                or trace["terminal_pending_prefixes"][str(b)] != [list(p) for p in sorted(terminal[b])]):
            raise ValueError("stage pending sibling or unresolved terminal lost")
    frontier = {
        "schema": "N26-successive-force-angular-frontier-v1", "N": 26,
        "families": [{"B": b, "I": 26 - b, **counts[b], "pending_subtrees": len(pending[b]),
                      "unresolved_terminal_subtrees": len(terminal[b]),
                      "family_exhausted": not pending[b]} for b in FAMILIES],
        "pending_states": [{"B": b, **refs[b].entry(p, state, refs[b].children(state))}
                           for b in FAMILIES for p, state in sorted(pending[b].items())],
        "older_forests_and_original_native_queues_preserved": True,
        "full_catalog_complete": False, "global_optimality_proved": False}
    return frontier, ledger, margins


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--area-bundle", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    manifest, source, old, multi, native, trace = input_gate(args.input, args.area_bundle)
    arcs = load_trig(args.input)[0]
    frontier, ledger, margins = replay_trace(args.input, source, old, multi, native, trace, arcs)
    controls = regular_ring_controls(arcs)
    negatives = []

    def reject(label, fn):
        try:
            fn()
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("bad stage input accepted: " + label)

    bad = deepcopy(trace)
    bad["pending_prefixes"]["14"].pop()
    reject("lost-stage-pending-sibling", lambda: replay_trace(args.input, source, old, multi, native, bad, arcs))
    bad_native = deepcopy(native)
    bad_native["runs"].pop()
    reject("missing-stage-native-event", lambda: replay_trace(args.input, source, old, multi, bad_native, trace, arcs))
    bad = deepcopy(trace)
    next(row for row in bad["events"] if row["kind"] == "split")["all_child_count"] += 1
    reject("changed-stage-split-count", lambda: replay_trace(args.input, source, old, multi, native, bad, arcs))
    first = next(row for row in trace["events"] if row["kind"] == "force_tree")
    ref = OriginReference(26, first["B"], "dfs", caps=CAPS, scale=D)
    state = ref.resolve(tuple(first["prefix"]))
    spec = {"N": 26, "B": first["B"], "next": state.next_vertex, "faces": list(state.faces)}
    bad_nodes = deepcopy(first["nodes"])
    row = next(node for node in bad_nodes if node["kind"] == "SPLIT")
    row["children"][1] = row["children"][0]
    reject("missing-stage-angular-half", lambda: verify_angular_tree(spec, bad_nodes, arcs))
    bad_nodes = deepcopy(first["nodes"])
    bad_nodes.append({"kind": "EMPTY"})
    reject("stage-unreachable-angular-node", lambda: verify_angular_tree(spec, bad_nodes, arcs))
    frontier_path, ledger_path = args.input / "FRONTIER.json", args.input / "LOWER-LEDGER.json"
    area.base.publish_or_match(frontier_path, frontier)
    area.base.publish_or_match(ledger_path, ledger)
    files = ["MANIFEST.json", "TRACE.json", "NATIVE-VERIFIED.json", "FRONTIER.json", "LOWER-LEDGER.json",
             *manifest["copied_files"]]
    kinds = {kind: sum(row[kind] for row in frontier["families"]) for kind in KINDS}
    report = {
        "schema": "N26-successive-force-angular-stage-acceptance-v1", "verified": True,
        "source_pending_subtrees": len(source["pending_states"]),
        "native_events_independently_replayed": len(trace["events"]),
        "event_counts": kinds,
        "strictly_excluded_whole_transport_subtrees": kinds["force"] + kinds["force_tree"] + kinds["area"],
        "complete_angle_tree_nodes": sum(row["nodes"] for row in ledger if row["kind"] == "force_tree"),
        "all_incoming_angle_boxes_covered": True,
        "minimum_strict_force_margin": str(min(margins)) if margins else None,
        "feasible_regular_ring_regression_controls": controls,
        "families": frontier["families"],
        "pending_cover_transport_subtrees": len(frontier["pending_states"]),
        "older_forests_and_original_native_queues_preserved": True,
        "unrestricted_reduction_final_joint_acceptance": False,
        "formal_machine_geometry_proof": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "negative_controls_rejected": negatives,
        "files": {name: area.base.sha(args.input / name) for name in dict.fromkeys(files)},
        "executed_checker_sha256": area.base.sha(__file__)}
    if report["executed_checker_sha256"] != report["files"]["verify_force_stage.py"]:
        raise ValueError("executed stage checker differs from published")
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
