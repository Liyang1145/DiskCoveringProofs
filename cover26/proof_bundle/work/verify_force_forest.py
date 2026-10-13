"""Pure exact current-frontier replay of native branches and N26 force leaves."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_origin import OriginReference
from audit_prefix_partition import check_frontier, linux
from n26_force import CAPS, D, U, angular_domain, force_check, load_trig, rod_graph, rootbox, spanning_tree
from verify_partial_area_closures import partial_bound
import verify_multislope_area as area


KERNEL_SOURCE = "a76a8ce6c0ee0ee0f513ae9eba086d5b6d1b6b3e39440ab0cac59ef5638620c9"
KERNEL_BINARY = "b07a612b71d7535a3d667dc764bcafadd104e14b6ce560f6810e56cfc9ba3a25"
FAMILIES = (14, 15, 16, 17)


def input_gate(folder, area_folder):
    manifest = json.loads((folder / "MANIFEST.json").read_text())
    for name, digest in manifest["copied_files"].items():
        if area.base.sha(folder / name) != digest:
            raise ValueError("changed forest input: " + name)
    if (manifest["kernel_source_sha256"] != KERNEL_SOURCE
            or manifest["kernel_binary_sha256"] != KERNEL_BINARY
            or area.base.sha(folder / "TRACE.json") != manifest["trace_sha256"]):
        raise ValueError("changed frozen source/binary/trace")
    source = json.loads((folder / "SOURCE-FRONTIER.json").read_text())
    previous = json.loads((folder / "SOURCE-ACCEPTANCE.json").read_text())
    if (not previous["current_bound_bytes_rechecked"]
            or previous["files"][manifest["source_frontier_original_key"]] != manifest["source_frontier_sha256"]
            or area.base.sha(folder / "SOURCE-FRONTIER.json") != manifest["source_frontier_sha256"]
            or area.base.sha(folder / "SOURCE-ACCEPTANCE.json") != manifest["source_acceptance_sha256"]):
        raise ValueError("unbound accepted starting frontier")
    accepted_path = area_folder / "VERIFIED.json"
    accepted = json.loads(accepted_path.read_text())
    if (not accepted["verified"] or accepted["global_optimality_proved"]
            or area.base.sha(accepted_path) != manifest["area_acceptance_sha256"]):
        raise ValueError("unaccepted area coefficients")
    for name, digest in accepted["files"].items():
        if area.base.sha(area_folder / name) != digest:
            raise ValueError("changed accepted area dependency")
    for name in ("verify_multislope_area.py", "verify_degree_area.py", "exact_arcs.py"):
        if area.base.sha(folder / name) != accepted["files"][name]:
            raise ValueError("forest imports different area arithmetic")
    old = json.loads((area_folder / "CERTIFICATE.json").read_text())
    multi = json.loads((area_folder / "MULTISLOPE-CERTIFICATE.json").read_text())
    area.parameter_gate(multi)
    native = json.loads((folder / "NATIVE-VERIFIED.json").read_text())
    if not native["verified_implementation_agreement"] or native["global_optimality_proved"]:
        raise ValueError("native/reference agreement absent")
    for name, digest in native["files"].items():
        if area.base.sha(folder / name) != digest:
            raise ValueError("changed native evidence")
    trace = json.loads((folder / "TRACE.json").read_text())
    if (trace["N"] != 26 or F(trace["radius_threshold"]) != U
            or trace["full_catalog_complete"] or trace["global_optimality_proved"]):
        raise ValueError("wrong forest scope")
    return manifest, source, old, multi, native, trace


def replay_trace(folder, source, old, multi, native, trace, arcs):
    refs = {b: OriginReference(26, b, "dfs", caps=CAPS, scale=D) for b in FAMILIES}
    pending, terminal = {b: {} for b in FAMILIES}, {b: set() for b in FAMILIES}
    for descriptor in source["pending_states"]:
        b, p = descriptor["B"], tuple(descriptor["prefix"])
        state = refs[b].resolve(p)
        if refs[b].entry(p, state, refs[b].children(state)) != {k: v for k, v in descriptor.items() if k != "B"}:
            raise ValueError("starting prefix state changed")
        if p in pending[b] or any(p[:len(q)] == q or q[:len(p)] == p for q in pending[b]):
            raise ValueError("starting frontier overlaps")
        pending[b][p] = state
    if len(native["runs"]) != len(trace["events"]) or native["native_events_checked"] != len(trace["events"]):
        raise ValueError("native event audit omitted a branch")
    counts = {b: dict.fromkeys(("split", "force", "area", "empty", "terminal"), 0) for b in FAMILIES}
    force_leaves, area_leaves = [], []
    for index, (event, run) in enumerate(zip(trace["events"], native["runs"])):
        b, p, kind = event["B"], tuple(event["prefix"]), event["kind"]
        if p not in pending[b] or p in terminal[b] or run["event_index"] != index:
            raise ValueError("event repeated, missing or outside current partition")
        state, ref = pending[b][p], refs[b]
        children = ref.children(state)
        depth = 1 if kind == "split" else 0
        result_path, launch_path = folder / run["result"], folder / run["launch"]
        if (result_path.name != f"native-{index:05d}.json"
                or launch_path.name != f"native-{index:05d}-launch.json"
                or area.base.sha(result_path) != run["result_sha256"]
                or area.base.sha(launch_path) != run["launch_sha256"]):
            raise ValueError("native result binding changed")
        launch = json.loads(launch_path.read_text())
        expected_tail = ["26", str(b), linux(result_path), str(D), *map(str, CAPS), "0",
                         "dfs", "frontier", ",".join(map(str, p)) if p else "-", str(depth), "1"]
        if launch["exit_code"] != 0 or launch["command"][-14:] != expected_tail:
            raise ValueError("native launch named a different scope")
        data = json.loads(result_path.read_text())
        if not data["origin_screen"]:
            raise ValueError("native origin screen omitted")
        check_frontier(data, ref, p, depth)
        if kind == "force":
            spec = {"N": 26, "B": b, "next": state.next_vertex, "faces": list(state.faces)}
            lower, upper = rootbox(angular_domain(spec))
            checked = force_check(spec, lower, upper, event["cert"], arcs)
            if F(checked["strict_margin_above_U"]) <= 0:
                raise ValueError("nonpositive exact rod-force margin")
            force_leaves.append({"B": b, "prefix": list(p), **checked})
            pending[b].pop(p)
        elif kind == "area":
            if event["cert"]["B"] != b or event["cert"]["prefix"] != list(p):
                raise ValueError("area leaf belongs to another partial state")
            value = partial_bound(event["cert"], state, old, multi)
            if value >= 0:
                raise ValueError("nonnegative exact area leaf")
            area_leaves.append({"B": b, "prefix": list(p), "area_dual_upper": str(value)})
            pending[b].pop(p)
        elif kind == "empty":
            if not state.pending or children:
                raise ValueError("terminal or branching state falsely called empty")
            pending[b].pop(p)
        elif kind == "split":
            if not children or event["all_child_count"] != len(children):
                raise ValueError("split lost an immediate sibling")
            pending[b].pop(p)
            for k, child in enumerate(children):
                target = p + (k,)
                if target in pending[b]:
                    raise ValueError("overlapping split")
                pending[b][target] = ref.normalize(child)
        elif kind == "terminal":
            if state.pending or state.next_vertex != 26:
                raise ValueError("false terminal state")
            area.base.degrees(b, list(state.faces))
            terminal[b].add(p)
        else:
            raise ValueError("unknown forest event")
        counts[b][kind] += 1
    for b in FAMILIES:
        if trace["pending_prefixes"][str(b)] != [list(p) for p in sorted(pending[b])]:
            raise ValueError("pending forest frontier lost or changed")
        if trace["terminal_pending_prefixes"][str(b)] != [list(p) for p in sorted(terminal[b])]:
            raise ValueError("unresolved terminal graph lost")
    frontier = {
        "schema": "N26-force-area-updated-transport-frontier-v1",
        "N": 26, "families": [{"B": b, "I": 26 - b, **counts[b],
                              "pending_subtrees": len(pending[b]),
                              "unresolved_terminal_subtrees": len(terminal[b]),
                              "family_exhausted": not pending[b]} for b in FAMILIES],
        "pending_states": [{"B": b, **refs[b].entry(p, state, refs[b].children(state))}
                           for b in FAMILIES for p, state in sorted(pending[b].items())],
        "original_native_queues_unchanged": True,
        "full_catalog_complete": False, "global_optimality_proved": False}
    return frontier, force_leaves, area_leaves


def regular_ring_controls(arcs):
    spec = {"N": 26, "B": 14, "next": 14, "faces": []}
    lower, upper = rootbox(angular_domain(spec))
    if any(not lo <= F(i, 14) <= hi for i, (lo, hi) in enumerate(zip(lower, upper), 1)):
        raise AssertionError("regular boundary ring outside necessary domain")
    radius_upper = F(arcs.sincos_turn(F(1, 28))[1][1], arcs.SCALE)
    vertices, edges = rod_graph(spec)
    chords = spanning_tree(vertices, edges)[2]
    for seed in range(32):
        cert = {"q": 1000, "l": [1 + (seed + 3 * i) % 7 for i in range(13)],
                "b": [((seed + 5 * i) % 11) - 5 for i in range(26)],
                "f": [((seed + 7 * i) % 23) - 11 for i in range(2 * len(chords))]}
        checked = force_check(spec, lower, upper, cert, arcs)
        if F(checked["required_radius_lower"]) > radius_upper:
            raise AssertionError("known feasible regular ring falsely excluded")
    return 32


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
    frontier, forces, areas = replay_trace(args.input, source, old, multi, native, trace, arcs)
    controls = regular_ring_controls(arcs)
    negatives = []

    def reject(label, fn):
        try:
            fn()
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("invalid force forest accepted: " + label)

    wrong = deepcopy(trace)
    wrong["pending_prefixes"]["14"].pop()
    reject("lost-pending-sibling", lambda: replay_trace(args.input, source, old, multi, native, wrong, arcs))
    wrong_native = deepcopy(native)
    wrong_native["runs"].pop()
    reject("missing-native-event", lambda: replay_trace(args.input, source, old, multi, wrong_native, trace, arcs))
    wrong = deepcopy(trace)
    wrong["events"][0]["kind"] = "empty"
    reject("branch-falsely-empty", lambda: replay_trace(args.input, source, old, multi, native, wrong, arcs))
    force_event = next(event for event in trace["events"] if event["kind"] == "force")
    ref = OriginReference(26, force_event["B"], "dfs", caps=CAPS, scale=D)
    state = ref.resolve(tuple(force_event["prefix"]))
    spec = {"N": 26, "B": force_event["B"], "next": state.next_vertex, "faces": list(state.faces)}
    lower, upper = rootbox(angular_domain(spec))
    wrong_cert = deepcopy(force_event["cert"])
    wrong_cert["l"][0] = -1
    reject("negative-arc-multiplier", lambda: force_check(spec, lower, upper, wrong_cert, arcs))
    wrong_cert = deepcopy(force_event["cert"])
    wrong_cert["f"].pop()
    reject("missing-cycle-coordinate", lambda: force_check(spec, lower, upper, wrong_cert, arcs))
    wrong_cert = deepcopy(force_event["cert"])
    wrong_cert["l"] = [0] * len(wrong_cert["l"])
    wrong_cert["b"] = [0] * len(wrong_cert["b"])
    wrong_cert["f"] = [0] * len(wrong_cert["f"])
    reject("zero-force", lambda: force_check(spec, lower, upper, wrong_cert, arcs))
    frontier_path, ledger_path = args.input / "FRONTIER.json", args.input / "LOWER-LEDGER.json"
    area.base.publish_or_match(frontier_path, frontier)
    area.base.publish_or_match(ledger_path, {"force_leaves": forces, "area_leaves": areas})
    files = ["MANIFEST.json", "TRACE.json", "NATIVE-VERIFIED.json", "FRONTIER.json", "LOWER-LEDGER.json",
             *manifest["copied_files"]]
    min_force = min(F(row["strict_margin_above_U"]) for row in forces)
    report = {
        "schema": "N26-exact-area-force-forest-acceptance-v1", "verified": True,
        "native_events_independently_replayed": len(trace["events"]),
        "force_subtrees_strictly_excluded": len(forces),
        "area_subtrees_strictly_excluded": len(areas),
        "empty_combinatorial_subtrees": sum(row["empty"] for row in frontier["families"]),
        "complete_immediate_sibling_replacements": sum(row["split"] for row in frontier["families"]),
        "minimum_exact_force_margin_above_U": str(min_force),
        "feasible_regular_ring_regression_controls": controls,
        "families": frontier["families"],
        "pending_cover_transport_subtrees": len(frontier["pending_states"]),
        "original_native_queues_preserved": True,
        "formal_machine_geometry_proof": False,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False, "negative_controls_rejected": negatives,
        "area_acceptance_sha256": manifest["area_acceptance_sha256"],
        "files": {name: area.base.sha(args.input / name) for name in dict.fromkeys(files)},
        "executed_checker_sha256": area.base.sha(__file__)}
    if report["executed_checker_sha256"] != report["files"]["verify_force_forest.py"]:
        raise ValueError("executed and published forest checkers differ")
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
