"""Exact complete angular-tree ancestor exclusions and frontier set subtraction."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_origin import OriginReference
from audit_prefix_partition import check_frontier, linux
from n26_force import CAPS, D, load_trig
from n26_force_angles import verify_angular_tree
from verify_degree_area import publish_or_match, sha


FAMILIES = (14, 15, 16, 17)
SOURCE_SHA = "a76a8ce6c0ee0ee0f513ae9eba086d5b6d1b6b3e39440ab0cac59ef5638620c9"
BINARY_SHA = "b07a612b71d7535a3d667dc764bcafadd104e14b6ce560f6810e56cfc9ba3a25"


def load_inputs(folder):
    manifest = json.loads((folder / "MANIFEST.json").read_text())
    for name, digest in manifest["copied_files"].items():
        if sha(folder / name) != digest:
            raise ValueError("changed coarse angular input")
    if (sha(folder / "TRACE.json") != manifest["trace_sha256"]
            or sha(folder / "peel_prefix_origin.cpp") != SOURCE_SHA
            or sha(folder / "peel_prefix_origin.linux") != BINARY_SHA):
        raise ValueError("changed trace/native source")
    source = json.loads((folder / "SOURCE-FRONTIER.json").read_text())
    forest = json.loads((folder / "SOURCE-FOREST-ACCEPTANCE.json").read_text())
    chain = json.loads((folder / "SOURCE-CHAIN-ACCEPTANCE.json").read_text())
    if (not forest["verified"] or forest["global_optimality_proved"]
            or not chain["current_bound_bytes_rechecked"]
            or sha(folder / "SOURCE-FRONTIER.json") != manifest["source_frontier_sha256"]
            or sha(folder / "SOURCE-FOREST-ACCEPTANCE.json") != manifest["source_forest_acceptance_sha256"]
            or sha(folder / "SOURCE-CHAIN-ACCEPTANCE.json") != manifest["source_chain_acceptance_sha256"]
            or chain["files"][manifest["source_frontier_original_key"]] != manifest["source_frontier_sha256"]
            or source["families"] != forest["families"]):
        raise ValueError("starting forest/chain is not accepted at the claimed scope")
    for name in ("n26_force.py", "exact_arcs.py", "verify_degree_area.py"):
        if sha(folder / name) != forest["files"][name]:
            raise ValueError("changed exact force arithmetic")
    native = json.loads((folder / "NATIVE-VERIFIED.json").read_text())
    if not native["verified_implementation_agreement"]:
        raise ValueError("native ancestor agreement absent")
    for name, digest in native["files"].items():
        if sha(folder / name) != digest:
            raise ValueError("changed native ancestor data")
    trace = json.loads((folder / "TRACE.json").read_text())
    if trace["N"] != 26 or trace["full_catalog_complete"] or trace["global_optimality_proved"]:
        raise ValueError("coarse angular scope overclaimed")
    return manifest, source, trace, native


def replay(folder, source, trace, native, arcs):
    refs = {b: OriginReference(26, b, "dfs", caps=CAPS, scale=D) for b in FAMILIES}
    pending = {b: {} for b in FAMILIES}
    for row in source["pending_states"]:
        b, p = row["B"], tuple(row["prefix"])
        state = refs[b].resolve(p)
        if refs[b].entry(p, state, refs[b].children(state)) != {k: v for k, v in row.items() if k != "B"}:
            raise ValueError("source prefix state changed")
        if p in pending[b]:
            raise ValueError("source prefix duplicated")
        pending[b][p] = row
    if len(native["runs"]) != len(trace["closures"]):
        raise ValueError("missing native ancestor")
    previous, ledger = [], []
    removed = dict.fromkeys(FAMILIES, 0)
    for i, (closure, run) in enumerate(zip(trace["closures"], native["runs"])):
        b, p = closure["B"], tuple(closure["prefix"])
        if b not in FAMILIES or any(qb == b and (p[:len(q)] == q or q[:len(p)] == p) for qb, q in previous):
            raise ValueError("ancestor exclusions overlap")
        descendants = [q for q in pending[b] if q[:len(p)] == p]
        if not descendants or len(descendants) != closure["source_active_descendants"]:
            raise ValueError("ancestor closure refers to a changed descendant scope")
        if any(p[:len(q)] == q for q in pending[b] if q not in descendants):
            raise ValueError("closure cuts inside an unsplit source prefix")
        state = refs[b].resolve(p)
        spec = {"N": 26, "B": b, "next": state.next_vertex, "faces": list(state.faces)}
        result_path, log_path = folder / run["result"], folder / run["launch"]
        if (run["closure_index"] != i or sha(result_path) != run["result_sha256"]
                or sha(log_path) != run["launch_sha256"]):
            raise ValueError("native ancestor binding changed")
        launch = json.loads(log_path.read_text())
        tail = ["26", str(b), linux(result_path), str(D), *map(str, CAPS), "0", "dfs",
                "frontier", ",".join(map(str, p)), "0", "1"]
        if launch["exit_code"] != 0 or launch["command"][-14:] != tail:
            raise ValueError("native ancestor invocation changed")
        data = json.loads(result_path.read_text())
        if not data["origin_screen"]:
            raise ValueError("native ancestor disables origin screen")
        check_frontier(data, refs[b], p, 0)
        tree_result = verify_angular_tree(spec, closure["nodes"], arcs)
        ledger.append({"B": b, "prefix": list(p), "source_descendants_removed": len(descendants),
                       **tree_result})
        for q in descendants:
            pending[b].pop(q)
        removed[b] += len(descendants)
        previous.append((b, p))
    for b in FAMILIES:
        if trace["pending_prefixes"][str(b)] != [list(p) for p in sorted(pending[b])]:
            raise ValueError("remaining frontier lost a source prefix")
    frontier = {
        "schema": "N26-angular-ancestor-filtered-frontier-v1", "N": 26,
        "families": [{"B": b, "I": 26 - b,
                      "source_pending_subtrees": sum(row["B"] == b for row in source["pending_states"]),
                      "source_subtrees_covered_by_ancestor_exclusions": removed[b],
                      "pending_subtrees": len(pending[b]), "family_exhausted": not pending[b]}
                     for b in FAMILIES],
        "pending_states": [row for b in FAMILIES for p, row in sorted(pending[b].items())],
        "all_unexcluded_source_prefixes_preserved": True,
        "old_forest_original_unchanged": True,
        "full_catalog_complete": False, "global_optimality_proved": False}
    return frontier, ledger


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.report.exists():
        raise FileExistsError(args.report)
    manifest, source, trace, native = load_inputs(args.input)
    arcs = load_trig(args.input)[0]
    frontier, ledger = replay(args.input, source, trace, native, arcs)
    negatives = []

    def reject(label, fn):
        try:
            fn()
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("invalid angular closure accepted: " + label)

    first = trace["closures"][0]
    ref = OriginReference(26, first["B"], "dfs", caps=CAPS, scale=D)
    state = ref.resolve(tuple(first["prefix"]))
    spec = {"N": 26, "B": first["B"], "next": state.next_vertex, "faces": list(state.faces)}
    bad = deepcopy(first["nodes"])
    split = next(node for node in bad if node["kind"] == "SPLIT")
    split["children"][1] = split["children"][0]
    reject("missing-angular-half", lambda: verify_angular_tree(spec, bad, arcs))
    bad = deepcopy(first["nodes"])
    next(node for node in bad if node["kind"] == "FORCE")["kind"] = "EMPTY"
    reject("false-empty-angular-box", lambda: verify_angular_tree(spec, bad, arcs))
    bad = deepcopy(first["nodes"])
    bad.append({"kind": "EMPTY"})
    reject("unreachable-angular-node", lambda: verify_angular_tree(spec, bad, arcs))
    bad = deepcopy(first["nodes"])
    next(node for node in bad if node["kind"] == "SPLIT")["mid"] = "-1"
    reject("split-outside-incoming-box", lambda: verify_angular_tree(spec, bad, arcs))
    bad_trace = deepcopy(trace)
    bad_trace["pending_prefixes"]["14"].pop()
    reject("lost-unexcluded-source-prefix", lambda: replay(args.input, source, bad_trace, native, arcs))
    bad_trace = deepcopy(trace)
    bad_trace["closures"][0]["source_active_descendants"] += 1
    reject("wrong-descendant-scope", lambda: replay(args.input, source, bad_trace, native, arcs))
    frontier_path, ledger_path = args.input / "FRONTIER.json", args.input / "LOWER-LEDGER.json"
    publish_or_match(frontier_path, frontier)
    publish_or_match(ledger_path, ledger)
    files = ["MANIFEST.json", "TRACE.json", "NATIVE-VERIFIED.json", "FRONTIER.json", "LOWER-LEDGER.json",
             *manifest["copied_files"]]
    report = {
        "schema": "N26-complete-angular-ancestor-closures-acceptance-v1", "verified": True,
        "whole_ancestor_subtrees_strictly_excluded": len(ledger),
        "complete_angular_nodes": sum(row["nodes"] for row in ledger),
        "complete_angular_splits": sum(row["counts"]["SPLIT"] for row in ledger),
        "strict_angular_force_leaves": sum(row["counts"]["FORCE"] for row in ledger),
        "source_pending_prefixes_covered": sum(row["source_descendants_removed"] for row in ledger),
        "minimum_strict_force_margin": str(min(F(row["minimum_strict_force_margin"]) for row in ledger)),
        "all_incoming_angle_boxes_covered": True,
        "native_ancestor_states_independently_replayed": len(ledger),
        "families": frontier["families"],
        "pending_cover_transport_subtrees": len(frontier["pending_states"]),
        "old_forests_and_original_queues_preserved": True,
        "formal_machine_geometry_proof": False,
        "unrestricted_reduction_final_joint_acceptance": False,
        "full_catalog_complete": False, "global_lower_bound_proved": False,
        "global_optimality_proved": False,
        "negative_controls_rejected": negatives,
        "files": {name: sha(args.input / name) for name in dict.fromkeys(files)},
        "executed_checker_sha256": sha(__file__)}
    if report["executed_checker_sha256"] != report["files"]["verify_angular_closures.py"]:
        raise ValueError("executed checker differs from published checker")
    args.report.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
