"""Positive angular regression fixtures for stages with no new angular trees.

An ancestor fixture is a regression control only, never a new stage payment.
All original numerical and closed-boundary geometry is replayed unchanged.
"""

from copy import deepcopy
from pathlib import Path

import verify_conditional_force_stage as exact


def has_split(event):
    return event.get("kind") == "force_tree" and any(
        node.get("kind") == "SPLIT" for node in event["nodes"])


def select_control(folder):
    """Find a genuinely recorded tree, including an already accepted ancestor."""
    current = folder
    visited, inventory = set(), []
    while True:
        key = exact.combinatorics.linux(current)
        if key in visited:
            raise ValueError("cyclic angular regression-control ancestry")
        visited.add(key)
        trace = exact.read(current / "TRACE.json")
        if current.resolve() != folder.resolve():
            accepted, paths = exact.bound(current)
            if accepted.get("radius_scope") != exact.SCOPE:
                raise ValueError("angular control ancestor changed conditional scope")
            inventory.extend(paths)
            acceptance = exact.sha(current / "VERIFIED.json")
        else:
            acceptance = None
        for index, event in enumerate(trace["events"]):
            if has_split(event):
                ref = exact.origin.OriginReference(
                    26, event["B"], "dfs", caps=exact.force.CAPS, scale=exact.force.D)
                state = ref.resolve(tuple(event["prefix"]))
                spec = {"N": 26, "B": event["B"], "next": state.next_vertex,
                        "faces": list(state.faces)}
                fixture = {
                    "schema": "N26-angular-stage-regression-control-v1",
                    "control_stage": key,
                    "control_trace_sha256": exact.sha(current / "TRACE.json"),
                    "control_acceptance_sha256": acceptance,
                    "event_index": index, "event": event, "spec": spec,
                    "from_current_stage": current.resolve() == folder.resolve(),
                    "new_geometric_payments_from_this_control": 0,
                }
                inventory.append(current / "TRACE.json")
                return fixture, inventory
        manifest = exact.read(current / "MANIFEST.json")
        inventory.append(current / "MANIFEST.json")
        current = exact.local_path(manifest["source_acceptance_original_path"]).parent


def check_control(fixture, arcs):
    if (
        fixture["schema"] != "N26-angular-stage-regression-control-v1"
        or type(fixture["new_geometric_payments_from_this_control"]) is not int
        or fixture["new_geometric_payments_from_this_control"] != 0
        or not has_split(fixture["event"])
    ):
        raise ValueError("angular regression control was promoted to a stage payment")
    positive = exact.angles.verify_angular_tree(
        fixture["spec"], fixture["event"]["nodes"], arcs)
    rejected = []

    def reject(label, nodes):
        try:
            exact.angles.verify_angular_tree(fixture["spec"], nodes, arcs)
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid angular regression control accepted: " + label)

    bad = deepcopy(fixture["event"]["nodes"])
    split = next(node for node in bad if node["kind"] == "SPLIT")
    split["children"][1] = split["children"][0]
    reject("conditional-angular-closed-half-lost", bad)
    bad = deepcopy(fixture["event"]["nodes"])
    bad.append({"kind": "EMPTY"})
    reject("conditional-angular-hidden-node", bad)
    return positive, rejected
