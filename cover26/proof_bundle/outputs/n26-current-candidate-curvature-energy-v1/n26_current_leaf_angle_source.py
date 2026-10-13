"""Semantic loading of the accepted leaf-pinned source, not a green-marker load."""

from pathlib import Path
import json

from n26_force import load_trig
import verify_leaf_pinned_candidate_angles as leaf


def input_gate(source_folder, correlated, sharp, historical, pinning_basis, stress, local,
               transport, pinning, caps):
    accepted, inventory = leaf.bound(source_folder)
    for name, digest in accepted["files"].items():
        path = Path(__file__).with_name(name)
        if name.endswith(".py") and path.exists() and leaf.sha(path) != digest:
            raise ValueError("continued leaf source imported changed arithmetic: " + name)
    old, old_report, radius, cells, matrix, cap, reference, data, old_pending, inputs = leaf.source_gate(
        correlated, sharp, historical, pinning_basis, stress, local, transport, pinning, caps)
    inventory.extend(inputs)
    discovery = json.loads((source_folder / "DISCOVERY.json").read_text())
    nodes = leaf.build_nodes(old, correlated, pinning, discovery)
    result, pending, ledger = leaf.replay(
        old["spec"], radius, cells, matrix, cap, reference, data, nodes, load_trig(source_folder)[0])
    sources = {"starting_partition": leaf.sha(correlated / "VERIFIED.json"),
               "pinning_reference": leaf.sha(pinning / "VERIFIED.json"),
               "sharp_caps": leaf.sha(caps / "VERIFIED.json"),
               "stress": leaf.sha(stress / "VERIFIED.json"), "local": leaf.sha(local / "VERIFIED.json"),
               "transport": leaf.sha(transport / "VERIFIED.json")}
    certificate = {"schema": "N26-leaf-specific-root-hull-pinned-angular-tree-v1",
                   "radius_scope": "same-root-Rstar", "spec": old["spec"],
                   "source_acceptance_sha256": sources, "nodes": nodes}
    if (any(accepted[key] != value for key, value in result.items())
            or certificate != json.loads((source_folder / "CERTIFICATE.json").read_text())
            or pending != json.loads((source_folder / "PENDING-ANGLES.json").read_text())
            or ledger != json.loads((source_folder / "LOWER-LEDGER.json").read_text())
            or reference != json.loads((source_folder / "REFERENCE-PINNING.json").read_text())
            or discovery["proposed_paid_LOCAL_indices"] != accepted["new_paid_source_OPEN_indices"]
            or accepted["source_unresolved_closed_angle_boxes"] != len(old_pending)):
        raise ValueError("entire current leaf-pinned source did not independently replay")
    return {"source": certificate, "accepted": accepted, "radius": radius, "cells": cells,
            "matrix": matrix, "cap": cap, "reference": reference, "data": data,
            "pending": pending, "ledger": ledger, "inventory": inventory}
