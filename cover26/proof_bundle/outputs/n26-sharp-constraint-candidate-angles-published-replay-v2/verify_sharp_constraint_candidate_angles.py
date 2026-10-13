"""Publish independently replayed sharp-cap-aware candidate angle continuation."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from n26_force import load_trig
import n26_sharp_constraint_tree as tree
import verify_sharp_radius_angle_caps as caps_checker


def lineage_gate(source_nodes, nodes):
    if len(nodes) < len(source_nodes):
        raise ValueError("sharp-cap continuation lost existing nodes")
    for i, old in enumerate(source_nodes):
        new = nodes[i]
        if old["kind"] != "OPEN" and old != new:
            raise ValueError("sharp-cap continuation changed an old proved node")
        if old["kind"] == "OPEN" and old != new:
            if new.get("kind") not in tree.KINDS or new["kind"] == "OPEN":
                raise ValueError("invalid replacement of original OPEN")
            if new["kind"] == "SPLIT" and any(k < len(source_nodes) for k in new["children"]):
                raise ValueError("sharp-cap split reuses old tree nodes")


def input_gate(source_folder, pinning_basis, stress_folder, local_folder, transport_folder,
               pinning_folder, caps_folder, proposal):
    source, old_report, radius_upper, cells, pending, geometry_data, inventory = caps_checker.source_gate(
        source_folder, pinning_basis, stress_folder, local_folder, transport_folder, pinning_folder)
    cap_report, files = caps_checker.checker.bound(caps_folder)
    inventory.extend(files)
    if (caps_checker.checker.sharp.pin.sha(caps_checker.__file__) != cap_report["files"]["verify_sharp_radius_angle_caps.py"]
            or caps_checker.checker.sharp.pin.sha(tree.sharp.__file__) != cap_report["files"]["n26_sharp_radius_constraints.py"]):
        raise ValueError("sharp-cap tree imported a different certified constraint implementation")
    cap_certificate = json.loads((caps_folder / "CERTIFICATE.json").read_text())
    cap_result, matrix, derivation = caps_checker.derive(
        source, radius_upper, pending, geometry_data, cap_certificate, load_trig(source_folder)[0])
    if (any(cap_report[key] != value for key, value in cap_result.items())
            or matrix != json.loads((caps_folder / "MATRIX.json").read_text())
            or derivation != json.loads((caps_folder / "DERIVATION.json").read_text())
            or cap_report["source_angle_acceptance_sha256"] != caps_checker.checker.sharp.pin.sha(source_folder / "VERIFIED.json")
            or cap_report["source_stress_acceptance_sha256"] != caps_checker.checker.sharp.pin.sha(stress_folder / "VERIFIED.json")):
        raise ValueError("certified sharp-cap interface did not independently replay")
    if (proposal["source_acceptance_sha256"] != caps_checker.checker.sharp.pin.sha(source_folder / "VERIFIED.json")
            or proposal["source_certificate_sha256"] != caps_checker.checker.sharp.pin.sha(source_folder / "CERTIFICATE.json")
            or proposal["pinning_acceptance_sha256"] != caps_checker.checker.sharp.pin.sha(pinning_folder / "VERIFIED.json")
            or proposal["spec"] != source["spec"] or proposal["radius_scope"] != "same-root-Rstar"
            or proposal["scale"] != cap_certificate["scale"] or proposal["caps"] != cap_certificate["caps"]):
        raise ValueError("sharp-cap proposal changed source, geometry, radius or constants")
    lineage_gate(source["nodes"], proposal["nodes"])
    return source, old_report, radius_upper, cells, matrix, cap_certificate, inventory


def replay_and_close(source, old_report, radius_upper, cells, matrix, proposal, arcs):
    nodes = deepcopy(proposal["nodes"])
    _, initially_pending, _ = tree.replay(source["spec"], radius_upper, cells, matrix, nodes, arcs)
    auto_empty, auto_local = [], []
    for row in initially_pending:
        if row["sharp_radius_domain_empty"]:
            nodes[row["index"]] = {"kind": "SHARP_EMPTY"}
            auto_empty.append(row["index"])
        elif row["sharp_radius_domain_inside_local"]:
            nodes[row["index"]] = {"kind": "SHARP_LOCAL"}
            auto_local.append(row["index"])
    lineage_gate(source["nodes"], nodes)
    result, pending, ledger = tree.replay(source["spec"], radius_upper, cells, matrix, nodes, arcs)
    old_counts = old_report["counts"]
    strict_new = result["counts"]["FORCE"] + result["counts"]["SHARP_FORCE"] - old_counts["FORCE"]
    local_new = result["counts"]["LOCAL"] + result["counts"]["SHARP_LOCAL"] - old_counts["LOCAL"]
    return nodes, result, pending, ledger, auto_empty, auto_local, strict_new, local_new


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--pinning-basis", type=Path, required=True)
    parser.add_argument("--stress", type=Path, required=True)
    parser.add_argument("--local", type=Path, required=True)
    parser.add_argument("--transport", type=Path, required=True)
    parser.add_argument("--pinning", type=Path, required=True)
    parser.add_argument("--caps", type=Path, required=True)
    parser.add_argument("--proposal", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    proposal = json.loads(args.proposal.read_text())
    source, old_report, radius_upper, cells, matrix, cap_certificate, inventory = input_gate(
        args.source, args.pinning_basis, args.stress, args.local, args.transport,
        args.pinning, args.caps, proposal)
    arcs = load_trig(args.source)[0]
    nodes, result, pending, ledger, auto_empty, auto_local, strict_new, local_new = replay_and_close(
        source, old_report, radius_upper, cells, matrix, proposal, arcs)
    tiny = [tuple(map(F, r)) for r in cap_certificate["known_candidate_tiny_angle_cells"]]
    retained = any(row["kind"] in ("LOCAL", "SHARP_LOCAL") and all(
        F(lo) <= a <= b <= F(hi) for lo, hi, (a, b) in zip(
            row.get("sharp_lower", row["lower"]), row.get("sharp_upper", row["upper"]), tiny))
        for row in ledger if row["kind"] in ("LOCAL", "SHARP_LOCAL"))
    if not retained:
        raise ValueError("known exact candidate tiny box was lost from proved local leaves")
    negatives = []

    def reject(label, fn):
        try:
            fn()
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("invalid sharp tree accepted: " + label)

    bad = deepcopy(nodes)
    next(n for n in bad if n["kind"] == "FORCE")["kind"] = "OPEN"
    reject("old-force-erased", lambda: lineage_gate(source["nodes"], bad))
    bad = deepcopy(nodes)
    next(n for n in bad[len(source["nodes"]):] if n["kind"] == "SPLIT")["children"][1] = \
        next(n for n in bad[len(source["nodes"]):] if n["kind"] == "SPLIT")["children"][0]
    reject("new-sharp-split-lost-half", lambda: tree.replay(source["spec"], radius_upper, cells, matrix, bad, arcs))
    bad = deepcopy(nodes)
    bad.append({"kind": "OPEN"})
    reject("unreachable-sharp-pending-node", lambda: tree.replay(source["spec"], radius_upper, cells, matrix, bad, arcs))
    reject("nonempty-root-falsely-sharp-empty", lambda: tree.replay(
        source["spec"], radius_upper, cells, matrix, [{"kind": "SHARP_EMPTY"}], arcs))
    reject("broad-root-falsely-sharp-local", lambda: tree.replay(
        source["spec"], radius_upper, cells, matrix, [{"kind": "SHARP_LOCAL"}], arcs))
    bad = deepcopy(nodes)
    next(n for n in bad if n["kind"] == "SHARP_EMPTY")["kind"] = "EMPTY"
    reject("sharp-infeasible-box-mislabelled-original-empty", lambda: tree.replay(
        source["spec"], radius_upper, cells, matrix, bad, arcs))
    controls = caps_checker.checker.direct.regular_ring_controls(arcs)
    sources = {
        "starting_partition": caps_checker.checker.sharp.pin.sha(args.source / "VERIFIED.json"),
        "sharp_constraint_interface": caps_checker.checker.sharp.pin.sha(args.caps / "VERIFIED.json"),
        "pinning": caps_checker.checker.sharp.pin.sha(args.pinning / "VERIFIED.json"),
        "stress": caps_checker.checker.sharp.pin.sha(args.stress / "VERIFIED.json"),
        "local": caps_checker.checker.sharp.pin.sha(args.local / "VERIFIED.json"),
        "transport": caps_checker.checker.sharp.pin.sha(args.transport / "VERIFIED.json"),
    }
    certificate = {
        "schema": "N26-sharp-radius-conditional-closed-angular-tree-v1",
        "radius_scope": "same-root-Rstar", "spec": source["spec"],
        "source_acceptance_sha256": sources, "nodes": nodes,
    }
    args.output.mkdir(parents=True)
    for name, value in (("CERTIFICATE.json", certificate), ("PENDING-ANGLES.json", pending), ("LOWER-LEDGER.json", ledger)):
        (args.output / name).write_text(json.dumps(value, separators=(",", ":")) + "\n", encoding="utf-8")
    (args.output / "SOURCE-CERTIFICATE.json").write_bytes((args.source / "CERTIFICATE.json").read_bytes())
    (args.output / "SOURCE-ACCEPTANCE.json").write_bytes((args.source / "VERIFIED.json").read_bytes())
    (args.output / "PROPOSAL.json").write_bytes(args.proposal.read_bytes())
    files = ["CERTIFICATE.json", "PENDING-ANGLES.json", "LOWER-LEDGER.json",
             "SOURCE-CERTIFICATE.json", "SOURCE-ACCEPTANCE.json", "PROPOSAL.json"]
    cap_report = json.loads((args.caps / "VERIFIED.json").read_text())
    for name in cap_report["files"]:
        if name.endswith(".py"):
            (args.output / name).write_bytes((args.caps / name).read_bytes())
            files.append(name)
    for name in ("n26_sharp_constraint_tree.py", "verify_sharp_constraint_candidate_angles.py"):
        (args.output / name).write_bytes(Path(__file__).with_name(name).read_bytes())
        files.append(name)
    (args.output / "SHARP-CONSTRAINT-PROOF.md").write_bytes((args.caps / "PROOF.md").read_bytes())
    files.append("SHARP-CONSTRAINT-PROOF.md")
    proof = Path(__file__).with_name("n26-sharp-constraint-tree-proof.md")
    if not proof.exists():
        proof = Path(__file__).with_name("PROOF.md")
    (args.output / "PROOF.md").write_bytes(proof.read_bytes())
    files.append("PROOF.md")
    report = {
        "schema": "N26-accepted-sharp-radius-conditional-candidate-angle-continuation-v1",
        "verified": True, **result,
        "source_acceptance_sha256": sources,
        "prior_all_proved_nodes_and_closed_splits_preserved": True,
        "new_strict_force_angle_boxes": strict_new,
        "new_paid_LOCAL_angle_boxes": local_new,
        "sharp_infeasible_boxes_paid": result["counts"]["SHARP_EMPTY"],
        "automatically_paid_sharp_empty_indices": auto_empty,
        "automatically_paid_sharp_local_indices": auto_local,
        "known_exact_candidate_tiny_box_retained_in_proved_LOCAL_leaf": retained,
        "direct_arc_force_positive_controls": controls,
        "discovery_numeric_status_not_used_as_proof": True,
        "current_global_combinatorial_frontier_nodes_removed": 0,
        "formal_machine_geometry_proof": False, "full_catalog_complete": False,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "negative_controls_rejected": negatives,
        "files": {name: caps_checker.checker.sharp.pin.sha(args.output / name) for name in dict.fromkeys(files)},
        "source_files": {str(path): caps_checker.checker.sharp.pin.sha(path) for path in inventory},
    }
    (args.output / "VERIFIED.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    excluded = {"files", "source_files", "automatically_paid_sharp_empty_indices",
                "automatically_paid_sharp_local_indices"}
    print(json.dumps({key: value for key, value in report.items() if key not in excluded}, indent=2), flush=True)


if __name__ == "__main__":
    main()
