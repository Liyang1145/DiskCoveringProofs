"""Exact leaf-specific energy pinning in a preserved correlated angle tree."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from audit_prefix_partition import linux
from n26_force import load_trig
import verify_correlated_candidate_angles as previous


HULL_LOCAL = "SHARP_HULL_LOCAL"
KINDS = (*previous.KINDS, HULL_LOCAL)
sha = previous.sha
refined = previous.previous.caps_checker.checker.refined
local_path = refined.base.local_path


def bound(folder):
    report, inventory = previous.previous.caps_checker.checker.bound(folder)
    for text, digest in report.get("source_files", {}).items():
        path = local_path(text.replace("\\", "/"))
        if sha(path) != digest:
            raise ValueError("leaf pinning source provenance bytes changed")
        inventory.append(path)
    return report, inventory


def source_gate(source_folder, sharp_basis, historical, pinning_basis, stress, local,
                transport, pinning, caps):
    accepted, inventory = bound(source_folder)
    for name, digest in accepted["files"].items():
        path = Path(__file__).with_name(name)
        if name.endswith(".py") and path.exists() and sha(path) != digest:
            raise ValueError("leaf pinning imported changed accepted arithmetic: " + name)
    source, old_report, radius, cells, matrix, cap, old_pending, inputs = previous.source_gate(
        sharp_basis, historical, pinning_basis, stress, local, transport, pinning, caps)
    inventory.extend(inputs)
    proposal = json.loads((source_folder / "PROPOSAL.json").read_text())
    if (proposal["source_acceptance_sha256"] != sha(sharp_basis / "VERIFIED.json")
            or proposal["source_certificate_sha256"] != sha(sharp_basis / "CERTIFICATE.json")
            or proposal["radius_scope"] != "same-root-Rstar" or proposal["spec"] != source["spec"]):
        raise ValueError("correlated source changed its historical sharp basis")
    nodes, result, pending, ledger, empty, paid_local = previous.replay_and_close(
        source, radius, cells, matrix, proposal, load_trig(source_folder)[0])
    sources = {"starting_partition": sha(sharp_basis / "VERIFIED.json"),
               "historical_cap_basis": sha(historical / "VERIFIED.json"),
               "sharp_caps": sha(caps / "VERIFIED.json"), "pinning": sha(pinning / "VERIFIED.json"),
               "stress": sha(stress / "VERIFIED.json"), "local": sha(local / "VERIFIED.json"),
               "transport": sha(transport / "VERIFIED.json")}
    certificate = {"schema": "N26-correlated-sharp-radius-closed-angular-tree-v1",
                   "spec": source["spec"], "radius_scope": "same-root-Rstar",
                   "source_acceptance_sha256": sources, "nodes": nodes}
    improved = sum(F(row["direct_arc_required_radius_lower"]) <= radius
                   for row in ledger if row["kind"] == previous.CORRELATED)
    if (any(accepted[key] != value for key, value in result.items())
            or certificate != json.loads((source_folder / "CERTIFICATE.json").read_text())
            or pending != json.loads((source_folder / "PENDING-ANGLES.json").read_text())
            or ledger != json.loads((source_folder / "LOWER-LEDGER.json").read_text())
            or accepted["new_strict_direct_force_leaves"] != result["counts"]["SHARP_FORCE"] - old_report["counts"]["SHARP_FORCE"]
            or accepted["new_strict_correlated_force_leaves"] != result["counts"][previous.CORRELATED]
            or accepted["correlated_leaves_not_payable_by_their_direct_arc_bound"] != improved
            or empty != accepted["automatically_paid_sharp_empty_indices"]
            or paid_local != accepted["automatically_paid_sharp_local_indices"]):
        raise ValueError("entire correlated source partition did not independently replay")
    pin_report, inputs = bound(pinning)
    inventory.extend(inputs)
    reference = json.loads((pinning / "CERTIFICATE.json").read_text())
    data = refined.source_gate(pinning_basis, stress, local, transport, reference)
    inventory.extend(data[5])
    pin_result = refined.derive(*data[:5], reference)
    if any(pin_report[key] != value for key, value in pin_result.items()):
        raise ValueError("unchanged positive reference network did not replay")
    if F(pin_result["accepted_local_box_original_coordinate_halfwidth"]) != F(7, 800000):
        raise ValueError("leaf pinning silently changed the certified unrestricted local allowance")
    return certificate, accepted, radius, cells, matrix, cap, reference, data, pending, inventory


def lineage_gate(old, nodes):
    if not isinstance(nodes, list) or len(nodes) < len(old):
        raise ValueError("leaf pinning lost source nodes")
    for i, original in enumerate(old):
        new = nodes[i]
        if original["kind"] != "OPEN" and new != original:
            raise ValueError("leaf pinning changed an old paid node")
        if original["kind"] == "OPEN" and new != original:
            if not isinstance(new, dict) or new.get("kind") not in KINDS or new["kind"] == "OPEN":
                raise ValueError("invalid replacement of leaf pinning OPEN")
            if new["kind"] == "SPLIT" and any(k < len(old) for k in new["children"]):
                raise ValueError("leaf pinning split reuses existing nodes")


def build_nodes(source, source_folder, pinning_folder, discovery):
    if (discovery["source_acceptance_sha256"] != sha(source_folder / "VERIFIED.json")
            or discovery["source_certificate_sha256"] != sha(source_folder / "CERTIFICATE.json")
            or discovery["basis_acceptance_sha256"] != sha(pinning_folder / "VERIFIED.json")):
        raise ValueError("leaf pinning discovery source or reference is unbound")
    indices = discovery["proposed_paid_LOCAL_indices"]
    if (type(indices) is not list or not indices or any(type(i) is not int for i in indices)
            or len(set(indices)) != len(indices)):
        raise ValueError("duplicate, empty or invalid leaf pinning index list")
    nodes = deepcopy(source["nodes"])
    for i in indices:
        if not 0 <= i < len(nodes) or nodes[i] != {"kind": "OPEN"}:
            raise ValueError("leaf pinning index is not a retained source OPEN")
        nodes[i] = {"kind": HULL_LOCAL}
    lineage_gate(source["nodes"], nodes)
    return nodes


def hull_for(row, tiny):
    if row["sharp_radius_domain_empty"]:
        raise ValueError("local pinning needs a nonempty sharp leaf")
    lo, hi = list(map(F, row["sharp_lower"])), list(map(F, row["sharp_upper"]))
    return [[str(min(a, x)), str(max(b, y))] for a, b, (x, y) in zip(lo, hi, tiny)]


def replay(spec, radius, cells, matrix, cap, reference, data, nodes, arcs, progress=False):
    ordinary = deepcopy(nodes)
    for node in ordinary:
        if node.get("kind") == HULL_LOCAL:
            if set(node) != {"kind"}:
                raise ValueError("leaf hull must be reconstructed, not supplied by a label")
            node["kind"] = "OPEN"
    result, pending, ledger = previous.replay(spec, radius, cells, matrix, ordinary, arcs)
    tiny = [tuple(map(F, row)) for row in cap["known_candidate_tiny_angle_cells"]]
    remaining, paid, errors, margins = [], 0, [], []
    for row in pending:
        if nodes[row["index"]]["kind"] != HULL_LOCAL:
            remaining.append(row)
            continue
        proposal = deepcopy(reference)
        proposal["closed_anchor_angle_cells"] = hull_for(row, tiny)
        pin = refined.derive(*data[:5], proposal)
        allowed = F(pin["accepted_local_box_original_coordinate_halfwidth"])
        error = F(pin["maximum_center_to_exact_rotated_root_euclidean_error_upper"])
        if allowed != F(7, 800000) or error >= allowed:
            raise ValueError("entire reconstructed leaf hull is not inside the accepted local allowance")
        ledger.append({**row, "kind": HULL_LOCAL, "root_containing_closed_hull_reconstructed": True,
                       "radius_at_least_same_root_Rstar": True,
                       "uses_radius_conditional_sharp_constraints": True,
                       "leaf_specific_nonlocal_pinning": pin})
        paid += 1
        errors.append(error)
        margins.append(allowed - error)
        if progress and paid % 20 == 0:
            print(json.dumps({"leaf_specific_LOCAL_boxes_exactly_replayed": paid}), flush=True)
    result["counts"]["OPEN"] -= paid
    result["counts"][HULL_LOCAL] = paid
    result["unresolved_closed_angle_boxes"] = len(remaining)
    result["all_radius_at_most_Rstar_candidate_domains_lower_bounded"] = not remaining
    result["candidate_transport_global_lower_bound_proved"] = not remaining
    result["leaf_specific_LOCAL_boxes"] = paid
    result["leaf_specific_pinning_maximum_center_error_upper"] = str(max(errors)) if errors else None
    result["leaf_specific_pinning_minimum_strict_entry_margin"] = str(min(margins)) if margins else None
    ledger.sort(key=lambda row: row["index"])
    return result, remaining, ledger


def main():
    parser = argparse.ArgumentParser()
    for name in ("source", "sharp-basis", "historical", "pinning-basis", "stress",
                 "local", "transport", "pinning", "caps", "discovery", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    for key in vars(args):
        setattr(args, key, getattr(args, key).resolve())
    if args.output.exists():
        raise FileExistsError(args.output)
    source, accepted, radius, cells, matrix, cap, reference, data, old_pending, inventory = source_gate(
        args.source, args.sharp_basis, args.historical, args.pinning_basis, args.stress,
        args.local, args.transport, args.pinning, args.caps)
    input_hashes = {linux(path): sha(path) for path in inventory}
    discovery = json.loads(args.discovery.read_text())
    nodes = build_nodes(source, args.source, args.pinning, discovery)
    arcs = load_trig(args.source)[0]
    result, pending, ledger = replay(source["spec"], radius, cells, matrix, cap,
                                    reference, data, nodes, arcs, progress=True)
    tiny = [tuple(map(F, row)) for row in cap["known_candidate_tiny_angle_cells"]]
    retained = any(row["kind"] in ("LOCAL", "SHARP_LOCAL") and all(
        F(lo) <= a <= b <= F(hi) for lo, hi, (a, b) in zip(
            row.get("sharp_lower", row["lower"]), row.get("sharp_upper", row["upper"]), tiny))
        for row in ledger if row["kind"] in ("LOCAL", "SHARP_LOCAL"))
    if not retained or len(old_pending) - len(pending) != result["leaf_specific_LOCAL_boxes"]:
        raise ValueError("leaf pinning lost candidate positive control or unresolved leaves")
    negatives = []

    def reject(label, fn):
        try:
            fn()
        except (ValueError, KeyError, TypeError, IndexError):
            negatives.append(label)
        else:
            raise AssertionError("invalid leaf-specific pinning accepted: " + label)

    bad = deepcopy(discovery)
    bad["proposed_paid_LOCAL_indices"].append(bad["proposed_paid_LOCAL_indices"][0])
    reject("duplicate-source-leaf", lambda: build_nodes(source, args.source, args.pinning, bad))
    bad = deepcopy(discovery)
    bad["proposed_paid_LOCAL_indices"][0] = next(i for i, node in enumerate(source["nodes"]) if node["kind"] == "FORCE")
    reject("paid-source-node-falsely-replaced", lambda: build_nodes(source, args.source, args.pinning, bad))
    bad = deepcopy(discovery)
    bad["basis_acceptance_sha256"] = "0" * 64
    reject("unbound-positive-reference-network", lambda: build_nodes(source, args.source, args.pinning, bad))
    bad = deepcopy(nodes)
    next(node for node in bad if node["kind"] == HULL_LOCAL)["hull"] = []
    reject("supplied-hull-cannot-omit-real-leaf-corners", lambda: replay(
        source["spec"], radius, cells, matrix, cap, reference, data, bad, arcs))
    bad = deepcopy(nodes)
    next(node for node in bad if node["kind"] == "SPLIT")["children"][1] = \
        next(node for node in bad if node["kind"] == "SPLIT")["children"][0]
    reject("missing-closed-half", lambda: replay(source["spec"], radius, cells, matrix, cap, reference, data, bad, arcs))
    reject("unreachable-new-local-leaf", lambda: replay(
        source["spec"], radius, cells, matrix, cap, reference, data, nodes + [{"kind": HULL_LOCAL}], arcs))
    reject("broad-root-falsely-leaf-local", lambda: replay(
        source["spec"], radius, cells, matrix, cap, reference, data, [{"kind": HULL_LOCAL}], arcs))
    bad = deepcopy(reference)
    bad["radius_scope"] = "at-most-U"
    reject("larger-U-radius-not-certified", lambda: refined.derive(*data[:5], bad))
    bad = deepcopy(reference)
    bad["weight_numerators"][0] = "0"
    reject("nonpositive-reference-rod", lambda: refined.derive(*data[:5], bad))
    controls = previous.correlated.controls(arcs)
    if controls != accepted["exact_correlated_force_positive_controls"]:
        raise ValueError("old correlated force positive controls changed")
    sources = {"starting_partition": sha(args.source / "VERIFIED.json"),
               "pinning_reference": sha(args.pinning / "VERIFIED.json"),
               "sharp_caps": sha(args.caps / "VERIFIED.json"),
               "stress": sha(args.stress / "VERIFIED.json"), "local": sha(args.local / "VERIFIED.json"),
               "transport": sha(args.transport / "VERIFIED.json")}
    certificate = {"schema": "N26-leaf-specific-root-hull-pinned-angular-tree-v1",
                   "radius_scope": "same-root-Rstar", "spec": source["spec"],
                   "source_acceptance_sha256": sources, "nodes": nodes}
    args.output.mkdir(parents=True)
    files = []
    for name, obj in (("CERTIFICATE.json", certificate), ("PENDING-ANGLES.json", pending), ("LOWER-LEDGER.json", ledger)):
        (args.output / name).write_text(json.dumps(obj, separators=(",", ":")) + "\n", encoding="utf-8")
        files.append(name)
    for original, name in ((args.discovery, "DISCOVERY.json"), (args.source / "CERTIFICATE.json", "SOURCE-CERTIFICATE.json"),
                           (args.source / "VERIFIED.json", "SOURCE-ACCEPTANCE.json"),
                           (args.pinning / "CERTIFICATE.json", "REFERENCE-PINNING.json")):
        (args.output / name).write_bytes(original.read_bytes())
        files.append(name)
    for name in accepted["files"]:
        if name.endswith(".py"):
            (args.output / name).write_bytes((args.source / name).read_bytes())
            files.append(name)
    name = "verify_leaf_pinned_candidate_angles.py"
    (args.output / name).write_bytes(Path(__file__).read_bytes())
    files.append(name)
    proof = Path(__file__).with_name("n26-leaf-specific-pinning-proof.md")
    if not proof.exists():
        proof = Path(__file__).with_name("PROOF.md")
    (args.output / "PROOF.md").write_bytes(proof.read_bytes())
    files.append("PROOF.md")
    for text, digest in input_hashes.items():
        if sha(local_path(text)) != digest:
            raise ValueError("leaf pinning dependency changed during acceptance")
    report = {
        "schema": "N26-accepted-leaf-specific-root-hull-pinned-candidate-angles-v1",
        "verified": True, **result, "source_acceptance_sha256": sources,
        "prior_all_proved_nodes_and_closed_splits_preserved": True,
        "known_exact_candidate_tiny_box_retained_in_proved_LOCAL_leaf": retained,
        "all_actual_sharp_leaf_corners_in_reconstructed_root_hull": True,
        "unchanged_positive_reference_network_and_same_root_replayed": True,
        "no_prior_center_or_internal_witness_neighbourhood_hypothesis": True,
        "unchanged_original_coordinate_local_allowance": "7/800000",
        "new_paid_source_OPEN_indices": discovery["proposed_paid_LOCAL_indices"],
        "independent_leaf_error_bounds_recomputed_not_discovery_numbers": True,
        "source_unresolved_closed_angle_boxes": len(old_pending),
        "old_correlated_force_positive_controls_replayed": controls,
        "negative_controls_rejected": negatives,
        "current_global_combinatorial_frontier_nodes_removed": 0,
        "formal_machine_geometry_proof": False, "full_catalog_complete": False,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "files": {name: sha(args.output / name) for name in dict.fromkeys(files)},
        "source_files": input_hashes}
    (args.output / "VERIFIED.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items()
                      if key not in ("files", "source_files", "new_paid_source_OPEN_indices")}, indent=2), flush=True)


if __name__ == "__main__":
    main()
