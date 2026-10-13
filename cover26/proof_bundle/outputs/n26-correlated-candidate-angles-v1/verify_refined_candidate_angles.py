"""Reclassify only geometrically paid OPEN leaves of an accepted angle tree."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import n26_sharp_candidate_angles as sharp
import n26_direct_arc_force as direct
import verify_refined_anchor_pinning as refined
from n26_force import load_trig


def bound(folder):
    report, inventory = sharp.pin.checked_bundle(folder)
    for path, digest in report.get("source_files", {}).items():
        if sharp.pin.sha(path) != digest:
            raise ValueError("changed accepted angle/pinning source")
        inventory.append(sharp.pin.local_path(path))
    return report, inventory


def lineage_gate(old_nodes, nodes, paid):
    if len(old_nodes) != len(nodes):
        raise ValueError("local reclassification lost or inserted a tree node")
    actual = []
    for i, (old, new) in enumerate(zip(old_nodes, nodes)):
        if old["kind"] != "OPEN":
            if old != new:
                raise ValueError("previously proved node was changed")
        elif new != old:
            if new != {"kind": "LOCAL"}:
                raise ValueError("unpaid OPEN leaf was not replaced by a pure LOCAL leaf")
            actual.append(i)
    if actual != paid:
        raise ValueError("newly paid angular leaf list differs")


def reconstruct(prior_folder, pinning_basis, stress_folder, local_folder, transport_folder, pinning_folder):
    old_report, inventory = bound(prior_folder)
    pin_report, paths = bound(pinning_folder)
    inventory.extend(paths)
    if (sharp.pin.sha(sharp.__file__) != old_report["files"]["n26_sharp_candidate_angles.py"]
            or sharp.pin.sha(direct.__file__) != old_report["files"]["n26_direct_arc_force.py"]
            or sharp.pin.sha(refined.__file__) != pin_report["files"]["verify_refined_anchor_pinning.py"]):
        raise ValueError("refined angle replay imported changed exact arithmetic")
    pin_proposal = json.loads((pinning_folder / "CERTIFICATE.json").read_text())
    data = refined.source_gate(pinning_basis, stress_folder, local_folder, transport_folder, pin_proposal)
    inventory.extend(data[5])
    pin_result = refined.derive(*data[:5], pin_proposal)
    if any(pin_report[key] != value for key, value in pin_result.items()):
        raise ValueError("refined nonlocal pinning did not replay")
    old_certificate = json.loads((prior_folder / "CERTIFICATE.json").read_text())
    final = data[3]["states"][-1]
    spec = {"N": 26, "B": 16, "next": 26, "faces": final["faces"]}
    if old_certificate["spec"] != spec:
        raise ValueError("old angle tree and refined pinning use different transport graphs")
    stress = json.loads((stress_folder / "VERIFIED.json").read_text())
    radius_upper = F(stress["modified_root_check"]["r_strict_interval"][1])
    basis = json.loads((pinning_basis / "VERIFIED.json").read_text())
    if (old_report["source_acceptance_sha256"]["pinning"] != sharp.pin.sha(pinning_basis / "VERIFIED.json")
            or old_report["source_acceptance_sha256"]["local"] != basis["source_acceptance_sha256"]["local"]
            or old_report["source_acceptance_sha256"]["stress"] != sharp.pin.sha(stress_folder / "VERIFIED.json")
            or old_report["source_acceptance_sha256"]["transport"] != sharp.pin.sha(transport_folder / "VERIFIED.json")):
        raise ValueError("old partition is not a bound ancestor of the refined same-root proof")
    old_cells = [tuple(map(F, row)) for row in json.loads(
        (pinning_basis / "CERTIFICATE.json").read_text())["closed_anchor_angle_cells"]]
    arcs = load_trig(prior_folder)[0]
    old_result, old_pending, old_ledger = sharp.replay(
        spec, radius_upper, old_cells, old_certificate["nodes"], arcs)
    if (any(old_report[key] != value for key, value in old_result.items())
            or old_pending != json.loads((prior_folder / "PENDING-ANGLES.json").read_text())
            or old_ledger != json.loads((prior_folder / "LOWER-LEDGER.json").read_text())):
        raise ValueError("accepted ancestor partition or its actual OPEN leaves changed")
    cells = [tuple(map(F, row)) for row in pin_proposal["closed_anchor_angle_cells"]]
    nodes = deepcopy(old_certificate["nodes"])
    paid = []
    for row in old_pending:
        if all(a <= F(lo) <= F(hi) <= b
               for lo, hi, (a, b) in zip(row["lower"], row["upper"], cells)):
            nodes[row["index"]] = {"kind": "LOCAL"}
            paid.append(row["index"])
    paid.sort()
    lineage_gate(old_certificate["nodes"], nodes, paid)
    result, pending, ledger = sharp.replay(spec, radius_upper, cells, nodes, arcs)
    sources = {
        "prior_partition": sharp.pin.sha(prior_folder / "VERIFIED.json"),
        "pinning_basis": sharp.pin.sha(pinning_basis / "VERIFIED.json"),
        "refined_pinning": sharp.pin.sha(pinning_folder / "VERIFIED.json"),
        "stress": sharp.pin.sha(stress_folder / "VERIFIED.json"),
        "local": sharp.pin.sha(local_folder / "VERIFIED.json"),
        "transport": sharp.pin.sha(transport_folder / "VERIFIED.json"),
    }
    certificate = {
        "schema": "N26-sharp-candidate-angle-local-reclassification-v1",
        "radius_scope": "same-root-Rstar", "spec": spec,
        "source_acceptance_sha256": sources, "newly_paid_LOCAL_indices": paid, "nodes": nodes,
    }
    return certificate, result, pending, ledger, inventory, pin_result, old_report, old_certificate


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--prior", type=Path, required=True)
    parser.add_argument("--pinning-basis", type=Path, required=True)
    parser.add_argument("--stress", type=Path, required=True)
    parser.add_argument("--local", type=Path, required=True)
    parser.add_argument("--transport", type=Path, required=True)
    parser.add_argument("--pinning", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    certificate, result, pending, ledger, inventory, pin_result, old_report, old_certificate = reconstruct(
        args.prior, args.pinning_basis, args.stress, args.local, args.transport, args.pinning)
    negatives = []

    def reject(label, fn):
        try:
            fn()
        except (ValueError, KeyError, TypeError):
            negatives.append(label)
        else:
            raise AssertionError("bad local angular refinement accepted: " + label)

    bad = deepcopy(certificate["nodes"])
    next(n for n in bad if n["kind"] == "FORCE")["kind"] = "OPEN"
    reject("previous-force-proof-erased", lambda: lineage_gate(
        old_certificate["nodes"], bad, certificate["newly_paid_LOCAL_indices"]))
    reject("new-local-leaf-not-counted", lambda: lineage_gate(
        old_certificate["nodes"], certificate["nodes"], []))
    bad = deepcopy(certificate["nodes"])
    next(n for n in bad if n["kind"] == "SPLIT")["children"].pop()
    reject("lost-closed-half", lambda: lineage_gate(
        old_certificate["nodes"], bad, certificate["newly_paid_LOCAL_indices"]))
    pin_cells = [tuple(map(F, r)) for r in pin_result["closed_anchor_angle_cells"]]
    radius_upper = F(json.loads((args.stress / "VERIFIED.json").read_text())["modified_root_check"]["r_strict_interval"][1])
    reject("broad-root-falsely-local", lambda: sharp.replay(
        certificate["spec"], radius_upper, pin_cells, [{"kind": "LOCAL"}], load_trig(args.prior)[0]))
    controls = direct.regular_ring_controls(load_trig(args.prior)[0])
    args.output.mkdir(parents=True)
    for name, value in (("CERTIFICATE.json", certificate), ("PENDING-ANGLES.json", pending), ("LOWER-LEDGER.json", ledger)):
        (args.output / name).write_text(json.dumps(value, separators=(",", ":")) + "\n", encoding="utf-8")
    files = ["CERTIFICATE.json", "PENDING-ANGLES.json", "LOWER-LEDGER.json"]
    modules = ["n26_sharp_candidate_angles.py", "n26_direct_arc_force.py", "n26_force.py",
               "verify_degree_area.py", "verify_anchor_pinning.py", "verify_contact_root.py",
               "verify_same_root_cover.py", "audit_prefix_origin.py", "audit_prefix_partition.py", "exact_arcs.py"]
    for name in modules:
        (args.output / name).write_bytes((args.prior / name).read_bytes())
        files.append(name)
    (args.output / "verify_refined_anchor_pinning.py").write_bytes((args.pinning / "verify_refined_anchor_pinning.py").read_bytes())
    (args.output / "verify_refined_candidate_angles.py").write_bytes(Path(__file__).read_bytes())
    (args.output / "BASE-ANGLE-PROOF.md").write_bytes((args.prior / "PROOF.md").read_bytes())
    files.extend(("verify_refined_anchor_pinning.py", "verify_refined_candidate_angles.py", "BASE-ANGLE-PROOF.md"))
    proof = Path(__file__).with_name("n26-refined-candidate-angles-proof.md")
    if not proof.exists():
        proof = Path(__file__).with_name("PROOF.md")
    (args.output / "PROOF.md").write_bytes(proof.read_bytes())
    files.append("PROOF.md")
    report = {
        "schema": "N26-sharp-candidate-refined-local-angle-reclassification-acceptance-v1",
        "verified": True, **result,
        "source_acceptance_sha256": certificate["source_acceptance_sha256"],
        "previously_proved_nodes_and_all_closed_splits_preserved": True,
        "newly_paid_LOCAL_indices": certificate["newly_paid_LOCAL_indices"],
        "newly_paid_angular_boxes": len(certificate["newly_paid_LOCAL_indices"]),
        "prior_unresolved_angular_boxes": old_report["unresolved_closed_angle_boxes"],
        "direct_arc_force_positive_controls": controls,
        "current_global_combinatorial_frontier_nodes_removed": 0,
        "formal_machine_geometry_proof": False, "full_catalog_complete": False,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "negative_controls_rejected": negatives,
        "files": {name: sharp.pin.sha(args.output / name) for name in files},
        "source_files": {str(path): sharp.pin.sha(path) for path in inventory},
    }
    (args.output / "VERIFIED.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key not in ("files", "source_files")}, indent=2), flush=True)


if __name__ == "__main__":
    main()
