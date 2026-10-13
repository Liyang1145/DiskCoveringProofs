"""Publish certified root-specific angle caps and their continuous interface."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

from n26_force import load_trig
import n26_sharp_radius_constraints as constraints
import verify_refined_candidate_angles as checker


def source_gate(source_folder, pinning_basis, stress_folder, local_folder, transport_folder, pinning_folder):
    source_report, inventory = checker.bound(source_folder)
    pin_report, files = checker.bound(pinning_folder)
    inventory.extend(files)
    if (checker.sharp.pin.sha(checker.sharp.__file__) != source_report["files"]["n26_sharp_candidate_angles.py"]
            or checker.sharp.pin.sha(checker.direct.__file__) != source_report["files"]["n26_direct_arc_force.py"]
            or checker.sharp.pin.sha(checker.refined.__file__) != pin_report["files"]["verify_refined_anchor_pinning.py"]):
        raise ValueError("sharp-cap acceptance imported changed exact source arithmetic")
    pin_proposal = json.loads((pinning_folder / "CERTIFICATE.json").read_text())
    data = checker.refined.source_gate(pinning_basis, stress_folder, local_folder, transport_folder, pin_proposal)
    inventory.extend(data[5])
    pin_result = checker.refined.derive(*data[:5], pin_proposal)
    if any(pin_report[key] != value for key, value in pin_result.items()):
        raise ValueError("sharp-cap source nonlocal pinning did not replay")
    source = json.loads((source_folder / "CERTIFICATE.json").read_text())
    if source["source_acceptance_sha256"] != source_report["source_acceptance_sha256"]:
        raise ValueError("angle source acceptance dictionary changed")
    expected = {
        "stress": checker.sharp.pin.sha(stress_folder / "VERIFIED.json"),
        "local": checker.sharp.pin.sha(local_folder / "VERIFIED.json"),
        "transport": checker.sharp.pin.sha(transport_folder / "VERIFIED.json"),
        "refined_pinning": checker.sharp.pin.sha(pinning_folder / "VERIFIED.json"),
    }
    if any(source["source_acceptance_sha256"][key] != value for key, value in expected.items()):
        raise ValueError("angle source is not bound to the same root/pinning")
    final = data[3]["states"][-1]
    if source["spec"] != {"N": 26, "B": 16, "next": 26, "faces": final["faces"]}:
        raise ValueError("candidate graph differs from its exact transported root")
    radius_upper = F(json.loads((stress_folder / "VERIFIED.json").read_text())["modified_root_check"]["r_strict_interval"][1])
    pin_cells = [tuple(map(F, row)) for row in pin_result["closed_anchor_angle_cells"]]
    result, pending, ledger = checker.sharp.replay(
        source["spec"], radius_upper, pin_cells, source["nodes"], load_trig(source_folder)[0])
    if (any(source_report[key] != value for key, value in result.items())
            or pending != json.loads((source_folder / "PENDING-ANGLES.json").read_text())
            or ledger != json.loads((source_folder / "LOWER-LEDGER.json").read_text())):
        raise ValueError("sharp-cap source accepted angle tree did not replay")
    return source, source_report, radius_upper, pin_cells, pending, data, inventory


def derive(source, radius_upper, pending, geometry_data, cap_certificate, arcs):
    caps, margins = constraints.cap_gate(radius_upper, cap_certificate, arcs)
    matrix, derivation = constraints.constraint_matrix(source["spec"], caps)
    if matrix is None:
        raise ValueError("sharp constraints rejected the known exact covering candidate")
    original, root, records = geometry_data[:3]
    rotated, _, _, _ = checker.sharp.pin.root_geometry(original, root, records)
    tiny = cap_certificate["known_candidate_tiny_angle_cells"]
    checker.sharp.pin.check_cells(tiny, rotated)
    angular = [(F(0), F(0)), *[tuple(map(F, row)) for row in tiny]]
    if any(angular[j][1] - angular[i][0] > F(matrix[i][j], constraints.SCALE)
           for i in range(16) for j in range(16) if i != j):
        raise ValueError("known root tiny angle box fails exact sharp-matrix positive control")
    empty = [row["index"] for row in pending
             if constraints.tighten(matrix, row["lower"], row["upper"]) is None]
    return {
        "four_strict_outward_sine_margins": list(map(str, margins)),
        "known_exact_root_survives_all_sharp_constraints_on_tiny_rational_cells": True,
        "source_candidate_OPEN_boxes_checked": len(pending),
        "candidate_OPEN_indices_infeasible_for_radius_at_most_Rstar": empty,
        "candidate_OPEN_boxes_infeasible_for_radius_at_most_Rstar": len(empty),
        "independent_center_all_pairs_and_anchor_Bellman_Ford_reconstruction": True,
        "scope": "Necessary constraints for radius <=Rstar, not unconditional emptiness in the original U-angle domain",
    }, matrix, derivation


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--pinning-basis", type=Path, required=True)
    parser.add_argument("--stress", type=Path, required=True)
    parser.add_argument("--local", type=Path, required=True)
    parser.add_argument("--transport", type=Path, required=True)
    parser.add_argument("--pinning", type=Path, required=True)
    parser.add_argument("--discovery", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    source, source_report, radius_upper, pin_cells, pending, data, inventory = source_gate(
        args.source, args.pinning_basis, args.stress, args.local, args.transport, args.pinning)
    proposed = json.loads(args.discovery.read_text())
    if (proposed["source_stress_acceptance_sha256"] != checker.sharp.pin.sha(args.stress / "VERIFIED.json")
            or proposed["source_angle_acceptance_sha256"] != checker.sharp.pin.sha(args.source / "VERIFIED.json")):
        raise ValueError("sharp cap discovery changed its same-root source")
    certificate = {key: proposed[key] for key in (
        "N", "radius_scope", "radius_upper", "scale", "caps", "known_candidate_tiny_angle_cells")}
    arcs = load_trig(args.source)[0]
    result, matrix, derivation = derive(source, radius_upper, pending, data, certificate, arcs)
    if result["candidate_OPEN_indices_infeasible_for_radius_at_most_Rstar"] != proposed["proposed_empty_candidate_OPEN_indices"]:
        raise ValueError("independent sharp constraint replay disagrees with discovery")
    negatives = []

    def reject(label, fn):
        try:
            fn()
        except (ValueError, KeyError, TypeError):
            negatives.append(label)
        else:
            raise AssertionError("invalid sharp cap accepted: " + label)

    bad = deepcopy(certificate)
    bad["caps"][0] = "1"
    reject("uncertified-too-small-sine-cap", lambda: constraints.cap_gate(radius_upper, bad, arcs))
    bad = deepcopy(certificate)
    bad["radius_upper"] = "1/10"
    reject("different-radius-endpoint", lambda: constraints.cap_gate(radius_upper, bad, arcs))
    bad = deepcopy(certificate)
    bad["scale"] = "10000000"
    reject("silently-reused-coarse-angle-scale", lambda: constraints.cap_gate(radius_upper, bad, arcs))
    bad = deepcopy(certificate)
    bad["known_candidate_tiny_angle_cells"][0] = ["0", "1/4"]
    reject("unisolated-root-angle-control", lambda: derive(source, radius_upper, pending, data, bad, arcs))
    args.output.mkdir(parents=True)
    for name, value in (("CERTIFICATE.json", certificate), ("MATRIX.json", matrix), ("DERIVATION.json", derivation)):
        (args.output / name).write_text(json.dumps(value, separators=(",", ":")) + "\n", encoding="utf-8")
    (args.output / "DISCOVERY.json").write_bytes(args.discovery.read_bytes())
    files = ["CERTIFICATE.json", "MATRIX.json", "DERIVATION.json", "DISCOVERY.json"]
    for name in source_report["files"]:
        if name.endswith(".py"):
            (args.output / name).write_bytes((args.source / name).read_bytes())
            files.append(name)
    for name in ("verify_sharp_radius_angle_caps.py", "n26_sharp_radius_constraints.py"):
        (args.output / name).write_bytes(Path(__file__).with_name(name).read_bytes())
        files.append(name)
    proof = Path(__file__).with_name("n26-sharp-radius-angle-caps-proof.md")
    if not proof.exists():
        proof = Path(__file__).with_name("PROOF.md")
    (args.output / "PROOF.md").write_bytes(proof.read_bytes())
    files.append("PROOF.md")
    report = {
        "schema": "N26-certified-root-radius-necessary-angle-constraint-interface-v1",
        "verified": True, **result,
        "source_angle_acceptance_sha256": checker.sharp.pin.sha(args.source / "VERIFIED.json"),
        "source_stress_acceptance_sha256": checker.sharp.pin.sha(args.stress / "VERIFIED.json"),
        "current_global_combinatorial_frontier_nodes_removed": 0,
        "current_angle_tree_nodes_reclassified_by_this_bundle": 0,
        "negative_controls_rejected": negatives,
        "formal_machine_geometry_proof": False, "full_catalog_complete": False,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "files": {name: checker.sharp.pin.sha(args.output / name) for name in dict.fromkeys(files)},
        "source_files": {str(path): checker.sharp.pin.sha(path) for path in inventory},
    }
    (args.output / "VERIFIED.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key not in ("files", "source_files")}, indent=2), flush=True)


if __name__ == "__main__":
    main()
