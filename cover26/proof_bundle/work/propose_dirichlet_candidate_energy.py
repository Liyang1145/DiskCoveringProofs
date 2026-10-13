"""Unaccepted exact Dirichlet candidates; standalone overlay acceptance needed."""

import argparse
import json
from pathlib import Path

from sympy import Matrix

from n26_force import load_trig
from fractions import Fraction as F
import n26_dirichlet_energy as energy
from verify_selected_type_trees import bound, read
from verify_terminal_catalog import sha


def main():
    parser = argparse.ArgumentParser()
    for key in ("source", "pinning", "caps", "output", "kernel-output"):
        parser.add_argument("--" + key, type=Path, required=True)
    parser.add_argument("--limit", type=int, default=354)
    args = parser.parse_args()
    if args.output.exists() or args.kernel_output.exists():
        raise FileExistsError("fresh exact Dirichlet discovery paths required")
    for folder in (args.source, args.pinning, args.caps):
        bound(folder)
    reference = read(args.pinning / "CERTIFICATE.json")
    lap = energy.laplacian(reference["edges"], [int(x) for x in reference["weight_numerators"]])
    domain = Matrix([row[16:] for row in lap[16:]]).to_DM()
    print(json.dumps({"unaccepted_exact_Dirichlet_inverse_started": True}), flush=True)
    inverse, denominator = domain.inv_den()
    nums = [[int(x) for x in row] for row in inverse.to_Matrix().tolist()]
    denominator = int(denominator)
    if denominator < 0:
        nums, denominator = [[-x for x in row] for row in nums], -denominator
    certificate = {"schema": "N26-exact-integer-ground-Dirichlet-inverse-v1",
                   "anchor_vertices": 16, "inverse_denominator": str(denominator),
                   "inverse_numerators": [[str(x) for x in row] for row in nums]}
    args.kernel_output.write_text(json.dumps(certificate, separators=(",", ":")) + "\n", encoding="utf-8")
    kernel = energy.kernel_gate(reference, certificate)
    cap, arcs = read(args.caps / "CERTIFICATE.json"), load_trig(args.caps)[0]
    radius2 = F(cap["radius_upper"])**2
    pending = read(args.source / "PENDING-ANGLES.json")
    numerical = Path(__file__).with_name("n26-dirichlet-candidate-entry-diagnostics-v1.json")
    if numerical.exists():
        diagnostic = read(numerical)
        if diagnostic["source_acceptance_sha256"] == sha(args.source / "VERIFIED.json"):
            by_index = {row["index"]: row["floating_energy_slack"] for row in diagnostic["results"]}
            pending.sort(key=lambda row: by_index[row["index"]])
    payments, checks = [], []
    for row in pending[:args.limit]:
        result = energy.bound(row["sharp_lower"], row["sharp_upper"], kernel, radius2, arcs)
        checks.append({"index": row["index"], **result})
        if result["radius_conditional_whole_angle_box_excluded"]:
            payments.append(row["index"])
        if len(checks) % 12 == 0:
            print(json.dumps({"verified": False, "Dirichlet_boxes_exactly_checked_for_discovery": len(checks),
                              "strict_whole_box_energy_proposals": len(payments)}), flush=True)
    args.output.write_text(json.dumps({
        "schema": "N26-unaccepted-current-candidate-Dirichlet-energy-overlay-v1",
        "verified": False, "radius_scope": "same-root-Rstar",
        "source_acceptance_sha256": sha(args.source / "VERIFIED.json"),
        "pinning_acceptance_sha256": sha(args.pinning / "VERIFIED.json"),
        "cap_acceptance_sha256": sha(args.caps / "VERIFIED.json"),
        "kernel_sha256": sha(args.kernel_output), "proposed_paid_OPEN_indices": payments,
        "checks": checks, "all_other_source_OPEN_boxes_retained": True,
        "independent_semantic_source_replay_and_standalone_acceptance_pending": True,
        "global_optimality_proved": False}, separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({"verified": False, "checks": len(checks), "proposed_exclusions": len(payments)}), flush=True)


if __name__ == "__main__":
    main()
