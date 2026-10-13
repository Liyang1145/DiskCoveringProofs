"""Exploration only: root-containing hulls of retained narrow angle leaves."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import verify_correlated_candidate_angles as angle
from n26_force import load_trig


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--maximum-width", default="1/1000000")
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    out = Path(__file__).resolve().parent.parent / "outputs"
    folder = out / "n26-correlated-candidate-angles-v1"
    accepted, inventory = angle.previous.caps_checker.checker.bound(folder)
    source, old_report, radius, cells, matrix, cap, pending_old, inputs = angle.source_gate(
        out / "n26-sharp-constraint-candidate-angles-v2", out / "n26-continued-candidate-angles-v1",
        out / "n26-anchor-pinning-v3", out / "n26-positive-stress-v1",
        out / "n26-centered-local-barrier-v2", out / "n26-candidate-transport-control-v1",
        out / "n26-refined-anchor-pinning-v2", out / "n26-sharp-radius-angle-caps-v2")
    inventory.extend(inputs)
    discovery = json.loads((folder / "PROPOSAL.json").read_text())
    nodes, result, pending, ledger, empty, local = angle.replay_and_close(
        source, radius, cells, matrix, discovery, load_trig(folder)[0])
    if (any(accepted[key] != value for key, value in result.items())
            or pending != json.loads((folder / "PENDING-ANGLES.json").read_text())
            or ledger != json.loads((folder / "LOWER-LEDGER.json").read_text())
            or nodes != json.loads((folder / "CERTIFICATE.json").read_text())["nodes"]):
        raise ValueError("leaf pinning discovery did not replay the actual retained source")
    refined = angle.previous.caps_checker.checker.refined
    basis = json.loads((out / "n26-refined-anchor-pinning-v2/CERTIFICATE.json").read_text())
    data = refined.source_gate(out / "n26-anchor-pinning-v3", out / "n26-positive-stress-v1",
                               out / "n26-centered-local-barrier-v2",
                               out / "n26-candidate-transport-control-v1", basis)
    inventory.extend(data[5])
    hashes = {str(path): angle.sha(path) for path in inventory}
    tiny = [tuple(map(F, row)) for row in cap["known_candidate_tiny_angle_cells"]]
    results, successes = [], []
    for row in pending:
        if row["sharp_radius_domain_empty"]:
            continue
        lo, hi = list(map(F, row["sharp_lower"])), list(map(F, row["sharp_upper"]))
        if max(b - a for a, b in zip(lo, hi)) > F(args.maximum_width):
            continue
        proposal = deepcopy(basis)
        proposal["closed_anchor_angle_cells"] = [
            [str(min(a, x)), str(max(b, y))] for a, b, (x, y) in zip(lo, hi, tiny)]
        try:
            pin = refined.derive(*data[:5], proposal)
        except ValueError as error:
            results.append({"index": row["index"], "proposed_local": False, "diagnostic": str(error)})
        else:
            successes.append(row["index"])
            results.append({"index": row["index"], "proposed_local": True,
                            "root_containing_closed_hull": proposal["closed_anchor_angle_cells"],
                            "max_center_error": pin["maximum_center_to_exact_rotated_root_euclidean_error_upper"],
                            "entry_margin": pin["strict_entry_margin_to_accepted_local_box"]})
        if len(results) % 20 == 0:
            print(json.dumps({"narrow_leaves_probed": len(results),
                              "unaccepted_leaf_specific_LOCAL": len(successes)}), flush=True)
    if any(angle.sha(path) != digest for path, digest in hashes.items()):
        raise ValueError("pinning discovery source changed during exploration")
    args.output.write_text(json.dumps({
        "schema": "N26-unaccepted-leaf-specific-root-hull-pinning-discovery-v1",
        "verified": False, "source_acceptance_sha256": angle.sha(folder / "VERIFIED.json"),
        "source_certificate_sha256": angle.sha(folder / "CERTIFICATE.json"),
        "basis_acceptance_sha256": angle.sha(out / "n26-refined-anchor-pinning-v2/VERIFIED.json"),
        "candidate_pending_leaves": len(pending), "narrow_leaves_probed": len(results),
        "proposed_paid_LOCAL_indices": successes, "results": results,
        "independent_new_leaf_semantics_and_full_chain_acceptance_pending": True,
        "global_optimality_proved": False}, separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({"verified": False, "narrow_leaves_probed": len(results),
                      "unaccepted_leaf_specific_LOCAL": len(successes)}), flush=True)


if __name__ == "__main__":
    main()
