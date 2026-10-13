"""Discovery-only fresh Schur references for actual positive partial kernels."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np
from scipy.optimize import minimize

from audit_prefix_origin import OriginReference
from audit_prefix_partition import linux
from n26_force import CAPS, D, load_trig
import n26_partial_prefix_quadratic_kernel as partial
import n26_sharp_partial_domains as independent
import n26_sharp_radius_constraints as constraints
from propose_common_grid_candidate_curvature import refine
from propose_quadratic_energy_minorant import rational_reference
from verify_conditional_force_stage import bound, read, sha, local_path


def stationary(kernel, matrix, lower, upper, reference_angles):
    b = kernel["B"]
    initial = rational_reference(reference_angles, lower, upper, matrix)
    x0 = np.array([float(F(x)) for x in initial])
    pairs = kernel["pairs"]
    weights = np.array([float(F(w, kernel["energy_denominator"])) for _, _, w in pairs])
    left, right = np.array([(i, j) for i, j, _ in pairs]).T
    rows, rhs = [], []
    for i in range(b):
        for j in range(b):
            if i == j:
                continue
            row = np.zeros(b - 1)
            if i:
                row[i - 1] -= 1
            if j:
                row[j - 1] += 1
            rows.append(row)
            rhs.append(float(F(matrix[i][j], constraints.SCALE)))
    rows, rhs = np.array(rows), np.array(rhs)

    def value(x):
        turns = np.r_[0., x]
        delta = 2 * np.pi * (turns[right] - turns[left])
        energy = 2 * np.dot(weights, 1 - np.cos(delta))
        gradient = np.zeros(b)
        np.add.at(gradient, left, -4 * np.pi * weights * np.sin(delta))
        np.add.at(gradient, right, 4 * np.pi * weights * np.sin(delta))
        return float(energy), gradient[1:]

    optimized = minimize(
        lambda x: value(x)[0], x0, jac=lambda x: value(x)[1],
        bounds=[(float(a), float(b)) for a, b in zip(lower, upper)],
        constraints={"type": "ineq", "fun": lambda x: rhs - rows @ x, "jac": lambda x: -rows},
        method="SLSQP", options={"ftol": 1e-13, "maxiter": 250, "disp": False},
    )
    return optimized.x, {"floating_stationary_success": bool(optimized.success),
                         "floating_stationary_energy_not_a_lower_bound": float(optimized.fun)}


def main():
    parser = argparse.ArgumentParser()
    for name in ("proposal", "kernels", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    incoming, kernels = read(args.proposal), read(args.kernels)
    folder, cap_folder = local_path(incoming["source_stage"]), local_path(incoming["caps"])
    acceptance, inventory = bound(folder)
    cap_acceptance, paths = bound(cap_folder)
    inventory.extend(paths)
    frontier = read(folder / "FRONTIER.json")
    if (
        incoming["schema"] != "N26-unaccepted-current-partial-prefix-energy-discovery-v1"
        or incoming["verified"] is not False
        or incoming["radius_scope"] != "at-most-same-root-Rstar-not-original-U"
        or incoming["source_acceptance_sha256"] != sha(folder / "VERIFIED.json")
        or incoming["source_frontier_sha256"] != sha(folder / "FRONTIER.json")
        or incoming["cap_acceptance_sha256"] != sha(cap_folder / "VERIFIED.json")
        or incoming["kernels_sha256"] != sha(args.kernels)
        or cap_acceptance["verified"] is not True
    ):
        raise ValueError("partial stationary discovery substituted its actual partial source")
    radius, arcs = F(acceptance["radius_upper"]), load_trig(folder)[0]
    caps, _ = constraints.cap_gate(radius, read(cap_folder / "CERTIFICATE.json"), arcs)
    refs = {b: OriginReference(26, b, "dfs", caps=CAPS, scale=D) for b in (14, 15, 16, 17)}
    inventory.extend((args.proposal, args.kernels, folder / "FRONTIER.json", Path(__file__),
                      Path(partial.__file__), Path(independent.__file__), Path(constraints.__file__),
                      Path(__file__).with_name("propose_common_grid_candidate_curvature.py"),
                      Path(__file__).with_name("propose_quadratic_energy_minorant.py")))
    hashes = {linux(path): sha(path) for path in inventory}
    results = []
    for original in incoming["results"]:
        record = deepcopy(original)
        index = record["source_index"]
        if type(index) is not int or not 0 <= index < len(frontier["pending_states"]):
            raise ValueError("partial stationary discovery changed source ownership")
        row = frontier["pending_states"][index]
        b, prefix = row["B"], tuple(row["prefix"])
        ref, state = refs[b], refs[b].resolve(prefix)
        if row["terminal"] or {"B": b, **ref.entry(prefix, state, ref.children(state))} != row:
            raise ValueError("partial stationary source is not an actual exact nonterminal prefix")
        spec = {"N": 26, "B": b, "next": row["next"], "faces": row["faces"]}
        matrix, _ = constraints.constraint_matrix(spec, caps)
        other, _ = independent.matrix(spec, caps)
        if record["spec"] != spec or matrix != other or record["sharp_domain_empty"] != (matrix is None):
            raise ValueError("partial stationary full graph or independently derived domain changed")
        if matrix is None or "kernel_index" not in record:
            results.append(record)
            continue
        kernel_record = kernels[record["kernel_index"]]
        if kernel_record["source_index"] != index:
            raise ValueError("partial stationary kernel source owner changed")
        kernel = partial.kernel_gate(spec, kernel_record["certificate"])
        lower = [F(-matrix[i][0], constraints.SCALE) for i in range(1, b)]
        upper = [F(matrix[0][i], constraints.SCALE) for i in range(1, b)]
        angles, numerical = stationary(kernel, matrix, lower, upper, record["numerical"]["joint_angles"])
        certificate, _, strategy = refine(
            kernel, matrix, {"lower": list(map(str, lower)), "upper": list(map(str, upper))},
            angles, radius, arcs
        )
        checked = partial.bound(kernel, matrix, lower, upper, certificate, radius, arcs)
        record["fresh_boundary_stationary_discovery"] = numerical
        record["fresh_boundary_stationary_angles_not_a_proof"] = list(map(float, angles))
        old = record.get("discovery_exact_result")
        if old is None or F(checked["minimum_strict_energy_margin"]) > F(old["minimum_strict_energy_margin"]):
            record.update({
                "certificate": certificate, "discovery_exact_result": checked,
                "partial_energy_whole_root_proposed": checked["radius_at_most_Rstar_partial_whole_box_excluded"],
                "exact_energy_margin_for_discovery": float(F(checked["minimum_strict_energy_margin"])),
                "curvature_strategy": strategy,
            })
        results.append(record)
        print(json.dumps({"verified": False, "source_index": index, "B": b,
                          "partial_energy_whole_root_proposed": record["partial_energy_whole_root_proposed"],
                          "exact_energy_margin_for_discovery": record["exact_energy_margin_for_discovery"],
                          **numerical}), flush=True)
    for text, digest in hashes.items():
        if sha(text) != digest:
            raise ValueError("partial stationary source byte changed during discovery")
    report = {key: val for key, val in incoming.items() if key not in ("results", "files")}
    report.update({
        "results": results, "input_discovery_sha256": sha(args.proposal),
        "fresh_Schur_stationary_references_after_explicit_partial_kernel_gate": True,
        "proposed_strict_whole_root_exclusions": sum(row["partial_energy_whole_root_proposed"] for row in results),
        "current_transport_subtrees_removed": 0,
        "files": hashes, "executed_producer_sha256": sha(__file__),
    })
    args.output.write_text(json.dumps(report, separators=(",", ":")) + "\n", encoding="utf-8")
    print(json.dumps({key: val for key, val in report.items() if key not in ("results", "files")}, indent=2),
          flush=True)


if __name__ == "__main__":
    main()
