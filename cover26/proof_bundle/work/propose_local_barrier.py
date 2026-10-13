"""Untrusted full-coordinate polynomial-barrier curvature proposal.

Stores a rational preconditioner for a future exact neighbourhood verifier.
Does NOT accept local/global optimality.
"""

import argparse
from fractions import Fraction as F
import json
from pathlib import Path

import numpy as np
import sympy as sp

from verify_contact_root import sha


WORK = Path(__file__).resolve().parent


def raw_template(count):
    variables = sp.symbols(" ".join(f"x{i}" for i in range(2 * count)) + " t")
    t = variables[-1]
    points = [sp.Matrix(variables[2 * i:2 * i + 2]) for i in range(count)]
    if count == 3:
        a, b, c = points
        u, v = b - a, c - a
        determinant = u[0] * v[1] - u[1] * v[0]
        polynomial = 4 * t * determinant**2
        polynomial -= (a - b).dot(a - b) * (b - c).dot(b - c) * (c - a).dot(c - a)
    else:
        a, b = points
        h, k = 1 + a.dot(a) - t, 1 + b.dot(b) - t
        polynomial = (h * b[1] - a[1] * k)**2 + (a[0] * k - h * b[0])**2
        polynomial -= 4 * (a[0] * b[1] - a[1] * b[0])**2
    coordinates = variables[:-1]
    derivative = sp.Matrix([sp.diff(polynomial, x) for x in coordinates])
    hessian = derivative.jacobian(coordinates)
    fun = sp.lambdify(variables, (polynomial, sp.diff(polynomial, t), derivative, hessian),
                      "numpy", cse=True)
    sparse = [{"powers": list(map(int, powers)), "coefficient": str(coefficient)}
              for powers, coefficient in sp.Poly(sp.expand(polynomial), *variables).terms()]
    return fun, sparse


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    folder = WORK.parent / "outputs/n26-positive-stress-v1"
    accepted = json.loads((folder / "VERIFIED.json").read_text())
    for name, digest in {**accepted["files"], **accepted["additional_files"]}.items():
        if sha(folder / name) != digest:
            raise ValueError("accepted first-order evidence changed")
    system = json.loads((folder / "ORIGINAL-SYSTEM.json").read_text())
    certificate = json.loads((folder / "ROOT-CERTIFICATE.json").read_text())
    root = [float(F(int(n), int(certificate["Qx"]))) for n in certificate["xnum"]]
    centers = np.array([[0 if m["variable"] is None else root[m["variable"]] * m["sign"]
                         for m in row] for row in system["center_map"]])
    stress = json.loads((folder / "STRESS-LEDGER.json").read_text())
    templates = {count: raw_template(count) for count in (2, 3)}
    hessian, penalty = np.zeros((52, 52)), np.zeros((52, 52))
    balance = np.zeros(52)
    contacts = []
    for record in stress["full_coordinate_stress_ledger"]:
        if record["orbit"] in (0, 5, 7):
            continue
        indices = record["vertices"]
        count = len(indices)
        fun, encoded = templates[count]
        value, dt, grad, hess = fun(*centers[indices].ravel(), root[13])
        weight = float(sum(map(F, record["physical_stress_interval"]), F(0)) / 2)
        gradient = np.asarray(grad).ravel() / float(dt)
        curvature = np.asarray(hess) / float(dt)
        coords = [2 * i + j for i in indices for j in range(2)]
        balance[coords] -= weight * gradient
        hessian[np.ix_(coords, coords)] -= weight * curvature
        penalty[np.ix_(coords, coords)] += 2 * np.outer(gradient, gradient)
        contacts.append({"kind": record["kind"], "vertices": indices, "orbit": record["orbit"]})
    # Rotational gauge y0=0 is the only deleted coordinate.
    gauge_indices = [i for i in range(52) if i != 1]
    proposals = []
    chosen = None
    for alpha in (F(1, 10), F(1), F(10), F(100), F(1000)):
        matrix = (hessian + float(alpha) * penalty)[np.ix_(gauge_indices, gauge_indices)]
        eigenvalues = np.linalg.eigvalsh((matrix + matrix.T) / 2)
        proposals.append({"alpha": str(alpha), "minimum_eigenvalue_proposal": float(eigenvalues[0]),
                          "maximum_eigenvalue_proposal": float(eigenvalues[-1])})
        if eigenvalues[0] > .001 and chosen is None:
            factor = np.linalg.cholesky(matrix)
            preconditioner = np.linalg.solve(factor.T, np.eye(51))
            scale = 10**14
            chosen = {"alpha": str(alpha), "preconditioner_denominator": str(scale),
                      "preconditioner_numerators": [[str(round(float(x) * scale)) for x in row]
                                                   for row in preconditioner]}
    args.output.write_text(json.dumps({
        "schema": "N26-full-coordinate-polynomial-barrier-coercivity-proposal-v1",
        "verified": False, "stress_acceptance_sha256": sha(folder / "VERIFIED.json"),
        "contacts": contacts, "generic_raw_contact_polynomials": {
            str(count): encoded for count, (fun, encoded) in templates.items()},
        "gauge_deleted_coordinate": 1, "gauge_dimension": 51,
        "gradient_balance_float_residual": float(np.max(np.abs(balance))),
        "curvature_proposals": proposals, "chosen": chosen,
        "suggested_neighbourhood_halfwidth": "1/100000000",
        "local_optimality_proved": False, "global_optimality_proved": False},
        indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"verified": False, "full_gauge_dimension": 51,
                      "gradient_balance_residual": float(np.max(np.abs(balance))),
                      "curvature_proposals": proposals, "chosen_alpha": None if chosen is None else chosen["alpha"],
                      "local_optimality_proved": False}), flush=True)


if __name__ == "__main__":
    main()
