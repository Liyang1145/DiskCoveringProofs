"""Extract a D2-symmetric candidate system, not an arbitrary-cover restriction."""

import argparse
import hashlib
import json
from pathlib import Path

import mpmath as mp
import numpy as np
import sympy as sp
from scipy.optimize import linprog

from moving_vertex_search import components, values_gradients


WORK = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def primitive(expression, variables):
    poly = sp.Poly(sp.expand(expression), *variables, domain=sp.QQ)
    _, poly = poly.clear_denoms()
    _, poly = poly.primitive()
    if poly.LC() < 0:
        poly = -poly
    return poly


def sparse(poly):
    return [{"coefficient": str(coefficient), "powers": [int(value) for value in powers]}
            for powers, coefficient in poly.terms()]


def cross(a, b):
    return a[0] * b[1] - a[1] * b[0]


def sub(a, b):
    return [a[0] - b[0], a[1] - b[1]]


def norm(a):
    return a[0] ** 2 + a[1] ** 2


def face_polynomial(points, face, t):
    a, b, c = [points[i] for i in face]
    return 4 * t * cross(sub(b, a), sub(c, a)) ** 2 - norm(sub(a, b)) * norm(sub(b, c)) * norm(sub(c, a))


def anchor_polynomial(points, edge, t):
    a, b = [points[i] for i in edge]
    h, k = 1 + norm(a) - t, 1 + norm(b) - t
    return (h * b[1] - a[1] * k) ** 2 + (a[0] * k - h * b[0]) ** 2 - 4 * cross(a, b) ** 2


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    path = WORK / "moving-vertex-search-v1/best-centers.npy"
    cnum = np.load(path)
    desc = components(cnum)
    values, gradients = values_gradients(cnum, desc)
    tnum = float(values.max())
    variables = sp.symbols("a b c d e f g h u v w z s t")
    a, b, c, d, e, f, g, h, u, v, w, z, s, t = variables
    points = [
        [a, 0], [c, d], [e, f], [g, h], [0, b], [-g, h], [-e, f], [-c, d],
        [-a, 0], [-c, -d], [-e, -f], [-g, -h], [0, -b], [g, -h], [e, -f], [c, -d],
        [s, 0], [u, 0], [w, z], [0, v], [-w, z], [-u, 0], [-w, -z], [0, -v],
        [w, -z], [-s, 0],
    ]
    seed = [
        cnum[0, 0], cnum[4, 1], cnum[1, 0], cnum[1, 1], cnum[2, 0], cnum[2, 1],
        cnum[3, 0], cnum[3, 1], cnum[17, 0], cnum[19, 1], cnum[18, 0], cnum[18, 1],
        cnum[16, 0], tnum,
    ]
    substitutions = dict(zip(variables, seed))
    symmetry_error = max(abs(float(sp.sympify(value).subs(substitutions)) - cnum[i, k])
                         for i, point in enumerate(points) for k, value in enumerate(point))
    if symmetry_error > 1e-10:
        raise ValueError("candidate is not in this D2 coordinate chart")
    active_faces = []
    slack_faces = []
    polynomials, metadata, factor_checks = [], [], []
    seen = set()
    ntri = len(desc["triangles"])
    for index, face in enumerate(desc["triangles"]):
        gap = tnum - values[index]
        if gap > 1e-8:
            slack_faces.append({"face": face.tolist(), "floating_squared_slack": float(gap)})
            continue
        active_faces.append(face.tolist())
        full = primitive(face_polynomial(points, face, t), variables)
        factors = sp.factor_list(full.as_expr(), *variables)[1]
        zero_factors = [factor for factor, multiplicity in factors
                        if abs(float(factor.subs(substitutions))) < 1e-8]
        if len(zero_factors) != 1:
            raise ValueError(("ambiguous active factor", face.tolist(), factors))
        chosen = primitive(zero_factors[0], variables)
        key = tuple(chosen.terms())
        if key not in seen:
            seen.add(key)
            polynomials.append(chosen)
            metadata.append({"kind": "active-face-orbit", "representative": face.tolist()})
        factor_checks.append({
            "face": face.tolist(), "full_polynomial": sparse(full),
            "chosen_polynomial": sparse(chosen),
            "other_factors": [
                {"polynomial": sparse(primitive(factor, variables)),
                 "multiplicity": int(multiplicity)}
                for factor, multiplicity in factors if factor != zero_factors[0]
            ],
        })
    for edge in desc["pairs"]:
        full = primitive(anchor_polynomial(points, edge, t), variables)
        key = tuple(full.terms())
        if key not in seen:
            seen.add(key)
            polynomials.append(full)
            metadata.append({"kind": "boundary-anchor-orbit", "representative": edge.tolist()})
    contact_count = len(polynomials)
    geometry_variables = variables
    contacts = sp.Matrix([poly.as_expr() for poly in polynomials])
    contact_jacobian = contacts.jacobian(geometry_variables)
    jc = np.asarray(contact_jacobian.subs(substitutions), dtype=float)
    physical_grad = -jc[:, :-1] / jc[:, -1, None]
    weight_lp = linprog(np.zeros(contact_count),
                        A_eq=np.vstack((physical_grad.T, np.ones(contact_count))),
                        b_eq=np.r_[np.zeros(len(variables)-1), 1.],
                        bounds=(0., None), method="highs")
    objective = np.zeros(len(geometry_variables))
    objective[-1] = 1.
    multiplier_seed = np.linalg.lstsq(jc.T, objective, rcond=None)[0]
    multipliers = sp.symbols(f"mu0:{contact_count}")
    lagrangian = t - sum(mu * equation for mu, equation in zip(multipliers, contacts))
    variables = geometry_variables + multipliers
    stationary = [sp.diff(lagrangian, value) for value in geometry_variables]
    expressions = sp.Matrix(list(contacts) + stationary)
    jacobian = expressions.jacobian(variables)
    seed = list(seed) + multiplier_seed.tolist()
    substitutions = dict(zip(variables, seed))
    jac = np.asarray(jacobian.subs(substitutions), dtype=float)
    singular_values = np.linalg.svd(jac, compute_uv=False)
    polynomials = [primitive(expression, variables) for expression in expressions]
    metadata += [{"kind": "D2-stationarity", "variable": str(value)}
                 for value in geometry_variables]
    print(json.dumps({"dimension": len(variables), "contact_orbits": contact_count,
                      "active_faces": len(active_faces), "slack_faces": len(slack_faces),
                      "symmetry_error": symmetry_error,
                      "contact_jacobian_rank": int(np.linalg.matrix_rank(jac[:contact_count])),
                      "augmented_singular_values": singular_values.tolist(),
                      "contact_equation_metadata": metadata[:contact_count],
                      "physical_stress_lp_success": bool(weight_lp.success),
                      "physical_stress_weights": None if not weight_lp.success else weight_lp.x.tolist(),
                      "contact_jacobian_singular_values": np.linalg.svd(jc, compute_uv=False).tolist(),
                      "signed_multiplier_seed": multiplier_seed.tolist(),
                      "stationarity_seed_residual": float(np.max(np.abs(jc.T @ multiplier_seed-objective))),
                      "jacobian_smallest_singular_value": float(singular_values[-1]),
                      "jacobian_condition": float(singular_values[0] / singular_values[-1])}), flush=True)
    if singular_values[-1] < 1e-14:
        raise ValueError("candidate definition is numerically singular; not an isolating root system")
    mp.mp.dps = 130
    # Use exactly the primitive integer system that the independent checker
    # will read, not a differently scaled symbolic system.
    expressions = sp.Matrix([poly.as_expr() for poly in polynomials])
    jacobian = expressions.jacobian(variables)
    func = sp.lambdify(variables, expressions, "mpmath", cse=True)
    jfunc = sp.lambdify(variables, jacobian, "mpmath", cse=True)
    solution = mp.matrix([mp.mpf(str(value)) for value in seed])
    history = []
    for iteration in range(15):
        residual = func(*solution)
        maximum = max(abs(value) for value in residual)
        history.append({"iteration": iteration, "max_residual": mp.nstr(maximum, 12)})
        if maximum < mp.mpf("1e-115"):
            break
        solution -= mp.lu_solve(jfunc(*solution), residual)
    if max(abs(value) for value in func(*solution)) >= mp.mpf("1e-110"):
        raise ValueError("high-precision proposal did not converge")
    inverse = jfunc(*solution) ** -1
    Qx, Qy = 10**100, 10**90
    args.output.mkdir(parents=True)
    center_map = []
    for point in points:
        row = []
        for value in point:
            value = sp.sympify(value)
            if value == 0:
                row.append({"variable": None, "sign": 0})
            else:
                coefficient, symbol = value.as_coeff_Mul()
                row.append({"variable": variables.index(symbol), "sign": int(coefficient)})
        center_map.append(row)
    system = {
        "schema": "N26-D2-candidate-contact-polynomial-system-v1",
        "N": 26, "B": 16, "dimension": len(variables),
        "variables": list(map(str, variables)), "radius_squared_index": 13,
        "geometry_variable_count": len(geometry_variables), "contact_equation_count": contact_count,
        "center_map": center_map, "equations": list(map(sparse, polynomials)),
        "equation_metadata": metadata,
        "all_faces": desc["triangles"].tolist(), "active_faces": active_faces,
        "slack_faces": slack_faces,
        "boundary_edges": desc["pairs"].tolist(),
        "face_factor_checks": factor_checks,
        "D2_symmetry_and_stationarity_are_candidate_only": True,
        "positive_stress_proved": False, "local_optimality_proved": False,
        "global_optimality_proved": False,
        "numeric_source_sha256": sha(path),
    }
    system_path = args.output / "SYSTEM.json"
    system_path.write_text(json.dumps(system, indent=2) + "\n", encoding="utf-8")
    proposal = {
        "schema": "N26-D2-contact-root-proposal-v1",
        "system_sha256": sha(system_path), "Qx": str(Qx), "Qy": str(Qy),
        "xnum": [str(int(mp.nint(value * Qx))) for value in solution],
        "Ynum": [[str(int(mp.nint(inverse[i, j] * Qy))) for j in range(len(variables))]
                 for i in range(len(variables))],
        "proposed_radius": mp.nstr(mp.sqrt(solution[13]), 110),
        "newton_history": history, "verified": False,
        "global_optimality_proved": False,
        "builder_source_sha256": sha(__file__),
    }
    (args.output / "ROOT-PROPOSAL.json").write_text(json.dumps(proposal, indent=2) + "\n",
                                                 encoding="utf-8")
    print(json.dumps({"proposed_radius": proposal["proposed_radius"],
                      "polynomial_terms": [len(poly.terms()) for poly in polynomials],
                      "verified": False}), flush=True)


if __name__ == "__main__":
    main()
