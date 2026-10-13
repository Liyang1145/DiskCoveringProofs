"""Exact unrestricted local lower bound using an interval polynomial barrier.

All numerical proposals are converted to rational data. Acceptance uses only
standard-library integers/Fraction and outward-rounded integer intervals.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
from math import isqrt
import json
from pathlib import Path

from verify_contact_root import sha


S = 10**40
ZERO = (0, 0)
ONE = (S, S)


def rational(value):
    value = F(value) * S
    return value.numerator // value.denominator, -((-value.numerator) // value.denominator)


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def neg(a):
    return -a[1], -a[0]


def sub(a, b):
    return add(a, neg(b))


def mul(a, b):
    values = [x * y for x in a for y in b]
    return min(values) // S, -((-max(values)) // S)


def square(a):
    values = [a[0]**2, a[1]**2]
    low = 0 if a[0] <= 0 <= a[1] else min(values)
    return low // S, -((-max(values)) // S)


def divide(a, b):
    if b[0] <= 0 <= b[1]:
        raise ValueError("local denominator could vanish")
    values = [F(x * S, y) for x in a for y in b]
    lo, hi = min(values), max(values)
    return lo.numerator // lo.denominator, -((-hi.numerator) // hi.denominator)


def sqrt_iv(a):
    if a[0] < 0:
        raise ValueError("negative local square-root domain")
    lo, hi = isqrt(a[0] * S), isqrt(a[1] * S)
    return lo, hi + (hi * hi < a[1] * S)


def times(k, a):
    return (k * a[0], k * a[1]) if k >= 0 else (k * a[1], k * a[0])


def norm(a):
    return add(square(a[0]), square(a[1]))


def cross(a, b):
    return sub(mul(a[0], b[1]), mul(a[1], b[0]))


def vsub(a, b):
    return [sub(x, y) for x, y in zip(a, b)]


def dist(a, b):
    return norm(vsub(a, b))


def padd(a, b):
    result = a.copy()
    for e, c in b.items():
        result[e] = result.get(e, 0) + c
    return {e: c for e, c in result.items() if c}


def pneg(a):
    return {e: -c for e, c in a.items()}


def psub(a, b):
    return padd(a, pneg(b))


def pmul(a, b):
    result = {}
    for e, c in a.items():
        for f, d in b.items():
            powers = tuple(x + y for x, y in zip(e, f))
            result[powers] = result.get(powers, 0) + c * d
    return {e: c for e, c in result.items() if c}


def pscale(k, a):
    return {e: k * c for e, c in a.items()}


def pnorm(a):
    return padd(pmul(a[0], a[0]), pmul(a[1], a[1]))


def pcross(a, b):
    return psub(pmul(a[0], b[1]), pmul(a[1], b[0]))


def pvector_sub(a, b):
    return [psub(x, y) for x, y in zip(a, b)]


def template(count):
    d = 2 * count + 1
    one = {(0,) * d: 1}
    variables = []
    for i in range(d):
        e = [0] * d
        e[i] = 1
        variables.append({tuple(e): 1})
    points = [variables[2 * i:2 * i + 2] for i in range(count)]
    t = variables[-1]
    if count == 3:
        a, b, c = points
        determinant = pcross(pvector_sub(b, a), pvector_sub(c, a))
        result = pscale(4, pmul(t, pmul(determinant, determinant)))
        product = one
        for x, y in ((a, b), (b, c), (c, a)):
            product = pmul(product, pnorm(pvector_sub(x, y)))
        return psub(result, product)
    a, b = points
    h, k = [psub(padd(one, pnorm(p)), t) for p in (a, b)]
    nx = psub(pmul(h, b[1]), pmul(a[1], k))
    ny = psub(pmul(a[0], k), pmul(h, b[0]))
    determinant = pcross(a, b)
    return psub(padd(pmul(nx, nx), pmul(ny, ny)), pscale(4, pmul(determinant, determinant)))


def decode(poly, dimension):
    result = {}
    for term in poly:
        powers, coefficient = tuple(term["powers"]), int(term["coefficient"])
        if (len(powers) != dimension or powers in result or not coefficient
                or any(type(p) is not int or not 0 <= p <= 8 for p in powers)):
            raise ValueError("invalid local polynomial")
        result[powers] = coefficient
    return result


def derivative(poly, j):
    result = {}
    for e, c in poly.items():
        if e[j]:
            f = list(e)
            f[j] -= 1
            result[tuple(f)] = c * e[j]
    return result


def powers_for(box, maxima):
    result = []
    for interval, maximum in zip(box, maxima):
        row = [ONE]
        for k in range(maximum):
            row.append(mul(row[-1], interval))
        result.append(row)
    return result


def evaluate(poly, powers):
    result = ZERO
    for e, c in poly.items():
        value = rational(c)
        for j, k in enumerate(e):
            if k:
                value = mul(value, powers[j][k])
        result = add(result, value)
    return result


def source_gate(folder, proposal):
    report_path = folder / "VERIFIED.json"
    report = json.loads(report_path.read_text())
    if (not report["verified"] or not report["full_coordinate_equilibrium_proved"]
            or not report["same_root_equality_proved_by_contact_transport_and_uniqueness"]
            or report["local_optimality_proved"]
            or proposal["stress_acceptance_sha256"] != sha(report_path)):
        raise ValueError("unbound exact first-order stress")
    for name, digest in {**report["files"], **report["additional_files"]}.items():
        if sha(folder / name) != digest:
            raise ValueError("changed first-order stress evidence")
    original = json.loads((folder / "ORIGINAL-SYSTEM.json").read_text())
    root = json.loads((folder / "ROOT-CERTIFICATE.json").read_text())
    ledger = json.loads((folder / "STRESS-LEDGER.json").read_text())
    records = [row for row in ledger["full_coordinate_stress_ledger"] if row["orbit"] not in (0, 5, 7)]
    if proposal["contacts"] != [{key: row[key] for key in ("kind", "vertices", "orbit")} for row in records]:
        raise ValueError("local barrier omitted or changed a positive contact")
    return original, root, records


def parameter_gate(proposal):
    chosen = proposal["chosen"]
    alpha = F(chosen["alpha"])
    delta = F(proposal["suggested_neighbourhood_halfwidth"])
    q = int(chosen["preconditioner_denominator"])
    matrix = chosen["preconditioner_numerators"]
    if (not 0 < alpha <= 1000 or not 0 < delta <= F(1, 10**6) or q <= 0
            or proposal["gauge_deleted_coordinate"] != 1 or proposal["gauge_dimension"] != 51
            or len(matrix) != 51 or any(len(row) != 51 for row in matrix)):
        raise ValueError("invalid local barrier or gauge/preconditioner")
    for count in (2, 3):
        if decode(proposal["generic_raw_contact_polynomials"][str(count)], 2 * count + 1) != template(count):
            raise ValueError("local contact polynomial not independently reconstructed")
    return alpha, delta, q


def circle_point(points, t, sign=None):
    a, b = points
    delta = vsub(b, a)
    length2 = norm(delta)
    h = divide(sub(norm(b), norm(a)), rational(2))
    foot = [mul(divide(h, length2), x) for x in delta]
    radicand = sub(ONE, divide(square(h), length2))
    factor = sqrt_iv(divide(radicand, length2))
    side = [neg(delta[1]), delta[0]]
    if sign is None:
        # At the certified root the rational anchor from t is exact. Its
        # proximity isolates one of the two bisector/circle branches.
        ha, hb = [divide(sub(add(ONE, norm(p)), t), rational(2)) for p in points]
        determinant = cross(a, b)
        anchor = [
            divide(sub(mul(ha, b[1]), mul(a[1], hb)), determinant),
            divide(sub(mul(a[0], hb), mul(ha, b[0])), determinant)]
        matches = []
        for proposed_sign in (1, -1):
            q = [add(x, times(proposed_sign, mul(factor, y))) for x, y in zip(foot, side)]
            if dist(q, anchor)[1] < rational(F(1, 10**20))[0]:
                matches.append(proposed_sign)
        if len(matches) != 1:
            raise ValueError("boundary contact branch not isolated")
        sign = matches[0]
    return [add(x, times(sign, mul(factor, y))) for x, y in zip(foot, side)], sign


def circumcenter(points):
    a, b, c = points
    u, v = vsub(b, a), vsub(c, a)
    determinant = times(2, cross(u, v))
    uu, vv = norm(u), norm(v)
    return [
        add(a[0], divide(sub(mul(uu, v[1]), mul(u[1], vv)), determinant)),
        add(a[1], divide(sub(mul(u[0], vv), mul(uu, v[0])), determinant))]


def derive(original, root, records, proposal, progress=False):
    alpha, delta, q = parameter_gate(proposal)
    z = [F(int(n), int(root["Qx"])) for n in root["xnum"]]
    rho = F(1, 10**85)
    root_box = [[rational(0) if m["variable"] is None else
                 (rational(m["sign"] * z[m["variable"]] - rho)[0],
                  rational(m["sign"] * z[m["variable"]] + rho)[1])
                 for m in row] for row in original["center_map"]]
    centers = []
    for i, row in enumerate(original["center_map"]):
        center = []
        for j, m in enumerate(row):
            if i == 0 and j == 1:
                center.append(ZERO)
            else:
                value = F(0) if m["variable"] is None else m["sign"] * z[m["variable"]]
                center.append((rational(value - delta)[0], rational(value + delta)[1]))
        centers.append(center)
    t = (rational(z[13] - rho)[0], rational(z[13] + rho)[1])
    if root_box[0][0][0] <= rational(F(9, 10))[1] or any(norm(p)[1] >= S for p in root_box):
        raise ValueError("rotational gauge neighbourhood assumptions failed")
    polynomials = {count: template(count) for count in (2, 3)}
    derivatives = {count: [derivative(poly, i) for i in range(2 * count + 1)]
                   for count, poly in polynomials.items()}
    hessians = {count: [[derivative(derivatives[count][i], j) for j in range(2 * count)]
                        for i in range(2 * count)] for count in (2, 3)}
    maxima = {count: [max(e[j] for e in poly) for j in range(2 * count + 1)]
              for count, poly in polynomials.items()}
    hessian = [[ZERO for j in range(51)] for i in range(51)]
    all_gaps, all_signs, score_bounds = [], [], []
    for index, record in enumerate(records):
        ids = record["vertices"]
        count = len(ids)
        contact_root = [coordinate for i in ids for coordinate in root_box[i]] + [t]
        contact_near = [coordinate for i in ids for coordinate in centers[i]] + [t]
        point_powers = powers_for(contact_root, maxima[count])
        near_powers = powers_for(contact_near, maxima[count])
        kappa = evaluate(derivatives[count][-1], point_powers)
        if kappa[0] <= 0 <= kappa[1]:
            raise ValueError("root contact's t derivative can vanish")
        weight = (rational(record["physical_stress_interval"][0])[0],
                  rational(record["physical_stress_interval"][1])[1])
        if weight[0] <= 0:
            raise ValueError("barrier uses a nonpositive pressure")
        value = evaluate(polynomials[count], near_powers)
        score = divide(value, kappa)
        if mul(rational(2 * alpha), (0, max(abs(score[0]), abs(score[1]))))[1] >= weight[0]:
            raise ValueError("quadratic penalty not dominated by linear pressure in the neighbourhood")
        gradients = [divide(evaluate(p, near_powers), kappa) for p in derivatives[count][:-1]]
        curvature = [[divide(evaluate(p, near_powers), kappa) for p in row] for row in hessians[count]]
        coordinates = [2 * i + j for i in ids for j in range(2)]
        for i, row in enumerate(curvature):
            u = coordinates[i]
            if u == 1:
                continue
            u -= u > 1
            for j in range(i, len(row)):
                v = coordinates[j]
                if v == 1:
                    continue
                v -= v > 1
                term = neg(mul(weight, row[j]))
                term = add(term, mul(rational(2 * alpha),
                                     add(mul(gradients[i], gradients[j]), mul(score, row[j]))))
                hessian[u][v] = add(hessian[u][v], term)
                if u != v:
                    hessian[v][u] = add(hessian[v][u], term)
        if count == 3:
            witness = circumcenter([centers[i] for i in ids])
            if norm(witness)[1] >= S:
                raise ValueError("local Voronoi witness could leave the unit disk")
        else:
            _, sign = circle_point([root_box[i] for i in ids], t)
            witness, _ = circle_point([centers[i] for i in ids], t, sign)
        radius2 = dist(witness, centers[ids[0]])
        gaps = [dist(witness, centers[i])[0] - radius2[1] for i in range(26) if i not in ids]
        if min(gaps) <= 0:
            raise ValueError("positive contact's local nearest-center status not strictly preserved")
        all_gaps.append(min(gaps))
        t_range = (min(t[0], radius2[0]), max(t[1], radius2[1]))
        sign_powers = powers_for(contact_near[:-1] + [t_range], maxima[count])
        derivative_ratio = divide(evaluate(derivatives[count][-1], sign_powers), kappa)
        if derivative_ratio[0] <= 0:
            raise ValueError("local polynomial score does not keep the covering-inequality sign")
        all_signs.append(derivative_ratio[0])
        score_bounds.append(max(abs(score[0]), abs(score[1])))
        if progress and (index + 1) % 12 == 0:
            print(json.dumps({"full_coordinate_barrier_contacts_checked": index + 1, "of": len(records)}), flush=True)
    matrix = [[rational(F(int(n), q)) for n in row]
              for row in proposal["chosen"]["preconditioner_numerators"]]
    # Exact outward interval R^T H R. Sparsity is just an optimization.
    rows = [[(j, a) for j, a in enumerate(row) if a != ZERO] for row in hessian]
    product = [[ZERO for j in range(51)] for i in range(51)]
    for i in range(51):
        for j in range(51):
            total = ZERO
            for k, value in rows[i]:
                if matrix[k][j] != ZERO:
                    total = add(total, mul(value, matrix[k][j]))
            product[i][j] = total
    transformed = [[ZERO for j in range(51)] for i in range(51)]
    columns = [[(k, matrix[k][i]) for k in range(51) if matrix[k][i] != ZERO] for i in range(51)]
    for i in range(51):
        for j in range(51):
            total = ZERO
            for k, value in columns[i]:
                total = add(total, mul(value, product[k][j]))
            transformed[i][j] = total
    margins = [
        transformed[i][i][0] - sum(max(abs(transformed[i][j][0]), abs(transformed[i][j][1]))
                                  for j in range(51) if j != i)
        for i in range(51)]
    if min(margins) <= 0:
        raise ValueError("local barrier Hessian not proved positive definite on the whole box")
    return {
        "gauge_dimension": 51, "only_removed_coordinate_is_rotation_gauge_y0": True,
        "neighbourhood_halfwidth": str(delta),
        "unrestricted_center_neighbourhood_halfwidth_before_rotation": str(delta / 8),
        "penalty_coefficient": str(alpha),
        "exact_interval_scale": str(S),
        "strict_preconditioned_Hessian_Gershgorin_margin": str(F(min(margins), S)),
        "strict_nearest_other_center_squared_distance_margin": str(F(min(all_gaps), S)),
        "minimum_contact_polynomial_radius_derivative_ratio": str(F(min(all_signs), S)),
        "maximum_normalized_contact_score_absolute": str(F(max(score_bounds), S)),
        "all_36_positive_contacts_stable_and_necessary_for_covering": True,
        "barrier_Hessian_positive_definite_on_entire_51_coordinate_box": True,
        "all_nonrotation_perturbations_included": True,
        "strict_local_optimality_modulo_rotations_proved": True}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--stress", type=Path, required=True)
    parser.add_argument("--proposal", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    proposal = json.loads(args.proposal.read_text())
    original, root, records = source_gate(args.stress, proposal)
    result = derive(original, root, records, proposal, progress=True)
    negatives = []

    def reject(label, fn):
        try:
            fn()
        except (ValueError, KeyError, TypeError):
            negatives.append(label)
        else:
            raise AssertionError("bad local barrier accepted: " + label)

    bad = deepcopy(proposal)
    bad["contacts"].pop()
    reject("omitted-positive-contact", lambda: source_gate(args.stress, bad))
    bad = deepcopy(proposal)
    bad["generic_raw_contact_polynomials"]["3"][0]["coefficient"] = "100"
    reject("changed-contact-polynomial", lambda: parameter_gate(bad))
    bad = deepcopy(proposal)
    bad["gauge_dimension"] = 13
    reject("D2-only-perturbation-domain", lambda: parameter_gate(bad))
    bad = deepcopy(proposal)
    bad["chosen"]["preconditioner_numerators"] = [["0"] * 51 for i in range(51)]
    reject("zero-preconditioner", lambda: derive(original, root, records, bad))
    bad = deepcopy(proposal)
    bad["stress_acceptance_sha256"] = "0" * 64
    reject("unbound-first-order-equilibrium", lambda: source_gate(args.stress, bad))
    args.output.mkdir(parents=True)
    certificate_path = args.output / "CERTIFICATE.json"
    certificate_path.write_bytes(args.proposal.read_bytes())
    checker_path = args.output / "verify_local_barrier.py"
    checker_path.write_bytes(Path(__file__).read_bytes())
    proof = Path(__file__).with_name("n26-local-barrier-proof.md")
    if not proof.exists():
        proof = Path(__file__).with_name("PROOF.md")
    proof_path = args.output / "PROOF.md"
    proof_path.write_bytes(proof.read_bytes())
    report = {
        "schema": "N26-unrestricted-exact-polynomial-local-lower-v1",
        "verified": True, **result,
        "same_root_entire_disk_cover_already_proved": True,
        "local_optimality_proved": True, "global_optimality_proved": False,
        "proof_scope": "Specified labelled candidate, all sufficiently small unrestricted center perturbations, modulo rotation",
        "formal_machine_geometry_proof": False,
        "negative_controls_rejected": negatives,
        "files": {p.name: sha(p) for p in (certificate_path, checker_path, proof_path)},
        "stress_acceptance_sha256": sha(args.stress / "VERIFIED.json")}
    (args.output / "VERIFIED.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: value for key, value in report.items() if key != "files"}, indent=2), flush=True)


if __name__ == "__main__":
    main()
