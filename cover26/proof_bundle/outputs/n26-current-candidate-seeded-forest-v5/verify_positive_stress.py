"""Exact same-root zero multipliers and full-coordinate nonnegative stress.

First-order equilibrium only: this is NOT a local minimum certificate.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
from functools import reduce
from math import gcd
import json
from pathlib import Path

import verify_contact_root as exact
import verify_same_root_cover as geo


WEAK = (0, 5, 7)
STRONG = tuple(i for i in range(12) if i not in WEAK)


def primitive26(poly):
    if not poly:
        raise ValueError("zero polynomial")
    coefficients = [c for c in poly.values()]
    denominator = 1
    for c in coefficients:
        denominator = denominator * c.denominator // gcd(denominator, c.denominator)
    integers = {e: int(c * denominator) for e, c in poly.items() if c}
    divisor = reduce(gcd, (abs(c) for c in integers.values()))
    sign = 1 if integers[max(integers)] > 0 else -1
    return {e: F(sign * c // divisor) for e, c in integers.items()}


def dictionary(poly):
    return {powers: coefficient for coefficient, powers in poly}


def add_poly(a, b):
    result = a.copy()
    for powers, coefficient in b.items():
        result[powers] = result.get(powers, F(0)) + coefficient
    return {powers: c for powers, c in result.items() if c}


def derivative_dict(poly, j):
    return dictionary(exact.derivative(list((c, e) for e, c in poly.items()), j))


def shape_gate(original, modified):
    if (original["dimension"] != 26 or original["radius_squared_index"] != 13
            or original["contact_equation_count"] != 12
            or original["geometry_variable_count"] != 14
            or modified["zero_stress_contact_indices"] != list(WEAK)):
        raise ValueError("wrong stress-system dimensions")
    _, original_polys, _, _ = exact.prepare(original)
    _, modified_polys, _, _ = exact.prepare(modified)
    contacts = list(map(dictionary, original_polys[:12]))
    # Independently reconstruct all stationarity equations from t-sum mu*P.
    for j in range(14):
        result = {(0,) * 26: F(int(j == 13))}
        for i, contact in enumerate(contacts):
            derivative = derivative_dict(contact, j)
            for powers, coefficient in derivative.items():
                exponent = list(powers)
                exponent[14 + i] += 1
                result = add_poly(result, {tuple(exponent): -coefficient})
        if primitive26(result) != dictionary(original_polys[12 + j]):
            raise ValueError("original stationarity is not the derivative of the contact Lagrangian")
    for i in range(26):
        expected = dictionary(original_polys[i])
        if i in WEAK:
            powers = [0] * 26
            powers[14 + i] = 1
            expected = {tuple(powers): F(1)}
        if dictionary(modified_polys[i]) != expected:
            raise ValueError("stress root changed more than the three zero-multiplier equations")
    if any(modified[key] != original[key] for key in (
            "center_map", "all_faces", "active_faces", "boundary_edges", "face_factor_checks",
            "equation_metadata", "variables")):
        raise ValueError("candidate coordinate/contact geometry changed")
    # Each of these coordinate stationarities leaves a single nonzero
    # multiplier once the three weak multipliers are exactly zero.
    for variable, selected in ((0, 8), (8, 2), (12, 6)):
        support = [i for i in STRONG if derivative_dict(contacts[i], variable)]
        if support != [selected]:
            raise ValueError("singleton-coordinate stationary identity missing")
    return original_polys


def interval_root(certificate, rho):
    z = [F(int(n), int(certificate["Qx"])) for n in certificate["xnum"]]
    return z, [(v - rho, v + rho) for v in z]


def barycentrics(points, face, witness):
    a, b, c = [points[i] for i in face]
    u, v = geo.vsub(b, a, exact.sub), geo.vsub(c, a, exact.sub)
    w = geo.vsub(witness, a, exact.sub)
    determinant = geo.ivcross(u, v)
    left = geo.ivdiv(geo.ivcross(w, v), determinant)
    right = geo.ivdiv(geo.ivcross(u, w), determinant)
    return [exact.sub(exact.sub(exact.point(1), left), right), left, right]


def transport_checks(original, certificate, original_polys):
    z, box = interval_root(certificate, F(1, 10**85))
    points = [[exact.point(0) if m["variable"] is None else
               exact.scale(m["sign"], box[m["variable"]]) for m in row]
              for row in original["center_map"]]
    contacts14 = [geo.primitive(geo.read_poly(p, 26)) for p in original["equations"][:12]]
    polypoints = [[{} if m["variable"] is None else
                   geo.variable(m["variable"], m["sign"]) for m in row]
                  for row in original["center_map"]]
    # Reconstruct the three raw face identities and their nonzero quotients.
    factors = (
        (0, (0, 1, 17), geo.pk(-1, geo.pp(geo.ps(geo.variable(0), geo.variable(8))))),
        (5, (16, 17, 18), geo.pk(-1, geo.pp(geo.ps(geo.variable(12), geo.variable(8))))),
        (7, (16, 19, 25), geo.pk(-4, geo.pp(geo.variable(12)))),
    )
    for i, face, factor in factors:
        if geo.face_poly(polypoints, face) != geo.pm(factor, contacts14[i]):
            raise ValueError("weak contact's independent exact nonzero-factor identity failed")
    if (box[0][0] <= box[8][1] or box[8][0] <= box[12][1] or box[12][0] <= 0):
        raise ValueError("weak face quotient could vanish")
    # All retained activity and boundary factor identities are checked exactly.
    records = {tuple(row["face"]): row for row in original["face_factor_checks"]}
    for i in STRONG:
        meta = original["equation_metadata"][i]
        if meta["kind"] == "active-face-orbit":
            face = tuple(meta["representative"])
            raw = geo.face_poly(polypoints, face)
            chosen = contacts14[i]
            if (geo.primitive(geo.read_poly(records[face]["chosen_polynomial"], 14)) != chosen
                    or not geo.divides(chosen, raw)):
                raise ValueError("strong face identity does not follow from the new root")
        elif meta["kind"] == "boundary-anchor-orbit":
            a, b = meta["representative"]
            if b != a + 1 or geo.primitive(geo.boundary_poly(polypoints, a)) != contacts14[i]:
                raise ValueError("strong boundary identity does not follow from the new root")
        else:
            raise ValueError("unknown retained contact kind")
    a, b = points[0], points[1]
    h, k = [exact.scale(F(1, 2), exact.sub(exact.add(exact.point(1), geo.ivnorm(p)), box[13]))
            for p in (a, b)]
    determinant = geo.ivcross(a, b)
    q = [
        geo.ivdiv(exact.sub(exact.mul(h, b[1]), exact.mul(a[1], k)), determinant),
        geo.ivdiv(exact.sub(exact.mul(a[0], k), exact.mul(h, b[0])), determinant)]
    ta = exact.sub(exact.mul(a[1], q[0]), exact.mul(a[0], q[1]))
    tb = exact.sub(exact.mul(b[1], q[0]), exact.mul(b[0], q[1]))
    gamma0 = geo.ivdiv(exact.scale(F(-1), tb), exact.sub(ta, tb))
    witness_u = geo.circumcenter(points, (1, 17, 18))
    witness_s = geo.circumcenter(points, (16, 18, 19))
    gamma_u = barycentrics(points, (1, 17, 18), witness_u)[1]
    gamma_s = barycentrics(points, (16, 18, 19), witness_s)[0]
    if min(gamma0[0], gamma_u[0], gamma_s[0], q[1][0], witness_u[1][0], witness_s[1][0]) <= 0:
        raise ValueError("stationary-coordinate witness branch is degenerate")
    maxima = [max(e[j] for p in original_polys[:12] for c, e in p) for j in range(26)]
    powers = exact.powers_for(box, maxima)
    pressure = {}
    for i in STRONG:
        dt = exact.evaluate(exact.derivative(original_polys[i], 13), powers)
        if not geo.nonzero(dt) or box[14 + i][1] >= 0:
            raise ValueError("strong multiplier or radius derivative sign not separated")
        weight = exact.mul(box[14 + i], dt)
        if weight[0] <= 0:
            raise ValueError("physical orbit stress not strictly positive")
        pressure[i] = weight
    # Classification of every full-coordinate contact by its checked orbit.
    contacts = [tuple(sorted(p.items())) for p in contacts14]
    orbits = {i: [] for i in range(12)}
    for face in original["active_faces"]:
        polynomial = geo.primitive(geo.read_poly(records[tuple(face)]["chosen_polynomial"], 14))
        index = contacts.index(tuple(sorted(polynomial.items())))
        orbits[index].append({"kind": "face", "vertices": face})
    for i in range(16):
        polynomial = geo.primitive(geo.boundary_poly(polypoints, i))
        index = contacts.index(tuple(sorted(polynomial.items())))
        orbits[index].append({"kind": "boundary", "vertices": [i, (i + 1) % 16]})
    # Establish that each orbit really is invariant under both reflections.
    descriptors = [tuple((m["variable"], m["sign"]) for m in row) for row in original["center_map"]]
    for axis in (0, 1):
        permutation = []
        for row in original["center_map"]:
            transformed = tuple((m["variable"], -m["sign"] if j == axis else m["sign"])
                                for j, m in enumerate(row))
            permutation.append(descriptors.index(transformed))
        for members in orbits.values():
            target = {(m["kind"], frozenset(m["vertices"])) for m in members}
            if {(m["kind"], frozenset(permutation[v] for v in m["vertices"])) for m in members} != target:
                raise ValueError("proposed orbit is not a full reflection orbit")
    ledger = []
    for i, members in orbits.items():
        if not members:
            raise ValueError("empty stress orbit")
        weight = exact.scale(F(1, len(members)), pressure[i]) if i in STRONG else exact.point(0)
        for member in members:
            ledger.append({**member, "orbit": i, "physical_stress_interval": list(map(str, weight))})
    if sum(row["orbit"] in STRONG for row in ledger) != 36 or len(ledger) != 46:
        raise ValueError("unexpected full-coordinate stress support")
    return {
        "stationary_coordinate_branch_margins": {
            "boundary_gamma0_lower": str(gamma0[0]), "face_gamma_u_lower": str(gamma_u[0]),
            "face_gamma_s_lower": str(gamma_s[0])},
        "weak_contact_nonzero_factor_identities_reconstructed": True,
        "same_root_transport_relations": [
            "q0=(a,R)", "circumcenter(1,17,18)=(u,R)",
            "circumcenter(16,18,19)=(s,R)", "a+u=2*c", "u+s=2*w",
            "all_three_omitted_contact_polynomials_are_zero"],
        "physical_stress_orbit_intervals": {str(i): list(map(str, p)) for i, p in pressure.items()},
        "full_coordinate_stress_ledger": ledger,
        "strictly_positive_contacts": 36, "exactly_zero_stress_contacts": 10,
        "full_coordinate_equilibrium_via_reflection_invariance_and_stationarity": True}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--original", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    modified_path = args.input / "SYSTEM.json"
    proposed_path = args.input / "ROOT-PROPOSAL.json"
    if not proposed_path.exists():
        proposed_path = args.input / "ROOT-CERTIFICATE.json"
    original_path, old_root_path = args.original / "SYSTEM.json", args.original / "ROOT-CERTIFICATE.json"
    original = json.loads(original_path.read_text())
    old_root = json.loads(old_root_path.read_text())
    modified = json.loads(modified_path.read_text())
    proposed = json.loads(proposed_path.read_text())
    if (proposed["system_sha256"] != exact.sha(modified_path)
            or modified["original_system_sha256"] != exact.sha(original_path)
            or proposed["original_root_certificate_sha256"] != exact.sha(old_root_path)):
        raise ValueError("stress root inputs unbound")
    polynomials = shape_gate(original, modified)
    original_root_check = exact.verify(original, old_root, F(1, 10**80))
    new_root_check = exact.verify(modified, proposed, F(1, 10**85))
    old_z, old_box = interval_root(old_root, F(1, 10**80))
    new_z, new_box = interval_root(proposed, F(1, 10**85))
    if any(not old_box[i][0] < new_box[i][0] < new_box[i][1] < old_box[i][1] for i in range(26)):
        raise ValueError("modified root not strictly inside original uniqueness box")
    transport = transport_checks(original, proposed, polynomials)
    # The proved transport of the three omitted equations makes the new root
    # solve the original system in its uniqueness box; hence the roots agree.
    cover = geo.geometry_check(original, proposed)
    negatives = []

    def reject(label, fn):
        try:
            fn()
        except (ValueError, KeyError, TypeError):
            negatives.append(label)
        else:
            raise AssertionError("bad stress root accepted: " + label)

    bad = deepcopy(modified)
    bad["equations"][0] = deepcopy(original["equations"][0])
    reject("omitted-exact-zero-multiplier", lambda: shape_gate(original, bad))
    bad = deepcopy(original)
    bad["equations"][12] = [{"powers": [0] * 26, "coefficient": "1"}]
    reject("unproved-stationarity", lambda: shape_gate(bad, modified))
    bad = deepcopy(modified)
    bad["center_map"][1][0]["sign"] = -1
    reject("changed-candidate-chart", lambda: shape_gate(original, bad))
    bad = deepcopy(proposed)
    bad["xnum"][14 + 8] = str(-int(bad["xnum"][14 + 8]))
    reject("changed-pressure-sign", lambda: transport_checks(original, bad, polynomials))
    bad = deepcopy(proposed)
    bad["xnum"][0] = str(int(bad["xnum"][0]) + int(bad["Qx"]) // 1000)
    reject("shifted-root", lambda: exact.verify(modified, bad, F(1, 10**85)))
    args.output.mkdir(parents=True)
    proof = Path(__file__).with_name("n26-positive-stress-proof.md")
    files = [
        (modified_path, args.output / "SYSTEM.json"),
        (proposed_path, args.output / "ROOT-CERTIFICATE.json"),
        (original_path, args.output / "ORIGINAL-SYSTEM.json"),
        (old_root_path, args.output / "ORIGINAL-ROOT-CERTIFICATE.json"),
        (Path(__file__), args.output / "verify_positive_stress.py"),
        (Path(exact.__file__), args.output / "verify_contact_root.py"),
        (Path(geo.__file__), args.output / "verify_same_root_cover.py"),
        (proof if proof.exists() else Path(__file__).with_name("PROOF.md"), args.output / "PROOF.md")]
    for source, target in files:
        target.write_bytes(source.read_bytes())
    # Also provide the original input names in a subdirectory for standalone replay.
    original_folder = args.output / "original"
    original_folder.mkdir()
    (original_folder / "SYSTEM.json").write_bytes(original_path.read_bytes())
    (original_folder / "ROOT-CERTIFICATE.json").write_bytes(old_root_path.read_bytes())
    ledger_path = args.output / "STRESS-LEDGER.json"
    ledger_path.write_text(json.dumps(transport, indent=2) + "\n", encoding="utf-8")
    report = {
        "schema": "N26-same-root-unrestricted-nonnegative-stress-v1", "verified": True,
        "modified_and_original_roots_exactly_isolated": True,
        "same_root_equality_proved_by_contact_transport_and_uniqueness": True,
        "zero_orbit_multipliers_proved": list(WEAK),
        "full_center_coordinate_dimension": 52,
        "strictly_positive_contact_stresses": 36, "exactly_zero_contact_stresses": 10,
        "stress_sum_exactly_one_from_stationarity": True,
        "full_coordinate_equilibrium_proved": True,
        "no_D2_restriction_on_perturbation_domain": True,
        "r_strict_interval": new_root_check["r_strict_interval"],
        "original_root_check": original_root_check, "modified_root_check": new_root_check,
        "same_root_entire_disk_cover_rechecked": cover["same_root_entire_disk_cover_proved"],
        "proof_scope": "First-order equilibrium of the specified known covering candidate only",
        "local_optimality_proved": False, "global_optimality_proved": False,
        "negative_controls_rejected": negatives,
        "files": {str(target.relative_to(args.output)): exact.sha(target) for source, target in files},
        "additional_files": {str(p.relative_to(args.output)): exact.sha(p) for p in (
            ledger_path, original_folder / "SYSTEM.json", original_folder / "ROOT-CERTIFICATE.json")}}
    (args.output / "VERIFIED.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({key: report[key] for key in (
        "verified", "same_root_equality_proved_by_contact_transport_and_uniqueness",
        "strictly_positive_contact_stresses", "exactly_zero_contact_stresses",
        "full_coordinate_equilibrium_proved", "no_D2_restriction_on_perturbation_domain",
        "local_optimality_proved", "global_optimality_proved")}), flush=True)


if __name__ == "__main__":
    main()
