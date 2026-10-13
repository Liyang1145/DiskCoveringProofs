"""Pure rational contraction certificate for a polynomial system.

Accepts neither floating residuals nor a numerical inverse. The proposed
preconditioner is rational and its inclusion/contraction bounds are rechecked.
"""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import hashlib
import json
from math import isqrt
from pathlib import Path


ZERO = (F(0), F(0))


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def point(value):
    value = F(value)
    return value, value


def add(a, b):
    return a[0] + b[0], a[1] + b[1]


def sub(a, b):
    return a[0] - b[1], a[1] - b[0]


def mul(a, b):
    values = [x * y for x in a for y in b]
    return min(values), max(values)


def scale(value, a):
    if value >= 0:
        return value * a[0], value * a[1]
    return value * a[1], value * a[0]


def absolute(a):
    return max(abs(a[0]), abs(a[1]))


def decode(polynomial, dimension):
    result = []
    seen = set()
    for term in polynomial:
        powers = tuple(term["powers"])
        coefficient = F(term["coefficient"])
        if (len(powers) != dimension or any(type(k) is not int or not 0 <= k <= 20 for k in powers)
                or powers in seen or coefficient.denominator != 1):
            raise ValueError("invalid sparse integer polynomial")
        seen.add(powers)
        result.append((coefficient, powers))
    return result


def derivative(polynomial, column):
    result = []
    for coefficient, powers in polynomial:
        if powers[column]:
            new = list(powers)
            new[column] -= 1
            result.append((coefficient * powers[column], tuple(new)))
    return result


def prepare(system):
    d = system["dimension"]
    if type(d) is not int or not 1 <= d <= 100 or len(system["equations"]) != d:
        raise ValueError("not a square polynomial system")
    polynomials = [decode(poly, d) for poly in system["equations"]]
    jacobian = [[derivative(poly, j) for j in range(d)] for poly in polynomials]
    maxima = [max((powers[j] for poly in polynomials for _, powers in poly), default=0)
              for j in range(d)]
    return d, polynomials, jacobian, maxima


def powers_for(box, maxima):
    values = []
    for interval, maximum in zip(box, maxima):
        row = [point(1)]
        for _ in range(maximum):
            row.append(mul(row[-1], interval))
        values.append(row)
    return values


def evaluate(polynomial, powers):
    result = ZERO
    for coefficient, exponents in polynomial:
        value = point(coefficient)
        for j, exponent in enumerate(exponents):
            if exponent:
                value = mul(value, powers[j][exponent])
        result = add(result, value)
    return result


def rational_ceiling(value, digits=30):
    scale_ = 10**digits
    k = value.numerator * scale_ // value.denominator + 1
    return str(F(k, scale_))


def verify(system, certificate, rho):
    d, polynomials, jacobian, maxima = prepare(system)
    if (len(certificate["xnum"]) != d or len(certificate["Ynum"]) != d
            or any(len(row) != d for row in certificate["Ynum"])):
        raise ValueError("root/inverse dimensions disagree")
    Qx, Qy = int(certificate["Qx"]), int(certificate["Qy"])
    if Qx <= 0 or Qy <= 0 or not 0 < rho <= 1:
        raise ValueError("invalid scale or box")
    z = [F(int(value), Qx) for value in certificate["xnum"]]
    Y = [[F(int(value), Qy) for value in row] for row in certificate["Ynum"]]
    if any(not any(row) for row in Y):
        raise ValueError("zero preconditioner row")
    ti = system["radius_squared_index"]
    if not (type(ti) is int and 0 <= ti < d and z[ti] - rho > 0):
        raise ValueError("radius squared not strictly positive")
    point_powers = powers_for(list(map(point, z)), maxima)
    residual = [evaluate(poly, point_powers)[0] for poly in polynomials]
    eta = [sum((value * residual[k] for k, value in enumerate(row)), F(0)) for row in Y]
    if max(map(abs, eta)) >= rho:
        raise ValueError("center correction already outside the box")
    box = [(value - rho, value + rho) for value in z]
    box_powers = powers_for(box, maxima)
    J = [[evaluate(poly, box_powers) for poly in row] for row in jacobian]
    columns = [[(k, J[k][j]) for k in range(d) if J[k][j] != ZERO] for j in range(d)]
    row_bounds = []
    for i in range(d):
        norm = F(0)
        for j in range(d):
            product = ZERO
            for k, interval in columns[j]:
                product = add(product, scale(Y[i][k], interval))
            norm += absolute(sub(point(int(i == j)), product))
        row_bounds.append(norm)
    contraction = max(row_bounds)
    inclusion = max(abs(value) / rho + bound for value, bound in zip(eta, row_bounds))
    if not contraction < 1 or not inclusion < 1:
        raise ValueError("strict inclusion or contraction failed")
    scale_ = 10**60
    lower_t, upper_t = box[ti]
    lower = isqrt(lower_t.numerator * scale_**2 // lower_t.denominator)
    upper = isqrt(upper_t.numerator * scale_**2 // upper_t.denominator) + 1
    if F(lower, scale_) ** 2 == lower_t:
        lower -= 1
    if not (F(lower, scale_) ** 2 < lower_t <= upper_t < F(upper, scale_) ** 2):
        raise ValueError("sqrt interval failed")

    def decimal(number):
        return str(number // scale_) + "." + str(number % scale_).zfill(60)

    return {
        "dimension": d, "box_half_width": str(rho),
        "inclusion_ratio_strict_upper": rational_ceiling(inclusion),
        "contraction_ratio_strict_upper": rational_ceiling(contraction),
        "r_strict_interval": [decimal(lower), decimal(upper)],
        "radius_squared_interval": list(map(str, box[ti])),
        "square_root_interval_checked_by_integer_squares": True,
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise FileExistsError(args.output)
    system_path = args.input / "SYSTEM.json"
    root_path = args.input / "ROOT-PROPOSAL.json"
    system = json.loads(system_path.read_text(encoding="utf-8"))
    certificate = json.loads(root_path.read_text(encoding="utf-8"))
    if system.get("N") != 26 or system.get("B") != 16:
        raise ValueError("wrong candidate order or boundary count")
    if certificate["system_sha256"] != sha(system_path):
        raise ValueError("unbound root system")
    checks = []
    for exponent in (50, 80):
        result = verify(system, certificate, F(1, 10**exponent))
        checks.append(result)
        print(json.dumps(result), flush=True)
    negatives = []

    def reject(label, s, c, rho=F(1, 10**80)):
        try:
            verify(s, c, rho)
        except (ValueError, KeyError, TypeError):
            negatives.append(label)
        else:
            raise AssertionError("bad root certificate accepted: " + label)

    wrong = deepcopy(certificate)
    wrong["xnum"].pop()
    reject("missing-root-coordinate", system, wrong)
    wrong = deepcopy(certificate)
    wrong["Ynum"] = [["0"] * system["dimension"] for _ in range(system["dimension"])]
    reject("zero-inverse", system, wrong)
    wrong = deepcopy(certificate)
    wrong["xnum"][0] = str(int(wrong["xnum"][0]) + int(wrong["Qx"]) // 100)
    reject("shifted-root", system, wrong)
    reject("box-crosses-nonpositive-radius", system, certificate, F(1))
    wrong_system = deepcopy(system)
    wrong_system["equations"].pop()
    reject("omitted-equation", wrong_system, certificate)
    wrong_system = deepcopy(system)
    wrong_system["equations"][0] = [{"coefficient": "1", "powers": [0] * system["dimension"]}]
    reject("changed-equation", wrong_system, certificate)
    args.output.mkdir(parents=True)
    copied_system = args.output / "SYSTEM.json"
    copied_root = args.output / "ROOT-CERTIFICATE.json"
    # Publish the very bytes whose hashes were bound above. Re-encoding JSON
    # across Windows/Linux can change newline bytes without changing content.
    copied_system.write_bytes(system_path.read_bytes())
    copied_root.write_bytes(root_path.read_bytes())
    if sha(copied_system) != certificate["system_sha256"]:
        raise ValueError("published system encoding changed")
    if sha(copied_root) != sha(root_path):
        raise ValueError("published root certificate encoding changed")
    report = {
        "schema": "N26-D2-polynomial-root-exact-contraction-v1",
        "verified": True, "isolated_polynomial_root_proved": True,
        "root_scope": "Specified D2 contact/stationarity system and rational box only",
        "r_strict_interval": checks[-1]["r_strict_interval"],
        "checks": checks, "negative_controls_rejected": negatives,
        "same_root_entire_disk_cover_proved": False,
        "local_optimality_proved": False, "global_optimality_proved": False,
        "files": {str(path): sha(path) for path in (
            Path(__file__), system_path, root_path, copied_system, copied_root)},
    }
    (args.output / "VERIFIED.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"isolated_polynomial_root_proved": True,
                      "r_strict_interval": report["r_strict_interval"],
                      "negative_controls": len(negatives),
                      "global_optimality_proved": False}), flush=True)


if __name__ == "__main__":
    main()
