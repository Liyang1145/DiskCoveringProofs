#!/usr/bin/env python3
"""Inventory audit for the seven Lean metric-class obligations.

This checks source/evidence consistency only.  It does not prove any interval
kernel, does not construct a Lean certificate, and does not claim kernel
acceptance.  Run from the repository root.
"""

from __future__ import annotations

import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[4]
LEAD = ROOT / "cover11/proof_bundle/research-2026/team-current/lead"
LEAN = ROOT / "n11-work/lean/N11Formalization"
PI_LOWER = Fraction(314159, 100000)


class AuditError(RuntimeError):
    pass


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AuditError(message)


def load_json(name: str) -> dict:
    path = LEAD / name
    require(path.is_file(), f"missing {path}")
    return json.loads(path.read_text())


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def decimal_fraction(value: object) -> Fraction:
    require(isinstance(value, (str, int)), f"not a decimal/string: {value!r}")
    return Fraction(str(value))


def interval(value: object) -> list:
    """Accept both JSON arrays and the stringified arrays in older q0 files."""
    if isinstance(value, str):
        text = value.strip()
        require(text.startswith("[") and text.endswith("]"), f"bad interval: {value!r}")
        value = [part.strip() for part in text[1:-1].split(",")]
    require(isinstance(value, list) and len(value) == 2, f"bad interval: {value!r}")
    return value


def check_certificate(name: str, span: int, coefficients: int, factors: int | None) -> dict:
    data = load_json(name)
    require(data.get("span") == span, f"{name}: expected span {span}")
    require(data.get("strict") is True, f"{name}: strict flag is not true")
    require(len(data.get("coefficients", [])) == coefficients,
            f"{name}: expected {coefficients} coefficients")
    if factors is not None:
        require(len(data.get("factors", [])) == factors,
                f"{name}: expected {factors} factors")
    upper = interval(data.get("upper"))
    pi = interval(data.get("pi"))
    require(decimal_fraction(upper[1]) < decimal_fraction(pi[0]),
            f"{name}: upper endpoint is not below the recorded pi lower endpoint")
    require(decimal_fraction(upper[1]) < PI_LOWER,
            f"{name}: upper endpoint is not below 314159/100000")
    return data


def check_controls() -> tuple[int, int]:
    degree3 = load_json("degree3_fraction_control.json")
    rows3 = degree3.get("results", [])
    require(len(rows3) == 9, "degree3: expected nine graph cases")
    require(sum(row.get("q") == 0 for row in rows3) == 1,
            "degree3: expected one q0 case")
    require(sum(row.get("q") == 1 for row in rows3) == 8,
            "degree3: expected eight q1 cases")
    for row in rows3:
        require(row.get("passed") is True, f"degree3: failed row {row}")
        require(decimal_fraction(row["upper_rational"]) < PI_LOWER,
                f"degree3: rational upper not below pi bound: {row}")
        require(decimal_fraction(row["upper_exact"]) <
                decimal_fraction(row["below_pi_lower"]),
                f"degree3: exact upper ordering failed: {row}")

    degree4 = load_json("degree4_triple_fraction_control.json")
    rows4 = degree4.get("results", [])
    require(len(rows4) == 4, "degree4: expected four reflection representatives")
    require({row.get("start") for row in rows4} == {0, 1, 2, 3},
            "degree4: representative starts are not exactly 0..3")
    require(all(row.get("q") == 1 and row.get("span") == 2 for row in rows4),
            "degree4: rows are not q1 span-2 cases")
    for row in rows4:
        require(row.get("passed") is True, f"degree4: failed row {row}")
        require(decimal_fraction(row["upper_exact"]) <
                decimal_fraction(row["below_pi_lower"]),
                f"degree4: exact upper ordering failed: {row}")
    return len(rows3), len(rows4)


def check_lean_interfaces() -> None:
    reduction = (LEAN / "ActualMetricClassReduction.lean").read_text()
    fields = [
        "q0_degree3 : Q0RunExclusion 1",
        "q0_degree4 : Q0RunExclusion 2",
        "q0_degree5 : Q0RunExclusion 3",
        "q1_degree3 : Q1RunExclusion 1",
        "q1_degree4 : Q1RunExclusion 2",
        "q1_degree5 : Q1RunExclusion 3",
        "q1_balanced : Q1RunExclusion 4",
    ]
    for field in fields:
        require(field in reduction, f"missing Lean field: {field}")

    finite = (LEAN / "CanonicalSharedMomentFiniteCertificate.lean").read_text()
    for token in ("def Q0FiniteTable", "def Q1FiniteTables",
                  "theorem seven_class_exclusions_of_finite"):
        require(token in finite, f"missing finite-table interface: {token}")

    balanced = (LEAN / "CanonicalBalancedFiniteClassCertificate.lean").read_text()
    for token in ("structure BalancedTwoFiniteTables",
                  "theorem balanced_exclusion_of_two_finite",
                  "theorem seven_classes_of_six_and_two"):
        require(token in balanced, f"missing balanced interface: {token}")


def main() -> int:
    try:
        degree3_cases, degree4_cases = check_controls()
        q0d4 = check_certificate("q0_moment_dual_certificate_0_2.json", 2, 112, 29)
        q0d5 = check_certificate("q0_closure_dual_certificate_0_3.json", 3, 121, 29)

        shared_names = [f"shared_factor_certificate_{k}_3.json" for k in range(4)]
        shared = [check_certificate(name, 3, 73, 29) for name in shared_names]
        compatible = check_certificate("compatible_position_certificate.json", 3, 24, None)
        balanced_names = [f"shared_moment_dense_certificate_{k}_4.json" for k in (0, 2)]
        balanced = [check_certificate(name, 4, 112, 29) for name in balanced_names]

        check_lean_interfaces()
    except (AuditError, KeyError, ValueError, TypeError) as error:
        print(f"SEVEN-CLASS INVENTORY AUDIT FAILED: {error}", file=sys.stderr)
        return 1

    print("SEVEN-CLASS INVENTORY AUDIT PASSED (source inventory only; no Lean proof claim)")
    print(f"degree-3 evidence: {degree3_cases} cases = 1 q0 + 8 q1")
    print(f"degree-4 q1 evidence: {degree4_cases} reflection representatives")
    print(f"q0(4,9): 112 coefficients, 29 factor records; upper={interval(q0d4['upper'])[1]}")
    print(f"q0(5,8): 121 coefficients, 29 factor records; upper={interval(q0d5['upper'])[1]}")
    print("q1(5,7): 4 shared-factor certificates + 1 compatible-position certificate")
    print(f"  shared uppers={[interval(row['upper'])[1] for row in shared]}")
    print(f"  start7 upper={interval(compatible['upper'])[1]}, N={compatible.get('N')}")
    print("q1(6,6): 2 dense moment certificates for representatives 0 and 2")
    print(f"  uppers={[interval(row['upper'])[1] for row in balanced]}")
    print("Lean interface audit: seven fields and finite-table consumers present")
    print("unpaid: source-to-Lean certificate construction and kernel check")
    for name in ("ActualMetricClassReduction.lean",
                 "CanonicalSharedMomentFiniteCertificate.lean",
                 "CanonicalBalancedFiniteClassCertificate.lean"):
        print(f"sha256 {sha256(LEAN / name)}  {name}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
