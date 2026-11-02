#!/usr/bin/env python3
"""Audit whether q0(5,8) closure multipliers fit CanonicalCoeffQ.

This is an interface/arithmetic check, not a Lean proof.  It uses the exact
decimal-rational reconstruction and the existing canonical field map.
"""
from __future__ import annotations

import hashlib
import json
from fractions import Fraction
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = HERE / "q0-degree5-exact-source.json"
MAPPING = HERE / "q0-degree5-canonical-map.json"
LEAN = ROOT / "n11-work/lean/N11Formalization/ActualCanonicalMomentTransport.lean"
EMITTER = ROOT / "cover11/proof_bundle/research-2026/team-current/lead/q0_closure_dual.py"
OUT = HERE / "q0-degree5-closure-interface-audit.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def frac(pair: list[int]) -> Fraction:
    return Fraction(pair[0], pair[1])


def pair(value: Fraction) -> list[int]:
    return [value.numerator, value.denominator]


def main() -> None:
    source = json.loads(SOURCE.read_text())
    mapping = json.loads(MAPPING.read_text())
    assert source["coefficient_count"] == 121
    assert mapping["source_sha256"] == sha256(SOURCE)
    z = [frac(value) for value in source["coefficients"]]
    emitter_text = EMITTER.read_text()

    mu = z[:11]
    side = z[11:32]
    radius = z[32:50]
    kap = z[50:71]
    width = z[71]
    eta = z[72]
    linear = z[73:112]
    closure = z[112:121]

    checks = {
        "group_count_121": len(mu) + len(side) + len(radius) + len(kap) + 2
        + len(linear) + len(closure) == 121,
        "closure_count_9": len(closure) == 9,
        "closure_strictly_positive": all(value > 0 for value in closure),
        "eta_zero": eta == 0,
        "width_zero": width == 0,
        "emitter_sha_matches_source_record": sha256(EMITTER) == source["source_emitter_sha256"],
        "emitter_has_switch_closure_term": "M[:,cl+bi]+=2*b" in emitter_text,
        "emitter_has_sector_closure_terms":
            "M[:,cl+(i-1)%9]=left+w/2;M[:,cl+i]=right+w/2" in emitter_text,
        "emitter_has_negative_pi_closure_constant": "const[cl:]=-pi" in emitter_text,
    }
    assert all(checks.values())

    station = sum(mu[:9]) + 2 * sum(mu[9:])
    kap_sum = sum(kap)
    closure_sum = sum(closure)
    source_pi_coeff = station + kap_sum - 2 * width - closure_sum
    canonical_pi_coeff = station + kap_sum - 2 * width - 2 * eta
    unscaled_difference = canonical_pi_coeff - source_pi_coeff
    assert unscaled_difference == closure_sum - 2 * eta

    report = {
        "status": "BLOCKED_CANONICAL_INTERFACE_MISSING_CLOSURE_FIELD",
        "claim_boundary": (
            "Exact source/interface arithmetic only; no factor bound, strict total, "
            "exclusion, or Lean kernel claim."
        ),
        "source": SOURCE.relative_to(ROOT).as_posix(),
        "source_sha256": sha256(SOURCE),
        "canonical_map": MAPPING.relative_to(ROOT).as_posix(),
        "canonical_map_sha256": sha256(MAPPING),
        "canonical_lean": LEAN.relative_to(ROOT).as_posix(),
        "canonical_lean_sha256": sha256(LEAN),
        "source_emitter": EMITTER.relative_to(ROOT).as_posix(),
        "source_emitter_sha256": sha256(EMITTER),
        "checks": checks,
        "mapped_values": {
            "station_coefficient": pair(station),
            "kap_sum": pair(kap_sum),
            "width": pair(width),
            "eta": pair(eta),
            "closure_sum": pair(closure_sum),
        },
        "constants": {
            "source_pi_coefficient": pair(source_pi_coeff),
            "canonical_from_existing_map_pi_coefficient": pair(canonical_pi_coeff),
            "canonical_minus_source": pair(unscaled_difference),
            "identity": "canonical_minus_source = closure_sum - 2*eta",
        },
        "obstruction": {
            "field_count": "closure has 9 entries; CanonicalCoeffQ has no closure field",
            "term_shape": (
                "the source adds closure[i-1]*(left+w/2)+closure[i]*(right+w/2) "
                "to sector i and closure[j]*2*b to switch j"
            ),
            "consequence": (
                "the scalar eta can at best repair the pi-constant, not the nine "
                "sector- and switch-dependent factor terms; do not emit Q0FiniteTable 3 "
                "from the current mapping"
            ),
        },
        "next_required_interface": (
            "Define and prove a closure-extended canonical certificate carrying a "
            "Fin 9 closure vector, nonnegativity, the -pi*sum closure constant, and "
            "closure-augmented sector/switch objectives."
        ),
    }
    OUT.write_text(json.dumps(report, indent=2) + "\n")
    print("BLOCKED: exact q0(5,8) closure group is not representable by CanonicalCoeffQ")
    print(f"closure_sum={closure_sum}")
    print(f"canonical_minus_source={unscaled_difference}")
    print(f"wrote {OUT.relative_to(ROOT)} sha256={sha256(OUT)}")


if __name__ == "__main__":
    main()
