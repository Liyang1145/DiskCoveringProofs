#!/usr/bin/env python3
"""Audit the exact q0(5,8) closure vector and its Lean additive terms."""
from __future__ import annotations

import hashlib
import json
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = HERE / "q0-degree5-exact-source.json"
LEAN = ROOT / "n11-work/lean/N11Formalization/Q0Degree5ClosureExtension.lean"
OUT = HERE / "q0-degree5-closure-extension-audit.json"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def frac(pair: list[int]) -> Fraction:
    return Fraction(pair[0], pair[1])


def pair(value: Fraction) -> list[int]:
    return [value.numerator, value.denominator]


def main() -> None:
    source = json.loads(SOURCE.read_text())
    closure = [frac(p) for p in source["coefficients"][112:121]]
    text = LEAN.read_text()
    required = [
        "def closure : ClosureVector := Q0Degree5SourceData.closure",
        "theorem closure_nonnegative : ∀ i : Fin 9, 0 ≤ closure i",
        "theorem closure_sum_pos : 0 < ∑ i : Fin 9, closure i",
        "2*t*(w i : ℝ)",
        "(w (i-1) : ℝ)*(left+width/2)+(w i : ℝ)*(right+width/2)",
        "-(Real.pi*(∑ i : Fin 9, (w i : ℝ)))",
        "def leftBaseAngle {c : Fin 11 → Point} {r : ℝ} (v : NineTies c r) (i : Fin 9) : ℝ",
        "def rightBaseAngle {c : Fin 11 → Point} {r : ℝ} (v : NineTies c r) (i : Fin 9) : ℝ",
        "theorem leftBaseAngle_nonnegative {c : Fin 11 → Point} {r : ℝ}",
        "theorem rightBaseAngle_nonnegative {c : Fin 11 → Point} {r : ℝ}",
        "theorem sectorTerm_nonnegative (i : Fin 9)",
        "theorem switchObjective_le_of_augmented {objective bound : ℝ}",
        "theorem sectorObjective_le_of_augmented {objective bound : ℝ}",
        "structure ClosureFactorBounds",
        "structure ClosureSectorCoordinates",
        "def ClosureFactorBounds.toCanonical",
        "structure ClosureCertificate",
        "def ClosureCertificate.toCanonical",
        "theorem ClosureCertificate.total_lt_pi",
        "theorem constantTerm_nonpositive",
        "theorem closureTotalUpper_lt_pi",
        "decide +kernel",
    ]
    forbidden = ["sorry", "admit", "axiom ", "native_decide", "ofReduceBool",
                 "implemented_by", "maxHeartbeats 0"]
    source_coordinate_required = {
        "source_sector_chord_length":
            "Real.sqrt (u^2+v^2-2*u*v*Real.cos a)",
        "source_sector_width":
            "2*Real.arcsin ((19/50 : ℝ)*sourceSectorChordLength a u v/2)",
        "source_left_atan2":
            "Complex.arg ⟨u-v*Real.cos a, v*Real.sin a⟩",
        "source_right_atan2":
            "Complex.arg ⟨v-u*Real.cos a, u*Real.sin a⟩",
        "source_coordinate_instance": "def sourceSectorCoordinates : ClosureSectorCoordinates",
        "source_left_nonnegative": "theorem sourceLeftBaseAngle_nonnegative",
        "source_right_nonnegative": "theorem sourceRightBaseAngle_nonnegative",
        "source_width_nonnegative": "theorem sourceSectorWidth_nonnegative",
    }
    checks = {
        "source_121_slots": source["coefficient_count"] == 121,
        "closure_count_9": len(closure) == 9,
        "closure_strictly_positive": all(x > 0 for x in closure),
        "lean_uses_hash_bound_source_vector": required[0] in text,
        "lean_has_nonnegativity": required[1] in text,
        "lean_has_positive_sum": required[2] in text,
        "lean_has_switch_term": required[3] in text,
        "lean_has_sector_term": required[4] in text,
        "lean_has_constant_term": required[5] in text,
        "lean_has_actual_left_base_angle": required[6] in text,
        "lean_has_actual_right_base_angle": required[7] in text,
        "lean_has_left_base_nonnegative": required[8] in text,
        "lean_has_right_base_nonnegative": required[9] in text,
        "lean_has_sector_term_nonnegative": required[10] in text,
        "lean_has_switch_bound_lifting": required[11] in text,
        "lean_has_sector_bound_lifting": required[12] in text,
        "lean_has_closure_sector_coordinates": required[13] in text,
        "lean_has_closure_factor_bounds": required[14] in text,
        "lean_has_base_interface_lifting": required[15] in text,
        "lean_has_closure_certificate": required[16] in text,
        "lean_has_canonical_certificate_conversion": required[17] in text,
        "lean_has_certificate_total_bound": required[18] in text,
        "lean_has_negative_constant_bound": required[19] in text,
        "lean_has_strict_total_lifting": required[20] in text,
        "lean_has_kernel_terminals": text.count(required[21]) == 2,
        "no_forbidden_tokens": not any(token in text for token in forbidden),
    }
    checks.update({name: needle in text
                   for name, needle in source_coordinate_required.items()})
    assert all(checks.values()), checks
    total = sum(closure)
    report = {
        "status": "PASS_SOURCE_AND_INTERFACE_EXTENSION_ONLY",
        "claim_boundary": (
            "Exact closure data and formula transcription only; no factor bound, "
            "strict total, exclusion, or Lean kernel verdict."
        ),
        "source": SOURCE.relative_to(ROOT).as_posix(),
        "source_sha256": sha256(SOURCE),
        "lean": LEAN.relative_to(ROOT).as_posix(),
        "lean_sha256": sha256(LEAN),
        "checks": checks,
        "closure_sum": pair(total),
        "constant_term_as_real": f"-pi*({pair(total)[0]}/{pair(total)[1]})",
        "unproved": [
            "sector factor bounds with the closure multipliers for 9 sectors",
            "face and switch factor bounds for 11 faces and 9 switches",
            "closure-aware strict rational total below piLo at the concrete source data",
            "q0_degree5 exclusion and remaining six classes",
        ],
    }
    OUT.write_text(json.dumps(report, indent=2) + "\n")
    print("PASS exact closure vector plus additive source-term interface")
    print(f"closure_sum={total}")
    print(f"wrote {OUT.relative_to(ROOT)} sha256={sha256(OUT)}")


if __name__ == "__main__":
    main()
