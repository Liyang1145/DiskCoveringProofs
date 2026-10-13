"""Exact arithmetic for a NEW global B17 necessary ownership-gap condition."""

from fractions import Fraction as F
import json
from pathlib import Path

import verify_conditional_force_stage as binding


def main():
    output = Path("outputs/n26-b17-nine-disk-core-short-gap-arithmetic-v1.json")
    if output.exists():
        raise FileExistsError(output)
    paper = Path(
        "C:/热爱单机但萌新/_incoming-local-math-20261004/recovered-20261004/workspace/"
        "research-2026/disk-cover-proof-library/papers/fejes-toth-2005-n8-n10.pdf")
    expected = "29ca1999cc706747658082c0e459da78fda62ec356d6277a4f16b4878bd16917"
    if binding.sha(paper) != expected:
        raise ValueError("primary publication bytes changed")
    resource = Path("outputs/n26-original-candidate-arithmetic-context-v1")
    accepted = binding.read(resource/"VERIFIED.json")
    for name, digest in accepted["files"].items():
        if binding.sha(resource/name) != digest:
            raise ValueError("fixed arithmetic/trigonometric DATA changed")
    arcs = binding.force.load_trig(resource)[0]
    u, lower9, alpha = F(234701, 1000000), F(207, 500), F(9, 200)
    # The primary radius theorem gives lambda9=sqrt(2)-1.
    sqrt_margin = 2-(1+lower9)**2
    if not 0 < u < F(1, 2) or sqrt_margin <= 0:
        raise AssertionError("nine-disk rational lower constant is not strictly weaker")
    kappa = u*(1+1/lower9)
    cosine_upper = F(arcs.sincos_turn(alpha/2)[0][1], arcs.SCALE)
    direct_margin = 1+kappa*kappa-2*kappa*cosine_upper-u*u
    # Independent elementary upper bound: pi>3.14159 and cos(x)<=1-x²/2+x⁴/24.
    pi_lower = F(314159, 100000)
    if not pi_lower < F(arcs.PI[0], arcs.SCALE):
        raise AssertionError("independent coarse pi lower bound not verified")
    x = pi_lower*alpha
    if not 0 < x < 1:
        raise AssertionError("elementary cosine Taylor range changed")
    cosine_taylor_upper = 1-x*x/2+x**4/24
    independent_margin = 1+kappa*kappa-2*kappa*cosine_taylor_upper-u*u
    if (not kappa < cosine_upper or not kappa < cosine_taylor_upper
            or direct_margin <= 0 or independent_margin <= 0):
        raise AssertionError("whole ownership-gap exclusion inequality is not strict")
    proof = Path(__file__).with_name("n26-b17-nine-disk-core-short-gap-proof.md")
    report = {
        "schema": "N26-B17-nine-disk-core-short-gap-exact-arithmetic-v1",
        "scope": "at-most-26-disks-rho-at-most-234701-over-1000000-B17-cyclic-owners",
        "external_radius_theorem_explicitly_imported_NOT_reproved": True,
        "external_theorem_primary_publication": (
            "Gabor Fejes Toth, MSRI Publications52 (2005),361-376; theorem p362,n=9"),
        "external_theorem_primary_pdf_sha256": expected,
        "external_theorem_only_radius_clause_used_NOT_center_coordinates_or_uniqueness": True,
        "nine_disk_unit_disk_radius_lower_exact_formula": "sqrt(2)-1",
        "strictly_weaker_rational_nine_disk_lower": str(lower9),
        "exact_sqrt_comparison_margin": str(sqrt_margin),
        "current_conservative_screen_radius": str(u),
        "necessary_deep_boundary_center_norm_upper": str(kappa),
        "necessary_at_least_one_cyclic_ownership_gap_STRICTLY_below_turns": str(alpha),
        "same_gap_degrees": str(360*alpha),
        "direct_outward_cosine_upper": str(cosine_upper),
        "direct_exact_squared_distance_margin_above_U_squared": str(direct_margin),
        "independent_verified_pi_lower": str(pi_lower),
        "independent_cosine_Taylor_upper": str(cosine_taylor_upper),
        "independent_exact_squared_distance_margin_above_U_squared": str(independent_margin),
        "both_exact_arithmetic_routes_strict": True,
        "entire_geometric_argument_in_separate_proof_NOT_a_sampling_claim": True,
        "proof_note_sha256": binding.sha(proof),
        "executed_arithmetic_checker_sha256": binding.sha(__file__),
        "trigonometric_DATA_acceptance_sha256": binding.sha(resource/"VERIFIED.json"),
        "original_frozen_source_executors_and_all_forests_UNMODIFIED": True,
        "new_source_frontier_nodes_removed": 0,
        "original_U_frontier_nodes_removed": 0,
        "new_geometric_payments": 0,
        "global_n26_lower_bound_proved": False,
        "global_n26_optimality_proved": False,
        "new_constraint_NOT_yet_admitted_into_current_enumeration": True,
        "n27_started": False,
    }
    with output.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    main()
