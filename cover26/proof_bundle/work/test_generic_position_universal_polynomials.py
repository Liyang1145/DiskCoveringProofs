"""Independent coordinate/determinant reconstruction and actual bad certificates."""

import argparse
from copy import deepcopy
import json
from pathlib import Path

import sympy as sp

import n26_generic_position_universal_polynomials as algebra
import verify_conditional_force_stage as binding


def independently_reconstruct(certificate):
    variables = sp.symbols(" ".join(algebra.VARIABLES), real=True)
    ax, ay, bx, by, cx, cy, dx, dy, px, py, ux, uy, eta, rho, r = variables
    a, b, c, d = [sp.Matrix(pair) for pair in
                   ((ax, ay), (bx, by), (cx, cy), (dx, dy))]
    p, movement = sp.Matrix([px, py]), sp.Matrix([ux, uy])
    v1, v2 = b-a, c-a
    rhs = sp.Matrix([b.dot(b)-a.dot(a), c.dot(c)-a.dot(a)])
    matrix = sp.Matrix([list(v1), list(v2)])
    det = matrix.det()
    numerators = matrix.adjugate()*rhs
    norm_polynomials = {
        "zero-centre": a.dot(a), "coincident-pair": v1.dot(v1),
        "collinear-triple": det,
        "cocircular-four": sp.Matrix([
            [centre[0], centre[1], centre.dot(centre), 1] for centre in (a, b, c, d)]).det(),
        "pair-bisector-tangent-to-unit-circle": rhs[0]**2-4*v1.dot(v1),
        "triple-bisector-intersection-on-unit-circle":
            numerators.dot(numerators)-4*det**2,
        "disk-footprint-tangent-to-unit-circle": (1+a.dot(a)-rho**2)**2-4*a.dot(a),
    }
    residuals = {
        "movement-squared-norm": (
            (a+movement).dot(a+movement)-a.dot(a)-2*a.dot(movement)-movement.dot(movement)),
        "cauchy-schwarz-square": (
            a.dot(a)*movement.dot(movement)-a.dot(movement)**2
            -sp.Matrix([list(a), list(movement)]).det()**2),
        "radial-shrink-norm": ((1-eta)*a).dot((1-eta)*a)-(1-eta)**2*a.dot(a),
        "radial-shrink-movement": (-eta*a).dot(-eta*a)-eta**2*a.dot(a),
        "half-slack-remains-strict": rho-r-(rho-r)/2-(rho-r)/2,
        "affine-pair-distance-difference": (
            (p-a).dot(p-a)-(p-b).dot(p-b)-(2*v1.dot(p)-rhs[0])),
        "first-cramer-bisector": (matrix*numerators-rhs*det)[0],
        "second-cramer-bisector": (matrix*numerators-rhs*det)[1],
        "cleared-unit-circle-criterion": (
            4*det**2*(p.dot(p)-1)-(numerators.dot(numerators)-4*det**2)
            -(2*det*p-numerators).dot(2*det*p+numerators)),
    }
    for field, expected in (("degeneracy_polynomials", norm_polynomials),
                            ("zero_polynomial_identities", residuals)):
        if set(certificate[field]) != set(expected):
            raise ValueError("independent generic-position check lost a geometric condition")
        for name, expression in expected.items():
            actual = algebra.sparse.decode(certificate[field][name], variables)
            if not sp.Poly(actual-expression, *variables, domain=sp.QQ).is_zero:
                raise ValueError("independent coordinate/determinant reconstruction failed: "+name)
    return len(norm_polynomials), len(residuals)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--certificate", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.certificate.exists() or args.report.exists():
        raise FileExistsError("generic-position certificate/control targets must be fresh")
    digests = {
        "executed_test_sha256": binding.sha(__file__),
        "tested_universal_algebra_sha256": binding.sha(algebra.__file__),
        "tested_sparse_polynomial_codec_sha256": binding.sha(algebra.sparse.__file__),
        "written_uniform_slack_density_and_irredundancy_proof_sha256": binding.sha(
            Path(__file__).with_name("n26-strict-slack-generic-position-proof.md")),
    }
    certificate = algebra.canonical()
    result = algebra.gate(certificate)
    conditions, identities = independently_reconstruct(certificate)
    rejected = []

    def reject(label, mutation):
        bad = deepcopy(certificate)
        mutation(bad)
        try:
            algebra.gate(bad)
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid generic-position certificate accepted: "+label)

    for label, mutation in (
        ("generic-position-strict-radius-slack-removed", lambda bad:
         bad["explicit_hypotheses"].__setitem__(0, "r<=rho")),
        ("generic-position-whole-disk-cover-replaced-by-samples", lambda bad:
         bad["explicit_hypotheses"].__setitem__(1, "finite-rational-points-covered")),
        ("generic-position-density-bridge-omitted", lambda bad:
         bad["explicit_scope_and_bridge"].pop(0)),
        ("generic-position-four-centre-degeneracy-omitted", lambda bad:
         bad["degeneracy_polynomials"].pop("cocircular-four")),
        ("generic-position-boundary-triple-condition-omitted", lambda bad:
         bad["degeneracy_polynomials"].pop("triple-bisector-intersection-on-unit-circle")),
        ("generic-position-pair-tangency-coefficient-corrupted", lambda bad:
         bad["degeneracy_polynomials"]["pair-bisector-tangent-to-unit-circle"][0].update(
             coefficient="17")),
        ("generic-position-nonzero-witness-zeroed", lambda bad:
         bad["nonzero_polynomial_witnesses"]["coincident-pair"].update(exact_evaluation=[])),
        ("generic-position-witness-substitution-forged", lambda bad:
         bad["nonzero_polynomial_witnesses"]["zero-centre"]["substitution"].update(ax="0")),
        ("generic-position-fixed-radius-reason-removed", lambda bad:
         bad["nonzero_polynomial_witnesses"]["disk-footprint-tangent-to-unit-circle"].update(
             nonzero_justification="positive-at-one-sampled-radius-only")),
        ("generic-position-universal-movement-identity-removed", lambda bad:
         bad["zero_polynomial_identities"].pop("movement-squared-norm")),
        ("generic-position-cramer-zero-residual-forged", lambda bad:
         bad["zero_polynomial_identities"].update(
             {"first-cramer-bisector": deepcopy(bad["degeneracy_polynomials"]["zero-centre"])})),
        ("generic-position-unknown-geometric-owner-added", lambda bad:
         bad["nonzero_polynomial_witnesses"]["zero-centre"].update(fake_root_owner=28)),
        ("generic-position-boolean-monomial-power", lambda bad:
         bad["degeneracy_polynomials"]["zero-centre"][0]["powers"].__setitem__(0, True)),
        ("generic-position-repeated-sparse-term", lambda bad:
         bad["degeneracy_polynomials"]["zero-centre"].append(deepcopy(
             bad["degeneracy_polynomials"]["zero-centre"][0]))),
        ("generic-position-promoted-to-global-proof", lambda bad:
         bad.update(global_optimality_proved=True)),
    ):
        reject(label, mutation)
    if (binding.sha(__file__) != digests["executed_test_sha256"]
            or binding.sha(algebra.__file__) != digests["tested_universal_algebra_sha256"]
            or binding.sha(algebra.sparse.__file__) != digests["tested_sparse_polynomial_codec_sha256"]
            or binding.sha(Path(__file__).with_name("n26-strict-slack-generic-position-proof.md"))
            != digests["written_uniform_slack_density_and_irredundancy_proof_sha256"]):
        raise ValueError("generic-position exact algebra or written bridge changed during controls")
    with args.certificate.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(certificate, indent=2)+"\n")
    report = {
        "schema": "N26-independent-universal-strict-slack-generic-position-controls-v1",
        "verified": False, "certificate_sha256": binding.sha(args.certificate),
        "actual_universal_symbolic_result": result,
        "independent_coordinate_norm_and_determinant_conditions_reconstructed": conditions,
        "independent_zero_polynomial_identities_reconstructed": identities,
        "actual_invalid_slack_density_condition_witness_coefficient_scope_controls_rejected": rejected,
        "finite_witnesses_prove_polynomial_nonzeroness_NOT_covering_by_samples": True,
        "not_a_proof_assistant_formalization_or_final_unrestricted_joint_acceptance": True,
        "frozen_native_geometry_flags_and_all_current_sources_UNMODIFIED": True,
        "formal_machine_geometry_proof": False, "new_geometric_payments": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "n27_started": False, **digests,
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "universal_strict_slack_generic_position_controls_completed": True,
        "symbolic_zero_identities": identities, "geometric_degeneracy_conditions": conditions,
        "actual_rejections": len(rejected), "formal_machine_geometry_proof": False,
        "global_optimality_proved": False,
    }), flush=True)


if __name__ == "__main__":
    main()
