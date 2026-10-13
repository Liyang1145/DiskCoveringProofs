"""Independent symbolic relations plus labelled finite regression controls."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import sympy as sp

import n26_unit_cap_universal_identities as algebra
import verify_conditional_force_stage as binding


def independent_symbolic_check(certificate):
    variables = sp.symbols(" ".join(algebra.VARIABLES), real=True)
    a, b, t, s, x, y, r2, d, u, z, v, h = variables
    centre, point = sp.Matrix([a, b]), sp.Matrix([x, y])
    plus, minus = sp.Matrix([t, s]), sp.Matrix([t, -s])
    dp = r2-(plus-centre).dot(plus-centre)
    dm = r2-(minus-centre).dot(minus-centre)
    dd = 1-point.dot(point)
    gap = r2-(point-centre).dot(point-centre)
    residuals = {
        "positive-a": 2*t*a-(1-r2+centre.dot(centre)+(dp+dm)/2),
        "closed-cap-y-bound": (s*s-y*y)-(dd+(x-t)*(x+t)),
        "cap-gap-b-nonnegative": gap-(dm+dd+2*a*(x-t)+2*b*(s+y)),
        "cap-gap-b-nonpositive": gap-(dp+dd+2*a*(x-t)-2*b*(s-y)),
        "squared-distance-bisector": (
            (point-centre).dot(point-centre)
            -(point-sp.Matrix([a+d, b])).dot(point-sp.Matrix([a+d, b]))
            -2*d*(x-t)),
        "projection-norm-gap": (u*u-1-2*(u-1)*z)-(u-1)*(u+1-2*z),
        "projection-nonnegative-decomposition": (
            (u-1)*(u+1-2*z)-(u-1)**2-2*(u-1)*(1-z)),
        "circle-footprint-half-angle-bound": 4*v*v*(h*h-1+r2)-(v*v-1+r2)**2,
    }
    for name, expected in residuals.items():
        actual = algebra.decode(certificate["identities"][name]["residual"], variables)
        if not sp.Poly(sp.expand(actual-expected), *variables, domain=sp.QQ).is_zero:
            raise ValueError("independent coordinate norm/geometry identity changed: "+name)
    return len(residuals)


def rational_regressions():
    t, s, a, r2 = F(399, 401), F(40, 401), F(49, 50), F(1, 20)
    count = 0
    assert t*t+s*s == 1 and t > 0 and s >= 0
    for b in (F(1, 100), F(-1, 100)):
        dp, dm = r2-(t-a)**2-(s-b)**2, r2-(t-a)**2-(-s-b)**2
        assert dp >= 0 and dm >= 0
        for x, y in ((t, s), (t, -s), (F(1), F(0)),
                     ((1+t)/2, F(0)), (t, F(0))):
            disk = 1-x*x-y*y
            assert disk >= 0 and x >= t
            expected = r2-(x-a)**2-(y-b)**2
            summands = (
                (dm, disk, 2*a*(x-t), 2*b*(s+y)) if b >= 0
                else (dp, disk, 2*a*(x-t), -2*b*(s-y))
            )
            assert all(value >= 0 for value in summands)
            assert expected == sum(summands) >= 0
            count += 1
    u = F(3, 2)
    for z in (F(-1), F(0), F(1)):
        assert (u*u-1)-2*(u-1)*z == (u-1)**2+2*(u-1)*(1-z) >= 0
        count += 1
    v = F(9, 10)
    h = (1+v*v-r2)/(2*v)
    assert 4*v*v*(h*h-(1-r2)) == (v*v-(1-r2))**2 >= 0 and h > 0
    return count+1


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--certificate", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.certificate.exists() or args.report.exists():
        raise FileExistsError("preserve the prior algebraic certificate/control report")
    executed_digest, module_digest = binding.sha(__file__), binding.sha(algebra.__file__)
    certificate = algebra.canonical()
    result = algebra.gate(certificate)
    independent = independent_symbolic_check(certificate)
    examples = rational_regressions()
    rejected = []

    def reject(label, mutation):
        bad = deepcopy(certificate)
        mutation(bad)
        try:
            algebra.gate(bad)
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(label)
        else:
            raise AssertionError("invalid universal algebraic witness accepted: "+label)

    for label, mutation in (
        ("cap-radius-strict-hypothesis-omitted", lambda bad: bad[
            "explicit_ordered_real_hypotheses"].remove("0<=r2<1")),
        ("cap-positive-threshold-weakened", lambda bad: bad[
            "explicit_ordered_real_hypotheses"].__setitem__(1, "t>=0")),
        ("cap-unit-disk-hypothesis-omitted", lambda bad: bad[
            "explicit_ordered_real_hypotheses"].remove("1-x^2-y^2>=0")),
        ("cap-one-sign-case-omitted", lambda bad: bad[
            "explicit_sign_derivations_and_exhaustive_cases"].pop(4)),
        ("cap-whole-polynomial-identity-omitted", lambda bad: bad[
            "identities"].pop("cap-gap-b-nonnegative")),
        ("cap-exact-identity-coefficient-corrupted", lambda bad: bad[
            "identities"]["cap-gap-b-nonnegative"]["residual"][0].update(coefficient="2")),
        ("cap-zero-circle-relation-corrupted", lambda bad: bad[
            "zero_constraints"]["circle"][-1].update(coefficient="-2")),
        ("cap-bisector-equality-owner-substituted", lambda bad: bad[
            "identities"]["squared-distance-bisector"].update(zero_constraint="circle")),
        ("cap-unknown-proof-field-added", lambda bad: bad[
            "identities"]["positive-a"].update(fake_source_owner=28)),
        ("cap-boolean-monomial-exponent", lambda bad: bad[
            "identities"]["positive-a"]["residual"][0]["powers"].__setitem__(0, True)),
        ("cap-duplicate-sparse-proof-term", lambda bad: bad[
            "zero_constraints"]["circle"].append(deepcopy(bad["zero_constraints"]["circle"][0]))),
        ("cap-symbolic-certificate-replaced-by-samples", lambda bad: bad.update(identities={"samples": []})),
        ("cap-algebra-promoted-to-global-geometry-proof", lambda bad: bad.update(
            formal_machine_geometry_proof=True, global_optimality_proved=True)),
    ):
        reject(label, mutation)
    if binding.sha(__file__) != executed_digest or binding.sha(algebra.__file__) != module_digest:
        raise ValueError("universal algebra checker changed during its actual controls")
    with args.certificate.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(certificate, indent=2)+"\n")
    report = {
        "schema": "N26-independent-universal-unit-cap-polynomial-controls-v1",
        "verified": False, "certificate_sha256": binding.sha(args.certificate),
        "actual_universal_symbolic_result": result,
        "independent_geometry_coordinate_polynomial_identities_checked": independent,
        "finite_exact_rational_regression_examples_only": examples,
        "finite_examples_are_NOT_the_universal_identity_or_continuous_geometry_proof": True,
        "actual_invalid_hypothesis_sign_case_coefficient_relation_scope_controls_rejected": rejected,
        "written_ordered_real_and_Voronoi_bridge_proof_sha256": binding.sha(
            Path(__file__).with_name("n26-unit-cap-domination-and-no-return-proof.md")),
        "not_a_proof_assistant_formalization_or_final_unrestricted_joint_acceptance": True,
        "frozen_native_geometry_flags_and_all_current_sources_UNMODIFIED": True,
        "formal_machine_geometry_proof": False, "new_geometric_payments": 0,
        "global_lower_bound_proved": False, "global_optimality_proved": False,
        "n27_started": False, "executed_test_sha256": executed_digest,
        "tested_universal_algebra_module_sha256": module_digest,
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as output:
        output.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "universal_unit_cap_polynomial_controls_completed": True,
        "symbolic_identities": independent, "finite_regression_examples_only": examples,
        "actual_rejections": len(rejected), "formal_machine_geometry_proof": False,
        "global_optimality_proved": False,
    }), flush=True)


if __name__ == "__main__":
    main()
