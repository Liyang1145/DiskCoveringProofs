"""Independent scalar-coordinate universal bridge relations and bad-premise controls."""

import argparse
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path

import sympy as sp

import n26_embedded_dual_bridge_algebra as algebra
import verify_conditional_force_stage as binding


def independent_identities(certificate):
    variables = sp.symbols(" ".join(algebra.VARIABLES), real=True)
    ax, ay, bx, by, cx, cy, dx, dy, qx, qy, t, s, k, epsilon, u, v = variables
    a, b, c, d, q = (coords for coords in ((ax, ay), (bx, by), (cx, cy), (dx, dy), (qx, qy)))
    def squared(point):
        return sum(z*z for z in point)
    def difference(left, right):
        return tuple(x-y for x, y in zip(left, right))
    def circle(point):
        return squared(point)-2*sum(x*y for x, y in zip(q, point))+k
    def area(first, second, third):
        return ((second[0]-first[0])*(third[1]-first[1])
                -(third[0]-first[0])*(second[1]-first[1]))
    ab = tuple(x+t*(y-x) for x, y in zip(a, b))
    cd = tuple(x+s*(y-x) for x, y in zip(c, d))
    weight_ab = t*(1-t)*squared(difference(a, b))
    weight_cd = s*(1-s)*squared(difference(c, d))
    star = tuple(x+epsilon*(y+z-2*x) for x, y, z in zip(a, b, c))
    bary = tuple(x+u*(y-x)+v*(z-x) for x, y, z in zip(a, b, c))
    variance = ((1-u-v)*u*squared(difference(a, b))+(1-u-v)*v*squared(difference(a, c))
                +u*v*squared(difference(b, c)))
    identities = {
        "ab-weighted-squared-norm": ((1-t)*squared(a)+t*squared(b), squared(ab)+weight_ab),
        "cd-weighted-squared-norm": ((1-s)*squared(c)+s*squared(d), squared(cd)+weight_cd),
        "ab-weighted-circle": ((1-t)*circle(a)+t*circle(b), circle(ab)+weight_ab),
        "cd-weighted-circle": ((1-s)*circle(c)+s*circle(d), circle(cd)+weight_cd),
        "crossing-circle-gap": (
            (1-s)*circle(c)+s*circle(d)-(1-t)*circle(a)-t*circle(b)-weight_cd+weight_ab,
            sum((z-x)*(z+x-2*y) for z, x, y in zip(cd, ab, q))),
        "nearest-site-bisector-normal": (
            squared(difference(q, a))-squared(difference(q, b)),
            2*sum((y-x)*z for x, y, z in zip(a, b, q))+squared(a)-squared(b)),
        "stellar-child-ab": (area(a, b, star), epsilon*area(a, b, c)),
        "stellar-child-bc": (area(b, c, star), (1-2*epsilon)*area(a, b, c)),
        "stellar-child-ca": (area(c, a, star), epsilon*area(a, b, c)),
        "stellar-oriented-area-sum": (area(a, b, star)+area(b, c, star)+area(c, a, star), area(a, b, c)),
        "common-witness-convex-variance": (
            (1-u-v)*squared(difference(a, q))+u*squared(difference(b, q))+v*squared(difference(c, q)),
            squared(difference(bary, q))+variance),
        "stellar-limit-vanishing-displacement": (
            squared(difference(star, a)), epsilon**2*sum((y+z-2*x)**2 for x, y, z in zip(a, b, c))),
    }
    if set(identities) != set(certificate["identities"]):
        raise AssertionError("independent bridge identity set changed")
    for name, pair in identities.items():
        for side, expected in zip(("left", "right"), pair):
            actual = algebra.sparse.decode(certificate["identities"][name][side], variables)
            if not sp.Poly(sp.expand(actual-expected), *variables, domain=sp.QQ).is_zero:
                raise AssertionError("independent scalar-coordinate identity mismatch")
        if not sp.Poly(sp.expand(pair[0]-pair[1]), *variables, domain=sp.QQ).is_zero:
            raise AssertionError("independent universal polynomial is not an identity")
    return len(identities)


def finite_controls():
    # Finite controls are labeled DATA, not universal clipping/coverage proofs.
    a, b, c, witness = (F(0), F(0)), (F(1), F(0)), (F(0), F(1)), (F(1, 2), F(1, 2))
    radius_squared = F(1, 2)
    maximum_error = F(0)
    for epsilon in (F(1, 4), F(1, 10), F(1, 100), F(1, 10000)):
        point = tuple((1-2*epsilon)*x+epsilon*y+epsilon*z for x, y, z in zip(a, b, c))
        if min(point) <= 0 or sum(point) >= 1 or sum((x-y)**2 for x, y in zip(point, witness)) > radius_squared:
            raise AssertionError("exact proper-star/common-witness finite control failed")
        maximum_error = max(maximum_error, sum(x*x for x in point))
    return {"exact_proper_star_examples_checked_NOT_universal_theorem": 4,
            "old_corner_copy_reuses_common_witness": True,
            "limit_shadow_position_is_old_corner_not_a_new_original_cell": True}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--certificate", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    if args.certificate.exists() or args.report.exists():
        raise FileExistsError("preserve bridge certificates and failed controls")
    proof = Path("work/n26-embedded-dual-and-corner-starring-bridge-proof.md")
    paths = [proof, Path(__file__), Path(algebra.__file__), Path(algebra.sparse.__file__),
             Path("work/n26-strict-slack-generic-position-proof.md"),
             Path("work/n26-unit-cap-domination-and-no-return-proof.md"),
             Path("outputs/n26-universal-unit-cap-polynomial-independent-controls-v1.json"),
             Path("outputs/n26-universal-strict-slack-generic-position-independent-controls-v1.json"),
             Path("outputs/n26-actual-current28-closed-ear-core-capacity-mathematical-audit-v1.json")]
    digests = {str(path): binding.sha(path) for path in paths}
    certificate = algebra.canonical()
    result = algebra.gate(certificate)
    independent = independent_identities(certificate)
    examples = finite_controls()
    rejected = []
    def reject(name, mutation):
        changed = deepcopy(certificate)
        mutation(changed)
        try:
            algebra.gate(changed)
        except (ValueError, KeyError, TypeError, IndexError):
            rejected.append(name)
        else:
            raise AssertionError("bad bridge premise or polynomial accepted: "+name)
    for name, mutation in (
        ("strict-empty-circle-hypothesis-omitted", lambda c: c["explicit_ordered_real_hypotheses"].pop(4)),
        ("second-empty-circle-hypothesis-omitted", lambda c: c["explicit_ordered_real_hypotheses"].pop(5)),
        ("proper-star-range-weakened", lambda c: c["explicit_ordered_real_hypotheses"].__setitem__(6, "epsilon>=0")),
        ("original-owner-count-relabelled-as-26-owner-count", lambda c: c["explicit_ordered_real_hypotheses"].pop()),
        ("shadow-zero-cell-area-premise-omitted", lambda c: c["explicit_ordered_real_hypotheses"].pop(9)),
        ("limit-embedding-scope-omitted", lambda c: c["continuous_and_topological_scope"].pop(4)),
        ("capacity-budget-interface-omitted", lambda c: c["continuous_and_topological_scope"].pop(6)),
        ("crossing-identity-coefficient-corrupted", lambda c: c["identities"]["ab-weighted-circle"]["left"][0].update(coefficient="123")),
        ("stellar-orientation-identity-omitted", lambda c: c["identities"].pop("stellar-child-bc")),
        ("convex-common-witness-replaced-by-samples", lambda c: c["identities"].__setitem__("common-witness-convex-variance", {"samples": []})),
        ("polynomial-identity-promoted-to-global-joint-proof", lambda c: c.update(geometric_reduction_proved=True, global_optimality_proved=True)),
    ):
        reject(name, mutation)
    for text, digest in digests.items():
        if binding.sha(Path(text)) != digest:
            raise ValueError("bridge input/proof/module changed during independent controls")
    with args.certificate.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(certificate, indent=2)+"\n")
    report = {
        "schema": "N26-independent-empty-circle-corner-starring-bridge-algebra-controls-v1",
        "verified": False, "input_sha256": digests,
        "certificate_sha256": binding.sha(args.certificate),
        "actual_universal_symbolic_result": result,
        "independent_scalar_coordinate_universal_identities_checked": independent,
        **examples, "actual_bad_premise_polynomial_and_scope_controls_rejected": rejected,
        "written_cover_to_embedded_original_dual_and_corner_copy_limit_argument_bound": True,
        "written_bridge_is_NOT_inferred_from_polynomial_tests_or_finite_examples": True,
        "all_frozen_area_capacity_implementations_and_source_payments_NOT_reproved": True,
        "actual_new_full_source_geometry_current_final_admission_NOT_performed": True,
        "frozen_geometric_reduction_proved": False, "new_geometric_payments": 0,
        "candidate_whole_roots_removed": 0,
        "source_frozen_code_histories_paid_leaves_and_ledgers_UNMODIFIED": True,
        "global_lower_bound_proved": False, "global_optimality_proved": False, "n27_started": False,
    }
    with args.report.open("x", encoding="utf-8", newline="\n") as target:
        target.write(json.dumps(report, indent=2)+"\n")
    print(json.dumps({
        "universal_empty_circle_and_star_identities": independent,
        "negative_premise_scope_and_coefficient_controls": len(rejected),
        "actual_full_geometry_current_final_admission": False,
        "new_geometric_payments": 0}), flush=True)


if __name__ == "__main__":
    main()
