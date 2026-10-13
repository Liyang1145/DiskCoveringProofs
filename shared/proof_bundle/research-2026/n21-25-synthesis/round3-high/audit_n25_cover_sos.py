"""Check the exact n25 full-cover geometry in a compact quartic encoding."""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
import argparse
import json
import sys
import n25_anchor_isolation as field
import exact_graph as exact
import quadratic_cover_sos as P
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
Q = field.Q
assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def evaluate(poly, geometry, square_slacks=None, divide_slack=None):
    result = Q.Q2(0)
    for monomial, coefficient in poly.items():
        multiplicities = Counter(monomial)
        term = Q.Q2(coefficient)
        if divide_slack is not None:
            assert multiplicities[divide_slack] >= 1
            multiplicities[divide_slack] -= 1
        for index, power in multiplicities.items():
            if index < len(geometry):
                value = geometry[index]
                for _ in range(power):
                    term *= value
            else:
                assert square_slacks is not None and power % 2 == 0
                value = square_slacks[index]
                for _ in range(power//2):
                    term *= value
        result += term
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    geometrypath = ROOT / "evidence/n25-isolation-exact-resume1/rotated-geometry.json"
    constpath = ROOT.parent / "evidence/core-reduction/constants/n25.json"
    geometry, constants = read(geometrypath), read(constpath)
    B, N = 16, 25
    masks = sorted(sum(1 << v for v in face) for face in geometry["faces"])
    bymask = {sum(1 << v for v in face): i for i, face in enumerate(geometry["faces"])}
    points = geometry["points_Qsqrt2"][:41]+[
        geometry["points_Qsqrt2"][41+bymask[mask]] for mask in masks]
    points = [[Q.Q2(*coordinate) for coordinate in point] for point in points]
    assert points[0] == [Q.Q2(1), Q.Q2(0)]
    assert geometry["t_Qsqrt2"] == ["1", "-2/3"]
    upper = F(constants["radius_upper"])
    assert (Q.Q2(upper*upper)-Q.Q2(1, -F(2, 3))).sign() > 0
    D, A = constants["angle_scale"], constants["angle_caps"][0]
    assert 0 < B*A < 2*D
    sys.path.insert(0, str(exact.kernel.ARCS))
    import exact_arcs as arcs
    assert F(arcs.sincos_turn(F(A, 2*D))[1][0], arcs.SCALE) > upper
    model = P.build(N, B, masks, upper, 8)
    values = [coordinate for point in points[1:] for coordinate in point]+[Q.Q2(1, -F(2, 3))]
    assert len(values) == model["G"]+1 == 145
    assert all(evaluate(poly, values).sign() == 0 for _, poly in model["equalities"])
    slack_squares = {}
    for index, (name, poly) in zip(model["slack_indices"], model["inequalities"], strict=True):
        value = evaluate(poly, values)
        assert value.sign() >= 0, ("exact cover-model constraint failed", name, value.dump())
        slack_squares[index] = value
    assert P.gradient_identity(model)
    assert evaluate(model["F"], values, slack_squares).sign() == 0
    for index in range(model["total_variables"]):
        derivative = P.derivative(model["F"], index)
        # Slack derivatives are s_j times a polynomial in s_j^2.
        actual = evaluate(derivative, values, slack_squares,
                          divide_slack=index if index >= len(values) else None)
        assert actual.sign() == 0
    assert not any(name in sys.modules for name in ("numpy", "scipy", "clarabel", "mpmath"))
    result = {"verified": True, "N": N, "B": B,
              "model": "full disk triangulation rods + positively ordered unit anchors + opposite halfplane",
              "full_center_faces": len(masks), "auxiliary_nodes": model["V"],
              "geometric_variables_with_t": len(values), "quadratic_equality_count": len(model["equalities"]),
              "quadratic_inequalities": len(model["inequalities"]),
              "quartic_total_variables": model["total_variables"],
              "quartic_degree": max(map(len, model["F"])), "quartic_sparse_monomials": len(model["F"]),
              "opposite_anchor": 8, "boundary_capacity_total_less_than_two_turns": True,
              "every_exact_geometry_constraint_verified": True,
              "quartic_zero_verified_with_nonnegative_algebraic_square_slacks": True,
              "all_quartic_first_derivatives_vanish_at_the_witness": True,
              "all_polynomial_gradient_identities_formally_compared": True,
              "ordinary_nonsingular_Krawczyk_cannot_accept_this_quartic_zero": True,
              "quartic_polynomial": P.serialize(model["F"]),
              "quadratic_equalities": [{"name": name, "polynomial": P.serialize(poly)}
                                       for name, poly in model["equalities"]],
              "quadratic_inequality_polynomials": [{"name": name, "polynomial": P.serialize(poly)}
                                                  for name, poly in model["inequalities"]],
              "squared_slack_values_Qsqrt2": {str(index): value.dump() for index, value in slack_squares.items()},
              "geometry_sha256": sha(geometrypath), "constants_sha256": sha(constpath),
              "source_sha256": sha(Path(__file__)), "compiler_source_sha256": sha(ROOT / "quadratic_cover_sos.py"),
              "field_source_sha256": sha(ROOT.parent / "n25_algebraic_upper.py"),
              "topology_checker_sha256": sha(ROOT / "cross_order_strict_transfer.py"),
              "no_optimizer_imported": True,
              "quantifier_elimination_implemented": False,
              "lower_bound_or_global_optimality_proved": False,
              "scope": "exact full candidate feasibility and algebraic interface; not a completed solver"}
    args.output.write_text(json.dumps(result, indent=2), encoding="utf8")
    print("N25 full-cover quartic exact PASS:", model["total_variables"], "variables;",
          len(model["F"]), "monomials; F=0 and all derivatives=0;",
          "no QE or global lower-bound claim", flush=True)


if __name__ == "__main__":
    main()
