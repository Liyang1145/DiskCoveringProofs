"""Exact D8 action on the one-dimensional stationary stress fibre.

Uses only Q(sqrt2) arithmetic. Geometric symmetry and graph permutations are
verified explicitly. The omitted fixed-anchor reaction is restored before
transport; no assumption about arbitrary optimum symmetry is made.
"""
from pathlib import Path
import argparse
import importlib.util
import json
import sys
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("n25_stress_character_field",
                                              ROOT.parent / "n25_algebraic_upper.py")
Q = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = Q
spec.loader.exec_module(Q)
assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"),
                      object_pairs_hook=no_duplicate_keys)


def compose(first, second):
    return [first[second[i]] for i in range(len(first))]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    geometrypath = ROOT / "evidence/n25-isolation-exact-resume1/rotated-geometry.json"
    fibrepath = ROOT / "evidence/n25-stress-freedom-exact-resume1/VERIFIED.json"
    geometry, fibre = read(geometrypath), read(fibrepath)
    assert fibre["verified"] and fibre["geometry_sha256"] == sha(geometrypath)
    assert fibre["source_sha256"] == sha(ROOT / "n25_stress_freedom.py")
    assert fibre["exact_affine_kernel_sha256"] == sha(ROOT.parent / "n25_core_analysis.py")
    assert fibre["affine_stress_free_dimension"] == 1
    points = [[Q.Q2(*v) for v in p] for p in geometry["points_Qsqrt2"]]
    edges = [tuple(edge) for edge in geometry["edges"]]
    base = [Q.Q2(*v) for v in fibre["base_multipliers_Qsqrt2"]]
    direction = [Q.Q2(*v) for v in fibre["null_direction_Qsqrt2"]]
    assert len(points) == 73 and len(edges) == 128
    assert len(base) == len(direction) == 143
    assert points[0] == [Q.Q2(1), Q.Q2(0)]
    lookup = {tuple(p): i for i, p in enumerate(points)}
    assert len(lookup) == 73
    rotation = [lookup[tuple(Q.rotate(p, 1))] for p in points]
    # Reflection axis is the high boundary centre c1, not the fixed q0 axis.
    axis = points[17]
    squared_axis = Q.dot(axis, axis)
    assert squared_axis.sign() > 0
    def reflect(p):
        coefficient = 2*Q.dot(p, axis)/squared_axis
        return [coefficient*axis[j]-p[j] for j in (0, 1)]
    reflection = [lookup[tuple(reflect(p))] for p in points]
    identity = list(range(73))
    assert sorted(rotation) == sorted(reflection) == identity
    assert reflection[17] == 17
    assert sorted(rotation[:16]) == sorted(reflection[:16]) == list(range(16))
    assert sorted(rotation[16:41]) == sorted(reflection[16:41]) == list(range(16, 41))
    assert sorted(rotation[41:]) == sorted(reflection[41:]) == list(range(41, 73))
    power = identity
    for _ in range(8):
        power = compose(rotation, power)
    assert power == identity and rotation[0] != 0
    assert compose(reflection, reflection) == identity
    inverse_rotation = [rotation.index(i) for i in identity]
    assert compose(reflection, compose(rotation, reflection)) == inverse_rotation
    edgeindex = {frozenset(edge): i for i, edge in enumerate(edges)}
    assert len(edgeindex) == len(edges)

    def completed(values, normalized):
        forces = [[Q.Q2(0), Q.Q2(0)] for _ in points]
        for (u, v), weight in zip(edges, values[:128]):
            for j in (0, 1):
                delta = weight*(points[u][j]-points[v][j])
                forces[u][j] += delta
                forces[v][j] -= delta
        # Force at q0 is radial; this is checked directly for both inputs.
        assert forces[0][1].sign() == 0
        mu0 = -forces[0][0]
        circle = [mu0]+values[128:]
        for node in range(16):
            for j in (0, 1):
                forces[node][j] += circle[node]*points[node][j]
        assert all(value.sign() == 0 for force in forces for value in force)
        assert sum(values[:128], Q.Q2(0)) == Q.Q2(1 if normalized else 0)
        return values[:128]+circle

    fullbase, fulldirection = completed(base, True), completed(direction, False)
    assert fullbase[:128] == [Q.Q2(*v) for v in geometry["weights_Qsqrt2"]]
    assert fullbase[128:] == [Q.Q2(*geometry["circle_multiplier_Qsqrt2"])]*16
    pivot = next(i for i, value in enumerate(fulldirection) if value.sign())
    records = []
    for name, permutation in (("rotation_pi_over_4", rotation),
                              ("reflection_high_centre_axis", reflection)):
        edgeperm = [edgeindex[frozenset((permutation[u], permutation[v]))]
                    for u, v in edges]
        assert sorted(edgeperm) == list(range(128))
        # Explicit transport of the whole multiplier vector.
        transport = edgeperm+[128+permutation[i] for i in range(16)]
        assert sorted(transport) == list(range(144))
        newbase = [None]*144
        newdirection = [None]*144
        for i, target in enumerate(transport):
            newbase[target] = fullbase[i]
            newdirection[target] = fulldirection[i]
        assert newbase == fullbase
        character = newdirection[pivot]/fulldirection[pivot]
        assert character in (Q.Q2(1), Q.Q2(-1))
        assert all(newdirection[i] == character*fulldirection[i] for i in range(144))
        records.append({"generator": name, "point_permutation": permutation,
                        "edge_permutation": edgeperm,
                        "fibre_character": int(character.a),
                        "base_stress_fixed": True,
                        "whole_null_direction_eigenvector_checked": True})
    chiR, chiS = (r["fibre_character"] for r in records)
    assert chiR != 1 or chiS != 1, "Invariant fibre would contradict paid invariant rank"
    # Exact maximal open interval for strictly positive rod stresses, in
    # the parameter normalization of the saved affine null direction.
    limits = [fullbase[i]/(fulldirection[i] if fulldirection[i].sign() > 0 else
                          -fulldirection[i])
              for i in range(128) if fulldirection[i].sign()]
    positive_radius = limits[0]
    for value in limits[1:]:
        if (value-positive_radius).sign() < 0:
            positive_radius = value
    assert positive_radius.sign() > 0
    endpoints = []
    for sign in (-1, 1):
        extremal = [a+sign*positive_radius*b for a, b in zip(fullbase, fulldirection)]
        assert all(value.sign() >= 0 for value in extremal[:128])
        zero_rods = [i for i, value in enumerate(extremal[:128]) if value.sign() == 0]
        assert zero_rods
        middle = [a+sign*(positive_radius/2)*b for a, b in zip(base, direction)]
        assert all(value.sign() > 0 for value in middle[:128])
        completed(middle, True)
        endpoints.append({"parameter_sign": sign, "zero_rod_indices": zero_rods})
    invariantpath = ROOT.parent / "evidence/n25-core-analysis-stable3/stress-verified.json"
    invariant = read(invariantpath)
    assert invariant["verified"] and invariant["D8_invariant_stress_free_dimension"] == 0
    report = {"verified": True, "N": 25,
              "geometry_sha256": sha(geometrypath), "affine_fibre_report_sha256": sha(fibrepath),
              "invariant_stress_report_sha256": sha(invariantpath),
              "generators": records,
              "full_restored_base_mu0_Qsqrt2": fullbase[128].dump(),
              "full_restored_direction_mu0_Qsqrt2": fulldirection[128].dump(),
              "stationarity_and_normalization_rechecked": True,
              "rotation_character": chiR, "reflection_character": chiS,
              "C8_invariant_stress_fibre_dimension": 1 if chiR == 1 else 0,
              "C4_invariant_stress_fibre_dimension": 1,
              "D8_invariant_stress_fibre_dimension": 0,
              "maximal_strict_positive_rod_parameter_radius_Qsqrt2": positive_radius.dump(),
              "positive_rod_interval_endpoints": endpoints,
              "positive_radius_uses_saved_null_direction_normalization": True,
              "geometric_symmetry_assumption_scope": "given exact n25 construction only",
              "global_optimality_proved": False,
              "source_sha256": sha(Path(__file__)),
              "field_arithmetic_sha256": sha(ROOT.parent / "n25_algebraic_upper.py")}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2), encoding="utf8")
    print("N25 exact stress character PASS: rotation", chiR, "reflection", chiS, flush=True)


if __name__ == "__main__":
    main()
