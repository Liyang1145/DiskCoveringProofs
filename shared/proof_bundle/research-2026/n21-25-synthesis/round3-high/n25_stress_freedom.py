"""Exact affine dimension of all stresses at the fixed algebraic n25 geometry.

Eliminate each 3-rod witness equilibrium and each free-anchor equilibrium
exactly, reducing 143 multiplier variables to 49 local kernel parameters.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse
import importlib.util
import json
import sys
from stream_catalog import sha

ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("n25_full_stress_exact_solver", ROOT.parent / "n25_core_analysis.py")
S = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = S
spec.loader.exec_module(S)
Q = S.Q
assert __debug__


def full_stress(parameters, columns):
    result = [Q.Q2(0) for _ in range(143)]
    for value, column in zip(parameters, columns):
        for index, coefficient in column.items():
            result[index] += value*coefficient
    return result


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    args.output.mkdir(parents=True)
    geometrypath = ROOT / "evidence/n25-isolation-exact-resume1/rotated-geometry.json"
    geometry = json.loads(geometrypath.read_text())
    points = [[Q.Q2(*v) for v in p] for p in geometry["points_Qsqrt2"]]
    edges = [tuple(edge) for edge in geometry["edges"]]
    baseweights = [Q.Q2(*v) for v in geometry["weights_Qsqrt2"]]
    mu = Q.Q2(*geometry["circle_multiplier_Qsqrt2"])
    assert len(points) == 73 and len(edges) == len(baseweights) == 128
    assert points[0] == [Q.Q2(1), Q.Q2(0)]
    assert all(Q.dot(point, point) == Q.Q2(1) for point in points[:16])
    squared_radius = Q.Q2(*geometry["t_Qsqrt2"])
    assert all(Q.dot(Q.sub(points[u], points[v]), Q.sub(points[u], points[v])) == squared_radius
               for u, v in edges)
    expected_edges = ([(i, 16+i) for i in range(16)] +
                      [(i, 16+(i+1) % 16) for i in range(16)] +
                      [(41+j, 16+k) for j, face in enumerate(geometry["faces"]) for k in face])
    assert edges == expected_edges
    columns, base_parameters, local_rank_witnesses = [], [], []
    for face in range(32):
        vectors = []
        for index in range(32+3*face, 35+3*face):
            u, v = edges[index]
            assert u == 41+face and 16 <= v < 41
            vectors.append(Q.sub(points[u], points[v]))
        coefficients = [Q.cross(vectors[1], vectors[2]),
                        Q.cross(vectors[2], vectors[0]),
                        Q.cross(vectors[0], vectors[1])]
        assert any(value.sign() != 0 for value in coefficients)
        assert all(sum((coefficients[j]*vectors[j][axis] for j in range(3)), Q.Q2(0)).sign() == 0
                   for axis in (0, 1))
        column = {32+3*face+j: value for j, value in enumerate(coefficients)}
        pivot = next(index for index, value in column.items() if value.sign())
        parameter = baseweights[pivot]/column[pivot]
        assert all(parameter*value == baseweights[index] for index, value in column.items())
        columns.append(column)
        base_parameters.append(parameter)
        local_rank_witnesses.append([value.dump() for value in coefficients])
    for anchor in range(1, 16):
        u = Q.sub(points[anchor], points[16+anchor])
        v = Q.sub(points[anchor], points[16+(anchor+1) % 16])
        q = points[anchor]
        coefficients = [Q.cross(v, q), Q.cross(q, u), Q.cross(u, v)]
        assert any(value.sign() != 0 for value in coefficients)
        assert all((coefficients[0]*u[axis]+coefficients[1]*v[axis]+coefficients[2]*q[axis]).sign() == 0
                   for axis in (0, 1))
        column = {anchor: coefficients[0], 16+anchor: coefficients[1],
                  128+anchor-1: coefficients[2]}
        values = {anchor: baseweights[anchor], 16+anchor: baseweights[16+anchor],
                  128+anchor-1: mu}
        pivot = next(index for index, value in column.items() if value.sign())
        parameter = values[pivot]/column[pivot]
        assert all(parameter*value == values[index] for index, value in column.items())
        columns.append(column)
        base_parameters.append(parameter)
        local_rank_witnesses.append([value.dump() for value in coefficients])
    # q0 is fixed, so its two rod multipliers have no q0 stationarity equations.
    columns += [{0: Q.Q2(1)}, {16: Q.Q2(1)}]
    base_parameters += [baseweights[0], baseweights[16]]
    assert len(columns) == len(base_parameters) == 49
    rows = []
    for node in range(16, 41):
        for axis in (0, 1):
            row = []
            for column in columns:
                value = Q.Q2(0)
                for edge, weight in column.items():
                    if edge >= 128:
                        continue
                    u, v = edges[edge]
                    if node == u:
                        value += weight*(points[u][axis]-points[v][axis])
                    elif node == v:
                        value += weight*(points[v][axis]-points[u][axis])
                row.append(value)
            rows.append(row+[Q.Q2(0)])
    rows.append([sum((value for index, value in column.items() if index < 128), Q.Q2(0))
                 for column in columns]+[Q.Q2(1)])
    assert all(sum((a*b for a, b in zip(row[:-1], base_parameters)), Q.Q2(0)) == row[-1] for row in rows)
    free, evaluator, rank = S.solve_affine(rows, 49)
    assert rank == 48 and len(free) == 1
    assert evaluator([base_parameters[free[0]]]) == base_parameters
    zeros = evaluator([Q.Q2(0)])
    ones = evaluator([Q.Q2(1)])
    direction_parameters = [b-a for a, b in zip(zeros, ones)]
    base = full_stress(base_parameters, columns)
    direction = full_stress(direction_parameters, columns)
    assert base[:128] == baseweights and base[128:] == [mu]*15
    assert any(value.sign() != 0 for value in direction)
    assert sum(direction[:128], Q.Q2(0)).sign() == 0
    def verify(values, normalized):
        forces = [[Q.Q2(0), Q.Q2(0)] for _ in points]
        for (u, v), weight in zip(edges, values[:128]):
            for axis in (0, 1):
                delta = points[u][axis]-points[v][axis]
                forces[u][axis] += weight*delta
                forces[v][axis] -= weight*delta
        for node in range(1, 16):
            for axis in (0, 1):
                forces[node][axis] += values[128+node-1]*points[node][axis]
        assert all(value.sign() == 0 for force in forces[1:] for value in force)
        assert sum(values[:128], Q.Q2(0)) == Q.Q2(1 if normalized else 0)
    verify(base, True)
    verify(direction, False)
    epsilon = None
    for exponent in range(1, 60):
        candidate = F(1, 10**exponent)
        plus = [a+candidate*b for a, b in zip(base, direction)]
        minus = [a-candidate*b for a, b in zip(base, direction)]
        if all(value.sign() > 0 for values in (plus, minus) for value in values[:128]) and all(
                value.sign() < 0 and (value+F(1, 100)).sign() > 0
                for values in (plus, minus) for value in values[128:]):
            epsilon = candidate
            verify(plus, True)
            verify(minus, True)
            break
    assert epsilon is not None
    result = {"verified": True, "N": 25, "geometry_sha256": sha(geometrypath),
              "full_multiplier_variables": 143, "eliminated_local_equations_rank": 94,
              "reduced_variables": 49, "reduced_affine_rank": rank,
              "full_affine_stationarity_rank": 142, "affine_stress_free_dimension": 1,
              "exact_constraint_jacobian_rank": 142,
              "strict_positive_two_sided_parameter_radius": str(epsilon),
              "base_multipliers_Qsqrt2": [v.dump() for v in base],
              "null_direction_Qsqrt2": [v.dump() for v in direction],
              "local_rank2_witnesses_Qsqrt2": local_rank_witnesses,
              "scope": "all normalized stationary multipliers at the fixed algebraic geometry/radius",
              "full_KKT_root_isolated": False, "geometry_isolation_not_contradicted": True,
              "global_optimality_proved": False, "source_sha256": sha(Path(__file__)),
              "exact_affine_kernel_sha256": sha(ROOT.parent / "n25_core_analysis.py")}
    (args.output / "VERIFIED.json").write_text(json.dumps(result, indent=2), encoding="utf8")
    print("N25 EXACT full stress freedom certified: rank 142 of 143; one-dimensional positive fibre", flush=True)


if __name__ == "__main__":
    main()
