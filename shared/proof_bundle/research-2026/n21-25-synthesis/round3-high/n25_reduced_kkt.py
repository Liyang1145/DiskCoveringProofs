"""Explicit 228-variable quadratic roots and nonsingularity prerequisites.

Nonsingularity is proved by the block argument in N25-STRESS-ENDPOINT-CORES.md:
equilibrium forces delta_t=0, exact augmented PD forces delta_geometry=0,
and extension into the paid full affine fibre forces delta_multipliers=0.
No claim about the full 288-variable root or global optimality is made.
"""
from pathlib import Path
from fractions import Fraction as F
import argparse
import json
import n25_anchor_isolation as local
from stream_catalog import sha, no_duplicate_keys

ROOT = Path(__file__).resolve().parent
Q = local.Q
assert __debug__


def read(path):
    return json.loads(path.read_text(encoding="utf8"), object_pairs_hook=no_duplicate_keys)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    assert not args.output.exists()
    isopath = ROOT / "evidence/n25-endpoint-core-isolation-resume1/REPORT.json"
    replaypath = ROOT / "evidence/n25-endpoint-core-isolation-replay-resume1/REPORT.json"
    fibrepath = ROOT / "evidence/n25-stress-freedom-exact-resume1/VERIFIED.json"
    characterpath = ROOT / "evidence/n25-stress-character-resume2.json"
    geop = ROOT / "evidence/n25-isolation-exact-resume1/rotated-geometry.json"
    iso, fibre, character, geo = map(read, (isopath, fibrepath, characterpath, geop))
    assert iso["verified"] and sha(isopath) == sha(replaypath)
    assert iso["source_sha256"] == sha(ROOT / "n25_endpoint_core_isolation.py")
    assert iso["geometry_sha256"] == fibre["geometry_sha256"] == sha(geop)
    assert iso["fibre_report_sha256"] == sha(fibrepath)
    assert iso["stress_character_sha256"] == sha(characterpath)
    assert fibre["verified"] and fibre["full_affine_stationarity_rank"] == 142
    assert fibre["full_multiplier_variables"] == 143 and fibre["affine_stress_free_dimension"] == 1
    assert fibre["source_sha256"] == sha(ROOT / "n25_stress_freedom.py")
    assert fibre["exact_affine_kernel_sha256"] == sha(ROOT.parent / "n25_core_analysis.py")
    assert character["verified"] and character["source_sha256"] == sha(ROOT / "n25_stress_character.py")
    base = [Q.Q2(*v) for v in fibre["base_multipliers_Qsqrt2"]]
    direction = [Q.Q2(*v) for v in fibre["null_direction_Qsqrt2"]]
    radius = Q.Q2(*character["maximal_strict_positive_rod_parameter_radius_Qsqrt2"])
    t = Q.Q2(*geo["t_Qsqrt2"])
    assert t == Q.R2
    results = []
    for core in iso["cores"]:
        assert core["verified"] and core["G"] == core["positive_leading_principal_minors"] == 120
        assert len(core["principal_minor_binary_sha256"]) == 120
        assert F(core["isolation_margin"]) == F(1, 25000)
        sign = core["parameter_sign"]
        assert sign in (-1, 1)
        fullstress = [a+sign*radius*b for a, b in zip(base, direction)]
        deleted = [i for i, v in enumerate(fullstress[:128]) if v.sign() == 0]
        selected = [i for i, v in enumerate(fullstress[:128]) if v.sign() > 0]
        assert len(deleted) == 36 and len(selected) == 92
        # An absent rod enforces the unique point of the paid affine fibre.
        pivot = next(i for i in deleted if direction[i].sign())
        assert base[pivot].sign() > 0 and -base[pivot]/direction[pivot] == sign*radius
        points = [[Q.Q2(*v) for v in p] for p in core["points_Qsqrt2"]]
        edges = [tuple(e) for e in core["edges"]]
        weights = [Q.Q2(*v) for v in core["weights_Qsqrt2"]]
        mu = [Q.Q2(*v) for v in core["free_circle_multipliers_Qsqrt2"]]
        assert weights == [fullstress[i] for i in selected] and mu == fullstress[128:]
        assert len(points) == 61 and len(edges) == len(weights) == 92 and len(mu) == 15
        assert points[0] == [Q.Q2(1), Q.Q2(0)]
        assert all(w.sign() > 0 for w in weights)
        assert sum(weights, Q.Q2(0)) == Q.Q2(1)
        forces = [[Q.Q2(0), Q.Q2(0)] for _ in points]
        for (u, v), w in zip(edges, weights):
            delta = Q.sub(points[u], points[v])
            assert Q.dot(delta, delta) == t
            for axis in (0, 1):
                forces[u][axis] += w*delta[axis]
                forces[v][axis] -= w*delta[axis]
        for node in range(1, 16):
            assert Q.dot(points[node], points[node]) == Q.Q2(1)
            for axis in (0, 1):
                forces[node][axis] += mu[node-1]*points[node][axis]
        assert all(value.sign() == 0 for force in forces[1:] for value in force)
        used = core["old_nodes_retained"]
        assert len(used) == 61 and used == sorted(set(used)) and used[:41] == list(range(41))
        absent_nodes = set(range(73))-set(used)
        oldedges = geo["edges"]
        assert all(i in deleted for node in absent_nodes for i, ed in enumerate(oldedges) if node in ed)
        # All 36 omitted multipliers can be set to zero without adding any
        # nonzero equilibrium equation at an omitted witness. A normalized
        # reduced solution extends to the full affine line, and the pivot
        # just checked fixes its sole parameter.
        G, M, B = 120, 92, 16
        dimension = G+1+M+B-1
        assert dimension == 228
        variables = [v.dump() for p in points[1:] for v in p]
        variables += [t.dump()]+[w.dump() for w in weights]+[m.dump() for m in mu]
        assert len(variables) == dimension
        results.append({"parameter_sign": sign, "dimension": dimension,
                        "G": G, "B": B, "M": M, "vertices": 61,
                        "edges": edges, "faces": core["faces"],
                        "root_variables_Qsqrt2": variables,
                        "all_quadratic_root_equations_rechecked": True,
                        "normalized_reduced_stress_unique_by_extension": True,
                        "deleted_rod_fixing_affine_parameter": pivot,
                        "deleted_rod_direction_Qsqrt2": direction[pivot].dump(),
                        "augmented_PD_dimension": 120,
                        "square_KKT_Jacobian_nonsingularity_block_prerequisites_verified": True,
                        "Jacobian_determinant_not_directly_computed_here": True})
    report = {"verified": True, "N": 25, "reduced_cores": results,
              "geometry_sha256": sha(geop), "isolation_report_sha256": sha(isopath),
              "isolation_replay_sha256": sha(replaypath),
              "affine_fibre_report_sha256": sha(fibrepath),
              "stress_character_sha256": sha(characterpath),
              "nonsingularity_written_argument": "N25-STRESS-ENDPOINT-CORES.md section 5",
              "nonsingularity_written_argument_sha256": sha(ROOT / "N25-STRESS-ENDPOINT-CORES.md"),
              "explicit_radius_object": "sqrt(1-2sqrt(2)/3)",
              "full_288_variable_KKT_root_isolated": False,
              "entire_angle_domain_proved": False, "global_optimality_proved": False,
              "source_sha256": sha(Path(__file__))}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2), encoding="utf8")
    print("N25 two exact 228D reduced quadratic roots + block nonsingularity prerequisites PASS",
          flush=True)


if __name__ == "__main__":
    main()
