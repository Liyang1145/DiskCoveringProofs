"""Try exact 120D isolation of the two extremal positive-stress subcores.

Every reported PASS requires positive fraction-free pivots and a positive
transported isolation margin. Failure is saved as not proved; it is never
upgraded to a mathematical counterexample. No angular/global lower bound
is claimed here.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
from math import isqrt
import argparse
import hashlib
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
    args.output.mkdir(parents=True)
    geometrypath = ROOT / "evidence/n25-isolation-exact-resume1/rotated-geometry.json"
    fibrepath = ROOT / "evidence/n25-stress-freedom-exact-resume1/VERIFIED.json"
    characterpath = ROOT / "evidence/n25-stress-character-resume2.json"
    geo, fibre, character = map(read, (geometrypath, fibrepath, characterpath))
    assert character["verified"] and character["geometry_sha256"] == sha(geometrypath)
    assert character["affine_fibre_report_sha256"] == sha(fibrepath)
    assert character["source_sha256"] == sha(ROOT / "n25_stress_character.py")
    points = [[Q.Q2(*v) for v in p] for p in geo["points_Qsqrt2"]]
    edges = [tuple(e) for e in geo["edges"]]
    base = [Q.Q2(*v) for v in fibre["base_multipliers_Qsqrt2"]]
    direction = [Q.Q2(*v) for v in fibre["null_direction_Qsqrt2"]]
    parameter = Q.Q2(*character["maximal_strict_positive_rod_parameter_radius_Qsqrt2"])
    gamma, lam, nu, radius = 500, F(1, 5000), F(1, 50), F(1, 50)
    scale = 10**15
    eps, buffer = F(2, scale), F(1, 10**8)
    results = []
    for sign in (-1, 1):
        multipliers = [a+sign*parameter*d for a, d in zip(base, direction)]
        selected = [i for i, w in enumerate(multipliers[:128]) if w.sign() > 0]
        assert len(selected) == 92 and all(w.sign() >= 0 for w in multipliers[:128])
        weights = [multipliers[i] for i in selected]
        assert sum(weights, Q.Q2(0)) == Q.Q2(1)
        assert all((Q.Q2(F(1, 10))-w).sign() > 0 for w in weights)
        mu = multipliers[128:]
        assert all(m.sign() < 0 and (m+nu).sign() > 0 for m in mu)
        used = sorted({v for i in selected for v in edges[i]})
        assert used[:41] == list(range(41)) and len(used) == 61
        labels = {v: i for i, v in enumerate(used)}
        active_faces = [j for j in range(32)
                        if all(i in selected for i in range(32+3*j, 35+3*j))]
        assert len(active_faces) == 20 and used[41:] == [41+j for j in active_faces]
        p = [points[i] for i in used]
        ed = [(labels[edges[i][0]], labels[edges[i][1]]) for i in selected]
        faces = [geo["faces"][j] for j in active_faces]
        assert ed == ([(i, 16+i) for i in range(16)] +
                      [(i, 16+(i+1) % 16) for i in range(16)] +
                      [(41+j, 16+k) for j, face in enumerate(faces) for k in face])
        assert all(Q.dot(Q.sub(p[u], p[v]), Q.sub(p[u], p[v])) == Q.Q2(*geo["t_Qsqrt2"])
                   for u, v in ed)
        forces = [[Q.Q2(0), Q.Q2(0)] for _ in p]
        for (u, v), w in zip(ed, weights):
            for axis in (0, 1):
                value = w*(p[u][axis]-p[v][axis])
                forces[u][axis] += value
                forces[v][axis] -= value
        for i in range(1, 16):
            for axis in (0, 1):
                forces[i][axis] += mu[i-1]*p[i][axis]
        assert all(v.sign() == 0 for f in forces[1:] for v in f)
        G = 120
        integer_points = [[local.rounded(v, scale, eps) for v in x] for x in p]
        integer_weights = [local.rounded(v, scale, eps) for v in weights]
        integer_mu = [local.rounded(v, scale, eps) for v in mu]
        lap = [[0]*G for _ in range(G)]
        jac, w2, degrees = [], [], Counter()
        for (u, v), w in zip(ed, integer_weights):
            degrees.update((u, v))
            row = [0]*G
            for axis in (0, 1):
                for node, direction_sign in ((u, 1), (v, -1)):
                    if node:
                        i = 2*(node-1)+axis
                        row[i] += 2*direction_sign*(integer_points[u][axis]-integer_points[v][axis])
                        for other, other_sign in ((u, 1), (v, -1)):
                            if other:
                                lap[i][2*(other-1)+axis] += w*direction_sign*other_sign
            jac.append(row)
            w2.append(w*w)
        ninteger = nu*scale
        assert ninteger.denominator == 1
        for node in range(1, 16):
            row = [0]*G
            for axis in (0, 1):
                i = 2*(node-1)+axis
                row[i] = 2*integer_points[node][axis]
                lap[i][i] += integer_mu[node-1]
            jac.append(row)
            w2.append(ninteger.numerator**2)
        assert sum(v*v for row in jac for v in row) < 144*scale*scale
        assert max(w2)*100 < scale*scale
        da = 4*(isqrt(4*len(ed)+30)+1)*eps
        error = (2*max(degrees.values())+1)*eps+gamma*(
            F(1, 100)*(24+da)*da+eps/4*(12+da)**2)
        assert error < buffer
        denominator = scale**4
        H = [[lap[i][j]*scale**3+gamma*sum(w2[k]*jac[k][i]*jac[k][j]
              for k in range(len(jac))) for j in range(G)] for i in range(G)]
        for i in range(G):
            subtract = (buffer+(lam if i < 30 else 0))*denominator
            assert subtract.denominator == 1
            H[i][i] -= subtract.numerator
        previous, minors, failure = 1, [], None
        for k in range(G):
            pivot = H[k][k]
            if pivot <= 0:
                failure = k
                break
            minors.append(hashlib.sha256(pivot.to_bytes((pivot.bit_length()+7)//8, "big")).hexdigest())
            for i in range(k+1, G):
                for j in range(i, G):
                    value, rem = divmod(pivot*H[i][j]-H[i][k]*H[k][j], previous)
                    assert not rem
                    H[i][j] = H[j][i] = value
            previous = pivot
        gap = lam-2*gamma*nu**2*radius**2
        assert gap > 0
        result = {"parameter_sign": sign, "verified": failure is None,
                  "positive_leading_principal_minors": len(minors),
                  "first_failed_pivot": failure, "gamma": gamma, "lambda": str(lam),
                  "nu": str(nu), "anchor_radius": str(radius), "isolation_margin": str(gap),
                  "matrix_perturbation_bound": str(error),
                  "principal_minor_binary_sha256": minors,
                  "core_nodes": 61, "positive_rods": 92, "G": G,
                  "old_nodes_retained": used, "old_face_indices_retained": active_faces,
                  "faces": faces, "edges": ed,
                  "points_Qsqrt2": [[v.dump() for v in x] for x in p],
                  "weights_Qsqrt2": [w.dump() for w in weights],
                  "free_circle_multipliers_Qsqrt2": [m.dump() for m in mu]}
        results.append(result)
        print("N25 extremal support sign", sign, "exact isolation",
              "PASS" if failure is None else "NOT PROVED", len(minors), "positive pivots", flush=True)
    report = {"verified": all(r["verified"] for r in results), "N": 25, "cores": results,
              "geometry_sha256": sha(geometrypath), "fibre_report_sha256": sha(fibrepath),
              "stress_character_sha256": sha(characterpath),
              "rounding_source_sha256": sha(ROOT / "n25_anchor_isolation.py"),
              "source_sha256": sha(Path(__file__)),
              "scope": "specified two 120D positive-core local anchor isolations only",
              "entire_angle_domain_proved": False, "global_optimality_proved": False}
    (args.output / "REPORT.json").write_text(json.dumps(report, indent=2), encoding="utf8")


if __name__ == "__main__":
    main()
