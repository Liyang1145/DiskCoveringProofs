"""Exact geometry isolation using the algebraic stress, not KKT root uniqueness.

Coordinates are rotated into q0=(1,0), and are then all in Q(sqrt(2)).
Multiplier freedom in a full KKT system does not prevent this geometric test.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
from math import isqrt
import argparse
import hashlib
import importlib.util
import json
import sys

ROOT = Path(__file__).resolve().parent
SYN = ROOT.parent
spec = importlib.util.spec_from_file_location("n25_local_exact_field", SYN / "n25_algebraic_upper.py")
Q = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = Q
spec.loader.exec_module(Q)
assert __debug__


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def numeric(v):
    return float(v.a)+float(v.b)*2**.5


def prepare():
    path = SYN / "evidence/n25-algebraic-upper-round2/geometry.json"
    stresspath = SYN / "evidence/n25-core-analysis-stable3/stress-verified.json"
    data = json.loads(path.read_text())
    stress = json.loads(stresspath.read_text())
    assert stress["verified"] and stress["geometry_sha256"] == sha(path)
    raw = [[Q.Q2(*v) for v in p] for p in data["anchors"]+data["centers"]+data["witnesses"]]
    reference = raw[0]
    points = [[Q.A2*Q.dot(reference, p), Q.A2*Q.cross(reference, p)] for p in raw]
    assert points[0] == [Q.Q2(1), Q.Q2(0)]
    edges = ([(i, 16+i) for i in range(16)] +
             [(i, 16+(i+1) % 16) for i in range(16)] +
             [(41+j, 16+k) for j, face in enumerate(data["faces"]) for k in face])
    weights = [Q.Q2(*stress["exact_weights_Qsqrt2"][k]) for k in stress["edge_orbit"]]
    mu = Q.Q2(*stress["exact_common_circle_multiplier"])
    assert sum(weights, Q.Q2(0)) == Q.Q2(1) and mu.sign() < 0
    for p in points[:16]:
        assert Q.dot(p, p) == Q.Q2(1)
    forces = [[Q.Q2(0), Q.Q2(0)] for _ in points]
    for (u, v), w in zip(edges, weights):
        delta = Q.sub(points[u], points[v])
        assert Q.dot(delta, delta) == Q.R2
        assert w.sign() > 0 and (Q.Q2(F(1, 10))-w).sign() > 0
        for axis in (0, 1):
            forces[u][axis] += w*delta[axis]
            forces[v][axis] -= w*delta[axis]
    for i in range(16):
        for axis in (0, 1):
            forces[i][axis] += mu*points[i][axis]
    assert all(v.sign() == 0 for p in forces for v in p)
    return data, points, edges, weights, mu, path, stresspath


def rounded(v, q, eps):
    s = 10**70
    low = isqrt(2*s*s)
    approximate = v.a+v.b*F(low, s)
    x = approximate*q
    r = (2*x.numerator+x.denominator)//(2*x.denominator)
    assert (Q.Q2(eps)-(v-Q.Q2(F(r, q)))).sign() > 0
    assert (Q.Q2(eps)+(v-Q.Q2(F(r, q)))).sign() > 0
    return r


def matrices(points, edges, weights, mu, q, eps):
    g = 2*(len(points)-1)
    p = [[rounded(v, q, eps) for v in point] for point in points]
    w = [rounded(v, q, eps) for v in weights]
    circle = rounded(mu, q, eps)
    lap = [[0]*g for _ in range(g)]
    jac, squareweights = [], []
    degrees = Counter()
    for (u, v), weight in zip(edges, w):
        degrees.update((u, v))
        row = [0]*g
        for axis in (0, 1):
            for node, sign in ((u, 1), (v, -1)):
                if node:
                    i = 2*(node-1)+axis
                    row[i] += 2*sign*(p[u][axis]-p[v][axis])
                    for other, other_sign in ((u, 1), (v, -1)):
                        if other:
                            lap[i][2*(other-1)+axis] += weight*sign*other_sign
        jac.append(row)
        squareweights.append(weight**2)
    nq = q//100
    for node in range(1, 16):
        row = [0]*g
        for axis in (0, 1):
            i = 2*(node-1)+axis
            row[i] = 2*p[node][axis]
            lap[i][i] += circle
        jac.append(row)
        squareweights.append(nq**2)
    return g, lap, jac, squareweights, degrees


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--output", type=Path, required=True)
    ap.add_argument("--probe-only", action="store_true")
    args = ap.parse_args()
    assert not args.output.exists()
    args.output.mkdir(parents=True)
    data, points, edges, weights, mu, path, stresspath = prepare()
    nu = F(1, 100)
    assert (mu+nu).sign() > 0
    q = 10**15
    eps, buffer = F(2, q), F(1, 10**8)
    g, lap, jac, squareweights, degrees = matrices(points, edges, weights, mu, q, eps)
    if args.probe_only:
        import numpy as np
        L = np.asarray(lap, dtype=float)/q
        A = np.asarray(jac, dtype=float)/q
        W = np.asarray(squareweights, dtype=float)/q**2
        P = np.diag([1.]*30+[0.]*(g-30))
        diagnostics = []
        for gamma in (200, 300, 500, 1000, 2000):
            for lam in (.0002, .0005, .001):
                least = float(np.linalg.eigvalsh(L+gamma*(A.T*W)@A-lam*P)[0])
                diagnostics.append({"gamma": gamma, "lambda": lam, "least_eigenvalue_numeric": least})
        report = {"N": 25, "G": g, "diagnostics": diagnostics, "exact_isolation_proved": False}
        (args.output / "NUMERIC.json").write_text(json.dumps(report, indent=2), encoding="utf8")
        print(json.dumps(report, indent=2), flush=True)
        return
    gamma, lam, radius = 500, F(1, 5000), F(1, 25)
    assert sum(v*v for row in jac for v in row) < 144*q*q
    assert max(squareweights)*100 < q*q
    structural_entries = 4*len(edges)+2*15
    da = 4*(isqrt(structural_entries)+1)*eps
    error = (2*max(degrees.values())+1)*eps + gamma*(
        F(1, 100)*(24+da)*da + eps/4*(12+da)**2)
    assert error < buffer
    denominator = q**4
    h = [[lap[i][j]*q**3 + gamma*sum(squareweights[k]*jac[k][i]*jac[k][j]
           for k in range(len(jac))) for j in range(g)] for i in range(g)]
    for i in range(g):
        subtract = (buffer+(lam if i < 30 else 0))*denominator
        assert subtract.denominator == 1
        h[i][i] -= subtract.numerator
    previous, minor_hashes = 1, []
    for k in range(g):
        pivot = h[k][k]
        assert pivot > 0, ("n25 geometry isolation not proved", k)
        minor_hashes.append(hashlib.sha256(pivot.to_bytes((pivot.bit_length()+7)//8, "big")).hexdigest())
        for i in range(k+1, g):
            for j in range(i, g):
                value, remainder = divmod(pivot*h[i][j]-h[i][k]*h[k][j], previous)
                assert remainder == 0
                h[i][j] = h[j][i] = value
        previous = pivot
    gap = lam-2*gamma*nu**2*radius**2
    assert gap > 0
    geometry = {"N": 25, "B": 16, "G": g, "points_Qsqrt2": [[v.dump() for v in p] for p in points],
                "edges": edges, "faces": data["faces"], "weights_Qsqrt2": [v.dump() for v in weights],
                "circle_multiplier_Qsqrt2": mu.dump(), "t_Qsqrt2": Q.R2.dump(),
                "q0_exactly_one_zero": True, "source_geometry_sha256": sha(path)}
    (args.output / "rotated-geometry.json").write_text(json.dumps(geometry, indent=2), encoding="utf8")
    report = {"verified": True, "N": 25, "geometry_dimension": g,
              "positive_leading_principal_minors": g, "gamma": gamma, "lambda": str(lam),
              "nu": str(nu), "anchor_radius": str(radius), "isolation_margin": str(gap),
              "matrix_perturbation_bound": str(error), "principal_minor_binary_sha256": minor_hashes,
              "geometry_sha256": sha(path), "stress_sha256": sha(stresspath),
              "rotated_geometry_sha256": sha(args.output / "rotated-geometry.json"),
              "KKT_multiplier_uniqueness_required": False,
              "scope": "specified positive-core anchor isolation, no global or entire-angle conclusion",
              "global_optimality_proved": False, "source_sha256": sha(Path(__file__))}
    (args.output / "VERIFIED.json").write_text(json.dumps(report, indent=2), encoding="utf8")
    print("N25 EXACT algebraic 144D core anchor isolation PASS, gap", gap, flush=True)


if __name__ == "__main__":
    main()
