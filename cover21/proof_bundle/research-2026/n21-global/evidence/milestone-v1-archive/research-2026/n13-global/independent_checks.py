"""Additional n13 audits, not a fully independent verifier.

Independently builds the 62-dimensional matrix and proves PD by fraction-free
elimination (no supplied congruence). Independently encloses trig functions with
90-digit fixed-point arithmetic on [-pi,pi], then reuses the inspected tree and
integer force kernels with that implementation. Does not overwrite source reports.
"""
from pathlib import Path
from fractions import Fraction as F
from functools import lru_cache
from math import factorial
from collections import Counter
import argparse
import gzip
import hashlib
import json
import sys
import time

if not __debug__:
    raise RuntimeError("Assertions must be enabled")
HERE = Path(__file__).resolve().parent
BUNDLE = HERE / "external/DiskCoveringSolve/cover13/proof_bundle"
CORE = BUNDLE / "core"
sys.path.insert(0, str(CORE))
S90 = 10**90
S60 = 10**60


def ceildiv(a, b):
    return -((-a) // b)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def atan(n):
    # 180 terms, followed by the explicit alternating-series remainder.
    z = sum((F((-1)**j, (2*j+1)*n**(2*j+1)) for j in range(180)), F(0))
    return z, z + F(1, 361*n**361)


al, ah = atan(5)
bl, bh = atan(239)
PI90 = ((16*al - 4*bh)*S90, (16*ah - 4*bl)*S90)
PI90 = (PI90[0].numerator // PI90[0].denominator,
        ceildiv(PI90[1].numerator, PI90[1].denominator))
assert 3*S90 < PI90[0] <= PI90[1] < 4*S90


def multiply(x, y):
    products = [a*b for a in x for b in y]
    return min(products)//S90, ceildiv(max(products), S90)


def next_term(t, x2, den):
    z = multiply(t, x2)
    return -ceildiv(z[1], den), -(z[0]//den)


@lru_cache(maxsize=100000)
def trig(u):
    # Unlike the producer, do not use quadrant rotation or [-pi/4,pi/4].
    u = F(u) % 1
    if u > F(1, 2):
        u -= 1
    vals = [2*u*p for p in PI90]
    x = (min(vals).numerator//min(vals).denominator,
         ceildiv(max(vals).numerator, max(vals).denominator))
    assert max(abs(v) for v in x) < 4*S90
    x2 = multiply(x, x)
    tc, ts = (S90, S90), x
    co, si = tc, ts
    for j in range(1, 61):
        tc = next_term(tc, x2, (2*j-1)*(2*j))
        ts = next_term(ts, x2, (2*j)*(2*j+1))
        co = (co[0]+tc[0], co[1]+tc[1])
        si = (si[0]+ts[0], si[1]+ts[1])
    # Taylor remainder: cos degree 120, sin degree 121. Bound |x| by 4.
    rc = ceildiv(4**121*S90, factorial(121))
    rs = ceildiv(4**122*S90, factorial(122))
    out = []
    for z, err in ((co, rc), (si, rs)):
        out.append(((z[0]-err)//10**30, ceildiv(z[1]+err, 10**30)))
    return tuple(out)


def halfplane(lo, hi):
    lo, hi = F(lo), F(hi)
    assert 0 <= hi-lo < F(1, 2)
    co, si = trig((lo+hi)/2)
    normal = []
    for interval in (co, si):
        v = F((interval[0]+interval[1])*10**15, 2*S60)
        rounded = (2*v.numerator+v.denominator)//(2*v.denominator)
        assert (rounded-1)*10**45 <= interval[0] <= interval[1] <= (rounded+1)*10**45
        normal.append(rounded)
    lowcos = trig((hi-lo)/2)[0][0]
    bound = (lowcos-2*10**45)*10**18//S60
    return normal, bound


def matrix_check():
    cert = json.loads((CORE/"cover13_krawczyk_cert.json").read_text())
    data = json.loads((CORE/"cover13_kkt_root_119d.json").read_text())
    root = [F(v, int(cert["Qx"])) for v in map(int, cert["xnum"])]
    rho = F(int(cert["rho_num"]), int(cert["rho_den"]))
    q = 10**15
    rounded = []
    for v in root:
        z = v*q
        rounded.append((2*z.numerator+z.denominator)//(2*z.denominator))
    relevant = list(range(62))+list(range(63, 119))
    assert all(abs(F(rounded[j], q)-root[j])+rho <= F(2, q) for j in relevant)
    assert all(0 < root[j]-rho < root[j]+rho < F(1, 10) for j in range(63, 110))
    assert all(-F(49, 2500) < root[j]-rho < root[j]+rho < 0 for j in range(110, 119))
    points = [[q, 0]]+[rounded[2*j:2*j+2] for j in range(31)]
    edges = [tuple(e) for e in data["edges"]]
    assert len(edges) == len(set(edges)) == 47
    jac, weights = [], []
    lap = [[0]*62 for _ in range(62)]
    degrees = Counter()
    for k, (u, v) in enumerate(edges):
        degrees.update((u, v))
        row = [0]*62
        for d in range(2):
            for a, sign in ((u, 1), (v, -1)):
                if a:
                    row[2*(a-1)+d] += sign*2*(points[u][d]-points[v][d])
                    for b, signb in ((u, 1), (v, -1)):
                        if b:
                            lap[2*(a-1)+d][2*(b-1)+d] += rounded[63+k]*sign*signb
        jac.append(row)
        weights.append(rounded[63+k]**2)
    nuq = 49*q//2500
    for a in range(1, 10):
        row = [0]*62
        for d in range(2):
            j = 2*(a-1)+d
            row[j] = 2*points[a][d]
            lap[j][j] += rounded[109+a]
        jac.append(row)
        weights.append(nuq**2)
    assert len(jac) == 56 and max(degrees.values()) <= 6
    assert sum(v*v for row in jac for v in row) < 81*q*q
    assert max(weights)*100 < q*q
    eps = F(2, q)
    da = 236*eps
    error = 13*eps+148*(F(1,100)*(18+da)*da+eps/4*(9+da)**2)
    assert error < F(1, 10**9)
    den = q**4
    matrix = [[lap[i][j]*q**3 + 148*sum(weights[k]*jac[k][i]*jac[k][j]
               for k in range(56)) for j in range(62)] for i in range(62)]
    for i in range(62):
        decrement = (F(1,10**9)+(F(19,10000) if i < 18 else 0))*den
        assert decrement.denominator == 1
        matrix[i][i] -= decrement.numerator
    assert all(matrix[i][j] == matrix[j][i] for i in range(62) for j in range(62))
    # Bareiss leading principal minors: exact division and Sylvester's criterion.
    previous = 1
    determinant_hashes = []
    for k in range(62):
        pivot = matrix[k][k]
        assert pivot > 0, ("nonpositive leading principal minor", k)
        determinant_hashes.append(hashlib.sha256(str(pivot).encode()).hexdigest())
        for i in range(k+1, 62):
            for j in range(i, 62):
                numerator = pivot*matrix[i][j]-matrix[i][k]*matrix[k][j]
                value, remainder = divmod(numerator, previous)
                assert remainder == 0
                matrix[i][j] = matrix[j][i] = value
        previous = pivot
    return {"positive_leading_principal_minors": 62, "method": "independent construction + integer Bareiss",
            "principal_minor_sha256": determinant_hashes, "operator_perturbation": str(error),
            "anchor_radius_squared": "1/64",
            "isolation_margin": str(F(19,10000)-296*F(49,2500)**2/64)}


def trees_check():
    import candidate_global as c
    import noncandidate_global as n
    c.sincos_turn = trig
    c.arc_halfplane = halfplane
    n.arc_halfplane = halfplane
    cert = json.loads(gzip.decompress((CORE/"candidate_global_certificate.json.gz").read_bytes()))
    counts = Counter()
    cap = F(1127,10000)
    lower = [max(F(0), 1-(10-i)*cap) for i in range(1,10)]
    upper = [min(F(1), i*cap) for i in range(1,10)]
    queue = [(0,lower,upper)]
    seen = set()
    rootq = c.root_coordinates()
    while queue:
        idx, lo, hi = queue.pop()
        assert idx not in seen
        seen.add(idx)
        node = cert["nodes"][idx]
        box = c.tighten(lo, hi)
        assert box is not None
        lo, hi = box
        if node["kind"] == "SPLIT":
            a, m = node["axis"], F(node["mid"])
            assert lo[a] < m < hi[a]
            up, low = list(hi), list(lo)
            up[a], low[a] = m, m
            queue.extend([(node["children"][0], list(lo), up),
                          (node["children"][1], low, list(hi))])
        elif node["kind"] == "DUAL":
            assert c.dual_check(lo, hi, node) > 0
            counts["DUAL"] += 1
        else:
            assert node["kind"] == "LOCAL" and c.local_check(lo, hi, rootq) >= 0
            counts["LOCAL"] += 1
    assert len(seen) == len(cert["nodes"]) == 1831
    assert counts == {"DUAL": 837, "LOCAL": 79}
    noncert = json.loads(gzip.decompress((BUNDLE/"enumeration/noncandidate_certificate.json.gz").read_bytes()))
    residual = json.loads((BUNDLE/"enumeration/metric_residuals_new.json").read_text())
    excluded = set()
    nnodes = nleaves = 0
    for case in noncert["cases"]:
        rid = case["residual_index"]
        assert rid not in excluded
        excluded.add(rid)
        row = residual[rid]
        b = row["B"]
        edges = n.edges(b,row["faces"])
        bounds = n.bounds(b,row["faces"])
        lo, hi = n.rootbox(bounds)
        queue = [(0,lo,hi)]
        seen = set()
        while queue:
            idx, lo, hi = queue.pop()
            assert idx not in seen
            seen.add(idx)
            node = case["nodes"][idx]
            box = n.tighten(bounds,lo,hi)
            assert box is not None
            lo, hi = box
            if node["kind"] == "SPLIT":
                a, m = node["axis"], F(node["mid"])
                assert lo[a] < m < hi[a]
                up, low = list(hi), list(lo)
                up[a], low[a] = m, m
                queue.extend([(node["children"][0], list(lo), up),
                              (node["children"][1], low, list(hi))])
            else:
                assert node["kind"] == "DUAL" and n.check_dual(b,edges,lo,hi,node) > 0
                nleaves += 1
        assert len(seen) == len(case["nodes"])
        nnodes += len(seen)
    assert excluded == set(range(1761))-{1138}
    assert (nnodes,nleaves) == (2908,2334)
    # Exact special values as additional controls.
    for turn, expected in ((F(0), ((1,1),(0,0))),
                           (F(1,4), ((0,0),(1,1))),
                           (F(1,2), ((-1,-1),(0,0)))):
        got = trig(turn)
        for interval, value in zip(got, expected):
            assert interval[0] <= value[0]*S60 <= interval[1]
    return {"candidate_nodes": 1831, "candidate_leaves": dict(counts),
            "noncandidate_cases": len(excluded), "noncandidate_nodes": nnodes,
            "noncandidate_dual_leaves": nleaves, "trig_cache": trig.cache_info()._asdict(),
            "scope": "independent transcendental intervals; inspected producer force/tree kernels reused"}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=HERE/"evidence/independent-checks.json")
    args = parser.parse_args()
    start = time.time()
    result = {"verified": True, "matrix": matrix_check(), "trees": trees_check(),
              "input_manifest_sha256": sha(BUNDLE/"MANIFEST_SHA256.json"),
              "audit_source_sha256": sha(Path(__file__)),
              "scope": "additional same-agent audits, not external peer review or fully independent verification",
              "seconds": time.time()-start}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2),encoding="utf8")
    print(json.dumps({k:v for k,v in result.items() if k != "matrix"},indent=2),flush=True)


if __name__ == "__main__":
    main()
