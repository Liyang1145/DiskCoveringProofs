"""r20-rigidity step 9: the two registered objects vs the saved candidate.

Reproduces REPORT.md §0/§4 statements:
  A  cert_sym60.json : mirror symmetry at 60 dps (axis scan + refinement), gamma (20-point
     critical set) vs T_cert, and the aligned sup-distance to the saved candidate
  B  n11/kkt2/frozen.json : same
Scope: read-only; calibration, no claim.
"""
import json, math, itertools
from pathlib import Path
import mpmath as mp

mp.mp.dps = 60
P = Path(__file__).parent
ROOT = P.parents[2]
T_CERT = mp.mpf('0.379983853119838689722261606136093214308718957')
raw = json.loads((ROOT / 'n11/upper/certified_object.json').read_text(encoding='utf-8-sig'))
LО = mp.mpf(raw['certified_interval']['lo'])
COBJ = [mp.matrix([mp.mpf(int(v)) / mp.mpf(10) ** 17 for v in a]) for a in raw['centers_scaled_1e17']]


def load(path, key, expo):
    p = ROOT / path
    if not p.exists():
        return None
    d = json.loads(p.read_text(encoding='utf-8-sig'))
    if key in d:
        vals = d[key]
        if isinstance(vals[0][0], str) or isinstance(vals[0][0], int):
            return [mp.matrix([mp.mpf(int(v)) / mp.mpf(10) ** expo for v in a]) for a in vals]
        return [mp.matrix([mp.mpf(float(v)) for v in a]) for a in vals]
    if 'centers' in d:
        return [mp.matrix([mp.mpf(float(v)) for v in a]) for a in d['centers']]
    return None


def dist(p, q):
    return mp.sqrt(sum((p[t] - q[t]) ** 2 for t in range(2)))


def gamma20(C):
    vals = []
    for (i, j, k) in itertools.combinations(range(11), 3):
        a, b, c = i, j, k
        A = mp.matrix([[C[b][0] - C[a][0], C[b][1] - C[a][1]],
                       [C[c][0] - C[a][0], C[c][1] - C[a][1]]])
        rhs = mp.matrix([(sum(C[b][t] ** 2 for t in range(2)) - sum(C[a][t] ** 2 for t in range(2))) / 2,
                         (sum(C[c][t] ** 2 for t in range(2)) - sum(C[a][t] ** 2 for t in range(2))) / 2])
        try:
            u = mp.lu_solve(A, rhs)
        except ZeroDivisionError:
            continue
        if sum(u[t] ** 2 for t in range(2)) > 1:
            continue
        vals.append(min(dist(u, C[q]) for q in range(11)))
    for i2 in range(11):
        for j2 in range(i2 + 1, 11):
            dv = C[i2] - C[j2]
            dd = sum(dv[t] ** 2 for t in range(2))
            A0 = mp.matrix([(sum(C[i2][t] ** 2 for t in range(2)) - sum(C[j2][t] ** 2 for t in range(2))) / 2
                            / dd * dv[t] for t in range(2)])
            nv = mp.matrix([-dv[1] / mp.sqrt(dd), dv[0] / mp.sqrt(dd)])
            s2 = 1 - sum(A0[t] ** 2 for t in range(2))
            if s2 <= 0:
                continue
            s = mp.sqrt(s2)
            for sg in (1, -1):
                p = mp.matrix([A0[t] + sg * s * nv[t] for t in range(2)])
                ds = sorted([(dist(p, C[q]), q) for q in range(11)])
                if {ds[0][1], ds[1][1]} == {i2, j2}:
                    vals.append(ds[0][0])
    return max(vals)


def mirror_mismatch(C, a):
    ca, sa = mp.cos(2 * a), mp.sin(2 * a)
    Y = [mp.matrix([C[i][0] * ca + C[i][1] * sa, C[i][0] * sa - C[i][1] * ca]) for i in range(11)]
    w = mp.mpf(0)
    for i in range(11):
        w = max(w, min(dist(Y[i], C[j]) for j in range(11)))
    return w


def best_axis(C, lo=-math.pi, hi=math.pi, n=4000):
    step = (hi - lo) / n
    best = (mp.mpf(1e9), lo)
    for k in range(n + 1):
        a = lo + step * k
        v = mirror_mismatch(C, a)
        if v < best[0]:
            best = (v, a)
    a0 = best[1]
    for _ in range(80):
        step /= 2
        for s in (-1, 0, 1):
            v = mirror_mismatch(C, a0 + s * step)
            if v < best[0]:
                best = (v, a0 + s * step)
        a0 = best[1]
    return best


def sup_align(C, X, refl=False):
    """min over rotations of max_i min_j |C_i - (R X)_j|"""
    if refl:
        X = [mp.matrix([X[i][0], -X[i][1]]) for i in range(11)]
    def f(th):
        c, s = mp.cos(th), mp.sin(th)
        R = [mp.matrix([X[i][0] * c - X[i][1] * s, X[i][0] * s + X[i][1] * c]) for i in range(11)]
        return max(min(dist(C[i], R[j]) for j in range(11)) for i in range(11))
    best = (mp.mpf(1e9), mp.mpf(0))
    for k in range(-2000, 2001):
        th = mp.mpf(k) * mp.pi / 2000
        v = f(th)
        if v < best[0]:
            best = (v, th)
    th0 = best[1]
    step = mp.pi / 2000
    for _ in range(60):
        step /= 2
        for s in (-1, 0, 1):
            v = f(th0 + s * step)
            if v < best[0]:
                best = (v, th0 + s * step)
        th0 = best[1]
    return best


def report(name, C):
    if C is None:
        print('%s : MISSING' % name)
        return
    g = gamma20(C)
    bm = best_axis(C)
    bal = sup_align(COBJ, C, refl=False)
    balr = sup_align(COBJ, C, refl=True)
    print('%s' % name)
    print('   gamma(60dps)      = %s' % mp.nstr(g, 32))
    print('   gamma - T_cert    = %s ;  gamma - lo(saved) = %s' % (mp.nstr(g - T_CERT, 5), mp.nstr(g - LО, 5)))
    print('   mirror mismatch   = %s at axis %s deg' % (mp.nstr(bm[0], 5), mp.nstr(mp.degrees(bm[1]), 10)))
    print('   aligned sup-dist to saved candidate: %.4e (no refl) / %.4e (with refl)'
          % (float(bal[0]), float(balr[0])))


report('cert_sym60.json (C249/C830 registered)', load('research-2026/session2/n11alg/cert_sym60.json',
                                                     'centers_scaled_1e60', 60))
report('n11/kkt2/frozen.json', load('n11/kkt2/frozen.json', 'centers', 1))
report('n11/upper/certified_object.json (saved candidate)', COBJ)
