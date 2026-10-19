"""Exact (Fraction) instantiation of the two q1-balanced representative CanonicalCoeffQ tables.

Source data: historical balanced-q1 dense proposal (repo Liyang1145/DiskCoveringProofs,
cover11/proof_bundle/research-2026/team-current/lead/shared_moment_dense_certificate_{0,2}_4.json,
field 'coefficients' = the 9-place rationals actually certified by certify_shared_moments_dense.py).

Historical labels: ring 0..8, hubs 9,10, ear (0,1,2), core [0,2,3,...,8]; start s = hub-9 run start.
Lean labels (ActualOrderedMetricGraphs): q1Ear={8,0,1}, coreSite 0 i = i+1, q1Faces k m.
Relabeling sigma: ring h -> (h-1) mod 9, hubs fixed.  hist start0 -> Lean k=7, hist start2 -> Lean k=1
(checked below by recomputing q1Faces from the Lean definitions).

Everything below transcribes the Lean definitions of
ActualCanonicalMomentTransport / ActualCanonicalSharedMomentConsumer / CanonicalSharedMomentFiniteCertificate
verbatim over Fractions. Output: class33/data/rep_k{7,1}.json.
"""
from fractions import Fraction as F
import json, sys, os
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
SUPP = ROOT / 'supp' / 'lead'

PI_LO = F(314159265358979323846, 10**20)
PI_HI = F(314159265358979323847, 10**20)
SHARP_ALPHA = F(863314, 1000000)

def sigma(h):
    return (h - 1) % 9 if h < 9 else h

# ---------------- Lean definitions -----------------
def nextSite(i): return (i + 1) % 9
def coreSite0(i): return (0 + i + 1) % 9          # coreSite 0 i = 0 + (i+1) in Fin 9
def q1Fan(k, m, i):
    return frozenset({coreSite0((i + k) % 8), coreSite0(((i + k) % 8 + 1) % 8), 9 if i < m else 10})
def centralFace(i): return frozenset({9, 10, i})
Q1EAR = frozenset({8, 0, 1})
def q1Faces(k, m):
    s = {q1Fan(k, m, i) for i in range(8)}
    s |= {centralFace(coreSite0(k)), centralFace(coreSite0((m + k) % 8))}
    s |= {Q1EAR}
    return s
def faceEdges(Fs):
    out = set()
    for f in Fs:
        l = sorted(f)
        for a in range(3):
            for b in range(a + 1, 3):
                out.add(frozenset({l[a], l[b]}))
    return out
def cycleEdge(k): return frozenset({k, nextSite(k)})
def label(f, s): return sorted(f)[s]
def flagEdge(f, s): return frozenset(f - {label(f, s)})
def earGaps(e): return {(e - 2) % 9, (e - 1) % 9, e}
def outsideGaps(e): return set(range(9)) - earGaps(e)
def stationWeight(i): return 1 if i < 9 else 2
def piProductUpper(b): return b * (PI_LO if b < 0 else PI_HI)

def q0Fan(m, i): return frozenset({i, nextSite(i), 9 if i < m else 10})
def q0Faces(m): return {q0Fan(m, i) for i in range(9)} | {centralFace(0), centralFace(m)}

def build(start, k, cls='q1bal'):
    if cls == 'q1bal':
        cert = json.loads((SUPP / f'shared_moment_dense_certificate_{start}_4.json').read_text())
        row = json.loads((SUPP / f'shared_moment_dense_{start}_4.json').read_text())
        sig = sigma; Fs = q1Faces(k, 4); off = 2; earC = 0
    else:  # q0: historical start0 span k  <->  Lean q0Faces k, identity labels
        cert = json.loads((SUPP / f'q0_moment_dual_certificate_{start}_{k}.json').read_text())
        row = json.loads((SUPP / f'q0_moment_dual_{start}_{k}.json').read_text())
        sig = lambda h: h; Fs = q0Faces(k); off = 1; earC = 0
    z = [F(c) for c in cert['coefficients']]
    assert len(z) == 112
    faces_h = [tuple(f) for f in row['faces']]
    edges_h = [tuple(e) for e in row['edges']]
    side, rr, kap, lam, eta, lin = 11, 32, 50, 71, 72, 73
    # --- graph check: sigma(hist faces) == Lean q1Faces k 4
    sigma_ = sig
    img = {frozenset(sigma_(v) for v in f) for f in faces_h}
    assert img == Fs, (start, k, sorted(map(sorted, img)), sorted(map(sorted, Fs)))
    assert len(Fs) == 11
    E = faceEdges(Fs)
    assert len(E) == 21
    eidx = {frozenset(sigma_(v) for v in e): n for n, e in enumerate(edges_h)}
    assert set(eidx) == E
    adj = {e: [t for t, f in enumerate(faces_h) if e[0] in f and e[1] in f] for e in edges_h}
    # --- D fields (Lean labels)
    mu = {sigma_(h): z[h] for h in range(11)}
    sideSecond = {e: z[side + n] for e, n in eidx.items()}
    sideFirst = {e: z[lin + n] for e, n in eidx.items()}
    kapL = {e: z[kap + n] for e, n in eidx.items()}
    def sgn_of(fL, eL):
        n = eidx[eL]; eh = edges_h[n]
        t = [t for t, f in enumerate(faces_h) if frozenset(sigma_(v) for v in f) == fL][0]
        return 1 if adj[eh][0] == t else -1
    faceMask = {(f, s): F(sgn_of(f, flagEdge(f, s))) for f in Fs for s in range(3)}
    switchMask = {i: F(-1) for i in range(9)}
    def hs(j): return (j + off) % 9   # Lean sector j <-> hist sector j+off
    leftSecond = {j: z[rr + 2 * hs(j)] for j in range(9)}
    rightSecond = {j: z[rr + 2 * hs(j) + 1] for j in range(9)}
    leftFirst = {j: z[lin + 21 + 2 * hs(j)] for j in range(9)}
    rightFirst = {j: z[lin + 21 + 2 * hs(j) + 1] for j in range(9)}
    width = z[lam]; etaV = z[eta]
    # --- structural fields
    balance = {}
    for e in E:
        s1 = sum((faceMask[(f, s)] for f in Fs for s in range(3) if flagEdge(f, s) == e), F(0))
        s2 = sum((switchMask[i] for i in range(9) if cycleEdge(i) == e), F(0))
        balance[e] = s1 + s2
    assert all(v == 0 for v in balance.values()), balance
    assert all(kapL[e] >= 0 for e in E) and etaV >= 0
    # --- canonical factor coefficients
    faces = {}
    for f in sorted(Fs, key=lambda f: sorted(f)):
        p = [-mu[label(f, s)] - kapL[flagEdge(f, s)] for s in range(3)]
        q = [faceMask[(f, s)] * sideSecond[flagEdge(f, s)] for s in range(3)]
        b = [faceMask[(f, s)] * sideFirst[flagEdge(f, s)] for s in range(3)]
        faces[tuple(sorted(f))] = dict(p=p, q=q, b=b)
    switches = {}
    for i in range(9):
        e = cycleEdge(i)
        switches[i] = dict(p=sum((mu[j] for j in e), F(0)) - kapL[e], q=switchMask[i] * sideSecond[e],
                           b=switchMask[i] * sideFirst[e], d2=leftSecond[i] + rightSecond[(i - 1) % 9],
                           d1=leftFirst[i] + rightFirst[(i - 1) % 9])
    sectors = {}
    for i in range(9):
        sectors[i] = dict(C=width + (etaV if i in outsideGaps(0) else 0), mu=mu[nextSite(i)],
                          dL=leftSecond[i], dR=rightSecond[i], bL=leftFirst[i], bR=rightFirst[i])
    const = sum((stationWeight(i) * mu[i] for i in range(11)), F(0)) + sum((kapL[e] for e in E), F(0)) - 2 * width - 2 * etaV
    sharp = piProductUpper(const) + 2 * SHARP_ALPHA * etaV
    # --- cross-check against the historical factor formulas (independent reading of the generator)
    for t, f in enumerate(faces_h):
        fL = tuple(sorted(sigma_(v) for v in f)); co = []
        for kk, i in enumerate(f):
            e = tuple(sorted(j for j in f if j != i)); ee = edges_h.index(e); sg = 1 if adj[e][0] == t else -1
            co.append((sigma_(i), -z[i] - z[kap + ee], z[side + ee] * sg, z[lin + ee] * sg))
        co.sort()
        assert [c[1] for c in co] == faces[fL]['p'] and [c[2] for c in co] == faces[fL]['q'] and [c[3] for c in co] == faces[fL]['b']
    for bi in range(9):
        i, j = bi, (bi + 1) % 9; ee = edges_h.index(tuple(sorted((i, j))))
        hist = dict(p=z[i] + z[j] - z[kap + ee], q=-z[side + ee], b=-z[lin + ee],
                    d2=z[rr + 2 * i + 1] + z[rr + 2 * j], d1=z[lin + 21 + 2 * i + 1] + z[lin + 21 + 2 * j])
        assert hist == switches[(bi - (off - 1)) % 9], bi
    for i in range(9):
        hist = dict(C=z[lam] + (z[eta] if (i - off) % 9 in outsideGaps(earC) else 0), mu=z[i], dL=z[rr + 2 * i], dR=z[rr + 2 * i + 1],
                    bL=z[lin + 21 + 2 * i], bR=z[lin + 21 + 2 * i + 1])
        assert hist == sectors[(i - off) % 9], i
    hist_upper = {fa['factor']: fa['upper'] for fa in cert['factors']}
    return dict(start=start, k=k, z=z, Fs=Fs, E=E, mu=mu, kap=kapL, sideFirst=sideFirst, sideSecond=sideSecond,
                faceMask=faceMask, leftSecond=leftSecond, rightSecond=rightSecond, leftFirst=leftFirst,
                rightFirst=rightFirst, width=width, eta=etaV, faces=faces, switches=switches, sectors=sectors,
                const=const, sharp=sharp, hist_upper=hist_upper, faces_h=faces_h, cls=cls)

def fstr(x): return f'{x.numerator}/{x.denominator}' if x.denominator != 1 else str(x.numerator)

def dump(T, path):
    out = dict(start_hist=T['start'], lean_k=T['k'], lean_m=4,
               mu={str(i): fstr(T['mu'][i]) for i in range(11)},
               kap={','.join(map(str, sorted(e))): fstr(T['kap'][e]) for e in sorted(T['E'], key=sorted)},
               sideFirst={','.join(map(str, sorted(e))): fstr(T['sideFirst'][e]) for e in sorted(T['E'], key=sorted)},
               sideSecond={','.join(map(str, sorted(e))): fstr(T['sideSecond'][e]) for e in sorted(T['E'], key=sorted)},
               faceMask={','.join(map(str, sorted(f))) + f'#{s}': fstr(T['faceMask'][(f, s)]) for (f, s) in sorted(T['faceMask'], key=lambda x: (sorted(x[0]), x[1]))},
               switchMask={str(i): '-1' for i in range(9)},
               leftSecond={str(j): fstr(T['leftSecond'][j]) for j in range(9)},
               rightSecond={str(j): fstr(T['rightSecond'][j]) for j in range(9)},
               leftFirst={str(j): fstr(T['leftFirst'][j]) for j in range(9)},
               rightFirst={str(j): fstr(T['rightFirst'][j]) for j in range(9)},
               width=fstr(T['width']), eta=fstr(T['eta']),
               faces={','.join(map(str, f)): {k2: [fstr(x) for x in v] for k2, v in d.items()} for f, d in T['faces'].items()},
               switches={str(i): {k2: fstr(v) for k2, v in d.items()} for i, d in T['switches'].items()},
               sectors={str(i): {k2: fstr(v) for k2, v in d.items()} for i, d in T['sectors'].items()},
               constantCoeff=fstr(T['const']), sharpConstantUpper=fstr(T['sharp']), sharpConstantUpper_float=float(T['sharp']))
    tmp = str(path) + '.tmp'; Path(tmp).write_text(json.dumps(out, indent=1)); os.replace(tmp, path)

if __name__ == '__main__':
    (ROOT / 'data').mkdir(exist_ok=True)
    for start, k, cls, name in [(0, 7, 'q1bal', 'rep_k7'), (2, 1, 'q1bal', 'rep_k1'), (0, 2, 'q0', 'q0_m2')]:
        T = build(start, k, cls)
        dump(T, ROOT / 'data' / f'{name}.json')
        print('rep k', k, 'hist start', start, 'balance OK, graph OK, hist-formula cross-check OK; const', float(T['const']), 'sharp', float(T['sharp']))
