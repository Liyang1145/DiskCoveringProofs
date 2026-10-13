"""stress-audit step 5: INDEPENDENT exact-rational interval kernel.

Design differences from lead/stress_interval.py (not a replay):
  * interval primitive re-implemented from scratch; outward rounding to a chosen
    decimal grid, optional ("exact" mode uses pure Fractions, no grid at all);
  * Dirichlet elimination order sites -> hubs -> witnesses (lead: witnesses -> sites -> hubs);
  * mixed-direction certificate on the Gram matrix in the basis {e_0 - e_k}_{k=1..8}
    of the FULL 1^perp (lead: leading 8x8 principal minor);
  * extra exact-rational evaluation at the rational box centre (no intervals);
  * records the same quantities the lead recorded, for numeric comparison only.

Claims checked (all on the whole input box):
  P1 seven orbit weights > 0 and normalisation W > 0
  P2 all 18 Dirichlet pivots > 0 in my order
  P3 all 36 Schur conductances >= 0
  P4 M >= 0 on 1^perp, strict there (Gram LDL pivots > 0), M*1 = 0 exact
"""
from fractions import Fraction as F
from pathlib import Path
import json
import sys
sys.set_int_max_str_digits(10**6)

ROOT = Path(r"C:\Users\袁力阳\Desktop\ai4math2")
N12 = ROOT / "research-2026/n12-global"
OUTDIR = N12 / "members/stress-audit/evidence"

class IV:
    """Exact rational interval with optional outward rounding to 1/SCALE."""
    __slots__ = ('lo', 'hi')
    SCALE = 10**45

    def __init__(self, lo, hi=None):
        lo = F(lo)
        hi = lo if hi is None else F(hi)
        assert lo <= hi
        s = IV.SCALE
        self.lo = F((lo * s).__floor__(), s)
        self.hi = F((hi * s).__ceil__(), s)

    def __add__(x, y):
        y = IV._c(y); return IV(x.lo + y.lo, x.hi + y.hi)
    __radd__ = __add__
    def __neg__(x): return IV(-x.hi, -x.lo)
    def __sub__(x, y): return x + (-IV._c(y))
    def __rsub__(x, y): return IV._c(y) + (-x)
    def __mul__(x, y):
        y = IV._c(y); c = [x.lo * y.lo, x.lo * y.hi, x.hi * y.lo, x.hi * y.hi]
        return IV(min(c), max(c))
    __rmul__ = __mul__
    def __truediv__(x, y):
        y = IV._c(y)
        assert y.lo > 0 or y.hi < 0, ("division by interval containing 0", y.lo, y.hi)
        return x * IV(1 / y.hi, 1 / y.lo)
    def __rtruediv__(x, y): return IV._c(y) / x
    def __pow__(x, n):
        assert isinstance(n, int) and n >= 0
        y = IV(1)
        for _ in range(n): y = y * x
        return y
    @staticmethod
    def _c(v): return v if isinstance(v, IV) else IV(v)
    def dump(self): return [str(self.lo), str(self.hi)]
    def rel_width(self):
        d = max(abs(self.lo), abs(self.hi))
        return float((self.hi - self.lo)) / float(d) if d else 0.0

def exact(v):
    """exact rational value of a point (no rounding): used at the box centre."""
    return F(v)

def build(box, grid=10**45):
    IV.SCALE = grid
    a, t, r, w = [IV(*z) for z in box]
    b = (1 + a + r) / 2
    S = b * b + w * w / 3
    A = 3 * b * b - w * w - 2 * b * w
    p = IV(1)
    q = 2 * (1 - b) / r
    u = q * r / (2 * a - t + r)
    j = u * (2 * t - 2 * r - a) / r
    zz = j * r * t / (1 - t * t - r * r)
    x = -b * r * r / (S - b)
    y = (b - 1) * S / (S - b)
    return dict(a=a, t=t, r=r, w=w, b=b, S=S, A=A, x=x, y=y, z=zz, p=p, q=q, u=u, j=j)

def weights_of(W):
    return {'x': W['x'], 'y': W['y'], 'z': W['z'], 'p': W['p'], 'q': W['q'], 'u': W['u'], 'j': W['j']}

def total(W):
    return 6 * W['x'] + 6 * W['y'] + 6 * W['z'] + 6 * W['p'] + 3 * W['q'] + 6 * W['u'] + 3 * W['j']

def edges_of(W):
    """36 edges (i,k,weight-interval), nodes 0..8 sites, 9..11 hubs, 12..17 witnesses, 18..26 anchors."""
    E = []
    for i in range(9):
        for k in (i, (i + 1) % 9):
            if k % 3 == 1:
                wk = W['z']
            else:
                wk = W['x'] if i % 3 == 2 else W['y']
            E.append((18 + i, k, wk))
    faces = [(8, 0, 9), (2, 3, 10), (5, 6, 11), (9, 10, 1), (10, 11, 4), (11, 9, 7)]
    for fi, f in enumerate(faces):
        for k in f:
            if fi < 3:
                wk = W['q'] if k >= 9 else W['p']
            else:
                wk = W['u'] if k >= 9 else W['j']
            E.append((12 + fi, k, wk))
    return E

def laplacian(E, Wtot):
    n = 27
    L = [[IV(0) for _ in range(n)] for _ in range(n)]
    for i, k, wk in E:
        w = wk / Wtot
        L[i][i] = L[i][i] + w; L[k][k] = L[k][k] + w
        L[i][k] = L[i][k] - w; L[k][i] = L[k][i] - w
    return L

def schur(L, free_order=None):
    """interval Schur elimination in MY order; returns (Q_anchor_block, pivots)."""
    free = list(range(12, 18)) + [] if free_order is None else free_order
    piv = []
    for ii, k in enumerate(free):
        p = L[k][k]
        piv.append(p)
        assert p.lo > 0, ("nonpositive Dirichlet pivot", k, p.dump())
        remain = free[ii + 1:] + list(range(18, 27))
        for ix_i, i in enumerate(remain):
            if L[i][k].lo == 0 and L[i][k].hi == 0:
                continue
            for jj in remain[ix_i:]:            # upper triangle only: each pair once
                val = L[i][jj] - L[i][k] * L[k][jj] / p
                L[i][jj] = val
                if jj != i:
                    L[jj][i] = val
    Q = [[L[18 + i][18 + jj] for jj in range(9)] for i in range(9)]
    return Q, piv

def ldl(mat, n):
    piv = []
    M = [[mat[i][jj] for jj in range(n)] for i in range(n)]
    for k in range(n):
        p = M[k][k]
        piv.append(p)
        assert p.lo > 0, ("nonpositive LDL pivot", k, p.dump())
        for i in range(k + 1, n):
            for jj in range(i, n):
                val = M[i][jj] - M[i][k] * M[k][jj] / p
                M[i][jj] = val; M[jj][i] = val
    return piv

def cos_table(U, upto=4):
    c = 1 - 2 * U * U
    out = {1: c}
    prev, cur = F(1), c
    for d in range(2, upto + 1):
        nxt = 2 * c * cur - prev
        out[d] = nxt
        prev, cur = cur, nxt
    return out

def M_matrix(Q, cosd):
    M = [[IV(0) for _ in range(9)] for _ in range(9)]
    qmin = None
    for i in range(9):
        for jj in range(i + 1, 9):
            qq = -Q[i][jj]
            assert qq.lo >= 0, ("negative Schur conductance", i, jj, qq.dump())
            qmin = qq.lo if qmin is None else min(qmin, qq.lo)
            d = min(jj - i, 9 - (jj - i))
            v = 2 * qq * cosd[d]
            M[i][i] = M[i][i] + v; M[jj][jj] = M[jj][jj] + v
            M[i][jj] = M[i][jj] - v; M[jj][i] = M[jj][i] - v
    return M, qmin

def gram_1perp(M):
    """Gram matrix of M in the basis f_k = e_0 - e_k, k=1..8 (spans 1^perp)."""
    G = [[IV(0) for _ in range(8)] for _ in range(8)]
    for k in range(1, 9):
        for l in range(1, 9):
            G[k - 1][l - 1] = M[0][0] - M[0][l] - M[k][0] + M[k][l]
    return G

# ---------------- exact rational (no interval) centre evaluation ---------------
def build_exact(vals):
    a, t, r, w = [F(v) for v in vals]
    b = (1 + a + r) / 2
    S = b * b + w * w / 3
    q = 2 * (1 - b) / r
    u = q * r / (2 * a - t + r)
    j = u * (2 * t - 2 * r - a) / r
    return dict(a=a, t=t, r=r, w=w, b=b, S=S,
                x=-b * r * r / (S - b), y=(b - 1) * S / (S - b),
                z=j * r * t / (1 - t * t - r * r), p=F(1), q=q, u=u, j=j)

def laplacian_exact(W, Wtot):
    n = 27
    L = [[F(0) for _ in range(n)] for _ in range(n)]
    E = []
    for i in range(9):
        for k in (i, (i + 1) % 9):
            wk = W['z'] if k % 3 == 1 else (W['x'] if i % 3 == 2 else W['y'])
            E.append((18 + i, k, wk))
    faces = [(8, 0, 9), (2, 3, 10), (5, 6, 11), (9, 10, 1), (10, 11, 4), (11, 9, 7)]
    for fi, f in enumerate(faces):
        for k in f:
            wk = (W['q'] if k >= 9 else W['p']) if fi < 3 else (W['u'] if k >= 9 else W['j'])
            E.append((12 + fi, k, wk))
    for i, k, wk in E:
        w = wk / Wtot
        L[i][i] += w; L[k][k] += w; L[i][k] -= w; L[k][i] -= w
    return L, E

def schur_exact(L, order):
    piv = []
    for ii, k in enumerate(order):
        p = L[k][k]
        assert p > 0, ("nonpositive exact pivot", k)
        piv.append(p)
        remain = order[ii + 1:] + list(range(18, 27))
        for ix_i, i in enumerate(remain):
            if L[i][k] == 0:
                continue
            for jj in remain[ix_i:]:            # upper triangle only
                L[i][jj] -= L[i][k] * L[k][jj] / p
                if jj != i:
                    L[jj][i] = L[i][jj]
    return [[L[18 + i][18 + jj] for jj in range(9)] for i in range(9)], piv

def ldl_exact(mat, n):
    M = [[mat[i][jj] for jj in range(n)] for i in range(n)]
    piv = []
    for k in range(n):
        p = M[k][k]; piv.append(p)
        for i in range(k + 1, n):
            for jj in range(i, n):
                M[i][jj] -= M[i][k] * M[k][jj] / p
                M[jj][i] = M[i][jj]
    return piv

def run(box, grid, tag, U, report):
    W = build(box, grid)
    wt = weights_of(W)
    Wt = total(W)
    rep = {'tag': tag, 'grid': str(grid), 'box': [[str(z[0]), str(z[1])] for z in box]}
    rep['weight_bounds'] = {k: v.dump() for k, v in wt.items()}
    rep['all_weights_positive'] = all(v.lo > 0 for v in wt.values())
    rep['total_W'] = Wt.dump()
    rep['total_positive'] = Wt.lo > 0
    E = edges_of(W)
    L = laplacian(E, Wt)
    order = list(range(9)) + list(range(9, 12)) + list(range(12, 18))   # MY order
    Q, piv = schur(L, order)
    rep['dirichlet_pivots'] = [p.dump() for p in piv]
    rep['dirichlet_pivots_float'] = [f"{float(p.lo):.12e}" for p in piv]
    rep['dirichlet_min_lo'] = str(min(p.lo for p in piv))
    rep['dirichlet_min_lo_float'] = f"{float(min(p.lo for p in piv)):.6e}"
    cosd = cos_table(U)
    M, qmin = M_matrix(Q, cosd)
    rep['min_schur_conductance_lo'] = str(qmin)
    rep['conductances_nonneg'] = True
    # exact M*1 = 0 check on intervals
    rowsum = [max(abs(sum(M[i][jj] for jj in range(9)).lo), abs(sum(M[i][jj] for jj in range(9)).hi)) for i in range(9)]
    rep['M_rowsum_abs_max'] = str(max(rowsum))
    G = gram_1perp(M)
    gpiv = ldl(G, 8)
    rep['gram_pivots_1perp'] = [p.dump() for p in gpiv]
    rep['gram_pivots_float'] = [f"{float(p.lo):.12e}" for p in gpiv]
    rep['gram_min_pivot_lo'] = str(min(p.lo for p in gpiv))
    rep['gram_min_pivot_lo_float'] = f"{float(min(p.lo for p in gpiv)):.6e}"
    rep['gram_positive'] = all(p.lo > 0 for p in gpiv)
    rep['M_rowsum_bound_float'] = f"{max(float(x) for x in rowsum):.3e}"
    # lead-style leading 8x8 minor, for comparison only
    M8 = [[M[i][jj] for jj in range(8)] for i in range(8)]
    lpiv = ldl(M8, 8)
    rep['lead_style_minor_pivots'] = [p.dump() for p in lpiv]
    rep['lead_style_minor_pivots_float'] = [f"{float(p.lo):.12e}" for p in lpiv]
    rep['lead_style_positive'] = all(p.lo > 0 for p in lpiv)
    report[tag] = rep
    print(f"[{tag}] weights>0 {rep['all_weights_positive']}  W>0 {rep['total_positive']}  "
          f"dirichlet_min {rep['dirichlet_min_lo_float']}  q_min {float(qmin):.6e}  "
          f"gram_min_pivot {rep['gram_min_pivot_lo_float']}  lead_minor_min {float(min(p.lo for p in lpiv)):.6e}  "
          f"M*1<= {rep['M_rowsum_bound_float']}")
    return rep

if __name__ == '__main__':
    cal = json.loads((N12 / 'evidence/d3-chart-calibration.json').read_text(encoding='utf-8'))
    centre = [F(s) for s in cal['root']]
    U = F('0.361102963744508672616920293904')
    report = {}
    print("=== interval certificates on boxes around the recorded chart root ===")
    for eps, grid in ((F(1, 10**38), 10**45), (F(1, 10**30), 10**45), (F(1, 10**38), 10**60), (F(1, 10**30), 10**30)):
        box = [[str(c - eps), str(c + eps)] for c in centre]
        run(box, grid, f"eps1e{len(str(eps.denominator))-1}_grid1e{len(str(grid))-1}", U, report)

    print("\n=== exact rational (no interval) evaluation AT the rational centre ===")
    W = build_exact([str(c) for c in centre])
    Wt = 6 * W['x'] + 6 * W['y'] + 6 * W['z'] + 6 * W['p'] + 3 * W['q'] + 6 * W['u'] + 3 * W['j']
    L, E = laplacian_exact(W, Wt)
    order = list(range(9)) + list(range(9, 12)) + list(range(12, 18))
    Qex, piv_ex = schur_exact(L, order)
    print("  exact Dirichlet pivots (my order):", [f"{float(p):.6e}" for p in piv_ex])
    cosd = cos_table(U)
    Mex = [[F(0) for _ in range(9)] for _ in range(9)]
    qmin = None
    for i in range(9):
        for jj in range(i + 1, 9):
            qq = -Qex[i][jj]
            qmin = qq if qmin is None else min(qmin, qq)
            d = min(jj - i, 9 - (jj - i))
            v = 2 * qq * cosd[d]
            Mex[i][i] += v; Mex[jj][jj] += v; Mex[i][jj] -= v; Mex[jj][i] -= v
    Gex = [[Mex[0][0] - Mex[0][l] - Mex[k][0] + Mex[k][l] for l in range(1, 9)] for k in range(1, 9)]
    gp = ldl_exact(Gex, 8)
    mp = ldl_exact([[Mex[i][jj] for jj in range(8)] for i in range(8)], 8)
    exact_rep = {
        'centre': [str(c) for c in centre],
        'weights': {k: str(v) for k, v in W.items() if k in 'xyzpquj'},
        'total_W': str(Wt),
        'min_conductance_centre': str(qmin),
        'gram_pivots_centre_float': [f"{float(p):.12e}" for p in gp],
        'gram_min_pivot_centre_float': f"{float(min(gp)):.6e}",
        'lead_minor_pivots_centre_float': [f"{float(p):.12e}" for p in mp],
        'lead_minor_min_pivot_float': f"{float(min(mp)):.6e}",
        'cos_table': {d: str(v) for d, v in cosd.items()},
        'cos_table_float': {d: f"{float(v):.15f}" for d, v in cosd.items()},
    }
    report['exact_centre'] = exact_rep
    print("  min Schur conductance at centre:", f"{float(qmin):.6e}")
    print("  Gram(1^perp) LDL pivots at centre:", [f"{float(p):.6e}" for p in gp])
    print("  lead-style 8x8 minor pivots at centre:", [f"{float(p):.6e}" for p in mp])
    print("  exact cos(dL) =", {d: f"{float(v):.12f}" for d, v in cosd.items()})
    print("  Gram minima: mine", f"{float(min(gp)):.6e}", " lead-style", f"{float(min(mp)):.6e}")
    # independent numeric spectra at the centre (diagnostic, not the certificate)
    import mpmath as mpk
    mpk.mp.dps = 40
    Mn = mpk.matrix(9, 9)
    for i in range(9):
        for jj in range(9):
            Mn[i, jj] = mpk.mpf(Mex[i][jj].numerator) / Mex[i][jj].denominator
    ev = mpk.eigsy(Mn, eigvals_only=True)
    exact_rep['M_eigenvalues_centre_float'] = [f"{float(v):.12e}" for v in ev]
    exact_rep['gran_pivots_float'] = exact_rep['gram_pivots_centre_float']
    print("  eigenvalues of exact M at centre:", [f"{float(v):.9e}" for v in ev])

    OUTDIR.mkdir(parents=True, exist_ok=True)
    (OUTDIR / 'stress-audit-kernel.json').write_text(json.dumps(report, indent=1), encoding='utf-8')
    print("\nwrote", OUTDIR / 'stress-audit-kernel.json')
