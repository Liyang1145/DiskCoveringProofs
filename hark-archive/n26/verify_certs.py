"""Independent re-check of certs/<index>.json (does NOT import certify_box/bnb).

For each certificate file:
 1. the root box equals the root25 OPEN box in pending.json (verbatim rationals
    extracted from the committed composition, SHA256 c1675552...);
 2. the split tree is a genuine closed partition: every split point lies strictly
    inside its box, children are the two closed halves;
 3. every LEAF: weights positive rationals; exact Schur complement by sequential
    Kron reduction in pure Fractions (witnesses by star-mesh, then centers by
    Gauss), all pivots > 0 (G positive definite), zero row sums, nonpositive
    off-diagonals;  then a rigorous mpmath-interval lower bound of
    Phi_w - W*RSTAR_UP^2 on the closed leaf (2nd-order Taylor at the centre,
    interval cubic remainder, exact-LDL PSD split, convex-QP supporting plane).
Verdict per file: CLOSED only if every leaf passes and there is no OPEN leaf.
"""
import os as _os, sys as _sys  # hark-archive portable paths (see hark-archive/_paths.py)
_hd = _os.path.dirname(_os.path.abspath(__file__))
while _os.path.basename(_hd) != 'hark-archive' and _os.path.dirname(_hd) != _hd: _hd = _os.path.dirname(_hd)
_sys.path.append(_hd); from _paths import DCP_N26
import json, os, sys
from fractions import Fraction as F
import numpy as np
from mpmath import iv, mp
iv.prec = 160

ROOT = DCP_N26
M = json.load(open(ROOT + '/model134.json')); E = [tuple(e) for e in M['edges']]
PEND = {b['index']: b for b in json.load(open(ROOT + '/pending.json'))['pending_closed_leaf_boxes']}
RUP = F("0.234700090400448239616790133776692127560495963654971391785925")
PI = iv.pi


def schur_kron(w):
    # adjacency dict of weights
    adj = {}
    def add(u, v, x):
        if u == v: return
        adj.setdefault(u, {}); adj.setdefault(v, {})
        adj[u][v] = adj[u].get(v, F(0)) + x; adj[v][u] = adj[v].get(u, F(0)) + x
    for (u, v), x in zip(E, w): add(u, v, x)
    # eliminate free vertices 75..16 (witnesses first, then centers)
    for k in range(75, 15, -1):
        nb = adj.pop(k)
        deg = sum(nb.values())
        if deg <= 0: raise AssertionError('nonpositive pivot')
        for u in nb: adj[u].pop(k)
        items = list(nb.items())
        for a in range(len(items)):
            for b in range(a + 1, len(items)):
                (u, x), (v, y) = items[a], items[b]
                add(u, v, x * y / deg)
    # pivots of Kron reduction = Schur pivots of G in this elimination order; all were >0
    pairs = {}
    for u in range(16):
        for v, x in adj.get(u, {}).items():
            if u < v and x != 0:
                if x < 0: raise AssertionError('negative pair')
                pairs[(u, v)] = x
    return pairs


def ivq(x):
    return iv.mpf(x.numerator) / iv.mpf(x.denominator)


def _tupF(t):
    sign, man, exp, bc = t
    if man == 0: return F(0)
    v = F(int(man)) * (F(2) ** int(exp)) if exp >= 0 else F(int(man), 2 ** (-int(exp)))
    return -v if sign else v


def lowF(x):  # exact rational lower endpoint of an iv.mpf (outward rounded by mpmath)
    return _tupF(x._mpi_[0])


def upF(x):
    return _tupF(x._mpi_[1])


def midF(x):
    return (lowF(x) + upF(x)) / 2


def ldl_psd(A):
    n = len(A); A = [row[:] for row in A]
    for k in range(n):
        p = A[k][k]
        if p < 0: return False
        if p == 0:
            if any(A[i][k] for i in range(k + 1, n)): return False
            continue
        for i in range(k + 1, n):
            if A[i][k]:
                f = A[i][k] / p
                for j in range(k + 1, n): A[i][j] -= f * A[k][j]
    return True


def leaf_bound(pairs, W, lo, hi):
    m = [F(0)] + [(a + b) / 2 for a, b in zip(lo, hi)]
    r = [F(0)] + [(b - a) / 2 for a, b in zip(lo, hi)]
    phi = iv.mpf(0); g = [iv.mpf(0) for _ in range(16)]
    H = [[iv.mpf(0) for _ in range(16)] for _ in range(16)]
    cub = F(0)
    for (i, j), c in pairs.items():
        ci = ivq(c); dd = 2 * PI * ivq(m[j] - m[i])
        co = iv.cos(dd); si = iv.sin(dd)
        phi += 2 * ci * (1 - co)
        gp = 4 * PI * ci * si; g[j] += gp; g[i] -= gp
        h = 8 * PI * PI * ci * co
        H[i][i] += h; H[j][j] += h; H[i][j] -= h; H[j][i] -= h
        cub += c * (r[i] + r[j]) ** 3
    n = 15; g = g[1:]; H = [row[1:] for row in H[1:]]; r = r[1:]
    Hq = [[midF(H[a][b]).limit_denominator(10 ** 30) for b in range(n)] for a in range(n)]
    for a in range(n):
        for b in range(a): Hq[a][b] = Hq[b][a]
    eps = max(max(upF(H[a][b] - ivq(Hq[a][b])), -lowF(H[a][b] - ivq(Hq[a][b]))) for a in range(n) for b in range(n))
    Hf = np.array([[float(x) for x in row] for row in Hq])
    lmin = float(np.linalg.eigvalsh(Hf).min()); sc = max(1.0, float(abs(Hf).max()))
    shift = F(min(0.0, lmin - 1e-8 * sc)).limit_denominator(10 ** 12)
    k = 0
    while not ldl_psd([[Hq[a][b] - (shift if a == b else 0) for b in range(n)] for a in range(n)]):
        shift -= F(1, 10 ** 6) * (2 ** k); k += 1
        if k > 60: return None
    Hs = [[Hq[a][b] - (shift if a == b else 0) for b in range(n)] for a in range(n)]
    gq = [midF(x).limit_denominator(10 ** 30) for x in g]
    gerr = [max(upF(x - ivq(q)), -lowF(x - ivq(q))) for x, q in zip(g, gq)]
    # proposal for QP minimiser: projected gradient iterations (floats only propose)
    gf = np.array([float(x) for x in gq]); Hsf = np.array([[float(x) for x in row] for row in Hs]); rf = np.array([float(x) for x in r])
    d = np.zeros(n); L = max(1e-12, float(np.linalg.eigvalsh((Hsf + Hsf.T) / 2).max()))
    for _ in range(3000):
        d = np.clip(d - (gf + Hsf @ d) / L, -rf, rf)
    # refinement in box-scaled variables u = d/r (better conditioned); still only a proposal
    from scipy.optimize import minimize as _min
    rs = np.where(rf > 0, rf, 1.0); Gs = gf * rs; Hu = (Hsf + Hsf.T) / 2 * np.outer(rs, rs)
    sc_ = max(1e-300, float(np.abs(Gs).max() + np.abs(Hu).max()))
    fq = lambda u: ((Gs @ u + 0.5 * u @ Hu @ u) / sc_, (Gs + Hu @ u) / sc_)
    u0 = np.clip(d / rs, -1, 1)
    ru = _min(fq, u0, jac=True, method='L-BFGS-B', bounds=[(-1, 1)] * n, options={'maxiter': 5000, 'ftol': 1e-30, 'gtol': 1e-30})
    if ru.fun * sc_ <= (Gs @ u0 + 0.5 * u0 @ Hu @ u0):
        d = np.clip(ru.x, -1, 1) * rs
    ds = [max(-ri, min(ri, F(float(x)).limit_denominator(10 ** 15))) for x, ri in zip(d, r)]
    Hd = [sum(Hs[a][b] * ds[b] for b in range(n)) for a in range(n)]
    q = sum(gq[a] * ds[a] for a in range(n)) + sum(ds[a] * Hd[a] for a in range(n)) / 2
    for a in range(n):
        gr = gq[a] + Hd[a]
        q += min(gr * (-r[a] - ds[a]), gr * (r[a] - ds[a]))
    q -= sum(e * ri for e, ri in zip(gerr, r))
    q += (shift / 2) * sum(x * x for x in r)          # shift <= 0
    l1 = sum(r)
    tot = phi + ivq(q - eps * l1 * l1 / 2 - W * RUP * RUP) - ivq(cub) * 8 * PI ** 3 / 3
    return lowF(tot)


def check_file(path):
    C = json.load(open(path)); idx = C['index']; B = PEND[idx]
    assert C['lower'] == B['lower'] and C['upper'] == B['upper'], 'root box mismatch'
    den = C['weight_den']; cache = {}; stats = {'leaves': 0, 'pass': 0, 'open': 0, 'fail': 0, 'min_margin_over_W': None}
    import time as _t, hashlib as _h
    _T0 = _t.time(); _BUD = float(os.environ.get('VC_BUDGET', '1e9'))
    _ck = ROOT + '/certs/%s.ckpt.json' % idx if os.environ.get('VC_BUDGET') else None
    _done = json.load(open(_ck)) if _ck and os.path.exists(_ck) else {}
    _cnt = [0]
    def rec(t, lo, hi, path=''):
        if t['kind'] == 'SPLIT':
            ax = t['axis']; mid = F(t['mid'])
            assert lo[ax] < mid < hi[ax], 'split not interior'
            h1 = list(hi); h1[ax] = mid; l2 = list(lo); l2[ax] = mid
            rec(t['children'][0], lo, h1, path + '0'); rec(t['children'][1], l2, hi, path + '1'); return
        if t['kind'] == 'OPEN':
            stats['open'] += 1; return
        if t['kind'] == 'LOCAL-PINNING-CELL':
            # leaf box must lie inside the archive's refined-pinning closed anchor-angle cell
            import hashlib
            src = C['local_cell_source']; pth = ROOT + '/repo/' + src['file']
            assert hashlib.sha256(open(pth, 'rb').read()).hexdigest() == src['sha256'], 'cell source hash'
            cells = json.load(open(pth))['closed_anchor_angle_cells']
            assert len(cells) == 15
            for k in range(15):
                assert F(cells[k][0]) <= lo[k] and hi[k] <= F(cells[k][1]), 'LOCAL leaf not inside pinning cell'
            stats['local'] = stats.get('local', 0) + 1; return
        if t['kind'] == 'LOCAL-SLAB-FOREST':
            # non-negative-weight local slab forest (local/FOREST-Q6.json): structural checks here;
            # per-slab arithmetic is certA+certB (local/verB.json state, rerun with local/certB.py).
            import hashlib
            pth = ROOT + '/' + t['file']
            assert hashlib.sha256(open(pth, 'rb').read()).hexdigest() == t['sha256'], 'forest file hash'
            FO = json.load(open(pth)); R = FO['region']
            assert [F(x) for x in R['lower']] == lo and [F(x) for x in R['upper']] == hi, 'forest region != leaf box'
            for nm, hx in FO['inputs_sha256'].items():
                rel = 'certs_old/1669.pre-local.json' if nm == 'certs/1669.json' else nm
                assert hashlib.sha256(open(ROOT + '/' + rel, 'rb').read()).hexdigest() == hx, 'input hash ' + nm
            sl = FO['slabs']; assert len(sl) == FO['counts']['slabs']
            boxes = [([F(x) for x in s_['lower']], [F(x) for x in s_['upper']]) for s_ in sl]
            def vol(b): 
                v = F(1)
                for a_, c_ in zip(*b): v *= (c_ - a_)
                return v
            for b_ in boxes:
                assert all(l_ <= a_ and c_ <= h_ and a_ <= c_ for a_, c_, l_, h_ in zip(b_[0], b_[1], lo, hi)), 'slab outside region'
            assert sum(vol(b_) for b_ in boxes) == vol((lo, hi)), 'slab volumes != region volume'
            for i_ in range(len(boxes)):
                for j_ in range(i_ + 1, len(boxes)):
                    A_, B_ = boxes[i_], boxes[j_]
                    assert any(min(A_[1][k], B_[1][k]) <= max(A_[0][k], B_[0][k]) for k in range(15)), 'slab interiors overlap'
            vb = json.load(open(ROOT + '/local/verB.json'))['done']
            cnt = {}; pcs = 0
            for s_ in sl:
                assert all('OPEN' not in p_ for p_ in s_['pieces']) and s_['closed']
                pcs += len(s_['pieces'])
                k_ = '%d_%d' % (s_['m'], cnt.setdefault(s_['m'], 0)); cnt[s_['m']] += 1
                assert k_ in vb and vb[k_]['pieces'] == len(s_['pieces']) and F(vb[k_]['min']) > 0, 'certB slab ' + k_
            assert pcs == FO['counts']['leaves']
            stats['slab_forest'] = stats.get('slab_forest', 0) + 1; stats['slab_forest_slabs'] = len(sl); return
        stats['leaves'] += 1
        if path in _done:
            stats['pass'] += 1; mm = F(_done[path]); stats['min_margin_over_W'] = mm if stats['min_margin_over_W'] is None else min(mm, stats['min_margin_over_W']); return
        if _t.time() - _T0 > _BUD:
            stats['deferred'] = stats.get('deferred', 0) + 1; return
        wn = t['w']; assert len(wn) == 134 and all(type(x) is int and x > 0 for x in wn)
        key = tuple(wn)
        if key not in cache:
            w = [F(x, den) for x in wn]; cache[key] = (schur_kron(w), sum(w, F(0)))
        pairs, W = cache[key]
        b = leaf_bound(pairs, W, lo, hi)
        if b is not None and b > 0:
            stats['pass'] += 1
            mm = b / W
            if _ck: _done[path] = str(mm)
            stats['min_margin_over_W'] = mm if stats['min_margin_over_W'] is None else min(mm, stats['min_margin_over_W'])
        else:
            stats['fail'] += 1
    rec(C['tree'], [F(x) for x in B['lower']], [F(x) for x in B['upper']])
    if _ck:
        json.dump(_done, open(_ck + '.tmp', 'w')); os.replace(_ck + '.tmp', _ck)
    stats['CLOSED'] = not stats.get('deferred') and stats['open'] == 0 and stats['fail'] == 0 and stats['pass'] == stats['leaves'] > 0
    if stats.get('slab_forest'):
        stats['CLOSED_WITH_LOCAL_SLAB_FOREST'] = stats['CLOSED']; stats['CLOSED'] = False
    if stats.get('local'):
        stats['CLOSED_WITH_LOCAL_CARVEOUT'] = stats['CLOSED']; stats['CLOSED'] = False
    stats['index'] = idx
    if stats['min_margin_over_W'] is not None: stats['min_margin_over_W'] = float(stats['min_margin_over_W'])
    return stats


if __name__ == '__main__':
    files = sys.argv[1:]
    for f in files:
        try:
            s = check_file(f)
        except Exception as e:
            import traceback; traceback.print_exc(); s = {"file": f, "error": repr(e)[:200]}
        print(json.dumps(s), flush=True)
