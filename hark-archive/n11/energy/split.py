#!/usr/bin/env python3
"""Refinement certificates for nodes with no single-cell Paid16 certificate.
A node's cell (integer DBM matrix, scale 4096) is recursively split with the
DBMTreeKernel rule (i,j,m):  left[a][b]  = min(D[a][b], D[a][i]+m+D[j][b])
                             right[a][b] = min(D[a][b], D[a][j]-m+D[i][b])
(exactly the Valid inequalities of DBMTreeKernel, with equality), at scale
S = 4096*2^SH (parent entries multiplied by 2^SH). Each leaf gets a Paid16-format
packet whose endpoint/lamB data refer to the LEAF matrix; checked exactly by
check_matrix() (same fields as checker.check, matrix instead of tree node).
Output split/<node>.json (tree of splits + leaf packets), ledger.jsonl."""
import sys, os, json, time, math
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
import gen
from gen import *
from checker import line_margin, endpointLo, rowA, PAIRS, Lq, LQ, Dq, DQ, T2

SD = os.path.join(HERE, 'split'); os.makedirs(SD, exist_ok=True)
SH = 8; S = 4096 * 2 ** SH
MAXDEPTH = int(os.environ.get('MAXDEPTH', '5')); MAXLEAVES = 64

class MCtx:
    """ctx look-alike over an explicit integer matrix at scale S"""
    def __init__(self, D): self.D = D
    def db(self, i, j): return F(self.D[i][j], S)
    def slo(self, k):
        i, j = PAIRS[k]; return max(-self.db(j, i), F(0))
    def shi(self, k):
        i, j = PAIRS[k]; return self.db(i, j)

def mint(D):  # tighten by shortest paths (Floyd); any tighter matrix is still a valid child bound? NO:
    return D  # we do NOT tighten: child entries are exactly the kernel min rule (sound by step_cover)

def check_matrix(D, p):
    mc = MCtx(D); beta = p['beta']; L = p['line']; lam = p['lam']; rf = p['rowFrom']; rt = p['rowTo']
    res = {}
    res['beta_nonneg'] = min(beta); res['beta_sum'] = 0 if sum(beta, F(0)) == 1 else -1
    res['lines'] = min(line_margin(l) for l in L)
    ep = []
    for k in range(36):
        i, j = PAIRS[k]
        ep.append((F(i - j) * LQ + Dq * mc.slo(k)) - L[k]['a'])
        ep.append(L[k]['b'] - (F(i - j) * Lq + DQ * mc.shi(k)))
    res['endpoints'] = min(ep)
    res['lam_nonneg'] = min(lam)
    w = [ctx.mix(beta, k) for k in range(36)]
    s = [l['s'] for l in L]; c = [l['c'] for l in L]
    g = [sum((w[k] * s[k] for k in range(36) if PAIRS[k][0] <= q < PAIRS[k][1]), F(0)) for q in range(9)]
    rho = [sum((lam[a] * rowA(rf[a], rt[a], q) for a in range(len(lam))), F(0)) for q in range(9)]
    res['reduced'] = min(endpointLo(Dq, DQ, g[q]) + rho[q] - p['rmin'] for q in range(9))
    cl = sum((w[k] * s[k] * (PAIRS[k][0] - PAIRS[k][1]) for k in range(36)), F(0))
    cv = sum((w[k] * c[k] for k in range(36)), F(0))
    lamB = sum((lam[a] * mc.db(rf[a], rt[a]) for a in range(len(lam))), F(0))
    low = cv + endpointLo(Lq, LQ, cl) - lamB + p['rmin']
    res['numeric'] = low - T2
    ok = all(v >= 0 for kk, v in res.items() if kk != 'numeric') and res['numeric'] > 0
    return ok, res

def intervalsM(D):
    mc = MCtx(D); A, B = [], []
    for k, (i, j) in enumerate(PAIRS):
        A.append(F(i - j) * LQ + Dq * mc.slo(k)); B.append(F(i - j) * Lq + DQ * mc.shi(k))
    return A, B

def nonempty(D):
    # LP feasibility of {y>=0, sum 1, t_b - t_a <= D[a][b]/S}
    Aub = np.array([[rowA(a, b, q) for q in range(9)] for a in range(10) for b in range(10) if a != b], float)
    bub = np.array([D[a][b] / S for a in range(10) for b in range(10) if a != b])
    r = linprog(np.zeros(9), A_ub=Aub, b_ub=bub + 1e-12, A_eq=np.ones((1, 9)), b_eq=[1], bounds=[(0, None)] * 9, method='highs')
    return r.status == 0

def solve_lpM(D, sk, ck, rows_idx=None):
    R = ROWS if rows_idx is None else [ROWS[i] for i in rows_idx]
    RM = ROWM if rows_idx is None else ROWM[rows_idx]
    dbv = np.array([D[a][b] / S for a, b in R]); nb, nl = 16, len(R)
    ij = np.array([i - j for i, j in PAIRS], float)
    objb = Wf @ (ck + Lc * sk * ij)
    mask = np.array([[1.0 if PAIRS[k][0] <= q < PAIRS[k][1] else 0.0 for k in range(36)] for q in range(9)])
    G = (mask * sk[None, :]) @ Wf.T
    nv = nb + nl + 1; c = np.zeros(nv); c[:nb] = -objb; c[nb:nb + nl] = dbv; c[-1] = -1
    Aub = np.zeros((9, nv)); Aub[:, :nb] = -Dc * G; Aub[:, nb:nb + nl] = -RM.T; Aub[:, -1] = 1
    Aeq = np.zeros((1, nv)); Aeq[0, :nb] = 1
    r = linprog(c, A_ub=Aub, b_ub=np.zeros(9), A_eq=Aeq, b_eq=[1.0], bounds=[(0, None)] * (nb + nl) + [(None, None)], method='highs')
    if r.status != 0: return None
    y = -r.ineqlin.marginals; y = np.maximum(y, 0); y = y / y.sum() if y.sum() > 0 else np.full(9, 1 / 9)
    return dict(val=-r.fun, beta=r.x[:nb], lam=r.x[nb:nb + nl], rows=R, y=y)

def build_packetM(D, A, B, kinds, beta, lam, rows, ystar):
    z = zvals(ystar)
    lines = [make_line(A[k], B[k], kinds[k][0], kinds[k][1], z[k]) for k in range(36)]
    bq = [fr(max(x, 0.0)) for x in beta]; tot = sum(bq)
    if tot == 0: return None
    bq = [x / tot for x in bq]
    idx = [i for i in sorted(range(len(lam)), key=lambda i: -lam[i])[:7] if lam[i] > 1e-13]
    lq = [fr(lam[i]) for i in idx]; rf = [rows[i][0] for i in idx]; rt = [rows[i][1] for i in idx]
    while len(lq) < 7: lq.append(F(0)); rf.append(0); rt.append(0)
    w = [ctx.mix(bq, k) for k in range(36)]; s = [l['s'] for l in lines]
    g = [sum((w[k] * s[k] for k in range(36) if PAIRS[k][0] <= q < PAIRS[k][1]), F(0)) for q in range(9)]
    rho = [sum((lq[a] * rowA(rf[a], rt[a], q) for a in range(7)), F(0)) for q in range(9)]
    rmin = F(math.floor(min(endpointLo(Dq, DQ, g[q]) + rho[q] for q in range(9)) * 10**15), 10**15)
    return dict(beta=bq, line=lines, rowFrom=rf, rowTo=rt, lam=lq, rmin=rmin)

def leaf_attempt(D, maxit=60):
    A, B = intervalsM(D); kinds = [arc_kind(A[k], B[k]) for k in range(36)]
    if any(k is None for k in kinds): return None, -1.0, 'straddle'
    y = np.full(9, 1 / 9); best = -1e9
    for it in range(maxit):
        sk, ck = float_lines(A, B, kinds, y); sol = solve_lpM(D, sk, ck)
        if sol is None: return None, -1.0, 'lp'
        nz = [i for i in range(len(sol['lam'])) if sol['lam'][i] > 1e-12]
        if len(nz) > 7:
            s2 = solve_lpM(D, sk, ck, sorted(nz, key=lambda i: -sol['lam'][i])[:7])
            if s2 is not None: sol = s2
        if sol['val'] > best:
            best = sol['val']
            if best > float(T2) + 1e-12:
                pk = build_packetM(D, A, B, kinds, sol['beta'], sol['lam'], sol['rows'], y)
                if pk is not None:
                    ok, res = check_matrix(D, pk)
                    if ok: return pk, float(res['numeric']), 'pass'
        y = y + (sol['y'] - y) / (it + 2) ** 0.6
    return None, best - float(T2), 'below'

def split_child(D, i, j, m):
    L = [[min(D[a][b], D[a][i] + m + D[j][b]) for b in range(10)] for a in range(10)]
    R = [[min(D[a][b], D[a][j] - m + D[i][b]) for b in range(10)] for a in range(10)]
    return L, R

def lp_range(D, i, j):
    Aub = np.array([[rowA(a, b, q) for q in range(9)] for a in range(10) for b in range(10) if a != b], float)
    bub = np.array([D[a][b] / S for a in range(10) for b in range(10) if a != b])
    c = np.array([rowA(i, j, q) for q in range(9)], float)
    out = []
    for sg in (1, -1):
        r = linprog(sg * c, A_ub=Aub, b_ub=bub, A_eq=np.ones((1, 9)), b_eq=[1], bounds=[(0, None)] * 9, method='highs')
        out.append(sg * r.fun)
    return out[0], out[1]

def choose_split(D):
    best = None
    for i in range(10):
        for j in range(i + 1, 10):
            lo, hi = lp_range(D, i, j)
            w = (hi - lo) * abs(Dc)
            if (hi - lo) * S >= 2 and (best is None or w > best[0]):
                best = (w, i, j, int(round((lo + hi) / 2 * S)))
    return best

def solve_node(D, depth, budget_t, leaves):
    if time.time() > budget_t: return dict(kind='timeout')
    if not nonempty(D): return dict(kind='fail', D=D, why='empty')
    pk, gap, why = leaf_attempt(D)
    if pk is not None:
        leaves.append(1); return dict(kind='leaf', D=D, packet=enc(pk), margin=gap)
    if depth >= MAXDEPTH or len(leaves) >= MAXLEAVES:
        return dict(kind='fail', D=D, gap=gap, why=why)
    sp = choose_split(D)
    if sp is None: return dict(kind='fail', D=D, gap=gap, why='nosplit')
    _, i, j, m = sp
    Lm, Rm = split_child(D, i, j, m)
    l = solve_node(Lm, depth + 1, budget_t, leaves)
    if l['kind'] in ('fail', 'timeout'): return dict(kind='fail', D=D, gap=gap, why='child', split=[i, j, m], left=l)
    r = solve_node(Rm, depth + 1, budget_t, leaves)
    if r['kind'] in ('fail', 'timeout'): return dict(kind='fail', D=D, gap=gap, why='child', split=[i, j, m], left=l, right=r)
    return dict(kind='split', D=D, split=[i, j, m], left=l, right=r)

def count_leaves(t):
    if t['kind'] == 'leaf': return 1
    if t['kind'] == 'empty': return 0
    if t['kind'] == 'split': return count_leaves(t['left']) + count_leaves(t['right'])
    return 0

if __name__ == '__main__':
    budget = float(sys.argv[1]) if len(sys.argv) > 1 else 100
    per = float(os.environ.get('PERNODE', '60'))
    todo = [int(x) for x in sys.argv[2:]]
    if not todo:
        for f in sorted(os.listdir(CERT), key=lambda s: int(s.split('.')[0])):
            r = json.load(open(os.path.join(CERT, f)))
            if r['status'] != 'pass':
                rf = os.path.join(HERE, 'refine', f)
                if os.path.exists(rf) and json.load(open(rf))['status'] == 'pass': continue
                todo.append(r['node'])
    t0 = time.time(); k = 0
    for n in todo:
        fp = os.path.join(SD, '%d.json' % n)
        if os.path.exists(fp): continue
        if time.time() - t0 > budget: break
        D0 = [[x * 2 ** SH for x in row] for row in ctx.tree[n]['db']]
        ts = time.time(); leaves = []
        tr = solve_node(D0, 0, ts + per, leaves)
        r = dict(node=n, status='pass' if tr['kind'] == 'split' else 'fail', leaves=count_leaves(tr) if tr['kind'] == 'split' else None,
                 scale=S, maxdepth=MAXDEPTH, tree=tr, sec=round(time.time() - ts, 2))
        json.dump(r, open(fp + '.tmp', 'w')); os.replace(fp + '.tmp', fp)
        with open(LEDGER, 'a') as L:
            L.write(json.dumps(dict(node=n, stage='split', status=r['status'], leaves=r['leaves'], sec=r['sec'],
                                    utc=time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()))) + '\n')
        k += 1; print(n, r['status'], r['leaves'], r['sec'], flush=True)
    print('done', k, round(time.time() - t0, 1))
