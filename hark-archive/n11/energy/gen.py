#!/usr/bin/env python3
"""Generate Paid16CellCertificate packets for remaining energy terminals.
Float LP (HiGHS) proposes beta / tangent points / dual rows; everything is then
rounded to rationals and rmin is computed EXACTLY so that `reduced` holds by
construction; the packet is accepted only if checker.check() passes exactly.
Resumable: one JSON per node under certs/, append-only ledger.jsonl.
Usage: gen.py [max_seconds] [node ...]"""
import sys, os, json, time, math
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
from checker import *

HERE = os.path.dirname(os.path.abspath(__file__))
CERT = os.path.join(HERE, 'certs'); os.makedirs(CERT, exist_ok=True)
LEDGER = os.path.join(HERE, 'ledger.jsonl')
d = load_parsed(); ctx = Ctx(d)
Wf = np.array([[x / 1e12 for x in row] for row in d['weights']])  # 16x36
Lc = 2 * math.asin(0.38); Dc = 9 * Lc - 2 * math.pi
PIf = math.pi

def fr(x, den=10**12):
    return F(round(x * den), den)
def fr_down(x, den=10**15):
    return F(math.floor(x * den), den)

def intervals(n):
    A, B = [], []
    for k, (i, j) in enumerate(PAIRS):
        A.append(F(i - j) * LQ + Dq * ctx.slo(n, k))
        B.append(F(i - j) * Lq + DQ * ctx.shi(n, k))
    return A, B

def arc_kind(a, b):
    """return ('inc'|'dec', m) if [a,b] fits an arc exactly, else None"""
    af = float(a)
    m0 = math.floor((af / PIf + 0.5) / 2)
    for m in (m0 - 1, m0, m0 + 1):
        if incArc(a, b, m) >= 0: return ('inc', m)
        if decArc(a, b, m) >= 0: return ('dec', m)
    return None

def make_line(a, b, kind, m, tpt):
    if kind == 'dec':
        # chord below both endpoints
        fa = 1 - math.cos(float(a)); fb = 1 - math.cos(float(b))
        s = fr((fb - fa) / max(float(b - a), 1e-30)) if b > a else fr(math.sin(float(a)))
        c = min(1 - cosHi(a) - s * a, 1 - cosHi(b) - s * b)
        c = c - F(1, 10**14)
        c = F(math.floor(c * 10**14), 10**14) if True else c
        return dict(a=a, b=b, s=s, c=c, t=F(0), e=F(0), shift=m, rule='decreasing')
    t = fr(min(max(tpt, float(a)), float(b)))
    if t < a: t = a
    if t > b: t = b
    s = fr(math.sin(float(t)), 10**13)
    e = max(sinHi(t) - s, s - sinLo(t), F(0))
    e = F(math.ceil(e * 10**14) + 1, 10**14)
    c = 1 - cosHi(t) - s * t - e * (b - a)
    c = F(math.floor(c * 10**14) - 1, 10**14)
    return dict(a=a, b=b, s=s, c=c, t=t, e=e, shift=m, rule='tangent')

ROWS = [(a, b) for a in range(10) for b in range(10) if a != b]
def rowvec(a, b):  # t_b - t_a = sum_q rowA(a,b,q) y_q
    return np.array([rowA(a, b, q) for q in range(9)], dtype=float)
ROWM = np.array([rowvec(a, b) for a, b in ROWS])  # R x 9

def solve_lp(n, sk, ck, rows_idx=None):
    """max_{beta,lam,rmin} cv+Lc*cl+rmin-lam.db  s.t. rmin <= Dc g_q + rho_q."""
    R = ROWS if rows_idx is None else [ROWS[i] for i in rows_idx]
    RM = ROWM if rows_idx is None else ROWM[rows_idx]
    dbv = np.array([ctx.tree[n]['db'][a][b] / 4096 for a, b in R])
    nb, nl = 16, len(R)
    # coefficient of beta_f in objective
    ij = np.array([i - j for i, j in PAIRS], dtype=float)
    objb = Wf @ (ck + Lc * sk * ij)  # 16
    # g_q(beta) = sum_k [i<=q<j] Wf[f,k] s_k beta_f
    mask = np.array([[1.0 if PAIRS[k][0] <= q < PAIRS[k][1] else 0.0 for k in range(36)] for q in range(9)])
    G = (mask * sk[None, :]) @ Wf.T  # 9x16
    nv = nb + nl + 1
    c = np.zeros(nv); c[:nb] = -objb; c[nb:nb + nl] = dbv; c[-1] = -1.0
    # rmin - Dc G beta - RM^T lam <= 0
    Aub = np.zeros((9, nv)); Aub[:, :nb] = -Dc * G; Aub[:, nb:nb + nl] = -RM.T; Aub[:, -1] = 1.0
    bub = np.zeros(9)
    Aeq = np.zeros((1, nv)); Aeq[0, :nb] = 1.0
    bounds = [(0, None)] * (nb + nl) + [(None, None)]
    r = linprog(c, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=[1.0], bounds=bounds, method='highs')
    if r.status != 0: return None
    y = -r.ineqlin.marginals  # duals of the 9 reduced constraints = minimiser y*
    y = np.maximum(y, 0); y = y / y.sum() if y.sum() > 0 else np.full(9, 1 / 9)
    return dict(val=-r.fun, beta=r.x[:nb], lam=r.x[nb:nb + nl], rows=R, y=y)

def zvals(y):
    t = np.concatenate([[0.0], np.cumsum(y)])
    return np.array([(i - j) * Lc + Dc * (t[j] - t[i]) for i, j in PAIRS])

def build_packet(n, A, B, kinds, beta, lam, rows, ystar):
    z = zvals(ystar)
    lines = [make_line(A[k], B[k], kinds[k][0], kinds[k][1], z[k]) for k in range(36)]
    # rational beta, exact sum 1
    bq = [fr(max(x, 0.0)) for x in beta]
    if sum(bq) == 0: return None
    tot = sum(bq); bq = [x / tot for x in bq]
    # choose <=7 rows by largest lam
    idx = sorted(range(len(lam)), key=lambda i: -lam[i])[:7]
    idx = [i for i in idx if lam[i] > 1e-13]
    lq = [fr(lam[i]) for i in idx]; rf = [rows[i][0] for i in idx]; rt = [rows[i][1] for i in idx]
    while len(lq) < 7: lq.append(F(0)); rf.append(0); rt.append(0)
    w = [ctx.mix(bq, k) for k in range(36)]
    s = [l['s'] for l in lines]
    g = [sum((w[k] * s[k] for k in range(36) if PAIRS[k][0] <= q < PAIRS[k][1]), F(0)) for q in range(9)]
    rho = [sum((lq[a] * rowA(rf[a], rt[a], q) for a in range(7)), F(0)) for q in range(9)]
    rmin = min(endpointLo(Dq, DQ, g[q]) + rho[q] for q in range(9))
    rmin = F(math.floor(rmin * 10**15), 10**15)
    return dict(nodeID=n, beta=bq, line=lines, rowFrom=rf, rowTo=rt, lam=lq, rmin=rmin)

def attempt(n):
    A, B = intervals(n)
    kinds = [arc_kind(A[k], B[k]) for k in range(36)]
    strad = [k for k in range(36) if kinds[k] is None]
    if strad:
        return dict(node=n, status='fail', reason='straddle', straddle=strad)
    y = np.full(9, 1 / 9)
    best = None; tried = 0
    for it in range(MAXIT):
        sk, ck = float_lines(A, B, kinds, y)
        sol = solve_lp(n, sk, ck)
        if sol is None: break
        nz = [i for i in range(len(sol['lam'])) if sol['lam'][i] > 1e-12]
        if len(nz) > 7:
            keep = sorted(nz, key=lambda i: -sol['lam'][i])[:7]
            s2 = solve_lp(n, sk, ck, keep)
            if s2 is not None: sol = s2
        if best is None or sol['val'] > best:
            best = sol['val']
            if sol['val'] > float(T2) + 1e-9:
                pk = build_packet(n, A, B, kinds, sol['beta'], sol['lam'], sol['rows'], y)
                tried += 1
                if pk is not None:
                    ok, res, low = check(ctx, pk)
                    if ok:
                        return dict(node=n, status='pass', margin=float(res['numeric']), iters=it + 1,
                                    packet=enc(pk), lp_val=sol['val'])
        y = y + (sol['y'] - y) / (it + 2) ** 0.6
    gap = (best - float(T2)) if best is not None else None
    return dict(node=n, status='fail', reason='lp_below_T2' if (gap is not None and gap <= 1e-9) else 'exact_round',
                lp_gap=gap, tried=tried)

MAXIT = 80
def float_lines(A, B, kinds, y):
    z = zvals(y); sk = np.zeros(36); ck = np.zeros(36)
    for k in range(36):
        a, b = float(A[k]), float(B[k])
        if kinds[k][0] == 'dec':
            fa, fb = 1 - math.cos(a), 1 - math.cos(b)
            sk[k] = (fb - fa) / (b - a) if b > a else math.sin(a)
            ck[k] = min(fa - sk[k] * a, fb - sk[k] * b)
        else:
            t = min(max(z[k], a), b)
            sk[k] = math.sin(t); ck[k] = 1 - math.cos(t) - sk[k] * t
    return sk, ck

def enc(x):
    if isinstance(x, F): return '%d/%d' % (x.numerator, x.denominator)
    if isinstance(x, dict): return {k: enc(v) for k, v in x.items()}
    if isinstance(x, list): return [enc(v) for v in x]
    return x

if __name__ == '__main__':
    budget = float(sys.argv[1]) if len(sys.argv) > 1 else 1000
    ids = json.load(open(os.path.join(HERE, 'ids.json')))
    todo = [int(x) for x in sys.argv[2:]] or ids['remaining']
    t0 = time.time(); done = 0
    for n in todo:
        fp = os.path.join(CERT, '%d.json' % n)
        if os.path.exists(fp): continue
        if time.time() - t0 > budget: break
        ts = time.time()
        try:
            r = attempt(n)
        except Exception as ex:
            r = dict(node=n, status='error', reason=repr(ex)[:300])
        r['sec'] = round(time.time() - ts, 2)
        tmp = fp + '.tmp'; json.dump(r, open(tmp, 'w')); os.replace(tmp, fp)
        with open(LEDGER, 'a') as L:
            L.write(json.dumps({k: v for k, v in r.items() if k != 'packet'} | {'utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}) + '\n')
        done += 1
    print('done', done, 'in', round(time.time() - t0, 1))
