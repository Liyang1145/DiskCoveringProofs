#!/usr/bin/env python3
"""Second pass on single-cell failures.
(1) long damped saddle iteration (MAXIT=600) in the same Paid16 format;
(2) Kelley upper bound V_up >= max_beta min_{y in cell} F_beta(y) (F = the
    best one-line-per-pair convex envelope objective), from cuts at all visited y.
    V_up < T^2 (float, with 1e-9 slack) means NO single-cell Paid16 certificate exists
    for this node (format-impossibility, float evidence only).
Writes refine/<node>.json, appends ledger.jsonl."""
import sys, os, json, time, math
import numpy as np
from scipy.optimize import linprog
import gen
from gen import *

RD = os.path.join(HERE, 'refine'); os.makedirs(RD, exist_ok=True)

def env_energy_fields(A, B, kinds, y):
    """E_f(y) = sum_k Wf[f,k] * phi_k(z_k(y)) with phi = 1-cos on inc arcs, chord on dec arcs."""
    z = zvals(y); ph = np.zeros(36)
    for k in range(36):
        a, b = float(A[k]), float(B[k]); zk = min(max(z[k], a), b)
        if kinds[k][0] == 'dec':
            fa, fb = 1 - math.cos(a), 1 - math.cos(b)
            ph[k] = fa + (fb - fa) * ((zk - a) / (b - a) if b > a else 0)
        else:
            ph[k] = 1 - math.cos(zk)
    return Wf @ ph

def kelley_up(cuts):
    # max v s.t. v <= sum_f beta_f E_f(y_i), beta in simplex
    m = len(cuts); E = np.array(cuts)
    c = np.zeros(17); c[-1] = -1
    Aub = np.hstack([-E, np.ones((m, 1))]); bub = np.zeros(m)
    Aeq = np.zeros((1, 17)); Aeq[0, :16] = 1
    r = linprog(c, A_ub=Aub, b_ub=bub, A_eq=Aeq, b_eq=[1], bounds=[(0, None)] * 16 + [(None, None)], method='highs')
    return -r.fun, r.x[:16]

def run(n, maxit=250):
    A, B = intervals(n); kinds = [arc_kind(A[k], B[k]) for k in range(36)]
    y = np.full(9, 1 / 9); best = -1e9; cuts = []
    for it in range(maxit):
        sk, ck = float_lines(A, B, kinds, y)
        sol = solve_lp(n, sk, ck)
        nz = [i for i in range(len(sol['lam'])) if sol['lam'][i] > 1e-12]
        if len(nz) > 7:
            s2 = solve_lp(n, sk, ck, sorted(nz, key=lambda i: -sol['lam'][i])[:7])
            if s2 is not None: sol = s2
        cuts.append(env_energy_fields(A, B, kinds, sol['y']))
        if sol['val'] > best:
            best = sol['val']
            if best > float(T2) + 1e-12:
                pk = build_packet(n, A, B, kinds, sol['beta'], sol['lam'], sol['rows'], y)
                if pk is not None:
                    ok, res, low = check(ctx, pk)
                    if ok:
                        return dict(node=n, status='pass', margin=float(res['numeric']), iters=it + 1, packet=enc(pk), stage='refine-long')
        y = y + (sol['y'] - y) / (it + 2) ** 0.6
    vup, _ = kelley_up(cuts)
    return dict(node=n, status='fail', best_gap=best - float(T2), vup_gap=vup - float(T2),
                format_impossible_float=bool(vup < float(T2) - 1e-9), stage='refine-long')

if __name__ == '__main__':
    budget = float(sys.argv[1]) if len(sys.argv) > 1 else 100
    fails = []
    for f in sorted(os.listdir(CERT)):
        r = json.load(open(os.path.join(CERT, f)))
        if r['status'] != 'pass': fails.append(r['node'])
    t0 = time.time(); k = 0
    for n in fails:
        fp = os.path.join(RD, '%d.json' % n)
        if os.path.exists(fp): continue
        if time.time() - t0 > budget: break
        ts = time.time(); r = run(n); r['sec'] = round(time.time() - ts, 2)
        json.dump(r, open(fp + '.tmp', 'w')); os.replace(fp + '.tmp', fp)
        with open(LEDGER, 'a') as L:
            L.write(json.dumps({kk: v for kk, v in r.items() if kk != 'packet'} | {'utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}) + '\n')
        k += 1
    print('done', k, 'of', len(fails), round(time.time() - t0, 1))
