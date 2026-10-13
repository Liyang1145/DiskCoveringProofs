"""R20-TC-ELIM (SUPERSEDED, NOT RUN — kept for provenance only).

The lead replaced this design (7 unknowns / 5 tight conditions + an 8D resultant/Groebner
sketch) by the smaller rational elimination now in `r20_tc_elim2.py` / `TC-FAMILY-ELIMINATION.md`:
on the symmetric active branch the hubs are eliminated rationally (y0 = 2ReU_3 - rho_4,
y1 = ReU_8 + R) and R, h come out in closed form, leaving 2 equations in the 4 angles.
This file was never executed and is NOT evidence.  Do not cite it.

Original docstring follows.
------------------------------------------------------------------------------------------
R20-TC-ELIM (r20-gluing, cline2 / DS v4.1f): bounded (<=1 h wall, sympy/mpmath only) probe for
eliminating the TC free parameters to a univariate q(R).

E0 (lead's lemma, own evidence): with e_k = e^{i(theta_k+a_k)}, C_k = rho_k e^{i theta_k},
    U_k = C_k + C_{k+1} - e_k  =>  U_k - C_k = C_{k+1} - e_k = e^{i theta_{k+1}}(rho_{k+1} - e^{-i a_{k+1}})
    => |U_k - C_k|^2 = rho_{k+1}^2 - 2 rho_{k+1} cos a_{k+1} + 1 = R^2   (ring-radius identity).
    Holds for every k; feeds the "concyclic/concurrent" rewriting of the 5 tight rows.

E1: the reduced polynomial content system, with the rotation variables c_k,s_k ELIMINATED
    explicitly by the recursion and with rho in place of t:
      variables (19): P_0..P_4, Q_0..Q_4, rho_0..rho_4 (rho_{8-k} := rho_k), h, y_0, y_1, R
      equations (17): 4 units, 2 w4, 5 ring-radius (rho^2 - 2 rho P + 1 - R^2),
                      1 hub (h^2 - (R^2 - d^2)), 5 tight rows (A7)
    => dim 19 - 17 = 2, matching the certified germ dimension.
E2: the threshold (criticality) condition dR in span{df}: verified numerically at the root,
    then measured for elimination cost (spike probe) and reported as verdict (a)/(b).

No claim registered.  No new box, no precision escalation, no branch-and-bound.
Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_elim.py
"""
import json
import sys
import time
from pathlib import Path

import numpy as np
import sympy as sp
from mpmath import mp, mpf, iv

HERE = Path(__file__).parent
LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
LOG = []


def P(*a):
    s = ' '.join(str(x) for x in a)
    print(s)
    LOG.append(s)
    sys.stdout.flush()


def nterm(e):
    return sp.count_ops(e) if e != 0 else 0


def main():
    t_start = time.time()
    mp.dps = 60

    # ---------------- E0: the concurrency/ring-radius lemma
    a0, a1, a2, a3, y0s, y1s, Rs = sp.symbols('a0 a1 a2 a3 y0 y1 R', real=True)
    th_s = sp.symbols('th0:9', real=True)
    av = [a0, a1, a2, a3, sp.pi - 2 * (a0 + a1 + a2 + a3), a3, a2, a1, a0]
    res = []
    for k in range(9):
        k2 = (k + 1) % 9
        rho_k = sp.cos(av[k]) - sp.sqrt(Rs ** 2 - sp.sin(av[k]) ** 2)
        rho_k2 = sp.cos(av[k2]) - sp.sqrt(Rs ** 2 - sp.sin(av[k2]) ** 2)
        # recursion: theta_{k+1} = theta_k + a_k + a_{k+1}  <=>  theta_k + a_k = theta_{k+1} - a_{k+1}
        th_k2 = th_s[k2]
        e_k = sp.exp(sp.I * (th_s[k] + av[k])).rewrite(sp.cos)
        C_k = rho_k * sp.exp(sp.I * th_s[k]).rewrite(sp.cos)
        C_k2 = rho_k2 * sp.exp(sp.I * th_s[k2]).rewrite(sp.cos)
        diff = sp.expand(sp.simplify((C_k2 - e_k) - (sp.exp(sp.I * (th_k2 - av[k2])).rewrite(sp.cos) * rho_k2
                                       - sp.exp(sp.I * (th_k2 - av[k2])).rewrite(sp.cos))))
        # |C_{k+1} - e_k|^2 with the recursion substituted
        z = C_k2 - e_k
        mag2 = sp.simplify(sp.expand(z * sp.conjugate(z).rewrite(sp.cos)))
        res.append((k, diff, mag2))
    # the ring-radius identity rho^2 - 2 rho cos a + 1 = R^2 at rho = cos a - sqrt(R^2 - sin^2 a)
    aa = sp.symbols('aa', real=True)
    rho_expr = sp.cos(aa) - sp.sqrt(Rs ** 2 - sp.sin(aa) ** 2)
    ring_id = sp.simplify(rho_expr ** 2 - 2 * rho_expr * sp.cos(aa) + 1 - Rs ** 2)
    P('=== E0: ring-radius / concurrency lemma ===')
    P('  ring identity  rho^2 - 2 rho cos a + 1 - R^2  at  rho = cos a - sqrt(R^2-sin^2 a)  =>  %s'
      % ring_id)
    P('  |U_k - C_k|^2 == rho_{k+1}^2 - 2 rho_{k+1} cos a_{k+1} + 1  (symbolic, all k): %s'
      % all(sp.simplify(r[2] - (sp.cos(av[(r[0] + 1) % 9]) - sp.sqrt(Rs ** 2 - sp.sin(av[(r[0] + 1) % 9]) ** 2)) ** 2
                     + 2 * (sp.cos(av[(r[0] + 1) % 9]) - sp.sqrt(Rs ** 2 - sp.sin(av[(r[0] + 1) % 9]) ** 2))
                     * sp.cos(av[(r[0] + 1) % 9]) - 1) == 0 for r in res))
    # numeric per-row |U - C| - R at the certified root
    import r20_tc_iv3 as I3
    import r20_tc_poly as TP
    d = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text())
    ch = d['certificate']['center_hex']
    avec = [mpf(float.fromhex(ch[k])) for k in range(4)]
    y0v, y1v, Rv = (mpf(float.fromhex(ch[4])), mpf(float.fromhex(ch[5])), mpf(float.fromhex(ch[6])))
    vals = TP.analytic_substitution(avec, y0v, y1v, Rv)
    a_all = avec + [mp.pi - 2 * sum(avec)] + [avec[3], avec[2], avec[1], avec[0]]
    th = [mpf(0)] * 9
    for k in range(5, 9):
        th[k] = th[k - 1] + a_all[k - 1] + a_all[k]
    for k in range(3, -1, -1):
        th[k] = th[k + 1] - (a_all[k] + a_all[k + 1])
    rho_v = [vals[TP.P[k]] - vals[TP.T[k]] for k in range(9)]
    Cy = [rho_v[k] * mp.sin(th[k]) for k in range(9)]
    Cx = [rho_v[k] * mp.cos(th[k]) for k in range(9)]
    Ux = [Cx[k] + Cx[(k + 1) % 9] - mp.cos(th[k] + a_all[k]) for k in range(9)]
    Uy = [Cy[k] + Cy[(k + 1) % 9] - mp.sin(th[k] + a_all[k]) for k in range(9)]
    dev = []
    for k in range(9):
        dck = mp.sqrt((Ux[k] - Cx[k]) ** 2 + (Uy[k] - Cy[k]) ** 2) - Rv
        dck2 = mp.sqrt((Ux[k] - Cx[(k + 1) % 9]) ** 2 + (Uy[k] - Cy[(k + 1) % 9]) ** 2) - Rv
        dev.append((k, dck, dck2))
    P('  numeric at the certified root: max_k |U_k - C_k| - R = %s ; max_k |U_k - C_{k+1}| - R = %s'
      % (mp.nstr(max(abs(x[1]) for x in dev), 6), mp.nstr(max(abs(x[2]) for x in dev), 6)))
    P('  per-row |U_k - C_k| - R : %s' % [mp.nstr(x[1], 3) for x in dev])

    # ---------------- E1: reduced polynomial system (c_k, s_k eliminated, rho in place of t)
    nn = 5
    Pv = sp.symbols('P0:%d' % nn, real=True)
    Qv = sp.symbols('Q0:%d' % nn, real=True)
    Rv_sym = sp.symbols('rho0:%d' % nn, real=True)
    hs, y0, y1, R = sp.symbols('h y0 y1 R', real=True)
    mir = lambda k: k if k <= 4 else 8 - k
    rho = [Rv_sym[mir(k)] for k in range(9)]
    W = (sp.Integer(1), sp.Integer(0))
    for k in range(4):
        W = (W[0] * Pv[k] - W[1] * Qv[k], W[0] * Qv[k] + W[1] * Pv[k])
    W2 = (W[0] ** 2 - W[1] ** 2, 2 * W[0] * W[1])
    eqs = []
    for k in range(4):
        eqs.append(('unit%d' % k, Pv[k] ** 2 + Qv[k] ** 2 - 1))
    eqs.append(('w4_re', sp.expand(Pv[4] + W2[0])))
    eqs.append(('w4_im', sp.expand(Qv[4] - W2[1])))
    for k in range(5):
        eqs.append(('ring%d' % k, Rv_sym[k] ** 2 - 2 * Rv_sym[k] * Pv[k] + 1 - R ** 2))
    dd = (y1 - y0) / 2
    eqs.append(('hub', hs ** 2 - (R ** 2 - dd ** 2)))
    # (c_k, s_k) by the explicit recursion (theta_4 = 0), written directly in P,Q
    cs = [None] * 9
    cs[4] = (sp.Integer(1), sp.Integer(0))
    rot = lambda p, q: (p[0] * q[0] - p[1] * q[1], p[0] * q[1] + p[1] * q[0])
    for k in range(5, 9):
        phi = rot((Pv[mir(k - 1)], Qv[mir(k - 1)]), (Pv[mir(k)], Qv[mir(k)]))
        cs[k] = rot(cs[k - 1], phi)
    for k in range(3, -1, -1):
        phi = rot((Pv[k], Qv[k]), (Pv[k + 1], Qv[k + 1]))
        cs[k] = rot(cs[k + 1], (phi[0], -phi[1]))
    Ux_s, Uy_s = [], []
    for k in range(9):
        k2 = (k + 1) % 9
        Ux_s.append(sp.expand(rho[k] * cs[k][0] + rho[k2] * cs[k2][0]
                              - (cs[k][0] * Pv[mir(k)] - cs[k][1] * Qv[mir(k)])))
        Uy_s.append(sp.expand(rho[k] * cs[k][1] + rho[k2] * cs[k2][1]
                              - (cs[k][1] * Pv[mir(k)] + cs[k][0] * Qv[mir(k)])))
    for (k, l) in [(1, 1), (2, 0), (3, 0), (8, 1)]:
        yv = y1 if l else y0
        eqs.append(('tight_k%d_l%d' % (k, l), sp.expand((Ux_s[k] - yv) ** 2 + Uy_s[k] ** 2 - R ** 2)))
    m_ = (y0 + y1) / 2
    eqs.append(('tight_hub', sp.expand((m_ - rho[6] * cs[6][0]) ** 2 + (hs - rho[6] * cs[6][1]) ** 2 - R ** 2)))
    ALLV = list(Pv) + list(Qv) + list(Rv_sym) + [hs, y0, y1, R]
    P()
    P('=== E1: reduced content system (c_k, s_k eliminated; rho in place of t) ===')
    P('  variables = %d : P0..P4, Q0..Q4, rho0..rho4, h, y0, y1, R' % len(ALLV))
    P('  equations = %d (4 unit, 2 w4, 5 ring-radius, 1 hub, 5 tight)' % len(eqs))
    degs = sorted({sp.total_degree(e) for _, e in eqs})
    P('  total degrees: %s ; largest expression: %s (ops)'
      % (degs, max(nterm(e) for _, e in eqs)))
    P('  -> dim = %d - %d = %d (matches the certified germ dimension)'
      % (len(ALLV), len(eqs), len(ALLV) - len(eqs)))
    # numeric verification at the root image
    subs = {}
    for k in range(5):
        subs[Pv[k]] = vals[TP.P[k]]; subs[Qv[k]] = vals[TP.Q[k]]; subs[Rv_sym[k]] = rho_v[k]
    subs[hs] = vals[TP.h_]; subs[y0] = y0v; subs[y1] = y1v; subs[R] = Rv
    worst = ('', mpf(0))
    for nm, e in eqs:
        v = abs(sp.N(e.subs(subs), 40))
        if v > worst[1]:
            worst = (nm, v)
    P('  numeric check at the certified root: worst |E| = %s (equation %s)'
      % (mp.nstr(worst[1], 6), worst[0]))

    # ---------------- E2: threshold condition dR in span{df}
    f5 = [e for nm, e in eqs if nm.startswith('tight')]
    Df = sp.Matrix([[sp.diff(e, v) for v in ALLV] for e in f5])
    gradR = sp.Matrix([sp.Integer(0)] * len(ALLV))
    gradR[len(ALLV) - 1] = sp.Integer(1)
    M = np.array([[float(sp.N(Df[i, j].subs(subs), 30)) for j in range(len(ALLV))] for i in range(5)])
    gR = np.array([float(sp.N(gradR[j].subs(subs), 30)) for j in range(len(ALLV))])
    lam, *_ = np.linalg.lstsq(M.T, gR, rcond=None)
    resid = float(np.max(np.abs(M.T @ lam - gR)))
    sing = np.linalg.svd(M, compute_uv=False)
    P()
    P('=== E2: threshold condition  dR in span{df} ===')
    P('  5x19 Jacobian at the root: sigma = %s' % np.round(sing, 6).tolist())
    P('  min_lambda || Df^T lambda - grad R ||_inf = %.3e   (0 => the root IS a threshold point)'
      % resid)
    P('  [numeric only; the algebraisation below is the object that would make it polynomial]')

    # ---------------- spike probe: bounded elimination attempts
    P()
    P('=== E3: bounded elimination probe (spike measurement; <=1 h wall total) ===')
    trials = []
    t0 = time.time()
    # (i) one resultant of two tight rows after fixing everything except two variables
    two = [Pv[0], Qv[0]]
    e1 = sp.Poly(sp.expand(f5[0].subs({v: subs[v] for v in ALLV if v not in two}), two).as_expr(), *two)
    e2 = sp.Poly(sp.expand(f5[1].subs({v: subs[v] for v in ALLV if v not in two}), two).as_expr(), *two)
    trials.append(dict(tag='resultant of 2 tight rows in 2 vars (rest fixed numerically)',
                       nvars=2, neqs=2, deg1=e1.total_degree(), deg2=e2.total_degree(),
                       terms1=len(e1.terms()), terms2=len(e2.terms())))
    try:
        r = sp.resultant(e1.as_expr(), e2.as_expr(), two[1])
        trials[-1]['resultant_terms'] = sp.count_ops(r)
        trials[-1]['resultant_degree'] = sp.Poly(r, two[0]).total_degree()
        trials[-1]['seconds'] = round(time.time() - t0, 2)
    except Exception as exc:                     # noqa: BLE001
        trials[-1]['error'] = str(exc)[:120]
    P('  (i) %s -> %s' % (trials[-1]['tag'], {k: v for k, v in trials[-1].items() if k != 'tag'}))
    # (ii) Groebner on a numerically-fixed slice: keep k variables, fix the rest
    for keep in (7, 6, 5):
        kv = [Pv[0], Qv[0], Rv_sym[0], Rv_sym[1], Pv[4], Qv[4], R][:keep]
        sub = {v: subs[v] for v in ALLV if v not in kv}
        gs = []
        for nm, e in eqs:
            ee = sp.expand(e.subs(sub))
            if ee != 0:
                gs.append(sp.Poly(ee, *kv).as_expr())
        t1 = time.time()
        try:
            G = sp.groebner(gs, *kv, order='lex')
            ok = True; ng = len(G.exprs)
        except Exception as exc:                 # noqa: BLE001
            ok = False; ng = -1; err = str(exc)[:80]
        trials.append(dict(tag='groebner slice, keep=%d vars' % keep, nvars=keep, neqs=len(gs),
                           seconds=round(time.time() - t1, 2), ok=ok, basis_size=ng,
                           max_basis_ops=(max((sp.count_ops(g) for g in G.exprs), default=0) if ok else None)))
        P('  (ii) %s -> %s' % (trials[-1]['tag'],
                               {k: v for k, v in trials[-1].items() if k != 'tag'}))
        if time.time() - t_start > 900:
            P('  wall cap reached; stopping the spike probe')
            break
    P()
    P('  TOTAL wall = %.1f s' % (time.time() - t_start))
    out = dict(role='E0/E1/E2/E3 elimination probe for the TC family (bounded)',
               E0=dict(ring_identity=str(ring_id),
                       per_row_dev=[(int(k), mp.nstr(x1, 6), mp.nstr(x2, 6)) for k, x1, x2 in dev],
                       max_dev_UC=mp.nstr(max(abs(x[1]) for x in dev), 6)),
               E1=dict(n_vars=len(ALLV), n_eqs=len(eqs), degrees=degs,
                       max_ops=max(nterm(e) for _, e in eqs),
                       worst_residual=mp.nstr(worst[1], 6), worst_eq=worst[0],
                       dim=len(ALLV) - len(eqs)),
               E2=dict(sigma=np.round(sing, 8).tolist(), min_lambda_residual=resid),
               E3=trials, wall_seconds=round(time.time() - t_start, 1),
               scope='bounded probe; no claim, no global elimination performed if E3 fails')
    (HERE / 'r20_tc_elim.json').write_text(json.dumps(out, indent=1, default=str))
    (HERE / 'r20_tc_elim.log').write_text('\n'.join(LOG) + '\n')
    P('saved r20_tc_elim.json / .log')


if __name__ == '__main__':
    main()
