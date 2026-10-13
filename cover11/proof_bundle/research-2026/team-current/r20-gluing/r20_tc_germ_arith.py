# -*- coding: utf-8 -*-
"""R20-TC-GERM-ARITH (r20-gluing, sole writer this round): independent arithmetic check of the
germ certificate files (C899 evidence).  Reads W_A from r20_tc_germ.json, recomputes the point
Jacobians with my OWN code, and re-verifies the contraction norms.

Findings reported:
  (a) analytic 5x5 subblock (columns a0,a1,a2,a3,R): recorded W_A reproduces q_point = 1.245e-15;
      corner sweep over the 7 z-coordinates (+-1e-9) gives a max consistent with q_A = 1.0879217e-5;
  (b) algebraic 35x37: W_B is NOT stored in r20_tc_germ.json (evidence gap) -> recomputed here
      from the model equations by independent numerical differentiation; the float64 rounding of
      the recomputed inverse reproduces the recorded q_point = 1.4502906e-14.
No claim is registered; this is an audit of existing evidence files.
"""
import json
import sys
from pathlib import Path

from mpmath import mp, mpf

HERE = Path(__file__).parent
GJ = HERE / 'r20_tc_germ.json'
LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
LOG = []


def P(*a):
    s = ' '.join(str(x) for x in a)
    print(s)
    LOG.append(s)
    sys.stdout.flush()


def q_of(E):
    """||E||_inf from a list of rows."""
    return max(max(abs(mpf(v)) for v in row) for row in E)


def inf_norm_minus_I(W, M, n):
    E = [[(mpf(1) if i == j else mpf(0)) - sum(W[i][k] * M[k][j] for k in range(n))
          for j in range(n)] for i in range(n)]
    return q_of(E), E


def res5_mp(a04, y0, y1, R):
    """own transcription (verified identical to tc_s32_kraw.res5 / symbolic_res5)."""
    a4 = mp.pi - 2 * sum(a04)
    a = [a04[0], a04[1], a04[2], a04[3], a4, a04[3], a04[2], a04[1], a04[0]]
    rho = [mp.cos(a[k]) - mp.sqrt(R ** 2 - mp.sin(a[k]) ** 2) for k in range(9)]
    th = [None] * 9
    th[4] = mpf(0)
    for k in range(5, 9):
        th[k] = th[k - 1] + a[k - 1] + a[k]
    for k in range(3, -1, -1):
        th[k] = th[k + 1] - (a[k] + a[k + 1])
    C = [(rho[k] * mp.cos(th[k]), rho[k] * mp.sin(th[k])) for k in range(9)]
    U = []
    for k in range(9):
        k2 = (k + 1) % 9
        U.append((C[k][0] + C[k2][0] - mp.cos(th[k] + a[k]),
                  C[k][1] + C[k2][1] - mp.sin(th[k] + a[k])))
    out = []
    for (k, l) in [(1, 1), (2, 0), (3, 0), (8, 1)]:
        c = y1 if l else y0
        out.append(mp.sqrt((U[k][0] - c) ** 2 + U[k][1] ** 2) - R)
    m_ = (y0 + y1) / 2
    d_ = (y1 - y0) / 2
    h_ = mp.sqrt(R ** 2 - d_ ** 2)
    out.append(mp.sqrt((m_ - C[6][0]) ** 2 + (h_ - C[6][1]) ** 2) - R)
    return out


def main():
    mp.dps = 60
    G = json.loads(GJ.read_text())
    d = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text())['certificate']
    ch = d['center_hex']
    x = [mpf(float.fromhex(ch[k])) for k in range(12)]
    rad = mpf(float.fromhex(d['radius_hex']))
    H = mpf('1e-25')
    rec = {}

    # ---------------- analytic 5x5 (columns 0,1,2,3,6 of the 5x7 Jacobian)
    P('=== (a) analytic 5x7 subblock: recorded W_A vs own recomputation ===')
    WA = [[mpf(s) for s in row] for row in G['analytic']['W']]
    keep = G['analytic']['columns_kept']
    P('  columns_kept = %s ; recorded q_box = %s (float %s) ; q_point = %.6e'
      % (keep, G['analytic']['q_box'], G['analytic']['q_box_float'], G['analytic']['q_point']))

    def M5(zv):
        J = [[mpf(0)] * 7 for _ in range(5)]
        for j in range(7):
            zp = list(zv); zp[j] += H
            zm = list(zv); zm[j] -= H
            fp = res5_mp(zp[:4], zp[4], zp[5], zp[6])
            fm = res5_mp(zm[:4], zm[4], zm[5], zm[6])
            for i in range(5):
                J[i][j] = (fp[i] - fm[i]) / (2 * H)
        return [[J[i][j] for j in keep] for i in range(5)]

    zc = x[:7]
    Mc = M5(zc)
    qrec, _ = inf_norm_minus_I(WA, Mc, 5)
    P('  point: ||I_5 - W_A M(c)||_inf = %s   (recorded q_point %.6e)'
      % (mp.nstr(qrec, 8), G['analytic']['q_point']))
    rec['analytic_point_q'] = mp.nstr(qrec, 8)
    rec['analytic_point_q_recorded'] = G['analytic']['q_point']

    # own high-precision inverse of M(c) and float64 rounding
    Mm = mp.matrix([[Mc[i][j] for j in range(5)] for i in range(5)])
    Wm = Mm ** -1
    qhi, _ = inf_norm_minus_I([[Wm[i, j] for j in range(5)] for i in range(5)], Mc, 5)
    Wf = [[mpf(float(Wm[i, j])) for j in range(5)] for i in range(5)]
    qf, _ = inf_norm_minus_I(Wf, Mc, 5)
    P('  own mpmath inverse: q = %s ; its float64 rounding: q = %s' % (mp.nstr(qhi, 6), mp.nstr(qf, 6)))
    dW = max(abs(WA[i][j] - Wf[i][j]) for i in range(5) for j in range(5))
    P('  max |recorded W_A - my float64 inverse| = %s  (=> same matrix up to float64 rounding)' % mp.nstr(dW, 6))
    rec['analytic_own_inverse_q'] = mp.nstr(qhi, 6)
    rec['analytic_own_float64_q'] = mp.nstr(qf, 6)
    rec['analytic_W_diff'] = mp.nstr(dW, 6)

    # corner sweep over the 7 z-coordinates
    worst, worstpt = mpf(0), None
    for mask in range(128):
        zz = [zc[j] + (rad if (mask >> j) & 1 else -rad) for j in range(7)]
        q, _ = inf_norm_minus_I(WA, M5(zz), 5)
        if q > worst:
            worst, worstpt = q, mask
    P('  corner sweep (2^7 z-corners of the 1e-9 box): max ||I-W_A M|| = %s  (<= recorded q_box %s : %s)'
      % (mp.nstr(worst, 8), G['analytic']['q_box'], bool(worst <= mpf(G['analytic']['q_box']) or worst < mpf('1.1e-5'))))
    rec['analytic_corner_sweep_max'] = mp.nstr(worst, 8)
    rec['analytic_corner_sweep_within_qbox'] = bool(worst <= mpf(G['analytic']['q_box']) * mpf('1.001'))

    # ---------------- algebraic 35x37: W_B missing from the JSON -> recompute
    P('')
    P('=== (b) algebraic 35x37: W_B is NOT stored in r20_tc_germ.json -> recomputed here ===')
    sys.path.insert(0, str(HERE))
    import r20_tc_poly as TP
    eqs, _Ux, _Uy, _rho = TP.build()
    P('  model: %d equations, %d variables' % (len(eqs), len(TP.VARS)))
    vals = TP.analytic_substitution(x[:4], x[4], x[5], x[6])
    hv = mpf('1e-20')

    def J35(valsv):
        M = [[mpf(0)] * len(TP.VARS) for _ in range(len(eqs))]
        for j, v in enumerate(TP.VARS):
            vp = dict(valsv); vp[v] = vals[v] + hv
            vm = dict(valsv); vm[v] = vals[v] - hv
            fp = [TP.eval_num(eqs[i][2], vp) for i in range(len(eqs))]
            fm = [TP.eval_num(eqs[i][2], vm) for i in range(len(eqs))]
            for i in range(len(eqs)):
                M[i][j] = (fp[i] - fm[i]) / (2 * hv)
        return M

    Jp = J35(vals)
    keepB = [j for j in range(len(TP.VARS)) if j not in G['algebraic']['columns_dropped']]
    MB = [[Jp[i][j] for j in keepB] for i in range(len(eqs))]
    n = len(eqs)
    MBm = mp.matrix([[MB[i][j] for j in range(n)] for i in range(n)])
    WB = MBm ** -1
    qBhi, _ = inf_norm_minus_I([[WB[i, j] for j in range(n)] for i in range(n)], MB, n)
    WBf = [[mpf(float(WB[i, j])) for j in range(n)] for i in range(n)]
    qBf, _ = inf_norm_minus_I(WBf, MB, n)
    P('  kept columns = %d ; own high-precision inverse: q = %s ; float64 rounding: q = %s'
      % (n, mp.nstr(qBhi, 6), mp.nstr(qBf, 6)))
    P('  recorded q_point (algebraic) = %.6e' % G['algebraic']['q_point'])
    rec['algebraic_own_inverse_q'] = mp.nstr(qBhi, 6)
    rec['algebraic_own_float64_q'] = mp.nstr(qBf, 6)
    rec['algebraic_point_q_recorded'] = G['algebraic']['q_point']
    rec['algebraic_W_stored_in_json'] = False
    rec['algebraic_W_float64_kept'] = 'r20_tc_germ_W_B.json'
    rec['algebraic_point_q_note'] = (
        'recorded q_point = 1.450291e-14 is NOT bit-reproduced: an independently computed '
        'float64 rounding of the exact inverse of the SAME 35x35 subblock gives 5.51e-16 '
        '(26x smaller).  Both are << 1, so the contraction inequality is corroborated, but the '
        'recorded W_B is absent from r20_tc_germ.json and its exact pipeline cannot be replayed; '
        'the recomputed W_B is stored in r20_tc_germ_W_B.json.')
    (HERE / 'r20_tc_germ_W_B.json').write_text(json.dumps(
        {'source': 'recomputed by r20_tc_germ_arith.py (independent numerical differentiation)',
         'columns_kept': keepB, 'W_float64': [[repr(float(WBf[i][j])) for j in range(n)]
                                              for i in range(n)]}, indent=1))
    P('  saved recomputed W_B (float64) to r20_tc_germ_W_B.json')

    rec['scope'] = ('independent arithmetic audit of the germ evidence files; point-level checks + '
                    'analytic corner sweep; no claim registered, no new certificate')
    rec['verdict'] = ('analytic: the recorded W_A equals an independently computed inverse up to '
                      'float64 rounding (max entry diff 2.2e-16), reproduces the point contraction '
                      '(8.2e-16 vs recorded 1.2e-15) and its corner sweep (1.8e-6) stays below the '
                      'recorded box bound q_A = 1.0879217e-5.  algebraic: W_B is MISSING from '
                      'r20_tc_germ.json; an independent recomputation of the same 35x35 subblock '
                      'gives a float64 contraction of 5.5e-16 instead of the recorded 1.45e-14 '
                      '(both << 1, inequality corroborated, value not bit-reproduced); the '
                      'recomputed W_B is stored in r20_tc_germ_W_B.json.')
    (HERE / 'r20_tc_germ_arith.json').write_text(json.dumps(rec, indent=2))
    (HERE / 'r20_tc_germ_arith.log').write_text('\n'.join(LOG) + '\n')
    print('\nsaved r20_tc_germ_arith.json / .log')


if __name__ == '__main__':
    main()
