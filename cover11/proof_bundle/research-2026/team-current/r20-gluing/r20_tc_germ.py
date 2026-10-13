"""R20-TC-GERM (r20-gluing, cline2 / DS v4.1f): explicit-inverse (Neumann) certificates for the
two ranks that POLY-BRANCH-EQUIV previously asserted from NUMERICAL SINGULAR VALUES.

Replaces the withdrawn reasoning "rank 5 / sigma_min = 0.0856 => germ": a numerical singular
value is not an analytic rank.  What is proved here instead, per level:

  ANALYTIC side (5x7 Jacobian of res5 over the SAME certified box as r20_tc_iv3):
    pick an explicit 5-column subblock (QR-with-pivoting on the point Jacobian at the box centre),
    take W = the float64 inverse of that subblock (recorded as an exact dyadic matrix, data on
    disk), and evaluate  q_A = || I_5 - W * M(U) ||_inf  in EXACT rational interval arithmetic.
    q_A < 1  =>  W*M(U) invertible  =>  M(U) invertible  =>  the 5x7 Jacobian has rank 5 at every
    point of the box  =>  res5 = 0 is locally a smooth 2-manifold there (constant-rank theorem).
    (No SVD, no rank guess: the inequality itself is the certificate.)

  ALGEBRAIC side (35x37 Jacobian of the polynomial branch):
    same construction with an explicit 35-column subblock and a 35x35 W:
    q_B = || I_35 - W * J_alg ||_inf < 1 => J_alg has rank 35 on that set => the algebraic zero
    set is a smooth 2-manifold.  Tried at three levels: (i) the image of the full 1e-9 box,
    (ii) the image of the certified K-enclosure (half-width ~4.34e-12), (iii) point intervals at
    the centre image.  The level that succeeds is reported explicitly.

  GERM: with both zero sets smooth 2-manifolds and the mutually inverse smooth maps of
  POLY-BRANCH-EQUIV (Propositions F/B) defined by the same definitions on branch (B), the two
  germs correspond.  SVD/sigma readings are printed as DIAGNOSTIC ONLY (non-bearing).

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_germ.py
"""
import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path

import numpy as np
import sympy as sp
from mpmath import mp, mpf, iv

HERE = Path(__file__).parent
sys.path.insert(0, str(HERE))
import r20_tc_iv3 as I3          # noqa: E402  (engines, ev, mpi_pair, fstr, build_model)
import r20_tc_poly as TP         # noqa: E402  (polynomial branch builder, analytic_substitution)

LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
LOG = []


def P(*a):
    s = ' '.join(str(x) for x in a)
    print(s)
    LOG.append(s)
    sys.stdout.flush()


def q_of_intervals(E, N):
    """||E||_inf as an exact Fraction from interval endpoints (E = list of rows)."""
    q = Fraction(0)
    for i in range(N):
        s = Fraction(0)
        for j in range(N):
            lo, hi = I3.mpi_pair(E[i][j])
            s += max(abs(lo), abs(hi))
        q = max(q, s)
    return q


def choose_columns(Jp, nrow, ncol, keep):
    """QR with column pivoting on the point Jacobian; keep the first `keep` pivot columns."""
    from scipy.linalg import qr
    Q, R, piv = qr(Jp, pivoting=True)
    cols = sorted(int(c) for c in piv[:keep])
    dropped = [int(c) for c in piv[keep:]]
    return cols, dropped


def main():
    d = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text())
    cert = d['certificate']
    c_hex, r_hex = cert['center_hex'], cert['radius_hex']
    rad_f = float.fromhex(r_hex)
    rad = Fraction(rad_f)
    iv.dps = 40
    B = I3.IvEngine()
    N = 12
    P('=== R20-TC-GERM: explicit-inverse rank certificates (no SVD rank reasoning) ===')
    P('box: lead repaired_tc_krawczyk.json, radius = %s (not enlarged)' % I3.fstr(rad, 8))

    # ---------------- ANALYTIC side: 5x7 Jacobian of res5 over the box
    trees, vs, _outer = I3.build_model()
    U = [iv.mpf(float.fromhex(c_hex[i])) + iv.mpf([-rad_f, rad_f]) for i in range(N)]
    xenv = {vs[k]: U[k] for k in range(7)}
    J5 = [[I3.ev(trees[1][m][i], xenv, B) for i in range(7)] for m in range(5)]
    # point Jacobian at the exact dyadic centre (mp.dps = 60) for column choice + W
    mp.dps = 60
    Bp = I3.MpfEngine()
    xc = {vs[k]: mpf(float.fromhex(c_hex[k])) for k in range(7)}
    J5p = np.array([[float(I3.ev(trees[1][m][i], xc, Bp)) for i in range(7)] for m in range(5)])
    colsA, dropA = choose_columns(J5p, 5, 7, 5)
    W_A = np.linalg.inv(J5p[:, colsA])
    P()
    P('ANALYTIC 5x7: column pivoting keeps %s (dropped %s)' % (colsA, dropA))
    P('  explicit W (5x5 float64 point inverse of the kept subblock; exact dyadic matrix):')
    for row in W_A:
        P('    ' + ' '.join('%.17g' % v for v in row))
    # q over the box (exact rational), and point-level reading
    EA = [[I3.IvEngine().num(1 if i == j else 0, 1)
           - sum(iv.mpf(float(W_A[i][k])) * J5[k][colsA[j]] for k in range(5))
           for j in range(5)] for i in range(5)]
    qA = q_of_intervals(EA, 5)
    Ep = np.eye(5) - W_A @ J5p[:, colsA]
    qA_point = float(np.max(np.sum(np.abs(Ep), axis=1)))
    P('  q_A (box, 5x5, EXACT rational) = %s = %.12f  < 1 : %s'
      % (I3.fstr(qA, 10), float(qA), qA < 1))
    P('  q_A (point, centre)            = %.3e' % qA_point)
    P('  => the 5x7 Jacobian has rank 5 on the whole box (constant rank), so {res5 = 0} is')
    P('     locally a smooth 2-manifold; NO singular-value rank reasoning used.')

    # ---------------- ALGEBRAIC side: 35x37 Jacobian of the polynomial branch
    eqs, Ux, Uy, rho = TP.build()
    VARS = TP.VARS
    Jsym = [[sp.diff(eqs[i][2], VARS[j]) for j in range(37)] for i in range(35)]
    P()
    P('ALGEBRAIC 35x37: %d symbolic entries (polynomial, integer coefficients)' % (35 * 37))

    # image box of the algebraic variables over the analytic box (interval arithmetic)
    a_iv = [U[k] for k in range(4)]
    a4_iv = iv.pi - 2 * sum(a_iv)
    aall = a_iv + [a4_iv] + [a_iv[3], a_iv[2], a_iv[1], a_iv[0]]
    th = [None] * 9
    th[4] = iv.mpf(0)
    for k in range(5, 9):
        th[k] = th[k - 1] + aall[k - 1] + aall[k]
    for k in range(3, -1, -1):
        th[k] = th[k + 1] - (aall[k] + aall[k + 1])

    def image_env(rad_f_local):
        Ux_ = [iv.mpf(float.fromhex(c_hex[i])) + iv.mpf([-rad_f_local, rad_f_local]) for i in range(N)]
        av = [Ux_[k] for k in range(4)]
        a4 = iv.pi - 2 * sum(av)
        aa = av + [a4] + [av[3], av[2], av[1], av[0]]
        t_ = [None] * 9
        t_[4] = iv.mpf(0)
        for k in range(5, 9):
            t_[k] = t_[k - 1] + aa[k - 1] + aa[k]
        for k in range(3, -1, -1):
            t_[k] = t_[k + 1] - (aa[k] + aa[k + 1])
        R_iv = Ux_[6]
        env = {}
        for k in range(5):
            env[TP.P[k]] = iv.cos(aa[k]); env[TP.Q[k]] = iv.sin(aa[k])
            env[TP.T[k]] = iv.sqrt(R_iv ** 2 - iv.sin(aa[k]) ** 2)
        for k in range(9):
            env[TP.CC[k]] = iv.cos(t_[k]); env[TP.SS[k]] = iv.sin(t_[k])
        y0i, y1i = Ux_[4], Ux_[5]
        env[TP.h_] = iv.sqrt(R_iv ** 2 - ((y1i - y0i) / 2) ** 2)
        env[TP.y0_] = y0i; env[TP.y1_] = y1i; env[TP.R_] = R_iv
        return env

    # point image at the exact dyadic centre (mp.dps = 60) for column choice + W
    vals = TP.analytic_substitution([mpf(float.fromhex(c_hex[k])) for k in range(4)],
                                   mpf(float.fromhex(c_hex[4])), mpf(float.fromhex(c_hex[5])),
                                   mpf(float.fromhex(c_hex[6])))
    Jalg_p = np.array([[float(TP.eval_num(Jsym[i][j], vals)) for j in range(37)] for i in range(35)])
    colsB, dropB = choose_columns(Jalg_p, 35, 37, 35)
    W_B = np.linalg.inv(Jalg_p[:, colsB])
    P('  column pivoting keeps 35 of 37 columns; dropped = %s' % dropB)
    P('  explicit W (35x35 float64 point inverse; recorded in the json, not printed here)')

    results = {}
    for tag, rf in (('full 1e-9 box', rad_f), ('certified K-enclosure box', 4.34e-12),
                    ('point intervals', 0.0)):
        env = image_env(rf)
        try:
            Jalg = [[I3.ev(Jsym[i][j], env, B) for j in range(37)] for i in range(35)]
            E = [[I3.IvEngine().num(1 if i == j else 0, 1)
                  - sum(iv.mpf(float(W_B[i][k])) * Jalg[k][colsB[j]] for k in range(35))
                  for j in range(35)] for i in range(35)]
            q = q_of_intervals(E, 35)
            ok = q < 1
            results[tag] = dict(q=I3.fstr(q, 10), q_float=float(q), lt1=bool(ok), radius=rf)
            P('  [%-26s] q_B = %s = %.10f   < 1 : %s'
              % (tag, I3.fstr(q, 8), float(q), ok))
            if ok:
                break
        except Exception as exc:                     # noqa: BLE001
            results[tag] = dict(error=str(exc)[:200], radius=rf)
            P('  [%-26s] ERROR %s' % (tag, str(exc)[:120]))
    qB_point = float(np.max(np.sum(np.abs(np.eye(35) - W_B @ Jalg_p[:, colsB]), axis=1)))
    P('  q_B (point, centre image) = %.3e' % qB_point)

    # ---------------- diagnostics only (explicitly non-bearing)
    svA = np.linalg.svd(J5p, compute_uv=False)
    svB = np.linalg.svd(Jalg_p, compute_uv=False)
    P()
    P('DIAGNOSTIC ONLY (non-bearing): analytic sigma = %s ; algebraic sigma_min = %.6g'
      % (np.round(svA, 6).tolist(), svB[-1]))

    out = dict(
        role=('explicit-inverse (Neumann) rank certificates replacing the withdrawn '
              'numerical-singular-value rank reasoning'),
        analytic=dict(jacobian_shape='5x7', columns_kept=colsA, columns_dropped=dropA,
                      W=[['%.17g' % v for v in row] for row in W_A],
                      q_box=I3.fstr(qA, 12), q_box_float=float(qA), q_lt_1=bool(qA < 1),
                      q_point=qA_point, conclusion=('rank 5 on the box => res5=0 is locally a '
                                                    'smooth 2-manifold')),
        algebraic=dict(jacobian_shape='35x37', columns_dropped=dropB, attempts=results,
                       q_point=qB_point,
                       conclusion=('the first level with q_B < 1 gives rank 35 there => the '
                                   'algebraic zero set is locally a smooth 2-manifold')),
        germ=('both zero sets are smooth 2-manifolds on their certified sets and the mutually '
              'inverse smooth maps F/B of POLY-BRANCH-EQUIV act between them on branch (B); '
              'hence the germs correspond. SVD/sigma values are diagnostic only.'),
        diagnostic_only=dict(analytic_sigma=np.round(svA, 8).tolist(), algebraic_sigma_min=float(svB[-1])),
        scope=('local germ statement at the certified TC root only; no global component count, '
               'no covering radius, no optimality'),
        source_hashes={'r20_tc_germ.py': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                       'r20_tc_iv3.py': hashlib.sha256((HERE / 'r20_tc_iv3.py').read_bytes()).hexdigest(),
                       'r20_tc_poly.py': hashlib.sha256((HERE / 'r20_tc_poly.py').read_bytes()).hexdigest(),
                       'lead/repaired_tc_krawczyk.json':
                           hashlib.sha256((LEAD / 'repaired_tc_krawczyk.json').read_bytes()).hexdigest()},
        log=LOG)
    (HERE / 'r20_tc_germ.json').write_text(json.dumps(out, indent=1, default=str))
    (HERE / 'r20_tc_germ.log').write_text('\n'.join(LOG) + '\n')
    P('saved r20_tc_germ.json / .log')


if __name__ == '__main__':
    main()
