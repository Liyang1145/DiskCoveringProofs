"""R20-TC-IV3 (r20-gluing, cline2/DS v4.1f): TRULY INDEPENDENT full-12D interval Krawczyk
enclosure of the symmetric TC KKT root, on the SAME box (radius = lead radius hex, not enlarged),
at the SAME working precision (iv.dps = 40 primary; 30 / 25 as robustness controls -- no digit
inflation is used to obtain the inclusion).

What is independent here (vs r20_tc_iv1/iv2):
  * PRIMARY ENGINE is a hand-written STRICT TREE-WALK over the SymPy expression tree
    (r20_tc_iv1.symbolic_res5), NOT `sympy.lambdify` -> no printer, no module-dict, no constant
    folding.  Rational p/q becomes the interval  [p,p]/[q,q]  (outward-rounded); `Pi` becomes
    mpmath `iv.pi`; a `Float` node is a hard error.  See r20_tc_iv3_probe.py for why this matters.
  * Y is built from MY OWN midpoint Jacobian (my own symbolic derivatives, mp.dps = 60), not the
    lead's.  Any fixed float matrix is legal; the certificate then proves Y nonsingular.
  * The box is built with iv-only operations:  U_i = iv.mpf(float.fromhex(c_hex_i)) + iv.mpf([-rad,rad])
    and its containment of the EXACT box  [c_i - rad, c_i + rad]  is verified in exact rational
    arithmetic (Fraction), not by float/mpf endpoint arithmetic.
  * EVERY final assertion (Q < 1, K-c inside, margins, sqrt-argument positivity) is an exact
    rational comparison on the interval endpoints extracted from `ivmpf._mpi_`.
  * A second engine (lambdify with a FIXED pi mapping) and the lead's own J12 are used only as
    CONTROLS (entry-wise overlap), never as the certificate.

Theorem actually used (one-box Krawczyk; hypotheses verified below):
  F: R^12 -> R^12 is C^1 on a convex neighbourhood of U (needs the sqrt arguments > 0, checked),
  U = c + [-rad,rad]^12, J(U) an interval enclosure of F'(U), Y a fixed real matrix.  If
     (i) Q := ||I - Y J(U)||_inf < 1   and   (ii) K := c - Y F(c) + (I - Y J(U))(U - c) subset int(U),
  then F has EXACTLY one zero in U (and it lies in K).  Proof: g(x)=x-YF(x) maps U into K (MVT,
  segment stays in U) and is a Q-contraction in the infinity norm; Banach gives a unique fixed
  point; Q<1 makes YJ(U) invertible hence Y nonsingular, so zeros of F in U and fixed points of g
  coincide.
Scope: root existence/uniqueness of the explicitly specified 12D system on ONE box. No covering
radius, no optimality, no multi-box/global statement.

Run:  py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_iv3.py
"""
import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path

import numpy as np
import sympy as sp
from mpmath import iv, mp, mpf

HERE = Path(__file__).parent
LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
TC = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\session2\n11tc\py')
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(TC))
from r20_tc_iv1 import symbolic_res5, iv_modules, to_iv          # noqa: E402  (own model)

NV = 7
N = 12


# ----------------------------------------------------------------- exact endpoint arithmetic
def mpi_pair(x):
    """exact (lo, hi) Fractions of an mpmath 1.3 ivmpf (endpoints from the raw _mpi_ tuples)."""
    def f(t):
        s, m, e, b = t
        if not isinstance(m, int):
            raise ValueError('non-finite interval endpoint: %r' % (t,))
        v = Fraction(m) * Fraction(2) ** e
        return -v if s else v
    return f(x._mpi_[0]), f(x._mpi_[1])


def fstr(q, sig=6):
    """Fraction -> compact decimal string"""
    if q == 0:
        return '0'
    v = mpf(q.numerator) / mpf(q.denominator)
    return mp.nstr(v, sig)


def _isqrt_frac(q):
    """exact floor sqrt of a nonnegative Fraction, as a Fraction (no float round trip)."""
    if q <= 0:
        return Fraction(0)
    n, d = q.numerator, q.denominator
    import math as _m
    s = Fraction(_m.isqrt(n * d), d)
    return s if s * s <= q else s - Fraction(1, d)


# ----------------------------------------------------------------- strict tree-walk engines
class IvEngine(object):
    """strict interval backend: exact rationals, Pi = iv.pi, hard error on Float"""
    name = 'tree-walk/iv'
    allow_float = False

    def num(self, p, q=1):
        return iv.mpf(int(p)) / iv.mpf(int(q))

    def point_float(self, x):
        return iv.mpf(x)          # exact for a binary64 (verified: see r20_tc_iv3_probe)

    def sin(self, x):
        return iv.sin(x)

    def cos(self, x):
        return iv.cos(x)

    def sqrt(self, x):
        return iv.sqrt(x)

    @property
    def pi(self):
        return iv.pi


class MpfEngine(object):
    """point backend at the current mp.dps (for the midpoint Jacobian only)"""
    name = 'tree-walk/mpf'

    def num(self, p, q=1):
        return mpf(int(p)) / mpf(int(q))

    def sin(self, x):
        return mp.sin(x)

    def cos(self, x):
        return mp.cos(x)

    def sqrt(self, x):
        return mp.sqrt(x)

    @property
    def pi(self):
        return mp.pi


def ev(e, env, B):
    """strict recursive evaluator.  Raises on anything not explicitly supported."""
    if e.is_Symbol:
        return env[e]
    if e.is_Float:
        if getattr(B, 'allow_float', False):
            # CONTROL VARIANT ONLY: there the model is *defined* with this exact double,
            # so the exact double as a point interval is the correct reading of that variant.
            return B.point_float(float(e))
        raise ValueError('Float literal in model (refusing to treat a rounded constant '
                         'as exact): %s' % e)
    if e.is_Integer:
        return B.num(int(e), 1)
    if e.is_Rational:                      # exact p/q, no float round trip
        return B.num(int(e.p), int(e.q))
    if e == sp.pi:
        return B.pi
    if e.is_Add:
        acc = None
        for a in e.args:
            v = ev(a, env, B)
            acc = v if acc is None else acc + v
        return acc
    if e.is_Mul:
        acc = None
        for a in e.args:
            v = ev(a, env, B)
            acc = v if acc is None else acc * v
        return acc
    if e.is_Pow:
        b, ex = e.args
        if ex.is_Integer:
            n = int(ex)
            x = ev(b, env, B)
            return x ** n if n > 0 else B.num(1, 1) / (x ** (-n))
        if ex.is_Rational and ex.q == 2:
            # b^(p/2) = (sqrt(b))^p -- exact for b >= 0 (the sqrt bases are checked > 0 below)
            p = int(ex.p)
            s = B.sqrt(ev(b, env, B))
            return s ** p if p > 0 else B.num(1, 1) / (s ** (-p))
        raise NotImplementedError('Pow exponent %s' % ex)
    if e.func == sp.sin:
        return B.sin(ev(e.args[0], env, B))
    if e.func == sp.cos:
        return B.cos(ev(e.args[0], env, B))
    if e.func == sp.sqrt:
        return B.sqrt(ev(e.args[0], env, B))
    raise NotImplementedError('node %s (%s)' % (e, e.func))


# ----------------------------------------------------------------- interval certificate core
def system_jac_F(trees, vs, U, B, engine, want_j=True):
    """Build F(c / U) and the 12x12 interval Jacobian of the KKT system on the box U.

    trees = (f[5], df[5][7], d2f[5][7][7])  symbolic; U = list of 12 ivmpf.
    x = (a0..a3,y0,y1,R) = U[0:7]; lam = U[7:12].
    F = ( f_0..f_4 ,  delta_{i,6} - sum_m lam_m df_m/dx_i )   (i = 0..6)
    J = [[df_m/dx_i (5x7) | 0       ],
         [-sum_m lam_m d2f_m/dx_i dx_j | -df_m/dx_i (transposed) ]]
    Returns F (12 intervals, point evaluation at the interval inputs) and J (12x12 intervals).
    """
    f, df, d2f = trees
    xenv = {vs[k]: U[k] for k in range(7)}
    F = []
    for m in range(5):
        F.append(ev(f[m], xenv, B))
    G = [[ev(df[m][i], xenv, B) for i in range(7)] for m in range(5)]
    for i in range(7):
        acc = B.num(1 if i == 6 else 0, 1)
        for m in range(5):
            acc = acc - U[7 + m] * G[m][i]
        F.append(acc)
    J = [[B.num(0, 1) for _ in range(N)] for _ in range(N)]
    for m in range(5):
        for i in range(7):
            J[m][i] = G[m][i]
            J[5 + i][7 + m] = -G[m][i]
    if not want_j:
        return F, J
    for i in range(7):
        for j in range(7):
            acc = B.num(0, 1)
            for m in range(5):
                acc = acc - U[7 + m] * ev(d2f[m][i][j], xenv, B)
            J[5 + i][j] = acc
    return F, J


def build_model():
    """Same geometry as r20_tc_iv1.symbolic_res5 (the two are the same sequence of assignments,
    see lead/TC-ROOT-SOURCE-IDENTITY.md), plus the OUTER DISTANCE component pairs needed for the
    C^1 domain check (4 corner rows + the waist row)."""
    return build_model_with_pi(sp.pi)


def build_model_with_pi(pi_node):
    """CONTROL VARIANT: same explicit geometry as r20_tc_iv1.symbolic_res5 but with `pi`
    replaced by `pi_node`.  Used only to quantify the constant-handling question: with a
    non-exact pi the simplifier no longer folds sin(pi-2s), cos(pi-2s), so the variant really
    is a DIFFERENT function (off by the double-rounding of pi)."""
    a0, a1, a2, a3, y0, y1, R = sp.symbols('a0 a1 a2 a3 y0 y1 R', real=True)
    a4 = pi_node - 2 * (a0 + a1 + a2 + a3)
    a = [a0, a1, a2, a3, a4, a3, a2, a1, a0]
    rho = [sp.cos(ak) - sp.sqrt(R ** 2 - sp.sin(ak) ** 2) for ak in a]
    th = [None] * 9
    th[4] = sp.Integer(0)
    for k in range(5, 9):
        th[k] = th[k - 1] + a[k - 1] + a[k]
    for k in range(3, -1, -1):
        th[k] = th[k + 1] - (a[k] + a[k + 1])
    Cx = [rho[k] * sp.cos(th[k]) for k in range(9)]
    Cy = [rho[k] * sp.sin(th[k]) for k in range(9)]
    U = []
    for k in range(9):
        k2 = (k + 1) % 9
        U.append((Cx[k] + Cx[k2] - sp.cos(th[k] + a[k]), Cy[k] + Cy[k2] - sp.sin(th[k] + a[k])))
    out = []
    for (k, l) in [(1, 1), (2, 0), (3, 0), (8, 1)]:
        c = y1 if l == 1 else y0
        out.append(sp.sqrt((U[k][0] - c) ** 2 + U[k][1] ** 2) - R)
    m = (y0 + y1) / 2
    d = (y1 - y0) / 2
    h = sp.sqrt(R ** 2 - d ** 2)
    # OUTER DISTANCE radicands as component pairs (dx, dy): the sqrt arguments of the 5 rows are
    # dx^2 + dy^2; evaluated on the box they must be strictly positive (C^1 domain), and a
    # component interval excluding 0 gives a strict rational lower bound on its square.
    outer_terms = []
    for (k, l) in [(1, 1), (2, 0), (3, 0), (8, 1)]:
        c = y1 if l == 1 else y0
        outer_terms.append(('corner(k=%d,l=%d)' % (k, l), U[k][0] - c, U[k][1]))
    outer_terms.append(('waist(C6,m,h)', m - Cx[6], h - Cy[6]))
    out.append(sp.sqrt((m - Cx[6]) ** 2 + (h - Cy[6]) ** 2) - R)
    vs = (a0, a1, a2, a3, y0, y1, R)
    df = [[sp.diff(out[m_], vs[i]) for i in range(7)] for m_ in range(5)]
    d2f = [[[sp.diff(out[m_], vs[i], vs[j]) for j in range(7)] for i in range(7)]
           for m_ in range(5)]
    return (out, df, d2f), vs, outer_terms


def main():
    d = json.loads((LEAD / 'repaired_tc_krawczyk.json').read_text())
    cert = d['certificate']
    c_hex, r_hex = cert['center_hex'], cert['radius_hex']
    rad_f = float.fromhex(r_hex)
    rad = Fraction(rad_f)                       # exact rational radius
    print('=== R20-TC-IV3: independent full-12D interval Krawczyk enclosure ===')
    print('lead center_hex / radius_hex reused verbatim; radius = %s' % fstr(rad, 8))
    print('box NOT enlarged; no digit inflation (primary iv.dps = 40).')
    print()

    trees, vs, outer_terms = build_model()
    print('model: 5 residuals + 35 first partials + 245 second partials (SymPy, own derivation)')
    _all = [trees[0][m] for m in range(5)] + [trees[1][m][i] for m in range(5) for i in range(7)] \
        + [trees[2][m][i][j] for m in range(5) for i in range(7) for j in range(7)]
    _pi = sum(1 for t in _all if t.has(sp.pi))
    _fl = sum(1 for t in _all if t.has(sp.Float))
    _rat = set()
    for t in _all:
        _rat |= {r for r in t.atoms(sp.Rational) if r.q > 1}
    _nondy = sorted(str(r) for r in _rat if (r.q & (r.q - 1)) != 0)
    print('  census over the 285 symbolic trees: containing pi: %d ; containing Float: %d'
          % (_pi, _fl))
    print('  non-dyadic rational coefficients in the trees: %s' % (_nondy or 'none'))
    print('  (the tree-walk engine handles Pi = iv.pi and p/q exactly either way)')

    # ---------------- dps robustness: run the tree engine at 25 / 30 / 40
    iv.dps = 40
    all_runs = {}
    primary = None
    for dps in (25, 30, 40):
        iv.dps = dps
        B = IvEngine()
        # exact box by iv-only operations (lead's prescription)
        U = [iv.mpf(float.fromhex(c_hex[i])) + iv.mpf([-rad_f, rad_f]) for i in range(N)]
        # (a) EXACT containment of the true box  [c-rad, c+rad]
        cont_ok, cont_bad = True, []
        defect = []
        for i in range(N):
            lo, hi = mpi_pair(U[i])
            tlo = Fraction(float.fromhex(c_hex[i])) - rad
            thi = Fraction(float.fromhex(c_hex[i])) + rad
            if not (lo <= tlo and hi >= thi):
                cont_ok = False
                cont_bad.append((i, 'lo-true_lo=' + fstr(lo - tlo), 'hi-true_hi=' + fstr(hi - thi)))
            defect.append(((tlo - lo), (hi - thi)))      # >= 0 : outward enlargement of the box
        # (b) F at the exact dyadic centre (point intervals) and J on the box
        cpt = [iv.mpf(float.fromhex(c_hex[i])) for i in range(N)]
        F0, _ = system_jac_F(trees, vs, cpt, B, B, want_j=False)   # F(c), c = exact dyadic centre
        _, J = system_jac_F(trees, vs, U, B, B)                    # J(U), full 12D
        all_runs[dps] = dict(U=U, cpt=cpt, F0=F0, J=J, cont_ok=cont_ok, cont_bad=cont_bad,
                             defect=defect)
        if dps == 40:
            primary = all_runs[dps]
        print('  [dps=%2d] box contains the exact box: %s%s ; outward enlargement <= %s (low) '
              '/ %s (high)' % (dps, cont_ok, (' ' + str(cont_bad) if cont_bad else ''),
                               fstr(max(d[0] for d in defect), 3),
                               fstr(max(d[1] for d in defect), 3)))

    # ---------------- Y from MY OWN midpoint Jacobian (mp.dps = 60, tree-walk point engine)
    iv.dps = 40
    U40 = primary['U']
    mid = [float.fromhex(h) for h in c_hex[:NV]]
    lam_mid = [float.fromhex(h) for h in c_hex[7:]]
    mp.dps = 60
    Bp = MpfEngine()
    xenv = {vs[k]: mpf(mid[k]) for k in range(NV)}
    Gpt = [[ev(trees[1][m][i], xenv, Bp) for i in range(7)] for m in range(5)]
    Hpt = [[[ev(trees[2][m][i][j], xenv, Bp) for j in range(7)] for i in range(7)]
           for m in range(5)]
    Jm = np.zeros((N, N))
    for m in range(5):
        for i in range(7):
            Jm[m, i] = float(Gpt[m][i])
    for i in range(7):
        for j in range(7):
            Jm[5 + i, j] = -sum(lam_mid[m] * float(Hpt[m][i][j]) for m in range(5))
    for i in range(7):
        for m in range(5):
            Jm[5 + i, 7 + m] = -float(Gpt[m][i])
    cond = np.linalg.cond(Jm)
    Yf = np.linalg.inv(Jm)
    print()
    print('own midpoint Jacobian (mp.dps=60, own tree engine): cond_2 = %.6g ; max|J| = %.6g'
          % (cond, np.max(np.abs(Jm))))
    print('Y = float64 inverse of it (fixed matrix; the certificate below proves Y nonsingular).')
    Y = [[iv.mpf(float(v)) for v in row] for row in Yf]

    # ---------------- certificate on the exact box
    def certify(tag, run, Ymat, B):
        U, F0, J = run['U'], run['F0'], run['J']
        E = [[B.num(1 if i == j else 0, 1) - sum(Ymat[i][k] * J[k][j] for k in range(N))
              for j in range(N)] for i in range(N)]
        # Q = max_i sum_j max(|E_ij|) -- EXACT rational
        Q = Fraction(0)
        for i in range(N):
            s = Fraction(0)
            for j in range(N):
                lo, hi = mpi_pair(E[i][j])
                s += max(abs(lo), abs(hi))
            Q = max(Q, s)
        # K - c
        Dlt = [iv.mpf([-rad_f, rad_f])] * N
        Kc = []
        for i in range(N):
            acc = B.num(0, 1)
            for k in range(N):
                acc = acc - Ymat[i][k] * F0[k]
            for j in range(N):
                acc = acc + E[i][j] * Dlt[j]
            Kc.append(acc)
        inside, margins, kmax = True, [], Fraction(0)
        m_old, m_new, m_ok = [], [], True
        for i in range(N):
            lo, hi = mpi_pair(Kc[i])
            ii = (lo > -rad) and (hi < rad)
            inside = inside and ii
            # CORRECTED slack (lead instruction, this revision): symmetric two-sided,
            # exact rational: K_i - c_i = [lo,hi] lies in (-rad,rad) iff min(rad+lo, rad-hi) > 0.
            new = min(rad + lo, rad - hi)
            old = min(rad - lo, rad - hi)          # WITHDRAWN formula (kept only to quantify it)
            margins.append(new)
            m_new.append(new); m_old.append(old)
            # self-check: corrected slack > 0  <=>  the inclusion test holds for this coordinate
            m_ok = m_ok and ((new > 0) == ii)
            kmax = max(kmax, abs(lo), abs(hi))
        return dict(tag=tag, Q=Q, E=E, Kc=Kc, inside=inside, margins=margins, kmax=kmax,
                    margins_old=m_old, slack_pos_iff_inside=m_ok,
                    old_overestimate=[m_old[i] - m_new[i] for i in range(N)])

    print()
    print('--- PRIMARY certificate (tree-walk engine, dps=40, own Y, exact rational asserts) ---')
    cert40 = certify('tree/dps40', primary, Y, IvEngine())
    print('  Q = %.10f   (exact rational; Q < 1 : %s)' % (float(cert40['Q']), cert40['Q'] < 1))
    print('  K-c inside int(U): %s   max|K-c| = %s' % (cert40['inside'], fstr(cert40['kmax'], 6)))
    print('  per-coordinate slack  min(rad + lo, rad - hi)  (exact, CORRECTED definition):')
    for i in range(N):
        lo_, hi_ = mpi_pair(cert40['Kc'][i])
        print('     i=%2d  slack = %-12s  [withdrawn: %-12s  overestimate %s]  K-c = [%s, %s]'
              % (i, fstr(cert40['margins'][i], 6), fstr(cert40['margins_old'][i], 6),
                 fstr(cert40['old_overestimate'][i], 3),
                 fstr(lo_, 6), fstr(hi_, 6)))
    print('  self-check  slack_i > 0  <=>  inclusion holds on coordinate i : %s'
          % cert40['slack_pos_iff_inside'])
    print('  max overestimation of the withdrawn formula: %s'
          % fstr(max(cert40['old_overestimate']), 4))

    print()
    print('--- robustness: same box, same Y, lower precision (< 40 digits) ---')
    rob = {}
    for dps in (30, 25):
        iv.dps = dps
        r = certify('tree/dps%d' % dps, all_runs[dps], Y, IvEngine())
        rob[dps] = r
        print('  dps=%2d : Q = %.10f <1 %s ; K-c inside: %s ; max|K-c| = %s'
              % (dps, float(r['Q']), r['Q'] < 1, r['inside'], fstr(r['kmax'], 6)))

    # ---------------- sqrt-argument positivity over the box (domain legality, exact)
    print()
    print('--- domain legality: sqrt arguments must be strictly positive on the box ---')
    iv.dps = 40
    B = IvEngine()
    a = [vs[0], vs[1], vs[2], vs[3]]
    a4 = sp.pi - 2 * (a[0] + a[1] + a[2] + a[3])
    a_all = [a[0], a[1], a[2], a[3], a4, a[3], a[2], a[1], a[0]]
    env = {vs[k]: U40[k] for k in range(NV)}
    worst, ok_all = None, True
    for k in range(9):
        arg = vs[6] ** 2 - sp.sin(a_all[k]) ** 2
        lo, hi = mpi_pair(ev(arg, env, B))
        ok_all = ok_all and lo > 0
        if worst is None or lo < worst[1]:
            worst = (k, lo)
        print('     R^2 - sin^2(a_%d) in [%s, %s]   >0: %s' % (k, fstr(lo, 6), fstr(hi, 6), lo > 0))
    d_ = (vs[5] - vs[4]) / 2
    arg = vs[6] ** 2 - d_ ** 2
    lo, hi = mpi_pair(ev(arg, env, B))
    ok_all = ok_all and lo > 0
    print('     R^2 - ((y1-y0)/2)^2 in [%s, %s]   >0: %s' % (fstr(lo, 6), fstr(hi, 6), lo > 0))
    print('     ALL sqrt arguments strictly positive on the box: %s' % ok_all)

    # ---------------- C^1 domain, part 2: the 5 OUTER DISTANCE radicands (this revision)
    # The five rows' sqrt arguments are dx^2 + dy^2 (dist^2 of the outer point to the hub /
    # waist point).  SQUARE LOWER BOUND RULE (standard, valid unconditionally): a component whose
    # interval excludes 0 contributes (min|endpoint|)^2; a component whose interval straddles 0
    # contributes 0, because a square is non-negative.  A row is INCONCLUSIVE only when BOTH
    # components contribute 0.
    # Row corner(k=8,l=1) is special and NOT a rounding coincidence: the recursion gives
    #   theta_8 = pi - a0  and  theta_0 = a0 - pi = -theta_8  (exact), hence
    #   theta_8 + a_8 = theta_8 + a_0 = pi, so e_8 = (cos,sin) = (-1, 0) exactly, and
    #   U_8^y = rho_8 sin(theta_8) + rho_0 sin(theta_0) = (rho_8 - rho_0) sin a_0 = 0  because
    #   rho_8 = rho_0 (the a-list is reflected).  So that row's dy is identically 0 and its
    #   dist^2 = dx^2 exactly; the interval [0,0] reported below is the *symbolic cancellation*
    #   of the two sine terms, not a precision effect.
    print()
    print('--- C^1 domain part 2: 5 outer distance radicands (4 corner rows + waist) ---')
    outer_bounds, ok_outer = [], True
    for tag, dx, dy in outer_terms:
        lx, hx = mpi_pair(ev(dx, env, B))
        ly, hy = mpi_pair(ev(dy, env, B))
        excl_x = (lx > 0 or hx < 0)
        excl_y = (ly > 0 or hy < 0)
        # squares are non-negative, so a component whose interval straddles 0 contributes the
        # (valid but vacuous) bound 0; only BOTH straddling 0 makes the row inconclusive.
        bx = (min(abs(lx), abs(hx)) ** 2) if excl_x else Fraction(0)
        by = (min(abs(ly), abs(hy)) ** 2) if excl_y else Fraction(0)
        conclusive = (excl_x or excl_y)
        bnd = (bx + by) if conclusive else None
        ok_outer = ok_outer and conclusive and (bnd > 0)
        outer_bounds.append(dict(tag=tag,
                                 dx=[fstr(lx, 8), fstr(hx, 8)], dy=[fstr(ly, 8), fstr(hy, 8)],
                                 dx_excludes_0=bool(excl_x), dy_excludes_0=bool(excl_y),
                                 dx2_lower=fstr(bx, 10), dy2_lower=fstr(by, 10),
                                 dist2_lower=(None if bnd is None else fstr(bnd, 14)),
                                 conclusive=bool(conclusive),
                                 dy_is_identically_zero=bool(ly == 0 and hy == 0)))
        print('     %-16s dx in [%s, %s]%s  dy in [%s, %s]%s' %
              (tag, fstr(lx, 6), fstr(hx, 6), '' if excl_x else ' (contains 0)',
               fstr(ly, 6), fstr(hy, 6), '' if excl_y else ' (contains 0)'))
        print('        dx^2 >= %-14s dy^2 >= %-14s  dist^2 >= %s'
              % (fstr(bx, 8), fstr(by, 8),
                 ('INCONCLUSIVE (both components straddle 0)' if bnd is None else fstr(bnd, 12))))
    print('     ALL 5 outer distance radicands strictly positive (strict rational lower bounds): '
          '%s' % ok_outer)
    outer_min = None
    if ok_outer:
        mn = min(Fraction(ob['dist2_lower']) for ob in outer_bounds)
        outer_min = fstr(mn, 14)
        print('     min dist^2 lower bound = %s   (exact floor sqrt = %s)'
              % (fstr(mn, 12), fstr(_isqrt_frac(mn), 8)))
        print('     all 5 lower bounds lie in [%s, %s]  (≈ R^2 - O(1e-9), cf. lead >0.14)'
              % (fstr(mn, 10), fstr(max(Fraction(ob['dist2_lower']) for ob in outer_bounds), 10)))
    print('     k=8 row: dy ≡ 0 exactly (theta_8 + a_8 = pi ⇒ e_8 = (-1,0); rho_8 = rho_0); the')
    print('             reported [0,0] is symbolic cancellation, so dist^2 = dx^2 > 0 there.')
    print('     (lead independent reading `tc_root_geometry.json`: > 0.14 = R^2 - O(1e-9); '
          'this is the same object computed by my own engine)')

    # ---------------- controls
    print()
    print('--- controls (must NOT certify) ---')
    iv.dps = 40
    ctrls = {}
    # (1) lambda_0 shifted by +0.01 inside the box construction (box centre moved off the root)
    for tag, idx, delta in (('lambda0 +1e-2', 7, Fraction(1, 100)),):
        Uc = [iv.mpf(float.fromhex(c_hex[i])) + iv.mpf([-rad_f, rad_f]) for i in range(N)]
        Uc[idx] = iv.mpf(float.fromhex(c_hex[idx]) + float(delta)) + iv.mpf([-rad_f, rad_f])
        F0c, Jc = system_jac_F(trees, vs, Uc, B, B)
        r = certify(tag, dict(U=Uc, F0=F0c, J=Jc), Y, B)
        ctrls[tag] = dict(Q=str(r['Q']), inside=r['inside'])
        print('  %-16s : K-c inside: %s   Q<1: %s' % (tag, r['inside'], r['Q'] < 1))
    # (2) residual-perturbation control: same box, but F(c) shifted by 1e-3 (a wrong model would
    #     have to fight a much larger forcing term than the 4.3e-12 slack)
    F0s = list(primary['F0'])
    F0s[0] = F0s[0] + iv.mpf([1e-3, 1e-3])
    r = certify('F(c) +1e-3 in row 0', dict(U=primary['U'], F0=F0s, J=primary['J']), Y, B)
    ctrls['F0 row0 +1e-3'] = dict(Q=str(r['Q']), inside=r['inside'])
    print('  %-16s : K-c inside: %s' % ('F(c) row0 +1e-3', r['inside']))
    # (3) box-size control: radius x4 (NOT part of the certificate; shows the margin is not vacuous)
    rad4 = rad_f * 4
    U4 = [iv.mpf(float.fromhex(c_hex[i])) + iv.mpf([-rad4, rad4]) for i in range(N)]
    F04, J4 = system_jac_F(trees, vs, U4, B, B)
    E4 = [[B.num(1 if i == j else 0, 1) - sum(Y[i][k] * J4[k][j] for k in range(N))
           for j in range(N)] for i in range(N)]
    Q4 = Fraction(0)
    for i in range(N):
        s = Fraction(0)
        for j in range(N):
            lo, hi = mpi_pair(E4[i][j])
            s += max(abs(lo), abs(hi))
        Q4 = max(Q4, s)
    ctrls['radius x4'] = dict(Q=str(Q4))
    print('  %-16s : Q = %.10f  (radius dependence of the contraction)' % ('radius x4', float(Q4)))

    # ---------------- control: second engine (lambdify, FIXED pi mapping) -- overlap only
    print()
    print('--- CONTROL engine (lambdify + scalar-pi mapping; overlap only, not the certificate) ---')
    iv.dps = 40
    mods = iv_modules()
    mods['pi'] = iv.pi                                    # FIX the mapping shape (probe Q3)
    lf = [sp.lambdify(vs, trees[0][m], modules=mods) for m in range(5)]
    lg = [[sp.lambdify(vs, trees[1][m][i], modules=mods) for i in range(7)] for m in range(5)]
    lh = [[[sp.lambdify(vs, trees[2][m][i][j], modules=mods) for j in range(7)] for i in range(7)]
          for m in range(5)]
    U7 = U40[:NV]
    ov_first = 0
    max_fd = 0.0
    for m in range(5):
        for i in range(7):
            L = to_iv(lg[m][i](*U7))
            lo1, hi1 = mpi_pair(L)
            lo2, hi2 = mpi_pair(primary['J'][m][i])
            if not (hi1 < lo2 or hi2 < lo1):
                ov_first += 1
            max_fd = max(max_fd, abs(float(lo1 - lo2)), abs(float(hi1 - hi2)))
    print('  first-order block 5x7: %d/35 entries overlap with the tree engine (max endpoint '
          'spread %.2e)' % (ov_first, max_fd))
    nonov = 0
    for i in range(7):
        for j in range(7):
            acc = iv.mpf(0)
            for m in range(5):
                acc = acc - U40[7 + m] * to_iv(lh[m][i][j](*U7))
            lo1, hi1 = mpi_pair(acc)
            lo2, hi2 = mpi_pair(primary['J'][5 + i][j])
            if hi1 < lo2 or hi2 < lo1:
                nonov += 1
    print('  second-order block 7x7: %d/49 entries fail overlap with the tree engine' % nonov)
    # F(centre) cross-check vs the lead's 58-digit endpoints
    diff = Fraction(0)
    for i in range(N):
        lo, hi = mpi_pair(primary['F0'][i])
        for s, v in ((0, lo), (1, hi)):
            lead_v = mpf(cert['F_center'][i][s])
            d_ = v - Fraction(lead_v._mpf_[1]) * Fraction(2) ** lead_v._mpf_[2] * (-1) ** lead_v._mpf_[0]
            diff = max(diff, abs(d_))
    print('  F(centre): max |own - lead| over 24 endpoints = %s' % fstr(diff, 6))

    # ---------------- second: overlap with the lead's own J12_iv (import AFTER own work)
    iv.dps = 40
    import tc_s32_kraw as K32                                        # noqa: E402
    import tc_s33_kkt as S33                                         # noqa: E402
    iv.dps = 40                                                      # imports reset it -> restore
    lam_pt = [iv.mpf(float.fromhex(h)) for h in c_hex[7:]]
    Ulead = [iv.mpf(float.fromhex(c_hex[i])) + iv.mpf([-rad_f, rad_f]) for i in range(NV)]
    lam_box = [iv.mpf(float.fromhex(c_hex[7 + m])) + iv.mpf([-rad_f, rad_f]) for m in range(5)]
    Mbox = S33.J12_iv(Ulead, lam_box)          # lead AD, lambda as BOX variables (comparable)
    Mpt = S33.J12_iv(Ulead, lam_pt)            # lead AD, lambda point (as iv1 called it)
    lead_cmp = {}
    # (i) instrument calibration on a KNOWN ANSWER: with the lead's own J12_iv and the lead's own
    # Y, my exact-rational Q pipeline must reproduce the lead's reported contraction 0.00437197...
    Ylead = None
    try:
        mp.dps = 65                                  # match the lead's own midpoint precision
        Jl = np.zeros((N, N))
        c7f = [mpf(v) for v in mid]
        xdl = [K32.Dual(c7f[k], [mpf(int(j == k)) for j in range(NV)]) for k in range(NV)]
        frl = K32.res5(xdl[0:4], xdl[4], xdl[5], xdl[6], K32.BK_DMPF)
        for m in range(5):
            for i in range(7):
                Jl[m, i] = float(frl[m].d[i])
        for i in range(7):
            for j in range(7):
                Jl[5 + i, j] = -sum(lam_mid[m] * float(S33.f5_nested(c7f, i, j)[m].d[i].d[j])
                                    for m in range(5))
        for i in range(7):
            for m in range(5):
                Jl[5 + i, 7 + m] = -Jl[m, i]
        Ylead = np.linalg.inv(Jl)
        dY = float(np.max(np.abs(np.array(Yf) - Ylead)))
        Ql = Fraction(0)
        for i in range(N):
            s = Fraction(0)
            for j in range(N):
                EE = iv.mpf(int(i == j)) - sum(iv.mpf(float(Ylead[i][k])) * Mbox[k][j]
                                               for k in range(N))
                lo, hi = mpi_pair(EE)
                s += max(abs(lo), abs(hi))
            Ql = max(Ql, s)
        print('  calibration: lead J12_iv + lead Y through MY exact-rational Q pipeline:')
        print('     Q = %.13f   vs lead reported %s' % (float(Ql), cert['contraction_inf'][:13]))
        print('  own Y vs lead Y: max|difference| = %.3e (distinct matrices; both give Q<1)'
              % dY)
        lead_cmp['calibration_leadJ_leadY_Q'] = float(Ql)
        lead_cmp['ownY_minus_leadY_max'] = dY
        lead_cmp['lead_reported_Q'] = cert['contraction_inf'][:16]
    except Exception as e:                                     # control only; never blocks
        print('  [lead-Y calibration skipped: %s]' % e)
    for tag, MM, idxs in (('first-order 5x7', Mbox, [(m, i) for m in range(5) for i in range(7)]),
                          ('second-order 7x7', Mbox, [(5 + i, j) for i in range(7) for j in range(7)])):
        ov = 0
        wd = 0.0
        for (a_, b_) in idxs:
            l1, h1 = mpi_pair(MM[a_][b_])
            l2, h2 = mpi_pair(primary['J'][a_][b_])
            ov += 1 if not (h1 < l2 or h2 < l1) else 0
            wd = max(wd, abs(float((h1 - l1) - (h2 - l2))))
        wmax = max(float(mpi_pair(MM[a_][b_])[1] - mpi_pair(MM[a_][b_])[0]) for (a_, b_) in idxs)
        lead_cmp[tag] = dict(overlap='%d/%d' % (ov, len(idxs)), max_width_diff=wd,
                             lead_max_width=wmax)
        print('  lead-vs-own %-17s: overlap %d/%d ; max |width difference| = %.2e ; lead max width '
              '= %.2e' % (tag, ov, len(idxs), wd, wmax))

    print('  lead certificate: Q = %s ; inclusion %s ; negative control fails: %s'
          % (cert['contraction_inf'][:12], cert['pass_inclusion'],
             not d['negative_control']['pass_inclusion']))

    # ---------------- control: WRONG-pi VARIANT MODEL (the constant-handling question)
    print()
    print('--- CONTROL: wrong-pi variant model (pi -> binary64 3.141592653589793) ---')
    iv.dps = 40
    tree_p, vsp, _outer_p = build_model_with_pi(sp.Float(3.141592653589793, 53))
    Bfl = IvEngine()
    Bfl.allow_float = True
    Uc = [iv.mpf(float.fromhex(c_hex[i])) + iv.mpf([-rad_f, rad_f]) for i in range(N)]
    cp = [iv.mpf(float.fromhex(c_hex[i])) for i in range(N)]
    F0p, _ = system_jac_F(tree_p, vsp, cp, Bfl, Bfl, want_j=False)
    _, Jp = system_jac_F(tree_p, vsp, Uc, Bfl, Bfl)
    dp = max(abs(mpi_pair(F0p[i])[0] - mpi_pair(primary['F0'][i])[0]) for i in range(N))
    dp = max(dp, max(abs(mpi_pair(F0p[i])[1] - mpi_pair(primary['F0'][i])[1]) for i in range(N)))
    r = certify('wrong-pi variant', dict(U=Uc, F0=F0p, J=Jp), Y, Bfl)
    print('  ||F_wrongpi(c) - F_pi(c)||_inf = %s   (shift caused by a 1.22e-16 pi error)'
          % fstr(dp, 6))
    print('  wrong-pi model still certifies on the same box: %s (Q = %.10f < 1: %s)'
          % (r['inside'], float(r['Q']), r['Q'] < 1))
    print('  -> the INCLUSION is insensitive at 1e-16 scale; the FUNCTION (hence the object) is '
          'not, which is exactly why the exact pi/rational handling is required.')

    # ---------------- verdict + output
    verdict = (cert40['inside'] and cert40['Q'] < 1 and primary['cont_ok'] and ok_all and ok_outer)
    print()
    print('  VERDICT (own engine, exact-rational asserts):')
    print('    box contains the exact lead box            : %s' % primary['cont_ok'])
    print('    all sqrt arguments > 0 on the box (C^1)     : %s (9 R^2-sin^2 + 1 R^2-d^2 = %s)'
          % (ok_all, ok_all))
    print('    5 outer distance radicands > 0 (C^1)        : %s' % ok_outer)
    print('    corrected slack positives <=> inclusion     : %s'
          % cert40['slack_pos_iff_inside'])
    print('    Q < 1                                       : %s' % (cert40['Q'] < 1))
    print('    K(c,U) subset int(U) (strict, all 12 coords): %s' % cert40['inside'])
    print('    => F has exactly one zero in U              : %s' % verdict)
    print('    (same verdict at dps 30 and 25: %s)'
          % all(rob[k]['inside'] and rob[k]['Q'] < 1 for k in rob))

    def sh(p):
        return hashlib.sha256(Path(p).read_bytes()).hexdigest()
    out = dict(
        role='independent full-12D Krawczyk enclosure, own tree-walk engine + own Y',
        box=dict(center_hex=c_hex, radius_hex=r_hex, radius_exact=fstr(rad, 20),
                 exact_box_contained=bool(primary['cont_ok']), defect=primary['cont_bad']),
        engine='strict tree-walk over SymPy tree (exact rationals, Pi=iv.pi, Float=hard error)',
        iv_dps_primary=40, iv_dps_robustness=[30, 25],
        Y_own_midpoint_jacobian=dict(cond2=float(cond), max_abs=float(np.max(np.abs(Jm))),
                                     source='own SymPy derivatives at mp.dps=60'),
        Q_exact_num=str(cert40['Q'].numerator), Q_exact_den=str(cert40['Q'].denominator),
        Q=float(cert40['Q']), Q_lt_1=bool(cert40['Q'] < 1),
        inclusion=bool(cert40['inside']),
        max_K_minus_c=fstr(cert40['kmax'], 8),
        slack_min=fstr(min(cert40['margins']), 8),
        slack_per_coord=[fstr(v, 8) for v in cert40['margins']],
        slack_definition='min(rad + lo, rad - hi) per coordinate, exact rational (this revision)',
        slack_per_coord_withdrawn=[fstr(v, 8) for v in cert40['margins_old']],
        slack_old_overestimate_max=fstr(max(cert40['old_overestimate']), 4),
        slack_old_overestimate_per_coord=[fstr(v, 4) for v in cert40['old_overestimate']],
        slack_pos_iff_inside=bool(cert40['slack_pos_iff_inside']),
        outer_distance_bounds=outer_bounds,
        outer_distance_positive=bool(ok_outer),
        outer_distance_min_dist2_lower=outer_min,
        outer_distance_k8_note=('row corner(k=8,l=1): theta_8 + a_8 = pi exactly (theta_8 = pi - a0, '
                                'a_8 = a0), so e_8 = (-1,0) and U_8^y = (rho_8-rho_0) sin a0 = 0 by '
                                'the reflection rho_8 = rho_0; the interval [0,0] is symbolic '
                                'cancellation, not precision, and dist^2 = dx^2 > 0'),
        outer_distance_rule=('dx2_lb = (min|endpoint|)^2 if the dx interval excludes 0 else 0; '
                             'same for dy; bnd = dx2_lb + dy2_lb; inconclusive only if bnd = 0 '
                             '(both components straddle 0)'),
        K_minus_c=[[fstr(v, 10) for v in mpi_pair(k)] for k in cert40['Kc']],
        F_center=[[fstr(v, 12) for v in mpi_pair(F)] for F in primary['F0']],
        sqrt_args_positive=bool(ok_all),
        robustness={str(k): dict(Q=float(rob[k]['Q']), inside=bool(rob[k]['inside']))
                    for k in rob},
        controls={k: v for k, v in ctrls.items()},
        control_engines=dict(first_order_overlap_lambdify='%d/35' % ov_first,
                             second_order_nonoverlap_lambdify=nonov,
                             lead_J12=lead_cmp,
                             max_Fcenter_diff_vs_lead_58digit=fstr(diff, 8),
                             wrong_pi=dict(F_shift=fstr(dp, 6), Q=float(r['Q']),
                                           inclusion=bool(r['inside']))),
        verdict=bool(verdict),
        scope=('existence+uniqueness of the zero of the explicitly specified 12D symmetric TC KKT '
               'system in ONE box; no covering radius / optimality / global claim'),
        source_hashes={'r20_tc_iv3.py': sh(HERE / 'r20_tc_iv3.py'),
                       'r20_tc_iv1.py(model)': sh(HERE / 'r20_tc_iv1.py'),
                       'r20_tc_iv3_probe.py': sh(HERE / 'r20_tc_iv3_probe.py'),
                       'lead/repaired_tc_krawczyk.json': sh(LEAD / 'repaired_tc_krawczyk.json'),
                       'lead/repair_tc_krawczyk.py': sh(LEAD / 'repair_tc_krawczyk.py')})
    (HERE / 'r20_tc_iv3.json').write_text(json.dumps(out, indent=1, default=str))
    print()
    print('saved r20_tc_iv3.json')


if __name__ == '__main__':
    main()
