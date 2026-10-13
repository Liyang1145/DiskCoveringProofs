"""weights_interface.py -- IMPORT-SAFE interval weights for the exact 12D TC root box.

Consumer: r20-rigidity (Hessian-kernel / second-order work).  Owner: r20-stress.

This module is deliberately self-contained: it reads only
    ../lead/repaired_tc_krawczyk.json      (the Krawczyk box in exact dyadic hex)
and returns plain `mpmath.iv` objects.  It does NOT import the phase7 scripts, does NOT
print or write anything at import time, and does NOT convert anything to float/json.

    import sys; sys.path.insert(0, '<repo>/research-2026/team-current/r20-stress')
    import weights_interface as WI
    W = WI.physical_weights()          # dict of mpmath.iv  (see BELOW)
    lo, hi = WI.endpoints(W['s'])      # mpmath.mpf endpoints, never floats
    WI.positive(W['nu_gap'][0])        # -> True iff lo > 0  (an interval decision)

WHAT THE INTERVALS MEAN (caliber / scope -- quoted in any downstream use)
    Box: the lead Krawczyk box  X = prod_i [c_i - r, c_i + r],  r = 1.0e-9 (hex radius),
    in the chart variables u = (a0,a1,a2,a3,y0,y1,R, lam0..lam4), enclosing the unique
    exact root of the symmetric TC KKT system.  Every interval returned ENCLOSES the value
    at that exact root.  Conditional on (i) that box's existence certificate, (ii) lead
    TC-BOUNDARY-CHART-RANK (rank DB=5, chart), (iii) lead TC-TO-PHYSICAL-KKT-LIFT
    (exact stationarity + odd-9 lift).  Nothing here is a proof of (i)-(iii).

    mu_pin[i]        = -lambda_i  (i=0..4) orbit-representative multipliers of the five
                       GENUINE physical chord-circle pin residuals
                       (fan(1,H1), fan(2,H0), fan(3,H0), fan(8,H1), central C6).
    nu_gap[j]        = per-gap multipliers (j=0..8) from the odd-9 cyclic formula
                       nu_j = (1/2) sum_k (-1)^k w_{j-k mod 9},  w_j = v_j / a'_j,
                       v_j = sum over the NINE contacts of mu_c d f_c/d rho_j.
    nu_orbit[o]      = symmetric-space (orbit-summed) multipliers = the values the 12D
                       linear solve gives; o = {0,7},{1,6},{2,5},{3,4},{8}.
    c_k[o]           = conversion 4 y^2 / F_out > 0 (o = 5 orbit reps); face weight
                       mu_o * c_o is the weight of the FACE branch in the minimax family.
    face_weight[9]   = weights of the NINE active face branches gamma_f (orbit split:
                       paired faces get mu_o c_o / 2, self-reflected fan(8,H1) full).
    tie_weight[9]    = weights of the NINE active boundary-tie branches t_j(c)
                       (= the switch waist legs), = nu_j * (a_{R,j} + a_{R,j+1}) > 0.
    s, one_minus_s   = sum(face_weight), 1 - s.
    tie_total        = sum(tie_weight)  ==  1 - s  ANALYTICALLY (R-stationarity identity);
                       the interval only needs to CONTAIN it -- see the note below.

EXACT vs INTERVAL (do not over-read the interval):
    * The 18 weights are positive and sum to 1 AT THE EXACT ROOT by the lead's analytic
      lift:  sum(face_weight) + sum(tie_weight) = 1  and
      sum(face_weight_i) D gamma_i + sum(tie_weight_j) D t_j = 0  (in the centre
      coordinates, hence in any slice).  Those two statements are ANALYTIC (root
      stationarity + odd-9 invertibility + the conversion identity), NOT interval facts.
    * The INTERVAL content is exactly: each individual weight is > 0 (so the positive
      weights exist with the required support) and the branch factors are positive.
      The interval sum merely CONTAINS 1; it is not used as an equality.
    * INTERVAL INTERSECTION IS NOT EQUALITY (caliber warning, lead 2026-09-25): an interval
      "touching" a target value only gives compatibility.  In particular "the 9 face
      circumradii and 9 tie radii equal R" is ANALYTIC (root F=0 + chart + positive
      conversion: Fin=0 & Fout>0 & y!=0 => rho_face=R ; g=0 => t_j=R).  What the interval
      run certifies is the POSITIVITY of F_out, y!=0 and of the weights themselves.

Repro / self-test:  py -3 -B -X utf8 research-2026/team-current/r20-stress/weights_interface.py
"""
import json
from contextlib import contextmanager
from pathlib import Path

from mpmath import iv, mpf

_HERE = Path(__file__).resolve().parent
_LEAD_JSON = _HERE.parent / 'lead' / 'repaired_tc_krawczyk.json'

# labels ---------------------------------------------------------------
FACE_LABELS = ['fan(1,H1)', 'fan(6,H1)', 'fan(2,H0)', 'fan(5,H0)', 'fan(3,H0)',
               'fan(4,H0)', 'fan(8,H1)', 'central(C6)', 'central(C2)']
TIE_LABELS = ['gap%d' % j for j in range(9)]
ORBIT_LABELS = ['{0,7}', '{1,6}', '{2,5}', '{3,4}', '{8}']
ORBIT_OF_CONTACT = [0, 0, 1, 1, 2, 2, 3, 4, 4]          # face index -> orbit (mu index)
ORBIT_SIZE = [2, 2, 2, 1, 2]


@contextmanager
def _ivdps(n):
    old = iv.dps
    iv.dps = max(old, n)
    try:
        yield
    finally:
        iv.dps = old


def root_box(dps=35):
    """The lead Krawczyk box as a list of 12 mpmath.iv (exact dyadic centres)."""
    with _ivdps(dps):
        cd = json.loads(_LEAD_JSON.read_text(encoding='utf-8'))['certificate']
        rad = float.fromhex(cd['radius_hex'])
        cen = [float.fromhex(h) for h in cd['center_hex']]
        return [iv.mpf(c) + iv.mpf([-rad, rad]) for c in cen]


# ------------------------------------------------------------------ interval forward AD
class _IVD(object):
    """interval value + interval partials w.r.t. rho_0..rho_8"""
    __slots__ = ('v', 'd')

    def __init__(self, v, d):
        self.v = v
        self.d = d

    def __add__(self, o):
        if isinstance(o, _IVD):
            return _IVD(self.v + o.v, [a + b for a, b in zip(self.d, o.d)])
        return _IVD(self.v + o, list(self.d))
    __radd__ = __add__

    def __sub__(self, o):
        if isinstance(o, _IVD):
            return _IVD(self.v - o.v, [a - b for a, b in zip(self.d, o.d)])
        return _IVD(self.v - o, list(self.d))

    def __rsub__(self, o):
        return _IVD(o - self.v, [-a for a in self.d])

    def __mul__(self, o):
        if isinstance(o, _IVD):
            return _IVD(self.v * o.v, [a * o.v + self.v * b for a, b in zip(self.d, o.d)])
        return _IVD(self.v * o, [a * o for a in self.d])
    __rmul__ = __mul__

    def inv(self):
        w = 1 / self.v
        return _IVD(w, [-a * w * w for a in self.d])

    def __truediv__(self, o):
        if isinstance(o, _IVD):
            return self * o.inv()
        return _IVD(self.v / o, [a / o for a in self.d])

    def __rtruediv__(self, o):
        return o * self.inv()


_ALL_CONTACTS = [('fan', 1, 1), ('fan', 6, 1), ('fan', 2, 0), ('fan', 5, 0), ('fan', 3, 0),
                 ('fan', 4, 0), ('fan', 8, 1), ('central', 6, 0), ('central', 2, 0)]
_ZIV = None


def _compute(box, dps):
    """Everything on the box.  Returns iv objects (never floats/strings)."""
    global _ZIV
    with _ivdps(dps):
        _ZIV = iv.mpf(0)
        one = iv.mpf(1)
        nin = 9

        def cst(x):
            return _IVD(x, [_ZIV] * nin)

        def var(x, j):
            d = [_ZIV] * nin
            d[j] = one
            return _IVD(x, d)

        def isqrt(x):
            if not (mpf(x.v.a) > 0):
                raise ValueError('isqrt: non-positive argument interval')
            s = iv.sqrt(x.v)
            return _IVD(s, [a / (2 * s) for a in x.d])

        a04 = list(box[0:4])
        y0, y1, R = box[4], box[5], box[6]
        lam = list(box[7:12])
        a4 = iv.pi - 2 * (a04[0] + a04[1] + a04[2] + a04[3])
        A = [a04[0], a04[1], a04[2], a04[3], a4, a04[3], a04[2], a04[1], a04[0]]
        SIN = [iv.sin(a) for a in A]
        RHO = [iv.cos(A[k]) - iv.sqrt(R * R - SIN[k] * SIN[k]) for k in range(9)]
        TH = [iv.mpf(0)] * 9
        for k in range(5, 9):
            TH[k] = TH[k - 1] + A[k - 1] + A[k]
        for k in range(3, -1, -1):
            TH[k] = TH[k + 1] - (A[k] + A[k + 1])

        CX = [var(RHO[j], j) * cst(iv.cos(TH[j])) for j in range(9)]
        CY = [var(RHO[j], j) * cst(iv.sin(TH[j])) for j in range(9)]
        HUB = [(cst(y0), cst(_ZIV)), (cst(y1), cst(_ZIV))]
        Rc = cst(R)
        HALF, QUARTER, ZERO = cst(iv.mpf('0.5')), cst(iv.mpf('0.25')), cst(_ZIV)

        out = []
        for (kind, k, l) in _ALL_CONTACTS:
            if kind == 'fan':
                P, Q, T = (CX[k], CY[k]), (CX[(k + 1) % 9], CY[(k + 1) % 9]), HUB[l]
            else:
                P, Q, T = HUB[0], HUB[1], (CX[k], CY[k])
            dx, dy = Q[0] - P[0], Q[1] - P[1]
            c2 = dx * dx + dy * dy
            c = isqrt(c2)
            Mx, My = (P[0] + Q[0]) * HALF, (P[1] + Q[1]) * HALF
            nx, ny = (ZERO - dy) / c, dx / c
            hh = isqrt(Rc * Rc - c2 * QUARTER)
            sgn_iv = (T[0] - Mx) * nx + (T[1] - My) * ny
            if mpf(sgn_iv.v.a) > 0:
                sg = iv.mpf(1)
            elif mpf(sgn_iv.v.b) < 0:
                sg = iv.mpf(-1)
            else:
                raise ValueError('pin side not decidable on the box for %s %s %s' % (kind, k, l))
            Ux, Uy = Mx + hh * sg * nx, My + hh * sg * ny
            Bx, By = Mx - hh * sg * nx, My - hh * sg * ny
            gx, gy = Ux - T[0], Uy - T[1]
            L = isqrt(gx * gx + gy * gy)
            f = L - Rc
            Fout = (Bx - T[0]) * (Bx - T[0]) + (By - T[1]) * (By - T[1]) - Rc * Rc
            out.append(dict(kind=kind, k=k, l=l, f=f, y=sgn_iv, hh=hh, Fout=Fout,
                            partials=[f.d[j] for j in range(9)]))

        MU = [-lam[i] for i in range(5)]
        v = [_ZIV] * 9
        for idx in range(9):
            o = ORBIT_OF_CONTACT[idx]
            w_c = MU[o] / ORBIT_SIZE[o]
            for j in range(9):
                v[j] = v[j] + w_c * out[idx]['partials'][j]

        APRIME = [(1 - R * R - RHO[j] * RHO[j]) / (2 * RHO[j] * RHO[j] * SIN[j]) for j in range(9)]
        AR = [R / (RHO[j] * SIN[j]) for j in range(9)]
        w = [v[j] / APRIME[j] for j in range(9)]
        NU = [sum(((-1) ** k) * w[(j - k) % 9] for k in range(9)) / 2 for j in range(9)]

        CK = []
        for idx in (0, 2, 4, 6, 7):                      # 5 orbit-representative faces
            CK.append(4 * (out[idx]['y'].v * out[idx]['y'].v) / out[idx]['Fout'].v)

        FACE_ORBIT = [MU[i] * CK[i] for i in range(5)]
        FACE_W = [FACE_ORBIT[ORBIT_OF_CONTACT[i]] / ORBIT_SIZE[ORBIT_OF_CONTACT[i]]
                  for i in range(9)]
        TIE_W = [NU[j] * (AR[j] + AR[(j + 1) % 9]) for j in range(9)]
        S_FACE = sum(FACE_ORBIT)
        ONE_MINUS_S = 1 - S_FACE
        TIE_TOT = sum(TIE_W)
        NU_ORBIT = [2 * NU[0], 2 * NU[1], 2 * NU[2], 2 * NU[3], NU[8]]

        return dict(
            scope='intervals on the lead Krawczyk 12D TC root box; conditional on that box + '
                  'lead TC-BOUNDARY-CHART-RANK + TC-TO-PHYSICAL-KKT-LIFT; same object = genuine '
                  'physical chord-circle pin residuals; weights are intervals, sums are analytic',
            box=list(box), R=R, rho=RHO, theta=TH, a=A, a_prime=APRIME, a_R=AR,
            mu_pin=MU, nu_gap=NU, nu_orbit=NU_ORBIT, c_k=CK,
            face_weight_9=FACE_W, face_weight_orbit=FACE_ORBIT,
            face_labels=FACE_LABELS, tie_labels=TIE_LABELS, orbit_labels=ORBIT_LABELS,
            tie_weight=TIE_W, s=S_FACE, one_minus_s=ONE_MINUS_S, tie_total=TIE_TOT,
            v=v, w=w, f_residual=[c['f'].v for c in out], F_out=[c['Fout'].v for c in out],
            y_height=[c['y'].v for c in out],
            partials=[[c['partials'][j] for j in range(9)] for c in out],
            contact_labels=['%s(%d,%d)' % (c['kind'], c['k'], c['l']) for c in out],
        )


def physical_weights(box=None, dps=35):
    """Return the interval weights / multipliers (dict of mpmath.iv).

    box: optional list of 12 iv (defaults to the lead Krawczyk box).  dps: min working
    precision for the iv context (restored afterwards)."""
    if box is None:
        box = root_box(dps)
    return _compute(box, dps)


def radial_partials(box=None, dps=35):
    """[[d f_c / d rho_j]] (9x9 mpmath.iv) and the contact labels, same box/caliber.

    Row c is the GENUINE physical chord-circle pin residual of contact c (labels: the
    five orbit representatives are the ones carrying mu, the other four are their mirrors),
    column j is the radial coordinate rho_j (theta, hubs, R fixed).  This is the kernel
    input; use physical_weights() for the multipliers themselves.
    """
    if box is None:
        box = root_box(dps)
    d = _compute(box, dps)
    return d['partials'], d['contact_labels']


def endpoints(x):
    """(lo, hi) as mpmath.mpf -- deliberately NOT floats."""
    return mpf(x.a), mpf(x.b)


def positive(x):
    """True iff the interval is strictly positive."""
    return mpf(x.a) > 0


def summarize(W, digits=20):
    """Human-readable list of (name, lo, hi) strings; no file/JSON side effects."""
    from mpmath import nstr
    rows = []
    for i, x in enumerate(W['mu_pin']):
        rows.append(('mu_pin[%d]' % i, nstr(mpf(x.a), digits), nstr(mpf(x.b), digits)))
    for j, x in enumerate(W['nu_gap']):
        rows.append(('nu_gap[%d]' % j, nstr(mpf(x.a), digits), nstr(mpf(x.b), digits)))
    for i, x in enumerate(W['c_k']):
        rows.append(('c_k[%d]' % i, nstr(mpf(x.a), digits), nstr(mpf(x.b), digits)))
    for i, x in enumerate(W['face_weight_9']):
        rows.append(('face_w[%s]' % W['face_labels'][i], nstr(mpf(x.a), digits), nstr(mpf(x.b), digits)))
    for j, x in enumerate(W['tie_weight']):
        rows.append(('tie_w[%s]' % W['tie_labels'][j], nstr(mpf(x.a), digits), nstr(mpf(x.b), digits)))
    for nm in ('s', 'one_minus_s', 'tie_total'):
        x = W[nm]
        rows.append((nm, nstr(mpf(x.a), digits), nstr(mpf(x.b), digits)))
    return rows


def _selftest():
    import sys
    W = physical_weights()
    ok = True
    bad = []
    for nm in ('mu_pin', 'nu_gap', 'c_k', 'face_weight_9', 'tie_weight'):
        for i, x in enumerate(W[nm]):
            if not positive(x):
                ok = False
                bad.append('%s[%d] not positive' % (nm, i))
    if not positive(W['s']):
        ok = False
        bad.append('s not positive')
    if not positive(W['one_minus_s']):
        ok = False
        bad.append('1-s not positive')
    if not positive(W['tie_total']):
        ok = False
        bad.append('tie_total not positive')
    # cross-check against the recorded phase-7 evidence (same box, same object)
    ref = _HERE / 'out' / 'phase7_interval_cyclic_nu.json'
    dev = None
    if ref.exists():
        D = json.loads(ref.read_text(encoding='utf-8'))
        dev = max(abs(mpf(W['nu_gap'][j].a) - mpf(D['nu'][j][0])) for j in range(9))
        if mpf(D['one_minus_s'][0]) > mpf(W['one_minus_s'].b) or \
           mpf(D['one_minus_s'][1]) < mpf(W['one_minus_s'].a):
            ok = False
            bad.append('1-s interval does not overlap the phase-7 record')
    for nm, lo, hi in summarize(W, 18):
        print('%-26s [%s, %s]' % (nm, lo, hi))
    print()
    print('all weights strictly positive            :', ok)
    print('violations                              :', bad if bad else 'none')
    if dev is not None:
        print('nu_gap lower endpoints vs phase7 record : %.3e' % float(dev))
    print('analytic (not interval): sum(weights)=1 and sum w_i Dg_i=0 at the exact root')
    return 0 if ok else 1


if __name__ == '__main__':
    raise SystemExit(_selftest())
