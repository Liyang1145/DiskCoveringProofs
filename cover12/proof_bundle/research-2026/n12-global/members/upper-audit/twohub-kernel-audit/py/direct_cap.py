"""direct_cap.py  (member upper-audit/twohub-kernel-audit, 2026-09-26)

INDEPENDENT direct computation of the two-hub k=10 dual objects at the fixed hub
configuration (t1=t2=1/5, delta=604457/200000) and the exact rational weights of
evidence/rational_dual_worst.json.

Objects (definition, as in members/two-hub/DUAL.md):
    U   = 22568935234031792038557518369/62500000000000000000000000000
    h_j = t_j u(delta_j);  d = |h1-h2|;  b = acos(clamp(d/(2U),-1,1))
    E_j = arc on S(h_j,U) with centre away_j = dir(h_j - h_{j'}), halfwidth pi - b
    ring at c = rho u(phi):  alpha(rho) = acos((1+rho^2-U^2)/(2 rho))
                             ell_j = |c-h_j|, beta_j = acos(ell_j/(2U)) if ell_j < 2U
                             psi_j = atan2(c-h_j)
    A_0 = arc(phi, alpha) on S^1 ;  A_j = arc(psi_j, beta_j) on S(h_j,U)
    cap(rho,phi) = int_{A_0} W_0 + sum_j int_{E_j cap A_j} W_j
    req          = int_{S^1} W_0 + sum_j int_{E_j} W_j
    (for this configuration |h_j| + U = 0.561... <= 1, so E_j is entirely inside D and
     no D-clipping of E_j is needed; checked exactly inside this script.)

TWO INDEPENDENT ROUTES (calibrated against each other at dps = 60):
  (R1) antiderivative  F_W(t) = w0 t + sum_k w_k sin(k t)/k - sum_k v_k cos(k t)/k
  (R2) mp.quad (tanh-sinh) of the weight function over each intersection SEGMENT
The circle intersection E_j cap A_j is computed as the union over integer shifts
k in {-2..2} of the unrolled interval intersections; the two-piece case
(beta_j > b) is therefore represented by TWO segments, and each is integrated
separately (this is the object the interval kernel must enclose).

Output: JSON in ../logs/direct_cap.json with the point list, both route values,
the per-component split and the segment counts.

Run:  py -3 -B py/direct_cap.py
"""
import json
import os
import sys
from fractions import Fraction as F

from mpmath import mp

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..', '..', '..'))
TWO_HUB = os.path.join(ROOT, 'research-2026', 'n12-global', 'members', 'two-hub')
EVID = os.path.join(TWO_HUB, 'evidence')
LOGS = os.path.join(HERE, '..', 'logs')

mp.dps = 60

U_FR = F(22568935234031792038557518369, 62500000000000000000000000000)
T1, T2, DELTA = F(1, 5), F(1, 5), F(604457, 200000)

WEIGHTS_JSON = os.path.join(EVID, 'rational_dual_worst.json')


def fr2mp(x):
    x = F(x)
    return mp.mpf(x.numerator) / mp.mpf(x.denominator)


W_FR = None
W = None
GEO = {}


def load_weights():
    global W_FR, W
    d = json.load(open(WEIGHTS_JSON, encoding='utf-8'))
    raw = [b['rational'] for b in d['blocks']] if 'blocks' in d else d['weights']
    W_FR = [[F(s) for s in blk] for blk in raw]
    W = [[fr2mp(c) for c in blk] for blk in W_FR]
    return W_FR


def setup_geometry():
    u = fr2mp(U_FR)
    t1, t2, delta = fr2mp(T1), fr2mp(T2), fr2mp(DELTA)
    h1 = (t1, mp.mpf(0))
    h2 = (t2 * mp.cos(delta), t2 * mp.sin(delta))
    dx, dy = h1[0] - h2[0], h1[1] - h2[1]
    d = mp.sqrt(dx * dx + dy * dy)
    b = mp.acos(min(mp.mpf(1), max(mp.mpf(-1), d / (2 * u))))
    away1 = mp.atan2(dy, dx)
    away2 = mp.atan2(-dy, -dx)
    GEO.update(u=u, h=[h1, h2], d=d, b=b,
               E=[(away1, mp.pi - b), (away2, mp.pi - b)])
    return GEO


def Wval(coef, th):
    v = coef[0]
    for k in range(1, 5):
        v += coef[k] * mp.cos(k * th) + coef[4 + k] * mp.sin(k * th)
    return v


def Fint(coef, th):
    s = coef[0] * th
    for k in range(1, 5):
        s += coef[k] * mp.sin(k * th) / k - coef[4 + k] * mp.cos(k * th) / k
    return s


def seg_int_R1(coef, lo, hi):
    """antiderivative route over an unrolled interval [lo,hi]."""
    return Fint(coef, hi) - Fint(coef, lo)


def seg_int_R2(coef, lo, hi):
    """independent quadrature route over [lo,hi]."""
    if hi <= lo:
        return mp.mpf(0)
    return mp.quad(lambda t: Wval(coef, t), [lo, hi])


def arc_segments(psi, beta, cE, hE):
    """E cap A as a list of unrolled segments [lo,hi] (at most 2 non-empty)."""
    segs = []
    for k in range(-2, 3):
        lo = max(psi - beta, cE - hE + 2 * mp.pi * k)
        hi = min(psi + beta, cE + hE + 2 * mp.pi * k)
        if hi > lo:
            segs.append((lo, hi))
    return segs


def cap_components(rho, phi, route='R1'):
    """returns (A0, t1, t2, seg counts) at a single (rho,phi)."""
    u = GEO['u']
    c = (rho * mp.cos(phi), rho * mp.sin(phi))
    arg = (1 + rho * rho - u * u) / (2 * rho)
    alpha = mp.acos(min(mp.mpf(1), max(mp.mpf(-1), arg)))
    f = seg_int_R1 if route == 'R1' else seg_int_R2
    a0 = f(W[0], phi - alpha, phi + alpha)
    terms = []
    nseg = []
    for j in range(2):
        hj = GEO['h'][j]
        ell = mp.sqrt((c[0] - hj[0]) ** 2 + (c[1] - hj[1]) ** 2)
        if ell < 2 * u:
            bet = mp.acos(min(mp.mpf(1), max(mp.mpf(-1), ell / (2 * u))))
            psi = mp.atan2(c[1] - hj[1], c[0] - hj[0])
            segs = arc_segments(psi, bet, GEO['E'][j][0], GEO['E'][j][1])
            nseg.append(len(segs))
            terms.append(sum(f(W[j + 1], lo, hi) for lo, hi in segs))
        else:
            nseg.append(0)
            terms.append(mp.mpf(0))
    return a0, terms[0], terms[1], nseg


def cap(rho, phi, route='R1'):
    a0, t1, t2, nseg = cap_components(rho, phi, route)
    return a0 + t1 + t2


def req(route='R1'):
    f = seg_int_R1 if route == 'R1' else seg_int_R2
    tot = f(W[0], -mp.pi, mp.pi)
    parts = [tot]
    for j in range(2):
        cE, hE = GEO['E'][j]
        parts.append(f(W[j + 1], cE - hE, cE + hE))
    return sum(parts), parts


def main():
    load_weights()
    setup_geometry()
    u = GEO['u']
    print('U    =', mp.nstr(u, 40))
    print('h1   =', (mp.nstr(GEO['h'][0][0], 30), mp.nstr(GEO['h'][0][1], 30)))
    print('h2   =', (mp.nstr(GEO['h'][1][0], 30), mp.nstr(GEO['h'][1][1], 30)))
    print('d    =', mp.nstr(GEO['d'], 30), ' b =', mp.nstr(GEO['b'], 30))
    print('E1   = (centre %s, half %s)' % (mp.nstr(GEO['E'][0][0], 30), mp.nstr(GEO['E'][0][1], 30)))
    print('E2   = (centre %s, half %s)' % (mp.nstr(GEO['E'][1][0], 30), mp.nstr(GEO['E'][1][1], 30)))
    # exact check |h_j| + U <= 1  (so E_j cap D = E_j, no clipping)
    for j, (t, _) in enumerate(((T1, 0), (T2, 0))):
        print('  |h_%d| + U <= 1 ?' % (j + 1), t + U_FR <= 1, ' (= %s)' % (t + U_FR))

    rq1, parts = req('R1')
    rq2, _ = req('R2')
    print('req  R1 =', mp.nstr(rq1, 40))
    print('req  R2 =', mp.nstr(rq2, 40), '  |R1-R2| =', mp.nstr(abs(rq1 - rq2), 5))
    print('  components (S^1 W0, E1 W1, E2 W2) =', [mp.nstr(p, 30) for p in parts])
    print('  recorded kernel req interval = [1.00003635467006350736152531965, 1.00003635467006350736152568154]')

    # nonnegativity of each weight block: w0 >= sum_k (|w_k|+|v_k|)
    print('weight nonnegativity (sufficient condition w0 >= sum(|w|+|v|)):')
    for j, blk in enumerate(W_FR):
        s = sum(abs(x) for x in blk[1:])
        print('  block %d: w0 = %-12s sum|.| = %-12s  ok = %s  (slack %s)'
              % (j, blk[0], s, blk[0] >= s, blk[0] - s))

    # ---- calibration points ----
    cal = []
    for (r, p) in ((0.673909311376261, 1.5047619108735262), (0.700, 1.0),
                   (0.850, 2.0), (0.930, 3.0), (0.640, 0.0), (0.66, 4.5)):
        v1 = cap(mp.mpf(r), mp.mpf(p), 'R1')
        v2 = cap(mp.mpf(r), mp.mpf(p), 'R2')
        cal.append(dict(rho=r, phi=p, R1=mp.nstr(v1, 30), R2=mp.nstr(v2, 30),
                        diff=mp.nstr(v1 - v2, 5)))
        print('  cal (%.4f,%.4f): R1=%s R2=%s diff=%s' % (r, p, mp.nstr(v1, 25), mp.nstr(v2, 25),
                                                          mp.nstr(v1 - v2, 5)))

    # ---- control point set ----
    pts = []
    rb = (mp.mpf('0.7710300479596416010030562882630485657941'),
          mp.mpf('0.7857114937045471869608314653390145452806'))
    pb = (mp.mpf('0.9424777960769379715387930206257331888339'),
          mp.mpf('1.021017612416682802500359105677877621237'))
    n = 10
    for i in range(n):
        for k in range(n):
            rho = rb[0] + (rb[1] - rb[0]) * mp.mpf(i) / (n - 1)
            phi = pb[0] + (pb[1] - pb[0]) * mp.mpf(k) / (n - 1)
            pts.append((rho, phi, 'worst-leaf-grid'))
    extra = [
        (mp.mpf('0.673909311376261'), mp.mpf('1.5047619108735262'), 'float-argmax'),
        (mp.mpf('0.673909'), mp.mpf('1.504725'), 'DUAL.md-argmax'),
        (mp.mpf(1) - u, mp.mpf(0), 'rho-min-phi-0'),
        (mp.mpf(1) - u, mp.pi, 'rho-min-phi-pi'),
        (mp.sqrt(1 - u * u), mp.mpf(0), 'rho-max-phi-0'),
        (mp.sqrt(1 - u * u), mp.pi, 'rho-max-phi-pi'),
        (mp.mpf('0.70'), 2 * mp.pi - mp.mpf('1e-9'), 'wrap-phi'),
        (mp.mpf('0.70'), mp.mpf('1e-9'), 'wrap-phi-0'),
        (mp.mpf('0.72'), mp.mpf('0.5'), 'generic'),
        (mp.mpf('0.80'), mp.mpf('4.0'), 'generic2'),
    ]
    pts.extend(extra)

    rows = []
    maxdiff = mp.mpf(0)
    two_piece = 0
    for (rho, phi, tag) in pts:
        a0, t1, t2, nseg = cap_components(rho, phi, 'R1')
        v1 = a0 + t1 + t2
        a0b, t1b, t2b, _ = cap_components(rho, phi, 'R2')
        v2 = a0b + t1b + t2b
        d = abs(v1 - v2)
        maxdiff = max(maxdiff, d)
        if any(s >= 2 for s in nseg):
            two_piece += 1
        rows.append(dict(rho=mp.nstr(rho, 25), phi=mp.nstr(phi, 25), tag=tag,
                         direct=mp.nstr(v1, 40), direct_R2=mp.nstr(v2, 40),
                         diff=mp.nstr(d, 5), a0=mp.nstr(a0, 40),
                         t1=mp.nstr(t1, 40), t2=mp.nstr(t2, 40), segs=nseg))
    print()
    print('control points: %d   (grid %dx%d + %d extra)' % (len(pts), n, n, len(extra)))
    print('max |R1-R2| over control points =', mp.nstr(maxdiff, 5))
    print('points with a TWO-SEGMENT (wide wrap) intersection:', two_piece)
    print('max direct cap over the 100-point worst-leaf grid =',
          max(mp.mpf(r['direct']) for r in rows if r['tag'] == 'worst-leaf-grid'))
    print('direct cap at the recorded float argmax =',
          [r['direct'] for r in rows if r['tag'] == 'float-argmax'][0])
    print('a0 / hub-term split at the float argmax:',
          [(r['a0'], r['t1'], r['t2'], r['segs']) for r in rows if r['tag'] == 'float-argmax'][0])

    os.makedirs(LOGS, exist_ok=True)
    out = dict(U=mp.nstr(u, 40), d=mp.nstr(GEO['d'], 30), b=mp.nstr(GEO['b'], 30),
               req_R1=mp.nstr(rq1, 45), req_R2=mp.nstr(rq2, 45),
               req_components=[mp.nstr(p, 30) for p in parts],
               max_route_diff=mp.nstr(maxdiff, 5), points=rows)
    json.dump(out, open(os.path.join(LOGS, 'direct_cap.json'), 'w'), indent=1)
    print('wrote logs/direct_cap.json')


if __name__ == '__main__':
    main()
