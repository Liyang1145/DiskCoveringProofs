"""twopiece_scan.py  (member upper-audit/twohub-kernel-audit, 2026-09-26)

Reachability of the TWO-PIECE arc-intersection branch (beta_j > b) for the interval
kernel py/certify_ring2.py, i.e. the case the Lead's hE-fix is about.

Two-piece needs  E_j cap A_j  to be disconnected, which (with hE = pi - b, hA = beta_j)
is equivalent to  beta_j > b  AND the hidden cap (centre = direction toward the other
hub, halfwidth b) strictly inside A_j.  Because the ring domain is |c| >= 1-U and the
kernel guard requires rho > |h_j|, we scan float configurations to see whether this is
reachable at all for hub norms t_j < 1-U (the domain) - and, if it is, run the
high-precision containment test there.

Run: py -3 -B py/twopiece_scan.py
"""
import math
import os
import sys
from fractions import Fraction as F

from mpmath import mp

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..', '..', '..'))
TWO_HUB = os.path.join(ROOT, 'research-2026', 'n12-global', 'members', 'two-hub')
LOGS = os.path.join(HERE, '..', 'logs')
sys.path.insert(0, os.path.join(TWO_HUB, 'py'))
sys.path.insert(0, HERE)

import certify_ring2 as cr
import direct_cap as dc

U = float(dc.U_FR)


def twopiece_margin(t1, t2, delta, rho, phi):
    """returns (reachable?, margin) with margin = beta_j - b - angular distance."""
    h1 = (t1, 0.0)
    h2 = (t2 * math.cos(delta), t2 * math.sin(delta))
    d = math.hypot(h1[0] - h2[0], h1[1] - h2[1])
    if d > 2 * U - 1e-9 or d <= 1e-9:
        return None
    b = math.acos(min(1.0, max(-1.0, d / (2 * U))))
    c = (rho * math.cos(phi), rho * math.sin(phi))
    best = None
    for (hj, hk) in ((h1, h2), (h2, h1)):
        if rho <= math.hypot(*hj):
            continue
        to = math.atan2(hk[1] - hj[1], hk[0] - hj[0])
        ell = math.hypot(c[0] - hj[0], c[1] - hj[1])
        if ell >= 2 * U or ell <= 0:
            continue
        bet = math.acos(min(1.0, max(-1.0, ell / (2 * U))))
        psi = math.atan2(c[1] - hj[1], c[0] - hj[0])
        dth = abs((psi - to + math.pi) % (2 * math.pi) - math.pi)
        m = bet - b - dth
        if best is None or m > best:
            best = m
    return best


def main():
    print('U = %.17f   ring domain rho in [1-U, sqrt(1-U^2)] = [%.6f, %.6f]'
          % (U, 1 - U, math.sqrt(1 - U * U)))
    print('scanning hub norms t_j < 1-U = %.6f, delta in (0,pi], the whole ring domain,')
    print('requiring the kernel guard rho > max(t1,t2) and d <= 2U:')
    best = None
    hits = 0
    n = 0
    allhits = []
    for it in range(1, 13):
        t1 = 0.65 * it / 12
        for jt in range(1, 13):
            t2 = 0.65 * jt / 12
            if max(t1, t2) >= 1 - U:
                continue
            for id_ in range(1, 25):
                delta = math.pi * id_ / 25
                for ir in range(1, 9):
                    rho = (1 - U) + (math.sqrt(1 - U * U) - (1 - U)) * ir / 8
                    if rho <= max(t1, t2):
                        continue
                    for ip in range(0, 48):
                        phi = 2 * math.pi * ip / 48
                        n += 1
                        m = twopiece_margin(t1, t2, delta, rho, phi)
                        if m is None:
                            continue
                        if m > 0:
                            hits += 1
                            allhits.append((m, t1, t2, delta, rho, phi))
                            if best is None or m > best[0]:
                                best = (m, t1, t2, delta, rho, phi)
    print('  grid points scanned           :', n)
    print('  two-piece reachable (margin>0):', hits)
    if best:
        print('  max margin = %.6f at t1=%.4f t2=%.4f delta=%.5f rho=%.6f phi=%.6f'
              % best)
        # test up to 12 diverse two-piece points through the fixed kernel
        uniq = {}
        for (m, t1, t2, delta, rho, phi) in allhits:
            key = (round(t1, 3), round(t2, 3), round(delta, 3))
            if key not in uniq or m > uniq[key][0]:
                uniq[key] = (m, t1, t2, delta, rho, phi)
        cand = sorted(uniq.values(), reverse=True)[:12]
        nviol = 0
        print('  high-precision containment tests at %d two-piece points:' % len(cand))
        for (m, t1, t2, delta, rho, phi) in cand:
            cr.T1, cr.T2, cr.DELTA = (F(t1).limit_denominator(10**6),
                                      F(t2).limit_denominator(10**6),
                                      F(delta).limit_denominator(10**6))
            dc.T1, dc.T2, dc.DELTA = cr.T1, cr.T2, cr.DELTA
            dc.setup_geometry()
            dc.load_weights()
            cert = cr.Cert(dc.W_FR, dps=25)
            ub, ok = cert.box_upper(mp.mpf(str(rho)), mp.mpf(str(rho)),
                                    mp.mpf(str(phi)), mp.mpf(str(phi)))
            direct = dc.cap(mp.mpf(str(rho)), mp.mpf(str(phi)), 'R1')
            segs = dc.cap_components(mp.mpf(str(rho)), mp.mpf(str(phi)), 'R1')[3]
            good = ok and cr.ehi(ub) >= direct
            nviol += 0 if good else 1
            print('    t=(%.4f,%.4f) d=%.4f rho=%.6f phi=%.6f segs=%s ok=%s contains=%s margin=%.3e'
                  % (t1, t2, delta, rho, phi, segs, ok, good,
                     float(cr.ehi(ub) - direct) if ok else float('nan')))
        print('  containment violations at two-piece points:', nviol)
    else:
        print('  => no two-piece-reachable point found in the scanned domain.')
        print('     (for the CERTIFIED configuration this is also proved exactly:')
        ell = (1 - dc.U_FR) - F(1, 5)
        print('      ell_j >= (1-U) - t_j = %s and d = 0.3992884952227919930977488823168...;' % ell)
        print('      ell_j > d  =>  beta_j < b  =>  hE + beta_j < pi.)')


if __name__ == '__main__':
    main()
