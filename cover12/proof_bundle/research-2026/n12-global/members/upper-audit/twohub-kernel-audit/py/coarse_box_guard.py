"""coarse_box_guard.py  (member upper-audit/twohub-kernel-audit, 2026-09-26)

Targeted probe of the Lead's guard concern for the unwrap branch of
py/certify_ring2.py: the lift/window check uses only the four CORNER angles, while the
true image of a polar box under (rho,phi) -> arg(rho u_phi - h) can vary inside the box.
The variation is bounded by the derivative bounds

    |d arg/d rho| = |h x u_phi| / ell^2            <= |h| / ell_min^2
    d arg/d phi   = rho (rho - <h,u_phi>) / ell^2  <= rho_max (rho_max+|h|) / ell_min^2

with ell_min = rho_min - |h| (valid because the kernel's guard enforces rho_min > |h|).
So a rigorous window check needs  corner-span + V < pi  with

    V = d_rho * |h|/ell_min^2 + d_phi * rho_max (rho_max+|h|)/ell_min^2 .

This script measures, on the kernel's OWN initial grid (10 x 40 boxes), the box-level
containment  kernel_ub >= max direct cap over a sub-grid, and prints V for each box, to
see whether coarse boxes are actually affected.

Run: py -3 -B py/coarse_box_guard.py [nsub]
"""
import os
import sys

from mpmath import mp

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..', '..', '..'))
TWO_HUB = os.path.join(ROOT, 'research-2026', 'n12-global', 'members', 'two-hub')
sys.path.insert(0, os.path.join(TWO_HUB, 'py'))
sys.path.insert(0, HERE)

import certify_ring2 as cr
import direct_cap as dc

NSUB = int(sys.argv[1]) if len(sys.argv) > 1 else 7


def main():
    dc.load_weights()
    dc.setup_geometry()
    W = dc.W_FR
    cert = cr.Cert(W, dps=25)
    u = dc.GEO['u']
    rl = cr.elo(cert.rho_lo)
    rh = cr.ehi(cert.rho_hi)
    ph = cr.ehi(cert.two_pi)
    nrho, nphi = 10, 40
    hmax = max(mp.sqrt(h[0] ** 2 + h[1] ** 2) for h in dc.GEO['h'])
    print('guard V-bound probe on the kernel initial grid (%dx%d), sub-grid %dx%d'
          % (nrho, nphi, NSUB, NSUB))
    print('rho in [%s, %s], |h|max = %s' % (mp.nstr(rl, 20), mp.nstr(rh, 20), mp.nstr(hmax, 20)))
    rows = (0, 9)
    nviol = 0
    nundec = 0
    worst = None
    for i in rows:
        r0 = rl + (rh - rl) * i / nrho
        r1 = rl + (rh - rl) * (i + 1) / nrho
        for j in range(nphi):
            p0 = ph * j / nphi
            p1 = ph * (j + 1) / nphi
            ub, ok = cert.box_upper(r0, r1, p0, p1)
            mx = None
            for a in range(NSUB):
                for b in range(NSUB):
                    rr = r0 + (r1 - r0) * mp.mpf(a) / (NSUB - 1)
                    pp = p0 + (p1 - p0) * mp.mpf(b) / (NSUB - 1)
                    v = dc.cap(rr, pp, 'R1')
                    if mx is None or v > mx:
                        mx = v
            # variation bound V over this box (informational)
            ellmin = r0 - hmax
            if ellmin <= 0:
                V = mp.inf
            else:
                V = (r1 - r0) * hmax / ellmin ** 2 + \
                    (p1 - p0) * r1 * (r1 + hmax) / ellmin ** 2
            line = ('row %d col %2d  rho=[%.5f,%.5f] phi=[%.4f,%.4f]  V=%.3f  '
                    'kernel=%s  max_direct=%.9f' %
                    (i, j, float(r0), float(r1), float(p0), float(p1), float(V),
                     ('%.9f' % float(cr.ehi(ub))) if ok else 'undecided', float(mx)))
            if not ok:
                nundec += 1
                print('  UNDECIDED  ' + line)
                continue
            if cr.ehi(ub) < mx:
                nviol += 1
                print('  VIOLATION  ' + line)
            if worst is None or (cr.ehi(ub) - mx) < worst[0]:
                worst = (cr.ehi(ub) - mx, i, j, V, mx)
    print()
    print('boxes tested=%d  violations=%d  undecided=%d' % (len(rows) * nphi, nviol, nundec))
    if worst:
        print('tightest margin %.3e at row %d col %d (V=%.3f, max_direct=%.9f)'
              % (float(worst[0]), worst[1], worst[2], float(worst[3]), float(worst[4])))
    print('note: sub-grid max is only a probe (a bound is sound at a box iff it dominates')
    print('      the TRUE sup; this test can only exhibit violations, not certify).')


if __name__ == '__main__':
    main()
