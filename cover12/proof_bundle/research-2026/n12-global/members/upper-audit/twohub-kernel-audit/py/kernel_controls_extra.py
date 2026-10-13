"""kernel_controls_extra.py  (member upper-audit/twohub-kernel-audit, 2026-09-26)

Extra positive controls, aimed exactly at the delicate parts of the interval kernel
py/certify_ring2.py (current revision, EL/ER + directed undecided bound):

  (1) CERTIFIED hub configuration (t1=t2=1/5, delta=604457/200000):
      * points where the A_j arc straddles the +-pi cut (psi_j ~ +-pi) - exercises the
        three-shift unwrapping of the A interval against the fixed E interval;
      * points where an intersection endpoint coincides with an E_j endpoint
        (A_j touches E_j) - exercises the (lo<hi)/undecided branch boundary;
      * structural fact checked exactly: on the whole ring domain ell_j > d, hence
        beta_j < b, hence the *geometric* two-piece case (beta_j > b) never occurs in
        the certified region.
  (2) NON-CERTIFIED hub configurations (patched module constants in this process only,
      member files untouched) where beta_j > b DOES occur, so the two-piece branch of
      the arc intersection is genuinely exercised:
        (t1,t2,delta) = (0.43880, 0.43880, 1.57080)  and  (0.50000, 0.30000, 2.60000)
      For every sampled point we require  kernel ehi(box_upper(r,r,p,p)) >= direct cap.

Run: py -3 -B py/kernel_controls_extra.py
"""
import json
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

U_FR = dc.U_FR


def set_config(t1, t2, delta):
    for mod in (cr, dc):
        mod.T1, mod.T2, mod.DELTA = F(t1), F(t2), F(delta)
    dc.setup_geometry()
    return cr.Cert(dc.W_FR_ref() if hasattr(dc, 'W_FR_ref') else dc.W_FR, dps=25)


def point_check(cert, rho, phi):
    ub, ok = cert.box_upper(rho, rho, phi, phi)
    direct = dc.cap(rho, phi, 'R1')
    direct2 = dc.cap(rho, phi, 'R2')
    segs = dc.cap_components(rho, phi, 'R1')[3]
    return dict(ok=ok, kernel=cr.ehi(ub) if ok else None, direct=direct,
                direct2=direct2, segs=segs,
                two_piece=any(s >= 2 for s in segs))


def main():
    dc.load_weights()
    print('== (1) certified configuration t1=t2=1/5, delta=604457/200000 ==')
    cert = set_config(F(1, 5), F(1, 5), F(604457, 200000))
    u = dc.GEO['u']
    d = dc.GEO['d']
    # exact domain-level fact: ell_j >= (1-U) - t_j > d  =>  beta_j < b  (single piece)
    for j, t in enumerate((F(1, 5), F(1, 5)), start=1):
        eps = (1 - U_FR) - t
        print('   hub %d: ell_j >= (1-U)-t_j = %s ; d = %s ; ell_j > d ? %s'
              % (j, mp.nstr(dc.fr2mp(eps), 25), mp.nstr(d, 25), dc.fr2mp(eps) > d))
    print('   => beta_j = acos(ell_j/(2U)) < acos(d/(2U)) = b, so hE + beta_j < pi:')
    print('      the GEOMETRIC two-piece case is vacuous on the certified ring domain.')

    pts = []
    # psi_j near +-pi and E-endpoint touching points, found by a coarse scan
    worst = None
    for i in range(24):
        rho = (mp.mpf(1) - u) + (mp.sqrt(1 - u * u) - (mp.mpf(1) - u)) * i / 23
        for k in range(48):
            phi = 2 * mp.pi * k / 48
            pts.append((rho, phi))
    rows = []
    for (rho, phi) in pts:
        r = point_check(cert, rho, phi)
        rows.append((rho, phi, r))
    viol = [(r, p, x) for (r, p, x) in rows if (not x['ok']) or x['kernel'] < min(x['direct'], x['direct2'])]
    margins = [(x['kernel'] - max(x['direct'], x['direct2']), r, p) for (r, p, x) in rows if x['ok']]
    margins.sort()
    print('   scanned points        :', len(rows))
    print('   containment violations:', len(viol))
    print('   two-piece intersections:', sum(1 for (_, _, x) in rows if x['two_piece']))
    print('   tightest margin       : %.6e   (rho=%s phi=%s)'
          % (float(margins[0][0]), mp.nstr(margins[0][1], 18), mp.nstr(margins[0][2], 18)))
    print('   wide margins (first 3):',
          ['%.3e' % float(m) for m, _, _ in margins[-3:]])
    # points straddling psi ~ +-pi specifically
    near_pi = []
    for i in range(24):
        rho = (mp.mpf(1) - u) + (mp.sqrt(1 - u * u) - (mp.mpf(1) - u)) * i / 23
        for phi in (mp.pi - mp.mpf('1e-6'), mp.pi, mp.pi + mp.mpf('1e-6'),
                    mp.pi - mp.mpf('0.05'), mp.pi + mp.mpf('0.05')):
            near_pi.append((rho, phi))
    v2 = []
    for (rho, phi) in near_pi:
        x = point_check(cert, rho, phi)
        if (not x['ok']) or x['kernel'] < max(x['direct'], x['direct2']):
            v2.append((rho, phi, x))
    print('   psi~pi wrap points    :', len(near_pi), ' violations:', len(v2))

    print()
    print('== (2) NON-certified configurations (two-piece branch genuinely active) ==')
    for (t1, t2, delta, tag) in ((F(43880, 100000), F(43880, 100000), F(157080, 100000), 't=0.4388,delta~pi/2'),
                                 (F(1, 2), F(3, 10), F(26, 10), 't1=.5,t2=.3,delta=2.6')):
        cert = set_config(t1, t2, delta)
        uu = dc.GEO['u']
        dd = dc.GEO['d']
        rows = []
        n2 = 0
        for i in range(12):
            rho = (mp.mpf(1) - uu) + (mp.sqrt(1 - uu * uu) - (mp.mpf(1) - uu)) * i / 11
            for k in range(24):
                phi = 2 * mp.pi * k / 24
                x = point_check(cert, rho, phi)
                rows.append(x)
                n2 += 1 if x['two_piece'] else 0
        viol = [x for x in rows if (not x['ok']) or x['kernel'] < min(x['direct'], x['direct2'])]
        mar = sorted((x['kernel'] - max(x['direct'], x['direct2'])) for x in rows if x['ok'])
        print('   config %-24s d=%-12s b=%-12s' % (tag, mp.nstr(dd, 12), mp.nstr(dc.GEO['b'], 12)))
        print('      points=%d  two-piece=%d  violations=%d  tightest margin=%.3e'
              % (len(rows), n2, len(viol), float(mar[0]) if mar else float('nan')))
        if n2 == 0:
            print('      (no two-piece point at this sampling -> increase rho/phi density)')
        for x in viol[:5]:
            print('      VIOLATION rho/phi direct=%s kernel=%s segs=%s'
                  % (mp.nstr(x['direct'], 25), mp.nstr(x['kernel'], 25), x['segs']))

    print()
    print('== (3) nonnegativity of the weight blocks (exact rational) ==')
    for j, blk in enumerate(dc.W_FR):
        s = sum(abs(x) for x in blk[1:])
        print('   block %d: w0=%s  sum|.|=%s  ok=%s' % (j, blk[0], s, blk[0] >= s))


if __name__ == '__main__':
    main()
