"""leaf_box_recheck.py  (member upper-audit/twohub-kernel-audit, 2026-09-26)

Inconsistency probe: the completed fixed-kernel sweep (run_fixed_sweep.py 400000 14)
recorded  worst_leaf_ub = 0.09995363239854560134043966480160594324602  for the box
rho in [0.8013105298085093720409675909822283984849, 0.8022281201675659711633285395494762722028]
phi in [0.8148505945248526212262481324159984861793, 0.8197593330460866731613460127317575132044]
but re-evaluating box_upper on that same box (fresh Cert, dps=25) gives a larger value.
This script checks determinism/state-dependence and grid-exactness of the box.

Run: py -3 -B py/leaf_box_recheck.py
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

BOX = ["0.8013105298085093720409675909822283984849",
       "0.8022281201675659711633285395494762722028",
       "0.8148505945248526212262481324159984861793",
       "0.8197593330460866731613460127317575132044"]


def show(tag, cert, box):
    ub, ok = cert.box_upper(*box)
    print('%-28s ok=%s  ehi=%s' % (tag, ok, mp.nstr(cr.ehi(ub), 32) if ok else 'n/a'))
    return ok, (cr.ehi(ub) if ok else None)


def main():
    dc.load_weights()
    W = dc.W_FR
    box = [mp.mpf(s) for s in BOX]
    c1 = cr.Cert(W, dps=25)
    show('fresh Cert #1', c1, box)
    show('same Cert again', c1, box)
    c2 = cr.Cert(W, dps=25)
    show('fresh Cert #2', c2, box)
    c3 = cr.Cert(W, dps=30)
    show('Cert dps=30', c3, box)
    # grid-exact endpoints, as produced by run(): rl + (rh-rl)*i/nrho
    cert = cr.Cert(W, dps=25)
    rl = cr.elo(cert.rho_lo); rh = cr.ehi(cert.rho_hi); ph = cr.ehi(cert.two_pi)
    nrho, nphi = 10, 40
    print('grid row boundaries:', [mp.nstr(rl + (rh - rl) * i / nrho, 20) for i in (0, 8, 9, 10)])
    hit = None
    for i in range(nrho):
        r0 = rl + (rh - rl) * i / nrho
        r1 = rl + (rh - rl) * (i + 1) / nrho
        for j in range(nphi):
            p0 = ph * j / nphi
            p1 = ph * (j + 1) / nphi
            if abs(r0 - box[0]) < mp.mpf('1e-9') and abs(p0 - box[2]) < mp.mpf('1e-9'):
                hit = (r0, r1, p0, p1)
    if hit:
        print('grid-exact box found at a top-level cell:')
        show('grid-exact endpoints', cert, list(hit))
        print('   grid box =', [mp.nstr(x, 32) for x in hit])
        print('   recorded  =', BOX)
    else:
        print('recorded box is NOT a top-level grid cell (deeper bisection), as expected;')
        print('endpoints were formed by mpf bisections at mp.dps = %s' % mp.dps)
    # how many depth levels? compare to the depth-6 bisection chain
    print()
    print('note: run() records worst_leaf = (ehi(ub), (r0,r1,p0,p1)) at acceptance time;')
    print('      a mismatch here means box_upper is not reproducible for that box.')


if __name__ == '__main__':
    main()
