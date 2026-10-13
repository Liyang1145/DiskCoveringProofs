"""kernel_controls.py  (member upper-audit/twohub-kernel-audit, 2026-09-26)

POSITIVE CONTROLS for the two-hub interval kernel py/certify_ring2.py:

  (A) reproduce the recorded sweep (run() writes nothing; main() is not called) and
      compare with evidence/certify_ring2_main.json;
  (B) for every direct-computation control point (logs/direct_cap.json, 110 points,
      two independent high-precision routes agreeing to ~1e-61), ask the kernel for
      the bound on the DEGENERATE box [rho,rho] x [phi,phi] and check
      ehi(ub) >= direct cap   (containment of the value at that point);
  (C) box-level check: for a sample of boxes (the recorded worst leaf, its halves and
      a few random sub-boxes) compare the kernel bound with the max direct cap over a
      fine sub-grid inside the box (a kernel bound must dominate it).

Nothing is written outside this member directory; the member's files are only imported.

Run: py -3 -B py/kernel_controls.py
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..', '..', '..', '..'))
TWO_HUB = os.path.join(ROOT, 'research-2026', 'n12-global', 'members', 'two-hub')
LOGS = os.path.join(HERE, '..', 'logs')
sys.path.insert(0, os.path.join(TWO_HUB, 'py'))

import certify_ring2 as cr            # read-only import of the member kernel
from mpmath import mp, iv

DPS = int(os.environ.get('KERNEL_DPS', '25'))


def main():
    W, meta = cr.load_weights()
    print('kernel revision: certify_ring2.py (see logs/kernel_revision.txt for the hash)')
    c = cr.Cert(W, dps=DPS)
    print('d =', mp.nstr(cr.elo(c.d), 30), ' b =', mp.nstr(cr.elo(c.b), 30))
    print('req interval = [%s, %s]' % (cr.elo(c.req), cr.ehi(c.req)))

    # ---------------- (A) reproduce the recorded sweep ----------------
    res = c.run(max_boxes=60000, max_depth=14, verbose=False)
    rec = json.load(open(os.path.join(TWO_HUB, 'evidence', 'certify_ring2_main.json'), encoding='utf-8'))
    print()
    print('(A) reproduced sweep vs evidence/certify_ring2_main.json')
    for k in ('nbox', 'leaves', 'unsolved', 'maxdepth', 'worst_leaf_ub', 'worst_any_ub', 'thr_scale'):
        mine = str(res[k]); theirs = str(rec[k])
        same = (mp.mpf(mine) == mp.mpf(theirs)) if k in ('worst_leaf_ub', 'worst_any_ub', 'thr_scale') else (mine == theirs)
        print('    %-14s mine=%-46s recorded=%-46s identical=%s' % (k, mine, theirs, same))
    print('    worst_leaf_box mine  =', [str(x) for x in res['worst_leaf_box']])
    print('    worst_leaf_box record=', rec['worst_leaf_box'])

    # ---------------- (B) pointwise containment ----------------
    D = json.load(open(os.path.join(LOGS, 'direct_cap.json'), encoding='utf-8'))
    print()
    print('(B) pointwise containment: kernel ehi(box_upper(rho,rho,phi,phi)) >= direct cap')
    bad = []
    worst_slack = None
    for row in D['points']:
        rho = mp.mpf(row['rho']); phi = mp.mpf(row['phi'])
        direct = mp.mpf(row['direct'])
        ub, ok = c.box_upper(rho, rho, phi, phi)
        if not ok:
            bad.append((row, 'undecided(ok=False)', None))
            continue
        u = cr.ehi(ub)
        slack = u - direct
        if worst_slack is None or slack < worst_slack[0]:
            worst_slack = (slack, row['tag'], row['rho'], row['phi'], direct, u)
        if slack < 0:
            bad.append((row, 'VIOLATION', slack))
        if any(s >= 2 for s in row['segs']):
            pass
    print('  control points tested      :', len(D['points']))
    print('  containment violations     :', len(bad))
    for row, why, slack in bad[:12]:
        print('    %-18s rho=%s phi=%s direct=%s kernel=%s' %
              (why + ' ' + row['tag'], row['rho'][:22], row['phi'][:22],
               row['direct'][:24], 'n/a'))
    if worst_slack:
        print('  tightest containment margin: %.6e  (tag=%s rho=%s phi=%s direct=%s kernel=%s)'
              % (worst_slack[0], worst_slack[1], worst_slack[2][:20], worst_slack[3][:20],
                 mp.nstr(worst_slack[4], 25), mp.nstr(worst_slack[5], 25)))
    print('  float-argmax point: direct =', [r['direct'] for r in D['points'] if r['tag'] == 'float-argmax'][0])

    # ---------------- (C) box-level containment ----------------
    print()
    print('(C) box-level: kernel bound vs max direct cap over a 10x10 sub-grid of the box')
    rb = (mp.mpf('0.7710300479596416010030562882630485657941'),
          mp.mpf('0.7857114937045471869608314653390145452806'))
    pb = (mp.mpf('0.9424777960769379715387930206257331888339'),
          mp.mpf('1.021017612416682802500359105677877621237'))
    boxes = [(rb[0], rb[1], pb[0], pb[1], 'recorded worst leaf')]
    rm, pm = (rb[0] + rb[1]) / 2, (pb[0] + pb[1]) / 2
    boxes += [(rb[0], rm, pb[0], pm, 'worst-leaf SW quarter'),
              (rm, rb[1], pm, pb[1], 'worst-leaf NE quarter'),
              (mp.mpf('0.63'), mp.mpf('0.64'), mp.mpf('0.0'), mp.mpf('0.2'), 'small box'),
              (mp.mpf('0.90'), mp.mpf('0.92'), mp.mpf('3.0'), mp.mpf('3.2'), 'small box 2')]
    # direct values on a grid built by the module that wrote direct_cap.json
    sys.path.insert(0, HERE)
    import direct_cap as dc
    dc.load_weights(); dc.setup_geometry()
    for (r0, r1, p0, p1, tag) in boxes:
        ub, ok = c.box_upper(r0, r1, p0, p1)
        mx = None; arg = None
        for i in range(10):
            for k in range(10):
                rr = r0 + (r1 - r0) * mp.mpf(i) / 9
                pp = p0 + (p1 - p0) * mp.mpf(k) / 9
                v = dc.cap(rr, pp, 'R1')
                if mx is None or v > mx:
                    mx = v; arg = (rr, pp)
        u = cr.ehi(ub) if ok else None
        print('    %-22s kernel_ub=%s  max_direct=%s  contains=%s  slack=%.3e'
              % (tag, mp.nstr(u, 30) if ok else 'undecided', mp.nstr(mx, 30), (u is not None and u >= mx),
                 float(u - mx) if ok else float('nan')))
        if ok and u < mx:
            print('       ^^ VIOLATION: kernel bound below a directly computed value inside the box')
            print('          at rho=%s phi=%s' % (mp.nstr(arg[0], 25), mp.nstr(arg[1], 25)))

    json.dump(dict(nbox=res['nbox'], leaves=res['leaves'], unsolved=res['unsolved'],
                   worst_leaf_ub=str(res['worst_leaf_ub']), violations=len(bad)),
              open(os.path.join(LOGS, 'kernel_controls.json'), 'w'), indent=1)


if __name__ == '__main__':
    main()
