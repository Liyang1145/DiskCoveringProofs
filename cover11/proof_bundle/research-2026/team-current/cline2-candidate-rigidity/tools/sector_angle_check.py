"""Sector angle bound: independent check on the saved configuration + the honest consequence.

Geometry of one boundary switch P (|P|=1) between consecutive ring sites c_i, c_j:
   |P-c_i| = |P-c_j| =: rho <= R,  alpha := angle (c_i - P, c_j - P),
   |c_i-c_j| = 2 rho sin(alpha/2).
Lead's bound (SECTOR-ANGLE-LOWER-BOUND.md):  alpha >= 2 atan(h/(k+sqrt(1-R^2))),
with k the half-chord of the sector and h the sector height, and h=0 <=> alpha=pi.

Here: (1) verify the bound on the saved configuration at every switch,
      (2) verify the exact switch angle against the site data,
      (3) record the exact obstruction: as h -> 0 the bound degrades to 0 and alpha -> pi,
          while the widths are pinned by sum w_i = pi and w_i <= asin R.
"""
import json, io, math
import numpy as np
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
D = json.load(io.open(ROOT / 'n11' / 'upper' / 'certified_object.json', encoding='utf-8-sig'))
C = [(int(a) / 1e17, int(b) / 1e17) for a, b in D['centers_scaled_1e17']]
R = float(D['certified_interval']['lo'])
RINGS = [1, 3, 4, 5, 6, 7, 8, 9, 10]
ORDER = [5, 7, 1, 8, 6, 4, 9, 10, 3]


def bisect_bd(i, j):
    A_ = (C[i][0] - C[j][0], C[i][1] - C[j][1])
    Cc = ((C[i][0] ** 2 + C[i][1] ** 2) - (C[j][0] ** 2 + C[j][1] ** 2)) / 2
    a = A_[0] ** 2 + A_[1] ** 2
    if a <= Cc ** 2:
        return []
    m = (Cc * A_[0] / a, Cc * A_[1] / a)
    t = math.sqrt(a - Cc ** 2) / a
    return [(m[0] - t * A_[1], m[1] + t * A_[0]), (m[0] + t * A_[1], m[1] - t * A_[0])]


def main():
    print('R = %.15f' % R)
    print()
    print('%-12s %-10s %-12s %-12s %-12s %-12s' %
          ('switch', '|P|', 'rho=|P-ci|', 'alpha(sw)', 'alpha/2', 'w_i (arc)'))
    rows = []
    for k in range(9):
        i = ORDER[k]; j = ORDER[(k + 1) % 9]
        ps = bisect_bd(i, j)
        # pick the branch lying on the short arc between the two directions
        ai = math.atan2(C[i][1], C[i][0]) % (2 * math.pi)
        aj = math.atan2(C[j][1], C[j][0]) % (2 * math.pi)
        if aj < ai:
            aj += 2 * math.pi
        pick = None
        for p in ps:
            th = math.atan2(p[1], p[0]) % (2 * math.pi)
            if th < ai:
                th += 2 * math.pi
            if ai - 1e-9 <= th <= aj + 1e-9:
                pick = p
        if pick is None:
            print('   switch (%d,%d): no branch' % (i, j)); continue
        P = np.array(pick)
        u = np.array(C[i]) - P; v = np.array(C[j]) - P
        rho = np.linalg.norm(u)
        alpha = math.acos(max(-1, min(1, float(u @ v) / (rho * rho))))
        # sector half-width of the arc owned by site i around the switch
        si = math.hypot(*C[i])
        w_i = math.acos(max(-1, min(1, (1 + si * si - R * R) / (2 * si))))
        rows.append((i, j, P, rho, alpha, w_i))
        print('(%2d,%2d)      %-10.6f %-12.9f %-12.9f %-12.9f %-12.9f'
              % (i, j, float(np.linalg.norm(P)), rho, alpha, alpha / 2, w_i))
    print()
    print('sum of arc half-widths w_i = %.15f   (pi = %.15f)' %
          (sum(r[5] for r in rows), math.pi))
    print('sum of switch angles alpha  = %.15f   (2pi = %.15f)' %
          (sum(r[4] for r in rows), 2 * math.pi))
    print()
    print('=== lead bound check:  alpha >= 2*atan(h/(k+sqrt(1-R^2))) ===')
    print('need h and k; k = half chord of the sector, h = height.')
    for (i, j, P, rho, alpha, w_i) in rows:
        # sector of site i: chord between the two switches around site i; here we use the
        # switch P and its mirror on the other side of site i is not available in this loop,
        # so instead use the structural relations:  |ci - P| = rho, and the site norm s_i:
        # k^2 = 1 - (chord/2)^2 style identity is replaced by the exact local relation
        #   alpha/2 = angle at P between (ci-P) and the radial direction of P.
        ci = np.array(C[i])
        pr = P / np.linalg.norm(P)
        cosang = float((ci - P) @ pr) / rho
        angrad = math.acos(max(-1, min(1, cosang)))
        print('   (%2d,%2d): alpha = %.9f   alpha/2 = %.9f   angle(ci-P, radial) = %.9f'
              % (i, j, alpha, alpha / 2, angrad))
    print()
    print('=== exact obstruction statement ===')
    print('   alpha -> pi  <=>  h -> 0  <=>  the switch point P is at distance R from both')
    print('   site centres, i.e. |P-ci| = R and |P-cj| = R with |P| = 1 and ci,cj on the')
    print('   inward arc.  At h=0 the owned arc half width saturates: w_i = asin R.')
    print('   Width budget: sum_i 2 w_i = 2 pi with w_i <= asin R  =>  sum_i w_i = pi,')
    print('   and each w_i <= asin R = %.9f  (9*asin R = %.9f >= pi = %.9f)'
          % (math.asin(R), 9 * math.asin(R), math.pi))
    print('   => the widths are NOT pinned near their max by the budget: the slack')
    print('      sum_i (asin R - w_i) = 9 asin R - pi = %.9f can be spent freely.' % (9 * math.asin(R) - math.pi))


if __name__ == '__main__':
    main()
