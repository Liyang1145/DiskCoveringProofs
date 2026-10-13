"""Verification of the CORRECT degenerate-corner facts (post-rejection).

Only re-derives, from the saved configuration, the quantities the lead named:
  * ring centre norms  (= sqrt(1-r^2) at the saturating/root position, NOT r)
  * the covered arc full width at saturation (= 2 asin r)
  * the switch-angle / wedge-angle bookkeeping (to identify which measure sums to 2 pi)
Nothing here is used as evidence for any claim; it is a calibration table so that the
invalid statements can be replaced by correct ones if the lead ever wants them.
"""
import json, io, math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
D = json.load(io.open(ROOT / 'n11' / 'upper' / 'certified_object.json', encoding='utf-8-sig'))
C = [(int(a) / 1e17, int(b) / 1e17) for a, b in D['centers_scaled_1e17']]
R = float(D['certified_interval']['lo'])
RINGS = [1, 3, 4, 5, 6, 7, 8, 9, 10]
ORDER = [5, 7, 1, 8, 6, 4, 9, 10, 3]
print('r (registered) = %.15f' % R)
print('sqrt(1-r^2)    = %.15f' % math.sqrt(1 - R * R))
print('r              = %.15f   <- the WRONG value I used for the ring-centre norm' % R)
print('2 asin r       = %.15f   <- full covered arc width at saturation' % (2 * math.asin(R)))
print()
print('ring centre norms (saved):')
for i in RINGS:
    print('   c%-2d  %.15f' % (i, math.hypot(*C[i])))
print()


def bisect_bd(i, j):
    ax, ay = C[i][0] - C[j][0], C[i][1] - C[j][1]
    Cc = ((C[i][0] ** 2 + C[i][1] ** 2) - (C[j][0] ** 2 + C[j][1] ** 2)) / 2
    a2 = ax * ax + ay * ay
    if a2 <= Cc ** 2:
        return []
    m = (Cc * ax / a2, Cc * ay / a2)
    t = math.sqrt(a2 - Cc ** 2) / a2
    return [(m[0] - t * ay, m[1] + t * ax), (m[0] + t * ay, m[1] - t * ax)]


print('switch data (P on bd D, |P-c_i| = |P-c_j| = rho):')
rows = []
for k in range(9):
    i, j = ORDER[k], ORDER[(k + 1) % 9]
    ai = math.atan2(C[i][1], C[i][0]) % (2 * math.pi)
    aj = math.atan2(C[j][1], C[j][0]) % (2 * math.pi)
    if aj < ai:
        aj += 2 * math.pi
    P = None
    for p in bisect_bd(i, j):
        th = math.atan2(p[1], p[0]) % (2 * math.pi)
        if th < ai:
            th += 2 * math.pi
        if ai - 1e-9 <= th <= aj + 1e-9:
            P = p
    if P is None:
        continue
    rho = math.hypot(P[0] - C[i][0], P[1] - C[i][1])
    u = (C[i][0] - P[0], C[i][1] - P[1])
    v = (C[j][0] - P[0], C[j][1] - P[1])
    ang_uv = math.acos(max(-1, min(1, (u[0] * v[0] + u[1] * v[1]) / (rho * rho))))
    # wedge half-angle from the switch towards the arc interior: angle between (P - c_owner)
    # and the radial direction of P
    rad = (P[0], P[1])
    nrad = math.hypot(*rad)
    cw = math.acos(max(-1, min(1, ((P[0] - C[i][0]) * rad[0] + (P[1] - C[i][1]) * rad[1]) / (rho * nrad))))
    # half-width of the arc owned by site i around the switch direction
    si = math.hypot(*C[i])
    w_i = math.acos(max(-1, min(1, (1 + si * si - R * R) / (2 * si))))
    rows.append((i, j, P, rho, ang_uv, cw, w_i))
    print('   (%2d,%2d): rho=%.12f  angle(c_i-P,c_j-P)=%.12f  angle(P-c_i, radial)=%.12f  w_i=%.12f'
          % (i, j, rho, ang_uv, cw, w_i))
print()
print('sum over switches of angle(c_i-P,c_j-P) = %.12f' % sum(r[4] for r in rows))
print('sum over switches of 2*angle(P-c_i,radial) = %.12f' % sum(2 * r[5] for r in rows))
print('sum of w_i (arc half-widths) = %.12f   (pi = %.12f)' % (sum(r[6] for r in rows), math.pi))
print('sum of chord half-angles at the owner: 2*sum(angle(c_i-P,radial)) = %.12f' %
      (2 * sum(r[5] for r in rows)))
print()
print('identity check:  for each switch, (angle(P-c_i,radial) + angle(P-c_j,radial)) - pi = half of (pi - angle(c_i-P,c_j-P)):')
for (i, j, P, rho, ang_uv, cw, w_i) in rows:
    rad = (P[0], P[1]); nrad = math.hypot(*rad)
    cwj = math.acos(max(-1, min(1, ((P[0] - C[j][0]) * rad[0] + (P[1] - C[j][1]) * rad[1]) / (rho * nrad))))
    print('   (%2d,%2d): cw_i+cw_j-pi = %+.6e   (pi-angle_uv)/2 = %+.6e'
          % (i, j, cw + cwj - math.pi, (math.pi - ang_uv) / 2))
