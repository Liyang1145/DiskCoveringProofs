"""cline2-coupled-factors R16b: analytic delta-derivative of the saturated-face boundary
objective, and the root structure that decides monotone-arcs vs residual-interior-maximum.

Conventions read off the lead's sources:
  * quad_range(a,b,x) = a*x^2 + b*x   (interval_joint_patch.py), so
    quad(beta,gamma,e) = beta*e^2 + gamma*e
    with beta1 = -z[16] = +0.405431351, gamma1 = -z[78] = -0.870277865,
         beta2 =  z[20] = +0.400827103, gamma2 =  z[82] = -0.86525597.
  * branch value (interval_hub_saturated.py:24-33):
      V(delta) = (z3-z1) delta + H r (sin b1 sin A + sin b2 sin B)
                 + sum_i [ a_i phi_i + quad(beta_i, gamma_i, e_i) ]
    with a1 = z1-z9, a2 = z3-z9, and for the ON-face index e = r sin(angle)/R, phi = b.
    Here I keep the R = 19/50 normalization explicit (it does not cancel in e).

Derivatives: exact closed forms per branch (H' from the branch equation), assembled by
chain rule.  This is reported as the derivative structure: sign-change counts and the
locations of the extrema, on a bounded parameter scan (not a grid-exhaustive search).
"""
import numpy as np, json, math
from pathlib import Path
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']
Z3_Z1 = zJ[3]-zJ[1]
A1 = zJ[1]-zJ[9]; A2 = zJ[3]-zJ[9]
B1 = -zJ[16]; G1 = -zJ[78]
B2 = zJ[20];  G2 = zJ[82]
R = 19/50


def quad(beta, gamma, e):
    return beta*e*e + gamma*e


def quad_d(beta, gamma, e):
    return 2*beta*e + gamma


def value_and_deriv(delta, r, b1, b2, j):
    """returns (V, dV/ddelta) or None.  Closed-form derivative per branch."""
    s = math.sqrt(1.0-r*r)
    A = b1-delta; B = b2+delta
    if A < 0 or B < 0:
        return None
    # ---- H and H' per branch ----
    if j == 0:
        H = 2*r*math.sin(b1+A); dH = 2*r*math.cos(b1+A)*(-1.0)
    elif j == 1:
        H = 2*r*math.sin(b2+B); dH = 2*r*math.cos(b2+B)*(+1.0)
    else:
        rad = (1.0-r)**2 - s*s*math.sin(delta)**2
        if rad <= 0:
            return None
        sq = math.sqrt(rad)
        sgn = 1.0 if j == 2 else -1.0
        H = s*math.cos(delta) + sgn*sq
        dH = -s*math.sin(delta) + sgn*(-s*s*math.sin(delta)*math.cos(delta)/sq)
    if H <= s-(1.0-r) or H >= 2*r:
        return None
    if H > 2*r*math.sin(b1+A)+1e-15 or H > 2*r*math.sin(b2+B)+1e-15:
        return None
    if H*H - 2*s*math.cos(delta)*H + 2*r*(1.0-r) > 1e-15:
        return None
    # ---- objective ----
    V = Z3_Z1*delta + H*r*(math.sin(b1)*math.sin(A) + math.sin(b2)*math.sin(B))
    dV = Z3_Z1 + dH*r*(math.sin(b1)*math.sin(A) + math.sin(b2)*math.sin(B)) \
        + H*r*(math.sin(b1)*math.cos(A)*(-1.0) + math.sin(b2)*math.cos(B)*(+1.0))
    for i, (b, ang, dang, aa, beta, gamma) in enumerate(
            [(b1, A, -1.0, A1, B1, G1), (b2, B, +1.0, A2, B2, G2)]):
        if j == i:
            e = r*math.sin(ang)/R
            de = r*math.cos(ang)*dang/R
            phi = b; dphi = 0.0
        else:
            Y = 2*r*math.sin(b)*math.sin(ang)
            X = H - 2*r*math.sin(b)*math.cos(ang)
            Q = X*X+Y*Y
            if Q < 1.0/50000**2 or Q > 4*r*r:
                return None
            e = math.sqrt(Q)/2.0/R
            phi = math.atan2(Y, X)
            dY = 2*r*math.sin(b)*math.cos(ang)*dang
            dX = dH - 2*r*math.sin(b)*(-math.sin(ang))*dang
            dphi = (X*dY - Y*dX)/Q
            de = (X*dX + Y*dY)/(2.0*math.sqrt(Q))/2.0/R
        V += aa*phi + quad(beta, gamma, e)
        dV += aa*dphi + quad_d(beta, gamma, e)*de
    return V, dV


def structure(r, b1, b2, j, n=4001):
    lo, hi = -b2, b1
    ds = np.linspace(lo, hi, n)
    out = [(d, value_and_deriv(d, r, b1, b2, j)) for d in ds]
    pts = [(d, v, dv) for d, rv in out if rv is not None for v, dv in [rv]]
    if len(pts) < 10:
        return None
    d = np.array([p[0] for p in pts]); v = np.array([p[1] for p in pts])
    dv = np.array([p[2] for p in pts])
    sgn = np.sign(dv)
    ch = int(np.sum(np.abs(np.diff(sgn)) > 0))
    return dict(n=len(d), dlo=d[0], dhi=d[-1], vmax=v.max(), d_at_vmax=d[np.argmax(v)],
                dvmax=dv.max(), dvmin=dv.min(), sign_changes=ch,
                interior_extremum=bool(d[np.argmax(v)] > d[0]+1e-9
                                       and d[np.argmax(v)] < d[-1]-1e-9))


print('z constants: z3-z1=%.9f a1=%.9f a2=%.9f beta1=%.9f gamma1=%.9f beta2=%.9f gamma2=%.9f'
      % (Z3_Z1, A1, A2, B1, G1, B2, G2))
bmax_ref = math.acos(0.375)
print(f'stated ranges: b1,b2 in [1, arccos r] (max {bmax_ref:.4f} at r=.375); r in [.375,.38]')
print('ridge is delta = b1 (A=0); domain is delta in [-b2, b1]\n')

import collections
print('=== analytic-derivative structure per branch ===')
res = []
for r in [0.375, 0.376, 0.377, 0.378, 0.379, 0.38]:
    bmax = math.acos(r)
    for b1 in np.linspace(1.0, bmax, 7):
        for b2 in np.linspace(1.0, bmax, 7):
            for j in range(4):
                st = structure(r, b1, b2, j)
                if st is None:
                    continue
                res.append(dict(r=r, b1=float(b1), b2=float(b2), j=j, **st))
print(f'{len(res)} branch profiles with analytic derivative')
c = collections.Counter((row['j'], row['sign_changes']) for row in res)
print('count by (branch j, number of derivative sign changes):')
for k in sorted(c):
    print(f'   j={k[0]}  sign_changes={k[1]} : {c[k]}')
print()
print('branches with an INTERIOR extremum (argmax strictly inside the delta domain):')
inter = [row for row in res if row['interior_extremum']]
print(f'   {len(inter)} of {len(res)}')
for row in sorted(inter, key=lambda t: -t['dvmax'])[:8]:
    print(f'   r={row["r"]} b1={row["b1"]:.4f} b2={row["b2"]:.4f} j={row["j"]} '
          f'sign_changes={row["sign_changes"]} argmax delta={row["d_at_vmax"]:.4f} '
          f'(domain [{row["dlo"]:.4f},{row["dhi"]:.4f}]) dv in '
          f'[{row["dvmin"]:.5f},{row["dvmax"]:.5f}]')
json.dump(res, open(OUT/'r16_deriv.json', 'w'), indent=1)
print('\nsaved out/r16_deriv.json')
