"""cline2-coupled-factors R16: saturated-face branch derivative structure in delta.

Object (lead SATURATED-FACE-BOUNDARY-CHART.md, C861/C862):
  face-1 boundary : H = 2r sin(b1+A),  A = b1 - delta      (hub on the first face circle)
  face-2 boundary : H = 2r sin(b2+B),  B = b2 + delta
  norm boundary   : H = s cos(delta) +- sqrt((1-r)^2 - s^2 sin^2 delta),  s = sqrt(1-r^2)
  objective       : B(delta) = (z3-z1) delta + H r (sin b1 sin A + sin b2 sin B)
                               + sum_i [ a_i phi_i + quad(b_i, g_i, rho_i) ]
  wedge closure   : delta in [-b2, b1];  delta = b1 is the RIDGE (A=0, both faces tight)

This script maps, on the fixed ranges b1,b2 in [1, arccos r], r in [.375,.38], the
DERIVATIVE STRUCTURE of B in delta on each branch: number of sign changes, monotone arcs,
and the location of the extrema relative to the ridge (delta=b1) and the domain endpoints.
It is a structural readout to decide between "monotone arcs / finite root structure" and
"residual interior maximum".  Numeric; no claim.
"""
import numpy as np, json, math, sys
from pathlib import Path
P = Path(__file__).parent
LEAD = P.parent / 'lead'
OUT = P / 'out'
OUT.mkdir(exist_ok=True)

# ---- frozen coefficients (the current ones) ----
zJ = json.loads((LEAD/'joint_nested_frozen.json').read_text())['z']
Z = {i: zJ[i] for i in range(len(zJ))}
Z3_Z1 = Z[3]-Z[1]
A1 = Z[1]-Z[9]      # face1 angular coefficient
A2 = Z[3]-Z[9]      # face2 angular coefficient
B1 = -Z[16]; G1 = -Z[78]     # quad coefficients used by the lead's setup for face1
B2 = Z[20];  G2 = Z[82]
print('z-based constants: z3-z1 =', Z3_Z1, ' a1 =', A1, ' a2 =', A2,
      ' (b1,g1) =', (B1, G1), ' (b2,g2) =', (B2, G2))


def quad(beta, gamma, e):
    """the lead's quad_range(beta,gamma,e) read as beta*e + gamma*e^2 (sign convention per setup)"""
    return beta*e + gamma*e*e


def branch_value(delta, r, b1, b2, j):
    s = math.sqrt(1.0-r*r)
    A = b1-delta; B = b2+delta
    if A < 0 or B < 0:
        return None
    if j == 0:
        H = 2*r*math.sin(b1+A)
    elif j == 1:
        H = 2*r*math.sin(b2+B)
    else:
        rad = (1.0-r)**2 - s*s*math.sin(delta)**2
        if rad < 0:
            return None
        H = s*math.cos(delta) + (1 if j == 2 else -1)*math.sqrt(rad)
    # filters from the lead's branch()
    if H <= s-(1.0-r) or H >= 2*r:
        return None
    if H > 2*r*math.sin(b1+A) or H > 2*r*math.sin(b2+B):
        return None
    if H*H - 2*s*math.cos(delta)*H + 2*r*(1.0-r) > 0:
        return None
    val = Z3_Z1*delta + H*r*(math.sin(b1)*math.sin(A) + math.sin(b2)*math.sin(B))
    for i, (b, ang, aa, bb, gg) in enumerate([(b1, A, A1, B1, G1), (b2, B, A2, B2, G2)]):
        if j == i:
            e = r*math.sin(ang)      # R = 19/50 cancels in e only if normalized; keep raw
            phi = b
        else:
            Y = 2*r*math.sin(b)*math.sin(ang)
            X = H - 2*r*math.sin(b)*math.cos(ang)
            Q = X*X+Y*Y
            if Q < 1.0/50000**2 or Q > 4*r*r:
                return None
            e = math.sqrt(Q)/2.0
            phi = math.atan2(Y, X)
        val += aa*phi + quad(bb, gg, e)
    return val


def profile(r, b1, b2, j, n=2001):
    """sample B(delta) on its admissible sub-interval and report derivative sign structure"""
    lo, hi = -b2, b1
    ds = np.linspace(lo, hi, n)
    vs = np.array([branch_value(d, r, b1, b2, j) if branch_value(d, r, b1, b2, j) is not None
                   else np.nan for d in ds])
    ok = ~np.isnan(vs)
    if ok.sum() < 10:
        return None
    d = ds[ok]; v = vs[ok]
    dv = np.gradient(v, d)
    sgn = np.sign(dv)
    changes = int(np.sum(np.abs(np.diff(sgn)) > 0))
    return dict(n=len(d), dlo=d[0], dhi=d[-1], vmin=v.min(), vmax=v.max(),
                dv_min=dv.min(), dv_max=dv.max(), sign_changes=changes,
                d_at_vmax=float(d[np.argmax(v)]), d_at_vmin=float(d[np.argmin(v)]),
                monotone=(changes == 0))


# ---- structural scan over the stated ranges (bounded: 9 x 9 x 4 = 324 profiles) ----
print('\n=== branch profile summary (r in [.375,.38], b1,b2 in [1, arccos r]) ===')
rows = []
for r in [0.375, 0.376, 0.377, 0.378, 0.379, 0.38]:
    bmax = math.acos(r)
    for b1 in np.linspace(1.0, bmax, 7):
        for b2 in np.linspace(1.0, bmax, 7):
            for j in range(4):
                pr = profile(r, b1, b2, j)
                if pr is None:
                    continue
                rows.append(dict(r=r, b1=float(b1), b2=float(b2), j=j, **pr))
print(f'{len(rows)} profiles computed')
import collections
cnt = collections.Counter((row['j'], row['monotone'], row['sign_changes']) for row in rows)
print('count by (branch, monotone, sign_changes):')
for k in sorted(cnt):
    print(f'   j={k[0]} monotone={k[1]} sign_changes={k[2]}: {cnt[k]}')
print('\nprofile count per branch:', {j: sum(1 for row in rows if row["j"] == j)
                                     for j in range(4)})
nonmono = [row for row in rows if not row['monotone']]
print(f'non-monotone profiles: {len(nonmono)} of {len(rows)}')
if nonmono:
    print('   worst (largest sign_changes):')
    for row in sorted(nonmono, key=lambda t: -t['sign_changes'])[:5]:
        print(f'      r={row["r"]} b1={row["b1"]:.4f} b2={row["b2"]:.4f} j={row["j"]} '
              f'sign_changes={row["sign_changes"]} dv in [{row["dv_min"]:.4f},'
              f'{row["dv_max"]:.4f}] argmax at delta={row["d_at_vmax"]:.4f}')
json.dump(rows, open(OUT/'r16_profiles.json', 'w'), indent=1)
print('\nsaved out/r16_profiles.json')
