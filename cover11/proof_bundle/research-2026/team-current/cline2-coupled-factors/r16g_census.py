"""cline2-coupled-factors R16g: precise active-set census at the admissibility boundaries.

Corrections to my earlier reading (verified here):
  * at delta = b1 (A = 0) only the face-1 cap is tight and the cap/domain boundaries differ
    from what I first assumed;
  * the run endpoints of each branch are where EITHER beta = 0 (norm circle) OR a cap
    constraint turns on OR the delta-domain end is reached.
This script labels every run endpoint and every interior root by its active constraint
(residual < 1e-7), and reports the largest admissible delta per branch.
"""
import numpy as np, json, math
from pathlib import Path
P = Path(__file__).parent
OUT = P / 'out'
zJ = json.loads((P.parent/'lead'/'joint_nested_frozen.json').read_text())['z']
Z3_Z1 = zJ[3]-zJ[1]
A1 = zJ[1]-zJ[9]; A2 = zJ[3]-zJ[9]
B1 = -zJ[16]; G1 = -zJ[78]; B2 = zJ[20]; G2 = zJ[82]
R = 19/50


def quad(beta, gamma, e):
    return beta*e*e + gamma*e


def H_of(delta, r, b1, b2, j):
    s = math.sqrt(1.0-r*r)
    if j == 0:
        return 2*r*math.sin(2*b1-delta)
    if j == 1:
        return 2*r*math.sin(2*b2+delta)
    q = (1.0-r)**2 - s*s*math.sin(delta)**2
    if q <= 0:
        return None
    return s*math.cos(delta) + (1 if j == 2 else -1)*math.sqrt(q)


def residuals(delta, r, b1, b2, j):
    s = math.sqrt(1.0-r*r)
    H = H_of(delta, r, b1, b2, j)
    if H is None:
        return None
    Aa = b1-delta; Bb = b2+delta
    a1 = 2*r*math.sin(b1+Aa) - H          # face-1 cap >= 0
    a2 = 2*r*math.sin(b2+Bb) - H          # face-2 cap >= 0
    be = H*H - 2*s*math.cos(delta)*H + 2*r*(1.0-r)   # exterior norm >= 0
    return H, a1, a2, be


def admissible(delta, r, b1, b2, j, tol=1e-12):
    rs = residuals(delta, r, b1, b2, j)
    if rs is None:
        return False
    H, a1, a2, be = rs
    if H <= s_minus(r) or H >= 2*r:
        return False
    return a1 >= -tol and a2 >= -tol and be >= -tol


def s_minus(r):
    return math.sqrt(1-r*r) - (1-r)


def label(delta, r, b1, b2, j, tol=1e-7):
    rs = residuals(delta, r, b1, b2, j)
    if rs is None:
        return 'infeasible'
    H, a1, a2, be = rs
    tags = []
    if abs(a1) < tol:
        tags.append('face1-cap')
    if abs(a2) < tol:
        tags.append('face2-cap')
    if abs(be) < tol:
        tags.append('norm-circle')
    if abs(delta-b1) < tol:
        tags.append('domain delta=b1')
    if abs(delta+b2) < tol:
        tags.append('domain delta=-b2')
    return '+'.join(tags) if tags else 'strict-interior-boundary'


print('=== run endpoints per branch, labelled (r=0.375,1.1,1.05 and 0.38,1.0,1.0) ===')
for (r, b1, b2) in [(0.375, 1.1, 1.05), (0.38, 1.0, 1.0), (0.375, 1.0, 1.0)]:
    print(f'  r={r} b1={b1} b2={b2}')
    for j in (0, 1, 2, 3):
        xs = np.linspace(-b2, b1, 20001)
        adm = [d for d in xs if admissible(d, r, b1, b2, j)]
        if not adm:
            print(f'     j={j}: infeasible everywhere')
            continue
        lo, hi = adm[0], adm[-1]
        print(f'     j={j}: admissible delta in [{lo:.6f},{hi:.6f}]  '
              f'({len(adm)}/{len(xs)} samples)')
        print(f'        lower end active: {label(lo, r, b1, b2, j)}')
        print(f'        upper end active: {label(hi, r, b1, b2, j)}')
        # value at ends
        d0 = lo+1e-9; d1 = hi-1e-9
        # compute V via the derivative module to reuse the full formula
        import sys
        sys.path.insert(0, str(P))
        import r16b_analytic_deriv as AA
        v0 = AA.value_and_deriv(lo, r, b1, b2, j)
        v1 = AA.value_and_deriv(hi, r, b1, b2, j)
        if v0 and v1:
            print(f'        V(lower)={v0[0]:.6f}  V(upper)={v1[0]:.6f}  '
                  f'dV(lower)={v0[1]:+.6f}  dV(upper)={v1[1]:+.6f}')

print('\n=== which cap turns on where: branch 0, condition a2 >= 0 ===')
for (r, b1, b2) in [(0.375, 1.1, 1.05), (0.38, 1.0, 1.0)]:
    xs = np.linspace(-b2, b1, 2001)
    print(f'  r={r} b1={b1} b2={b2}:')
    for j in (0,):
        prev = None
        for d in xs:
            rs = residuals(d, r, b1, b2, j)
            if rs is None:
                prev = None; continue
            H, a1, a2, be = rs
            ok = (a1 >= 0 and a2 >= 0 and be >= 0)
            if prev is not None and ok != prev:
                print(f'     j={j}: admissibility changes at delta ~ {d:.6f} '
                      f'({label(d, r, b1, b2, j)})')
            prev = ok
