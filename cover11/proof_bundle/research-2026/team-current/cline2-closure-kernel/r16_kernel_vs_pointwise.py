"""R16 decisive numeric: evaluate the KERNEL's own inner bound (interval_hub_norm_only.bound)
at fixed outer (r,b1,b2) inside the certificate domain [0.375,0.38]x[1,acos(.375)]^2, and a
pointwise (non-interval) version of the same objective over the same legal domain, then compare
with the certified upper 28.103151732510888.
"""
import math, sys, os, json
from pathlib import Path

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
sys.path.insert(0, str(LEAD))
os.chdir(LEAD)

import interval_joint_patch as k
import interval_hub_norm_only as hn

cert = json.loads((LEAD / 'patch_outer_norm_boundary_certificate.json').read_text())
print('certified upper =', cert['upper'], ' domain =', cert['domain'])

Rf = 0.38
z = [float(zz.a) for zz in k.z]

print('\n=== kernel inner bound at fixed outer points ===')
for (r, b1, b2) in [(0.376, 1.05, 1.05), (0.375, 1.0, 1.0), (0.38, 1.1, 1.1),
                    (0.377, 1.02, 1.08), (0.379, 1.18, 1.02)]:
    box = [k.I(r, r), k.I(b1, b1), k.I(b2, b2)]
    row = hn.bound(box, tol=1e-5, maxeval=129)
    if row is None:
        print(f'  (r,b1,b2)=({r},{b1},{b2}): bound() returned None')
        continue
    print(f'  (r,b1,b2)=({r},{b1},{b2}): kernel inner upper = {row["upper"]:.9f}')
    for nm in ('widths', 'normbranches'):
        if nm in row:
            ups = [x['upper'] for x in row[nm]]
            print(f'      {nm} uppers: {[round(u, 9) for u in ups]}')

print('\n=== pointwise version of the same objective over the legal domain ===')
print('(three disks, wedge, Y>=0, Q in [1/50000^2, 4r^2] -- all the kernel filters, floats)')


def obj_point(r, b1, b2, v, t):
    s = math.sqrt(1 - r * r)
    disks = [(r * math.sin(2 * b1), -r * math.cos(2 * b1), r),
             (r * math.sin(2 * b2), r * math.cos(2 * b2), r),
             (s, 0.0, 1 - r)]
    if v <= 0:
        return None
    for i, (dx, dy, rr) in enumerate(disks):
        for j2, (ex, ey, er) in enumerate(disks):
            if i == j2:
                continue
            if (v - ex) ** 2 + (t - ey) ** 2 - er * er > 1e-12:
                return None
    if (t + v * math.tan(b2)) < -1e-12 or (v * math.tan(b1) - t) < -1e-12:
        return None
    ans = (r * (math.sin(b1) ** 2 + math.sin(b2) ** 2) * v
           + r * (math.sin(b2) * math.cos(b2) - math.sin(b1) * math.cos(b1)) * t)
    for b, sg, a, bb, gg in [(b1, -1, z[1] - z[9], -z[16], -z[78]),
                             (b2, 1, z[3] - z[9], z[20], z[82])]:
        Y = 2 * r * math.sin(b) ** 2 + sg * t
        X = v - r * math.sin(2 * b)
        if Y < 0:
            return None
        Q = X * X + Y * Y
        if Q < 1 / 50000 ** 2 or Q > 4 * r * r:
            return None
        ee = math.sqrt(Q) / (2 * Rf)
        ans += a * math.atan2(Y, X) + bb * ee + gg * ee * ee
    return ans


best = (-1e18, None)
for j in range(3):
    if j == 0:
        r_, b1_, b2_ = 0.376, 1.05, 1.05
    else:
        r_, b1_, b2_ = 0.376, 1.05, 1.05
    s = math.sqrt(1 - r_ * r_)
    disks = [(r_ * math.sin(2 * b1_), -r_ * math.cos(2 * b1_), r_),
             (r_ * math.sin(2 * b2_), r_ * math.cos(2 * b2_), r_),
             (s, 0.0, 1 - r_)]
    cx, cy, rho = disks[j]
    N = 100000
    for kk in range(N + 1):
        th = -math.pi + 2 * math.pi * kk / N
        v = cx + rho * math.cos(th)
        t = cy + rho * math.sin(th)
        val = obj_point(r_, b1_, b2_, v, t)
        if val is not None and val > best[0]:
            best = (val, (j, th, v, t))
print(f'  max over the three circles at (r,b1,b2)=(0.376,1.05,1.05) = {best[0]:.9f}')
print(f'  attained at j={best[1][0]} theta={best[1][1]:.6f} (v,t)=({best[1][2]:.9f},{best[1][3]:.9f})')
print(f'  certified upper for the whole domain = {cert["upper"]:.9f}')
print(f'  margin (certified - pointwise) = {cert["upper"] - best[0]:+.9f}')
