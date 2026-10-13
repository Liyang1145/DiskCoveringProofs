"""R16 decisive check: run the LEAD's own kernels (imported, no edits, no certificate writes if
possible) to get the legal domain and objective, then compare the certified upper bound against
an independent numeric scan of the same objective on the same legal set.

Also prints the built disks and the polar/Cartesian parametrisations so the coverage question is
settled on the code's own objects.
"""
import json, math, sys
from pathlib import Path

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
LEAD = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\lead')
sys.path.insert(0, str(LEAD))
import os
os.chdir(LEAD)

import interval_hub_boundary as hb
import interval_hub_saturated as hs
import interval_hub_norm_only as hn
import interval_joint_patch as k

print('=== module constants ===')
print('R =', k.R if hasattr(k, 'R') else 'n/a')
print('z[0:12] =', [float(v.a) for v in k.z[:12]])
print('domain  =', k.domain)
R0 = 0.38 if not hasattr(k, 'R') else k.R
try:
    Rf = float(k.R.a)
except Exception:
    Rf = float(k.R) if isinstance(k.R, float) else 0.38
print('Rf =', Rf)

print('\n=== the disks as the code builds them (r=0.375, b1=b2=1) ===')
r, b1, b2 = 0.375, 1.0, 1.0
s = math.sqrt(1 - r * r)
disks = [(r * math.sin(2 * b1), -r * math.cos(2 * b1), r),
         (r * math.sin(2 * b2), r * math.cos(2 * b2), r),
         (s, 0.0, 1 - r)]
for i, d in enumerate(disks):
    print(f'  disk{i}: center=({d[0]:.9f},{d[1]:.9f}) radius={d[2]:.9f}')

print('\n=== polar branch H (j=2,3) vs the circle (s,0)+(1-r)(cos th, sin th) ===')
print('check: is (H(de), s*sin(de)) on that circle for every de?')
for de in (0.0, 0.1, 0.2, 0.3):
    rad = (1 - r) ** 2 - s * s * math.sin(de) ** 2
    if rad < 0:
        print(f'  de={de}: radicand<0')
        continue
    for sg, tag in ((1, 'j=2'), (-1, 'j=3')):
        H = s * math.cos(de) + sg * math.sqrt(rad)
        t = s * math.sin(de)
        dist = math.hypot(H - s, t)
        print(f'  de={de} {tag}: H={H:.9f} t={t:.9f}  |c-(s,0)|={dist:.9f}  (1-r)={1-r:.9f}  '
              f'on-circle={abs(dist - (1 - r)) < 1e-12}')

print('\n=== legal set: scan (v,t) on the three circles, apply the code filters, evaluate objective ===')
import numpy as np
f = hn  # norm-only kernel


def obj_from_circle(r, b1, b2, v, t):
    """rebuild the objective exactly as interval_hub_boundary.circle does, with floats"""
    if v <= 0:
        return None
    for (dx, dy, rr) in disks[:2]:
        if (v - dx) ** 2 + (t - dy) ** 2 - rr * rr > 1e-12:
            return None
    if (t + v * math.tan(b2)) < -1e-12 or (v * math.tan(b1) - t) < -1e-12:
        return None
    z = [float(zz.a) for zz in k.z]
    ans = r * (math.sin(b1) ** 2 + math.sin(b2) ** 2) * v + \
        r * (math.sin(b2) * math.cos(b2) - math.sin(b1) * math.cos(b1)) * t
    for b, sg, a, bb, gg in [(b1, -1, z[1] - z[9], -z[16], -z[78]),
                             (b2, 1, z[3] - z[9], z[20], z[82])]:
        Y = 2 * r * math.sin(b) ** 2 + sg * t
        X = v - r * math.sin(2 * b)
        if Y < 0:
            return None
        Q = max(X * X + Y * Y, 1 / 50000 ** 2)
        if Q > 4 * r * r + 1e-12:
            return None
        ee = math.sqrt(Q) / (2 * Rf)
        ans += a * math.atan2(Y, X) + k.quad_range(bb, gg, ee) if False else 0.0
    return ans


print('\nnumeric max of the FLOAT kernel objective on the three circles (r=0.375,b1=b2=1):')
best = (-1e18, None)
for j in range(3):
    cx, cy, rho = disks[j]
    for kk in range(200001):
        th = -math.pi + 2 * math.pi * kk / 200000
        v = cx + rho * math.cos(th)
        t = cy + rho * math.sin(th)
        if v <= 0:
            continue
        ok = True
        for i, (dx, dy, rr) in enumerate(disks):
            if i == j:
                continue
            if (v - dx) ** 2 + (t - dy) ** 2 > rr * rr + 1e-12:
                ok = False; break
        if not ok:
            continue
        if (t + v * math.tan(b2)) < -1e-12 or (v * math.tan(b1) - t) < -1e-12:
            continue
        z = [float(zz.a) for zz in k.z]
        ans = (r * (math.sin(b1) ** 2 + math.sin(b2) ** 2) * v
               + r * (math.sin(b2) * math.cos(b2) - math.sin(b1) * math.cos(b1)) * t)
        for b, sg, a, bb, gg in [(b1, -1, z[1] - z[9], -z[16], -z[78]),
                                 (b2, 1, z[3] - z[9], z[20], z[82])]:
            Y = 2 * r * math.sin(b) ** 2 + sg * t
            X = v - r * math.sin(2 * b)
            Y = max(Y, 0.0)
            Q = min(max(X * X + Y * Y, 1 / 50000 ** 2), 4 * r * r)
            ee = math.sqrt(Q) / (2 * Rf)
            ans += a * math.atan2(Y, X)
            # quad_range(bb,gg,ee): evaluate the interval integrand numerically
            ans += (bb * ee + gg * ee * ee / 2)
        if ans > best[0]:
            best = (ans, (j, v, t))
print(f'  max = {best[0]:.9f} at {best[1]}')
