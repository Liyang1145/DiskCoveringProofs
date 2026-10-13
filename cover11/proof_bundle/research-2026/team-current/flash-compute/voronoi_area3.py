# -*- coding: utf-8 -*-
"""voronoi_area3.py -- which (q,k) allocations are excluded by the area envelope, at which r.

For each allocation: 9 boundary cells with equal q = (42 - k1 - k2)/9 (Jensen concavity in q),
interior cells with k1 <= k2, envelope
    E = 9 * max_{alpha >= alpha_min} [ Seg(f(alpha)) + (r^2/2) sin alpha + (r^2/2) q sin((2pi-alpha)/q) ]
        + (r^2/2) k1 sin(2pi/k1) + (r^2/2) k2 sin(2pi/k2),
alpha_min = the value with 9 f(alpha) = 2pi, and f is the SOUND bound
f_safe(alpha) = 2 asin(r * max(sin(alpha/2), 1/2))  (equals f_opt = 2 asin(r sin(alpha/2)) for alpha>=pi/3).
E < pi  =>  that allocation is impossible at that r.
Also prints the envelope of the actually-observed allocation of the saved object.

Numeric screening only, not a certificate.
"""
import math, json

ROOT = r"C:\Users\袁力阳\Desktop\ai4math2"


def fb_safe(r, a):
    return 2 * math.asin(min(1.0, r * max(math.sin(a / 2), 0.5)))


def fb_opt(r, a):
    return 2 * math.asin(min(1.0, r * math.sin(a / 2)))


def cell_env(r, q, a, fb=fb_safe):
    b = fb(r, a)
    return (b - math.sin(b)) / 2 + 0.5 * r * r * math.sin(a) + 0.5 * r * r * q * math.sin((2 * math.pi - a) / q)


def hub_env(r, k):
    return 0.5 * r * r * k * math.sin(2 * math.pi / k)


def best_alpha(r, q, n=9, fb=fb_safe, steps=600):
    lo = None
    for k in range(steps + 1):
        a = 1e-9 + (math.pi - 1e-9) * k / steps
        if n * fb(r, a) >= 2 * math.pi:
            lo = a
            break
    if lo is None:
        return None
    best = None
    for k in range(steps + 1):
        a = lo + (math.pi - lo) * k / steps
        v = cell_env(r, q, a, fb)
        if best is None or v > best[0]:
            best = (v, a)
    return best


def E_alloc(r, k1, k2, q):
    b = best_alpha(r, q)
    if b is None:
        return None
    return 9 * b[0] + hub_env(r, k1) + hub_env(r, k2), b[1]


def threshold(k1, k2, q, lo=0.347, hi=0.45, it=40):
    """r where E_alloc = pi.  E is increasing in r (envelope ~ r^2), so:
       E > pi  =>  r is above the crossing  =>  hi = mid."""
    for _ in range(it):
        mid = (lo + hi) / 2
        v = E_alloc(mid, k1, k2, q)
        if v is None:
            return None
        val = v[0]
        if val > math.pi:
            hi = mid
        else:
            lo = mid
    return (lo + hi) / 2


if __name__ == "__main__":
    print("allocation scan: equal q = (42-k1-k2)/9, k1<=k2, need 42-k1-k2 >= 18")
    print("E_max > pi means: this allocation is NOT excluded at that r")
    print()
    print("  k1  k2    q      r* (E=pi)     E(0.38)-pi   E(0.3710)-pi")
    rows = []
    for k1 in range(3, 13):
        for k2 in range(k1, 13):
            qtot = 42 - k1 - k2
            if qtot < 18:
                continue
            q = qtot / 9.0
            rstar = threshold(k1, k2, q)
            e38 = E_alloc(0.38, k1, k2, q)[0] - math.pi
            e371 = E_alloc(0.3710, k1, k2, q)[0] - math.pi
            rows.append((rstar, k1, k2, q, e38, e371))
    rows.sort(key=lambda t: (t[0] is None, t[0] if t[0] is not None else 1.0))
    for rstar, k1, k2, q, e38, e371 in rows:
        excl = "EXCLUDED" if rstar is not None and rstar > 0.3709 else ""
        print("  %2d  %2d  %6.3f   %.6f     %+.4f      %+.4f  %s" % (k1, k2, q, rstar, e38, e371, excl))
    print()
    # observed allocation of the saved certified object (q multiset 3,3,3,4,4,3,3,3,3 ; k=7,6)
    qs = [3, 3, 3, 4, 4, 3, 3, 3, 3]
    print("observed allocation of the saved object: q multiset %s, k1=7, k2=6" % qs)
    for r in (0.3800, 0.3790, 0.3760, 0.3720, 0.3710, 0.3700, 0.3680):
        # optimise alpha over the two groups (7 cells q=3, 2 cells q=4)
        best = None
        for ka in range(201):
            a3 = 1e-6 + (math.pi - 1e-6) * ka / 200
            for kb in range(201):
                a4 = 1e-6 + (math.pi - 1e-6) * kb / 200
                if 7 * fb_safe(r, a3) + 2 * fb_safe(r, a4) < 2 * math.pi:
                    continue
                v = 7 * cell_env(r, 3, a3) + 2 * cell_env(r, 4, a4)
                if best is None or v > best[0]:
                    best = (v, a3, a4)
        if best is None:
            print("   r=%.4f : no feasible alpha" % r)
            continue
        tot = best[0] + hub_env(r, 7) + hub_env(r, 6)
        print("   r=%.4f  E_obs=%.6f  slack=%+.6f   (alpha3=%.4f alpha4=%.4f)"
              % (r, tot, tot - math.pi, best[1], best[2]))
