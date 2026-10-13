# -*- coding: utf-8 -*-
"""P21: STRESS TEST of the finite criterion on random q0-like configurations.

Criterion under test:
    max_{x in D} min_k |x - c_k|  ==  max_{x in S} min_k |x - c_k|
where S = {9 ring-ring switches on bd D} u {circumcentres of (hub, ring_i, ring_{i+1})}.

For each random configuration we report the reference value (dense polar grid + local
refinement) and the finite-set value, and the gap.
"""
import os, sys, math, json
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fan_core import HERE
from scipy.optimize import minimize

OUT = os.path.join(HERE, os.pardir, "out")
lines = []
def P(s=""):
    lines.append(s); print(s)

NR, NTH = 700, 3600
rs = np.linspace(0, 1, NR); ths = np.linspace(0, 2*np.pi, NTH, endpoint=False)
RR, TT = np.meshgrid(rs, ths, indexing='ij')
PTS = np.stack([(RR*np.cos(TT)).ravel(), (RR*np.sin(TT)).ravel()], axis=1)


def val_ref(ALL):
    d = np.linalg.norm(PTS[:, None, :]-ALL[None, :, :], axis=2).min(axis=1)
    i = int(np.argmax(d)); best = float(d[i])
    def neg(p):
        if p[0]**2+p[1]**2 > 1.0:
            return 1e4*(p[0]**2+p[1]**2-1.0)
        return -float(np.min(np.linalg.norm(ALL-p, axis=1)))
    res = minimize(neg, PTS[i], method='Nelder-Mead',
                   options=dict(xatol=1e-14, fatol=1e-16, maxiter=4000))
    return max(best, -res.fun)


def circum(ALL, h, i, j):
    a, b, c = ALL[h], ALL[i], ALL[j]
    dd = 2*(a[0]*(b[1]-c[1])+b[0]*(c[1]-a[1])+c[0]*(a[1]-b[1]))
    if abs(dd) < 1e-14:
        return None
    a2 = a@a; b2 = b@b; c2 = c@c
    return np.array([(a2*(b[1]-c[1])+b2*(c[1]-a[1])+c2*(a[1]-b[1]))/dd,
                     (a2*(c[0]-b[0])+b2*(a[0]-c[0])+c2*(b[0]-a[0]))/dd])


def val_finite(ALL, R, ring_idx, hub_idx, order):
    S = []
    n = len(ring_idx)
    for k in range(n):
        a = order[k]; b = order[(k+1) % n]
        ca, cb = ALL[a], ALL[b]
        dd = np.linalg.norm(ca-cb)
        if dd <= 0 or dd > 2*R:
            continue
        m = (ca+cb)/2
        hh = math.sqrt(max(R*R-dd*dd/4, 0.0))
        pp = np.array([-(cb-ca)[1], (cb-ca)[0]])/dd
        for sgn in (1, -1):
            q = m+sgn*hh*pp
            if np.linalg.norm(q) <= 1.0:
                S.append(q)
        for h in hub_idx:
            t = circum(ALL, h, a, b)
            if t is not None and np.linalg.norm(t-ALL[h]) <= R+1e-9:
                S.append(t)
    if not S:
        return 0.0, 0
    v = max(float(np.min(np.linalg.norm(ALL-q, axis=1))) for q in S)
    return v, len(S)


if __name__ == "__main__":
    rng = np.random.default_rng(4242)
    P("stress test: %-6s %-18s %-18s %-12s %-8s" % ("trial", "reference", "finite-set", "gap", "#S"))
    worst = -1e9
    for trial in range(400):
        R = rng.uniform(0.30, 0.395)
        rho = 1 - R + rng.uniform(0.03, 0.30, 9)       # ring moduli inside (1-R, 1+R)
        rho = np.minimum(rho, 1.0 - 1e-9)
        psi = np.sort(rng.uniform(0, 2*np.pi, 9))
        C = np.stack([rho*np.cos(psi), rho*np.sin(psi)], axis=1)
        H = rng.normal(0, 0.12, (2, 2))
        H *= (1-R)*np.minimum(1.0, (1-R)/np.maximum(1e-9, np.linalg.norm(H, axis=1)))[:, None]
        ALL = np.vstack([C, H])
        order = list(range(9))
        vref = val_ref(ALL)
        vfin, ns = val_finite(ALL, R, list(range(9)), [9, 10], order)
        gap = vref-vfin
        if gap > worst:
            worst = gap
        if trial < 25 or gap > 1e-3:
            P("  %-6d %-18.12f %-18.12f %-12.2e %-8d" % (trial, vref, vfin, gap, ns))
    P("")
    P("worst (reference - finite) gap over 400 random configurations = %.3e" % worst)
    P("(a positive gap means the finite set MISSED the true maximiser)")
    with open(os.path.join(OUT, "p21_criterion_stress.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines)+"\n")
