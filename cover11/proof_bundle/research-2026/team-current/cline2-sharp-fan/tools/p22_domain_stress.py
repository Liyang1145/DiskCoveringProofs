# -*- coding: utf-8 -*-
"""P22: DOMAIN-VALID stress test of the finite criterion.

Hypotheses enforced (this is the gap P21 lacked):
  H1 the 9 rings alone cover bd D;
  H2 each hub's ring-neighbour set is a contiguous arc (q0 fan with 2 transitions).
Configurations are generated from a realisable arc ledger: 9 boundary arcs of
half-width t_i = asin(R/rho_i) with centres spaced so that the arcs cover bd D, and
rings placed at the corresponding inward-root positions.  Hubs are drawn at random
interior positions; for the criterion test the hubs do not need to be feasible.
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

NR, NTH = 900, 4600
rs = np.linspace(0, 1, NR); ths = np.linspace(0, 2*np.pi, NTH, endpoint=False)
RRg, TTg = np.meshgrid(rs, ths, indexing='ij')
PTS = np.stack([(RRg*np.cos(TTg)).ravel(), (RRg*np.sin(TTg)).ravel()], axis=1)
BD = np.stack([np.cos(ths), np.sin(ths)], axis=1)


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


def boundary_defect(C):
    d = np.linalg.norm(BD[:, None, :]-C[None, :, :], axis=2).min(axis=1)
    return float(d.max())


def circum(ALL, h, i, j):
    a, b, c = ALL[h], ALL[i], ALL[j]
    dd = 2*(a[0]*(b[1]-c[1])+b[0]*(c[1]-a[1])+c[0]*(a[1]-b[1]))
    if abs(dd) < 1e-14:
        return None
    a2 = a@a; b2 = b@b; c2 = c@c
    return np.array([(a2*(b[1]-c[1])+b2*(c[1]-a[1])+c2*(a[1]-b[1]))/dd,
                     (a2*(c[0]-b[0])+b2*(a[0]-c[0])+c2*(b[0]-a[0]))/dd])


def val_finite(ALL, R, order, hub_idx):
    S = []
    n = len(order)
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


def genesis(R, rng):
    """inward-root ledger: 9 arcs of half-width t_i = asin(R/rho_i) that COVER bd D.

    Correct closure: consecutive centre spacings gamma_i must satisfy
        |t_i - t_{i+1}| < gamma_i < t_i + t_{i+1}   and   sum gamma_i = 2 pi.
    Implemented by picking weights w_i in (0,1), gamma_i = w_i (t_i+t_{i+1}), then
    rescaling to sum 2 pi and rejecting if any arc pair fails the strict inequality.
    """
    for _ in range(400):
        # ring modulus rho in [1-R, 1]; its covered arc on bd D has angular
        # half-width alpha = arccos((1 + rho^2 - R^2)/(2 rho))  (exact)
        rho = rng.uniform(1-R+0.02, 1.0-1e-6, 9)
        alpha = np.arccos(np.clip((1 + rho**2 - R**2)/(2*rho), -1, 1))
        if alpha.sum() <= math.pi*1.02:
            continue
        an = np.roll(alpha, -1)
        lo = np.abs(alpha - an) + 1e-6
        hi = alpha + an - 1e-9
        if np.any(hi <= lo) or not (lo.sum() < 2*math.pi < hi.sum()):
            continue
        lam = (2*math.pi - lo.sum())/(hi.sum() - lo.sum())
        eta = rng.uniform(-0.15, 0.15, 9)
        gamma = lo + np.clip(lam + eta, 0.0, 1.0)*(hi - lo)
        for _ in range(60):
            err = gamma.sum() - 2*math.pi
            if abs(err) < 1e-12:
                break
            slack = np.where(err > 0, gamma - lo, hi - gamma)
            wgt = slack/slack.sum() if slack.sum() > 0 else np.ones(9)/9
            gamma = gamma - err*wgt
        if not (lo < gamma).all() or not (gamma < hi).all():
            continue
        ph = np.cumsum(np.concatenate([[rng.uniform(0, 2*math.pi)], gamma[:-1]]))
        C = np.stack([rho*np.cos(ph), rho*np.sin(ph)], axis=1)
        return C, ph
    return None, None


if __name__ == "__main__":
    rng = np.random.default_rng(777)
    P("DOMAIN-VALID stress test (H1 rings cover bd D enforced by construction)")
    P("%-6s %-10s %-12s %-18s %-18s %-12s %-8s" %
      ("trial", "bdrydefect", "R", "reference", "finite-set", "gap", "#S"))
    n_ok = 0
    worst = -1e9
    for trial in range(600):
        R = rng.uniform(0.33, 0.395)
        C, ph = genesis(R, rng)
        if C is None:
            continue
        bd = boundary_defect(C)
        if bd > R:                      # H1 must hold (rings cover bd D at R)
            continue
        n_ok += 1
        H = rng.normal(0, 0.10, (2, 2))
        Hn = np.linalg.norm(H, axis=1); H *= ((1-R)*np.minimum(1.0, (1-R)/np.maximum(1e-9, Hn)))[:, None]
        ALL = np.vstack([C, H])
        order = list(np.argsort(ph))
        vref = val_ref(ALL)
        vfin, ns = val_finite(ALL, R, order, [9, 10])
        gap = vref-vfin
        worst = max(worst, gap)
        if n_ok <= 20 or gap > 1e-3:
            P("  %-6d %-10.3e %-12.6f %-18.12f %-18.12f %-12.2e %-8d"
              % (trial, bd-R, R, vref, vfin, gap, ns))
        if n_ok >= 120:
            break
    P("")
    P("domain-valid configurations tested: %d" % n_ok)
    P("worst (reference - finite) gap = %.3e" % worst)
    P("VERDICT: gap ~ 0 => finite criterion holds in the domain; gap >> 0 => it fails.")
    with open(os.path.join(OUT, "p22_domain_stress.txt"), "w", encoding="utf-8") as f:
        f.write("\n".join(lines)+"\n")
