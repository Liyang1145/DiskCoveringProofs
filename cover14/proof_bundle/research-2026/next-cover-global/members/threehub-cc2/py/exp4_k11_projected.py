# -*- coding: utf-8 -*-
"""
exp4_k11_projected.py -- members/threehub-cc2

k=11 branch, CONSTRAINED search (fixes exp3's soft-penalty drift).
  * variables: 11 active centres (rho_i >= 1-U hard-bounded, angles free), 3 hubs.
  * the hub core condition "B(0,a) is covered by the three radius-U hub disks" is
    enforced by HARD PROJECTION: after every accepted step the hub triple is scaled
    about 0 (h_j -> s h_j, s <= 1, s maximal) so that core_radius(hubs) <= U.  Scaling
    about the origin is monotone: |x - s h| <= |x - h| for every |x| <= |h|, so
    core_radius is non-increasing in s and the bisection is valid.
  * objective: coverD (max over a dense S1 set of the nearest-centre distance).
Report: coverD_fine (7200 pts), core_radius, min active norm, max hub norm, worst pt.

CONTROLS
  * saved rational construction: coverD = 0.33173203427623404 (instrument check)
  * control C (exp2): forcing 11+3 out of the saved 14 gives core_radius 0.4691 > U,
    so the k=11 family must rebuild the hub triple; it cannot contain the save.
BUDGET 6 min.
"""
import json, math, time, sys
import numpy as np

U = 0.33173203427623414
A = 1.0 - 2.0 * U
INACT = 1.0 - U


def grid(nth):
    th = np.linspace(0, 2 * math.pi, nth, endpoint=False)
    return np.cos(th), np.sin(th)


CSC, SNC = grid(720)
CSF, SNF = grid(7200)

_CT = np.linspace(0, 2 * math.pi, 72, endpoint=False)
_CR = np.linspace(A, 0.0, 36)
_TT, _RT = np.meshgrid(_CT, _CR)
COREPTS = np.stack([(_RT * np.cos(_TT)).ravel(), (_RT * np.sin(_TT)).ravel()], axis=1)

rng = np.random.default_rng(1717)


def coverD(C, cs, sn):
    C = np.asarray(C, float)
    dx = cs[:, None] - C[None, :, 0]
    dy = sn[:, None] - C[None, :, 1]
    return float(np.sqrt(dx * dx + dy * dy).min(axis=1).max())


def core_radius(hub):
    hub = np.asarray(hub, float)
    d = np.sqrt(((COREPTS[:, None, :] - hub[None, :, :]) ** 2).sum(axis=2)).min(axis=1)
    return float(d.max())


def project(hub):
    """maximal shrink about 0 with core_radius <= U (bisection on s in [0,1])"""
    hub = np.asarray(hub, float)
    if core_radius(hub) <= U:
        return hub
    lo, hi = 0.0, 1.0
    for _ in range(40):
        mid = 0.5 * (lo + hi)
        if core_radius(mid * hub) <= U:
            lo = mid
        else:
            hi = mid
    return lo * hub


def unpack(v):
    act = np.stack([v[0:11] * np.cos(v[11:22]), v[0:11] * np.sin(v[11:22])], axis=1)
    hub = np.array([v[22:24], v[24:26],
                    [v[26] * math.cos(v[27]), v[26] * math.sin(v[27])]])
    return act, hub


def pack(act, hub):
    rho = np.linalg.norm(act, axis=1)
    ang = np.arctan2(act[:, 1], act[:, 0])
    return np.concatenate([rho, ang, hub[0], hub[1],
                           [math.hypot(*hub[2]), math.atan2(hub[2][1], hub[2][0])]])


def objective(v):
    act, hub = unpack(v)
    return coverD(np.vstack([hub, act]), CSC, SNC)


def hill(v0, iters, step0=0.1):
    v = np.array(v0, float)
    act, hub = unpack(v)
    hub = project(hub)
    ang0 = np.arctan2(act[:, 1], act[:, 0])
    rho0 = np.clip(np.linalg.norm(act, axis=1), INACT, 2.0)
    v = pack(np.stack([rho0 * np.cos(ang0), rho0 * np.sin(ang0)], axis=1), hub)
    f = objective(v)
    step = step0
    for it in range(iters):
        T = 0.002 * (1 - it / iters) + 1e-10
        v2 = v.copy()
        u = rng.random()
        if u < 0.55:
            k = int(rng.integers(0, 11))
            v2[11 + k] += step * rng.normal()
        elif u < 0.7:
            k = int(rng.integers(0, 11))
            v2[k] = min(max(v2[k] + step * rng.normal(), INACT), 1.6)
        elif u < 0.95:
            k = int(rng.integers(22, 26))
            v2[k] += step * rng.normal()
        else:
            v2[26] = min(max(v2[26] + step * rng.normal(), 0.05), INACT - 1e-6)
            v2[27] += step * rng.normal()
        # hard projection of the hub triple
        act2, hub2 = unpack(v2)
        hub2 = project(hub2)
        v2 = pack(act2, hub2)
        f2 = objective(v2)
        if f2 < f - 1e-14 or rng.random() < math.exp(-(f2 - f) / T):
            v, f = v2, f2
        if it % 1500 == 1499:
            step = max(step * 0.8, 2e-5)
    return v, f


def report(v):
    act, hub = unpack(v)
    hub = project(hub)
    C = np.vstack([hub, act])
    cf = coverD(C, CSF, SNF)
    cc = core_radius(hub)
    na = np.linalg.norm(act, axis=1)
    nh = np.linalg.norm(hub, axis=1)
    dx = CSF[:, None] - C[None, :, 0]
    dy = SNF[:, None] - C[None, :, 1]
    d = np.sqrt(dx * dx + dy * dy).min(axis=1)
    k = int(np.argmax(d))
    return dict(coverD=cf, core_radius=cc, min_active_norm=float(na.min()),
                max_hub_norm=float(nh.max()), core_ok=bool(cc <= U + 1e-12),
                active_ok=bool(na.min() >= INACT - 1e-12), hub_ok=bool(nh.max() < INACT),
                worst_pt=[round(float(CSF[k]), 6), round(float(SNF[k]), 6)],
                hub=[list(map(float, h)) for h in hub])


t0 = time.time()
out = {"schema": "mathlab-evidence/v1", "U": U, "a_core": A, "runs": []}
print("=== instrument check ===")
from fractions import Fraction as F
d0 = json.load(open("research-2026/next-cover-global/lead/improved-upper-test.json"))
Csav = np.array([[float(F(x[0])), float(F(x[1]))] for x in d0["centers"]])
print("  saved coverD(fine) =", coverD(Csav, CSF, SNF), "vs threshold", d0["threshold_decimal"])
sys.stdout.flush()

print()
print("=== k=11 constrained sweep (hard-projected hub core condition) ===")
rows = []
bestv, bestrep = None, None
for t0_ in [0.30, 0.34, 0.38, 0.42, 0.46, 0.50]:
    for psi in [0.0, 0.5, 1.1]:
        for s in range(2):
            hub = np.array([[t0_ * math.cos(psi + 2 * math.pi * k / 3),
                             t0_ * math.sin(psi + 2 * math.pi * k / 3)] for k in range(3)])
            if s:
                hub = hub + rng.normal(scale=0.05, size=hub.shape)
            ang = (np.arange(11) / 11.0 * 2 * math.pi if s == 0
                   else np.sort(rng.random(11) * 2 * math.pi))
            rho = INACT * (1 + 0.03 * rng.random(11))
            act = np.stack([rho * np.cos(ang), rho * np.sin(ang)], axis=1)
            v0 = pack(act, hub)
            v, f = hill(v0, 3500)
            rep = report(v)
            rep.update(t=float(t0_), psi=float(psi), s=s)
            rows.append(rep)
            if bestv is None or rep["coverD"] < bestv:
                bestv, bestrep = rep["coverD"], rep
            print("  " + json.dumps({k: rep[k] for k in
                                     ("t", "psi", "s", "coverD", "core_radius", "min_active_norm",
                                      "max_hub_norm", "worst_pt")}), flush=True)
            sys.stdout.flush()

out["runs"] = rows
out["best"] = bestrep
out["elapsed_s"] = time.time() - t0
feas = [q for q in rows if q["core_ok"] and q["active_ok"] and q["hub_ok"]]
out["n_feasible_rows"] = len(feas)
out["min_coverD_feasible"] = min([q["coverD"] for q in feas], default=None)
out["status"] = "inconclusive"
out["summary"] = ("k=11 constrained: %d/%d rows feasible; min coverD over feasible rows = "
                  "%s ; U = %.12f ; best hub core_radius = %.9f" %
                  (len(feas), len(rows),
                   ("%.12f" % out["min_coverD_feasible"]) if feas else "none", U,
                   min(q["core_radius"] for q in rows)))
print()
print(out["summary"])
with open("research-2026/next-cover-global/members/threehub-cc2/evidence/"
          "exp4_k11_projected.json", "w") as f:
    json.dump(out, f, indent=1)
