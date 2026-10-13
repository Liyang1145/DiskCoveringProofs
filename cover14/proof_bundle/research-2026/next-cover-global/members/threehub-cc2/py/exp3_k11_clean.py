# -*- coding: utf-8 -*-
"""
exp3_k11_clean.py -- members/threehub-cc2

CLEAN MECHANISM TEST, k=11 branch.
Variables: 11 active centres in polar (rho_i >= 1-U hard-bounded) and 3 hubs
(h1, h2 free in the disk, h3 as (t,psi)); soft penalty only for the HUB core
condition (hub disks cover B(0,a)) which is the one primitive I cannot cheaply
project onto.

    Phi(v) = coverD(C) + lam * max(0, core_radius(hubs) - U)^2

coverD = max over S1 of the distance to the nearest of the 14 centres (clipped
criterion, exact for finite disk families).

Two evaluators: coarse (600 S1 pts, 80x40 core grid) for the search, fine
(7200 S1 pts) for reporting the final value.

REPORTED per row: coverD_fine, core_radius(hubs) (must be <= U), min active norm
(must be >= 1-U), max hub norm (must be < 1-U), and the worst uncovered point.

BUDGET 5 min.
"""
import json, math, time, sys
import numpy as np

U = 0.33173203427623414
A = 1.0 - 2.0 * U
INACT = 1.0 - U

def grid(nth):
    th = np.linspace(0, 2 * math.pi, nth, endpoint=False)
    return th, np.cos(th), np.sin(th)

THC, CSC, SNC = grid(720)
THF, CSF, SNF = grid(7200)

CORETH = np.linspace(0, 2 * math.pi, 60, endpoint=False)
CORERR = np.linspace(A, 0.0, 30)
_TT, _RT = np.meshgrid(CORETH, CORERR)
COREPTS = np.stack([(_RT * np.cos(_TT)).ravel(), (_RT * np.sin(_TT)).ravel()], axis=1)

rng = np.random.default_rng(99)


def coverD(C, cs=None, sn=None):
    cs = CSC if cs is None else cs
    sn = SNC if sn is None else sn
    C = np.asarray(C, float)
    dx = cs[:, None] - C[None, :, 0]
    dy = sn[:, None] - C[None, :, 1]
    return float(np.sqrt(dx * dx + dy * dy).min(axis=1).max())


def core_radius(hub):
    hub = np.asarray(hub, float)
    d = np.sqrt(((COREPTS[:, None, :] - hub[None, :, :]) ** 2).sum(axis=2)).min(axis=1)
    return float(d.max())


def unpack(v):
    act = np.stack([v[0:11] * np.cos(v[11:22]), v[0:11] * np.sin(v[11:22])], axis=1)
    h1 = v[22:24]
    h2 = v[24:26]
    h3 = np.array([v[26] * math.cos(v[27]), v[26] * math.sin(v[27])])
    return act, np.vstack([h1, h2, h3])


def Phi(v, lam=20.0):
    act, hub = unpack(v)
    c = coverD(np.vstack([hub, act]))
    cc = core_radius(hub)
    return c + lam * max(0.0, cc - U) ** 2, c, cc


def hill(v0, iters, step0=0.1, lam=20.0):
    v = np.array(v0, float)
    f, c, cc = Phi(v, lam)
    step = step0
    for it in range(iters):
        T = 0.003 * (1 - it / iters) + 1e-9
        v2 = v.copy()
        u = rng.random()
        if u < 0.5:
            k = int(rng.integers(0, 11))
            v2[11 + k] += step * rng.normal()
            if rng.random() < 0.15:
                v2[k] = min(max(v2[k] + step * rng.normal(), INACT), 1.5)
        elif u < 0.8:
            k = int(rng.integers(0, 11))
            v2[k] = min(max(v2[k] + step * rng.normal(), INACT), 1.5)
        elif u < 0.93:
            k = int(rng.integers(22, 26))
            v2[k] += step * rng.normal()
        else:
            v2[26] = min(max(v2[26] + step * rng.normal(), 0.05), INACT - 1e-6)
            v2[27] += step * rng.normal()
        f2, c2, cc2 = Phi(v2, lam)
        if f2 < f - 1e-14 or rng.random() < math.exp(-(f2 - f) / T):
            v, f, c, cc = v2, f2, c2, cc2
        if it % 1500 == 1499:
            step = max(step * 0.8, 3e-5)
    return v, f, c, cc


def report(v):
    act, hub = unpack(v)
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
                max_hub_norm=float(nh.max()),
                core_ok=bool(cc <= U + 1e-9), active_ok=bool(na.min() >= INACT - 1e-9),
                hub_ok=bool(nh.max() < INACT),
                worst_pt=[round(float(CSF[k]), 6), round(float(SNF[k]), 6)],
                active_norms=sorted(round(float(q), 6) for q in na),
                hub=[list(map(float, h)) for h in hub])


def start_with_hub(hub, seed_ang=None):
    act_ang = np.sort(rng.random(11) * 2 * math.pi) if seed_ang is None else np.array(seed_ang)
    rho = INACT * (1 + 0.05 * rng.random(11))
    return np.concatenate([rho, act_ang, hub[0], hub[1],
                           [math.hypot(*hub[2]), math.atan2(hub[2][1], hub[2][0])]])


def run(t, psi, starts, iters, seed_ang=None):
    best = None
    for s in range(starts):
        hub = np.array([[t * math.cos(psi + 2 * math.pi * k / 3),
                         t * math.sin(psi + 2 * math.pi * k / 3)] for k in range(3)])
        if s % 2 == 1:
            hub = hub + rng.normal(scale=0.015, size=hub.shape)
        v0 = start_with_hub(hub, seed_ang if s == 0 else None)
        v, f, c, cc = hill(v0, iters)
        rep = report(v)
        if best is None or rep["coverD"] < best[0]["coverD"]:
            best = (rep, v)
    return best


t0 = time.time()
out = {"schema": "mathlab-evidence/v1", "U": U, "a_core": A,
       "instrument": "coverD on S1 (clipped criterion), core_radius on polar grid", "runs": []}

print("=== C0  instrument re-check on the saved rational construction ===")
from fractions import Fraction as F
d0 = json.load(open("research-2026/next-cover-global/lead/improved-upper-test.json"))
Csav = np.array([[float(F(x[0])), float(F(x[1]))] for x in d0["centers"]])
print("  saved coverD(fine) =", coverD(Csav, CSF, SNF), " (threshold",
      d0["threshold_decimal"], ")")
print("  saved coverD(coarse) =", coverD(Csav))
sys.stdout.flush()

print()
print("=== C1  forced 11-active split of the saved construction (see exp2 control C) ===")
print("  removing one hub destroys the core condition: core_radius of best 3 hubs =",
      0.46911244211532965, "> U:", U)
print("  => any k=11 cover must REBUILD the hub triangle; not reachable from the save.")
sys.stdout.flush()

print()
print("=== k=11 sweep (11 active, 3 hubs) ===")
rows = []
for t, psi, iters in [(0.34, 0.0, 3000), (0.36, 0.0, 3000), (0.38, 0.0, 3000),
                      (0.34, 0.7, 3000), (0.36, 0.7, 3000), (0.30, 0.0, 3000),
                      (0.32, 0.0, 3000), (0.40, 0.0, 3000)]:
    rep, v = run(t, psi, starts=3, iters=iters)
    rep["t"] = t
    rep["psi"] = psi
    rows.append(rep)
    print("  " + json.dumps({k: rep[k] for k in
                             ("t", "psi", "coverD", "core_radius", "core_ok",
                              "min_active_norm", "active_ok", "max_hub_norm",
                              "hub_ok", "worst_pt")}), flush=True)
    sys.stdout.flush()

out["runs"] = rows
out["elapsed_s"] = time.time() - t0
feas = [q for q in rows if q["core_ok"] and q["active_ok"] and q["hub_ok"]]
out["n_feasible_rows"] = len(feas)
out["min_coverD_feasible"] = min([q["coverD"] for q in feas], default=None)
out["status"] = "inconclusive"
out["summary"] = ("k=11: %d/%d rows satisfy core+activity conditions; min coverD over "
                  "those = %s vs U = %.12f" %
                  (len(feas), len(rows),
                   ("%.12f" % out["min_coverD_feasible"]) if feas else "none", U))
print()
print(out["summary"])
with open("research-2026/next-cover-global/members/threehub-cc2/evidence/exp3_k11_clean.json",
          "w") as f:
    json.dump(out, f, indent=1)
