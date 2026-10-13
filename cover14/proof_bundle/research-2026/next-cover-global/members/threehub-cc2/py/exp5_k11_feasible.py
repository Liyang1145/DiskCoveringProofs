# -*- coding: utf-8 -*-
"""
exp5_k11_feasible.py -- members/threehub-cc2  (v2)

CONSTRAINED search for the k=11 branch.
  hub feasibility: C(hub) := max_{x in B(0,a)} min_j |x-h_j| <= U
  objective:       coverD = max over S1 of nearest-centre distance
  representation:  [11 angles, 11 active radii >= 1-U, 3 hub points]
  hub projection:  radially clip the hubs into B(0,U) (necessary: an infeasible
                   hub has |h| > U, since the farthest point of B(0,a) from any
                   hub is >= max_j |h_j| -- kept as a cheap projector), then
                   reject the step unless C(hub2) <= C(hub) + 0.002 (monotone
                   feasibility guard); the search therefore stays feasible
                   whenever it starts feasible, and feasibility is reported.

Facts used (elementary, proved in MEMBER-NOTES):
  * active centres (|c| >= 1-U) cannot cover the open core: |c-x| > (1-U)-a = U.
  * hence the hub triple alone covers the closed core, so every hub has |h| <= U,
    and 3-fold symmetry with t = U is the extreme legal case.
BUDGET 6 min.
"""
import json, math, time, sys
import numpy as np

U = 0.33173203427623414
A = 1.0 - 2.0 * U
INACT = 1.0 - U
NACT = 11


def grid(nth):
    th = np.linspace(0, 2 * math.pi, nth, endpoint=False)
    return np.cos(th), np.sin(th)


CSC, SNC = grid(900)
CSF, SNF = grid(9000)

_CT = np.linspace(0, 2 * math.pi, 90, endpoint=False)
_CR = np.linspace(A, 0.0, 45)
_TT, _RT = np.meshgrid(_CT, _CR)
COREPTS = np.stack([(_RT * np.cos(_TT)).ravel(), (_RT * np.sin(_TT)).ravel()], axis=1)

rng = np.random.default_rng(31337)


def coverD(C, cs, sn):
    C = np.asarray(C, float)
    dx = cs[:, None] - C[None, :, 0]
    dy = sn[:, None] - C[None, :, 1]
    return float(np.sqrt(dx * dx + dy * dy).min(axis=1).max())


def core_radius(hub, pts=COREPTS):
    hub = np.asarray(hub, float)
    d = np.sqrt(((pts[:, None, :] - hub[None, :, :]) ** 2).sum(axis=2)).min(axis=1)
    return float(d.max())


def unpack(v):
    ang, rho = v[:NACT], v[NACT:2 * NACT]
    act = np.stack([rho * np.cos(ang), rho * np.sin(ang)], axis=1)
    return act, v[2 * NACT:].reshape(3, 2)


def clip_hub(hub):
    hub = np.asarray(hub, float)
    n = np.linalg.norm(hub, axis=1)
    sc = np.where(n > U, U / np.maximum(n, 1e-12), 1.0)
    return hub * sc[:, None]


def hill(v0, iters, step0=0.12):
    v = np.array(v0, float)
    act, hub = unpack(v)
    hub = clip_hub(hub)
    v = np.concatenate([v[:2 * NACT], hub.ravel()])
    C = core_radius(hub)
    f = coverD(np.vstack([hub, act]), CSC, SNC)
    step = step0
    for it in range(iters):
        T = 0.0025 * (1 - it / iters) + 1e-11
        v2 = v.copy()
        u = rng.random()
        if u < 0.6:
            v2[int(rng.integers(0, NACT))] += step * rng.normal()
        elif u < 0.85:
            k = int(rng.integers(NACT, 2 * NACT))
            v2[k] = min(max(v2[k] + step * rng.normal(), INACT), 1.8)
        else:
            k = int(rng.integers(2 * NACT, 2 * NACT + 6))
            v2[k] += step * rng.normal()
        act2, hub2 = unpack(v2)
        hub2 = clip_hub(hub2)
        C2 = core_radius(hub2)
        if C2 > min(C, U) + 0.004:      # monotone feasibility guard
            continue
        v2 = np.concatenate([v2[:2 * NACT], hub2.ravel()])
        f2 = coverD(np.vstack([hub2, act2]), CSC, SNC)
        if f2 < f - 1e-14 or rng.random() < math.exp(-(f2 - f) / T):
            v, f, C = v2, f2, C2
        if it % 2000 == 1999:
            step = max(step * 0.8, 2e-5)
    return v, f


def report(v):
    act, hub = unpack(v)
    hub = clip_hub(hub)
    C = np.vstack([hub, act])
    dx = CSF[:, None] - C[None, :, 0]
    dy = SNF[:, None] - C[None, :, 1]
    d = np.sqrt(dx * dx + dy * dy).min(axis=1)
    k = int(np.argmax(d))
    na = np.linalg.norm(act, axis=1)
    nh = np.linalg.norm(hub, axis=1)
    cr = core_radius(hub)
    return dict(coverD=float(d[k]), core_radius=cr, core_ok=bool(cr <= U),
                min_active_norm=float(na.min()), active_ok=bool(na.min() >= INACT - 1e-12),
                max_hub_norm=float(nh.max()), hub_ok=bool(nh.max() <= U + 1e-12),
                worst_pt=[round(float(CSF[k]), 6), round(float(SNF[k]), 6)],
                hub=[[round(float(x), 9) for x in h] for h in hub],
                active=[[round(float(x), 6) for x in q] for q in act])


t0 = time.time()
out = {"schema": "mathlab-evidence/v1", "U": U, "a_core": A, "runs": []}
print("=== hub-core legality for equilateral triples (C(t) = max(t, t/2) = t) ===")
for t in [0.15, 0.25, 0.3137, 0.32, U, 0.34]:
    h = np.array([[t * math.cos(2 * math.pi * k / 3), t * math.sin(2 * math.pi * k / 3)]
                  for k in range(3)])
    print(f"  t={t:.9f}  C={core_radius(h):.9f}  legal={core_radius(h) <= U}")
sys.stdout.flush()

print()
print("=== k=11 constrained restarts ===")
rows, best = [], None
for trial in range(12):
    t_h = float(rng.uniform(0.18, U * 0.995))
    psi = float(rng.uniform(0, 2 * math.pi))
    hub = np.array([[t_h * math.cos(psi + 2 * math.pi * k / 3),
                     t_h * math.sin(psi + 2 * math.pi * k / 3)] for k in range(3)])
    hub = hub + rng.normal(scale=0.012, size=hub.shape)
    if trial % 3 == 1:
        hub = rng.normal(scale=0.12, size=(3, 2))
    if trial % 2 == 0:
        ang = np.sort((np.arange(NACT) + 0.35 * rng.random(NACT)) * 2 * math.pi / NACT)
    else:
        ang = np.sort(rng.random(NACT) * 2 * math.pi)
    rho = INACT * (1 + 0.3 * rng.random(NACT))
    v0 = np.concatenate([ang, rho, hub.ravel()])
    v, f = hill(v0, 3000)
    rep = report(v)
    rep["trial"] = trial
    rows.append(rep)
    if best is None or rep["coverD"] < best["coverD"]:
        best = rep
    print("  " + json.dumps({k: rep[k] for k in
                             ("trial", "coverD", "core_radius", "core_ok", "min_active_norm",
                              "active_ok", "max_hub_norm", "worst_pt")}), flush=True)
    sys.stdout.flush()

out["runs"] = rows
out["best"] = best
out["elapsed_s"] = time.time() - t0
feas = [q for q in rows if q["core_ok"] and q["active_ok"] and q["hub_ok"]]
out["n_feasible"] = len(feas)
out["min_coverD_feasible"] = min([q["coverD"] for q in feas], default=None)
out["status"] = "inconclusive"
out["summary"] = ("k=11: %d/%d feasible restarts; min coverD = %s ; U = %.12f" %
                  (len(feas), len(rows),
                   ("%.12f" % out["min_coverD_feasible"]) if feas else "none", U))
print()
print(out["summary"])
with open("research-2026/next-cover-global/members/threehub-cc2/evidence/"
          "exp5_k11_feasible.json", "w") as f:
    json.dump(out, f, indent=1)
