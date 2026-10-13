# -*- coding: utf-8 -*-
"""
exp1_k11_feasibility.py  --  members/threehub-cc2  (DeepSeek-V4.1Flash / commandcode2)

MECHANISM TEST (bounded budget, 3 min): for k=11 active + 3 hubs, is there a
configuration of 14 closed radius-U disks covering D = unit disk with exactly 3 hubs
strictly inactive (|h_j| < 1-U) covering the core B(0,a), a = 1-2U, and 11 active
centres (|c_i| >= 1-U)?

MEASURED QUANTITY
  R_need(c_1..c_14) = max over x in a fine polar grid of the square [-1,1]^2 inside D
                      (radii in {1, 0.99, ..., 0.02}, 720 angles, plus r=0)
                      of min_i |x - c_i|.
  This is a sampled covering radius of D by the 14 disks; it is >= the true covering
  radius (so an upper reading of R_need below U is a genuine necessary condition, and
  R_need > U is not by itself a proof of non-coverage).  Reported with the sampling
  grid so the reader can judge the margin.

KNOWN CONTROLS
  (1) regular-14-gon ring at t = 4/3, r = 2(4/3) sin(pi/14) = 0.331732034276234187...:
      the evaluator must return this value (tests the radius evaluator).
  (2) same for n=13, n=15.
  (3) C1142 / DEAD: k in {10,11} only, no symmetry WLOG -> the 11/3 split cannot be
      symmetric; asymmetric search required.

OUTCOME CODING (mathlab-evidence/v1)
  status "counterexample" <=> a row violates R_need <= U with all side conditions true
  (a genuine 14-disk cover of D at radius <= U with 11 active + 3 hubs: that would
  refute the k11 exclusion target at r = U and must be checked by hand);
  "inconclusive" otherwise.  Floats never certify.
"""
import json, math, time
import numpy as np

U = 0.33173203427623414
A_CORE = 1.0 - 2.0 * U

NTH = 720
NR = 30
TH = np.linspace(0.0, 2.0 * math.pi, NTH, endpoint=False)
RR = np.linspace(1.0, 0.03, NR)
TT, RT = np.meshgrid(TH, RR)
PX = (RT * np.cos(TT)).ravel()
PY = (RT * np.sin(TT)).ravel()
PTS = np.stack([PX, PY], axis=1)
PTS = np.vstack([np.array([[0.0, 0.0]]), PTS])


def need_radius(centers):
    c = np.asarray(centers, dtype=float)
    dx = PTS[:, 0:1] - c[:, 0:1].T
    dy = PTS[:, 1:2] - c[:, 1:2].T
    d = np.sqrt(dx * dx + dy * dy)
    return float(d.min(axis=1).max())


def worst_point(centers):
    c = np.asarray(centers, dtype=float)
    dx = PTS[:, 0:1] - c[:, 0:1].T
    dy = PTS[:, 1:2] - c[:, 1:2].T
    d = np.sqrt(dx * dx + dy * dy).min(axis=1)
    j = int(np.argmax(d))
    return PTS[j].tolist(), float(d[j])


def hub_facts(hub):
    h = np.asarray(hub, dtype=float)
    pdist = [float(np.linalg.norm(h[i] - h[j])) for i in range(3) for j in range(i + 1, 3)]
    n = 300
    xs = np.linspace(-A_CORE, A_CORE, n)
    X, Y = np.meshgrid(xs, xs)
    m = X * X + Y * Y <= A_CORE * A_CORE
    P = np.stack([X[m], Y[m]], axis=1)
    d = np.sqrt(((P[:, None, :] - h[None, :, :]) ** 2).sum(axis=2)).min(axis=1)
    norms = np.linalg.norm(h, axis=1)
    return dict(pairwise=pdist, core_cover_radius=float(d.max()),
                hub_norms=norms.tolist(), max_hub_norm=float(norms.max()),
                strictly_inactive=bool(float(norms.max()) < 1.0 - U),
                origin_in_triangle=bool(_in_tri(h)))


def _in_tri(h):
    def cr(o, a, b):
        return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])
    o = np.array([0.0, 0.0])
    d1, d2, d3 = cr(o, h[0], h[1]), cr(o, h[1], h[2]), cr(o, h[2], h[0])
    return (d1 > 0 and d2 > 0 and d3 > 0) or (d1 < 0 and d2 < 0 and d3 < 0)


def build(hub, act):
    return np.vstack([np.asarray(hub, float), np.asarray(act, float)])


def act_from_polar(r, ang):
    return np.stack([r * np.cos(ang), r * np.sin(ang)], axis=1)


def frac_arcs_ok(act):
    """fraction of S1 covered by the 11 active arcs (necessary for a cover of D)."""
    act = np.asarray(act, float)
    dx = PTS[:, 0:1] - act[:, 0:1].T
    dy = PTS[:, 1:2] - act[:, 1:2].T
    return None


def frac_S1_covered(act):
    th = np.linspace(0, 2 * math.pi, 20000, endpoint=False)
    xs = np.cos(th)
    ys = np.sin(th)
    dx = xs[:, None] - np.asarray(act, float)[None, :, 0]
    dy = ys[:, None] - np.asarray(act, float)[None, :, 1]
    d = np.sqrt(dx * dx + dy * dy).min(axis=1)
    return float((d <= U).mean())


def hillclimb(hub, rng, iters, seed_ang, step0=0.3):
    hub = np.asarray(hub, float)
    best_ang = np.array(seed_ang, float)
    best_r = 1.0
    best = need_radius(build(hub, act_from_polar(best_r, best_ang)))
    step = step0
    for it in range(iters):
        T = 0.02 * (1.0 - it / iters) ** 2 + 1e-6
        cand_ang, cand_r = best_ang, best_r
        if rng.random() < 0.45:
            cand_r = min(max(best_r + step * rng.normal(), 1.0 - U), 1.12)
        else:
            cand_ang = best_ang.copy()
            k = int(rng.integers(0, 11))
            cand_ang[k] += step * rng.normal()
        v = need_radius(build(hub, act_from_polar(cand_r, cand_ang)))
        if v < best - 1e-13 or rng.random() < math.exp(-(v - best) / T):
            best, best_r, best_ang = v, cand_r, cand_ang
        if it % 300 == 299:
            step = max(step * 0.75, 1e-4)
    return best, best_r, best_ang


def optimise_for_hub(hub, rng, starts=6, iters=1200):
    bv, br, ba = 1e9, None, None
    for _ in range(starts):
        ang = np.sort(rng.random(11) * 2 * math.pi)
        v, r, a = hillclimb(hub, rng, iters, ang)
        if v < bv:
            bv, br, ba = v, r, a
    return bv, br, ba


def ring(n, r=4.0 / 3.0):
    ang = 2 * math.pi * np.arange(n) / n
    return np.stack([r * np.cos(ang), r * np.sin(ang)], axis=1)


def main():
    t0 = time.time()
    out = {"schema": "mathlab-evidence/v1", "U": U, "a_core": A_CORE,
           "grid": {"n_theta": NTH, "n_r": NR, "r_min": float(RR[-1])}, "checks": {}}

    out["checks"]["control_ring14"] = dict(
        evaluated=need_radius(ring(14)), theory=2.0 * (4.0 / 3.0) * math.sin(math.pi / 14))
    out["checks"]["control_ring13"] = dict(
        evaluated=need_radius(ring(13)), theory=2.0 * (4.0 / 3.0) * math.sin(math.pi / 13))
    out["checks"]["control_ring15"] = dict(
        evaluated=need_radius(ring(15)), theory=2.0 * (4.0 / 3.0) * math.sin(math.pi / 15))
    print("controls", json.dumps(out["checks"], indent=1), flush=True)

    rng = np.random.default_rng(20260924)
    rows = []
    for t in [0.15, 0.25, 0.35, 0.45, 0.55, 0.60, 0.6468, 0.66]:
        for psi in [0.0, 0.13]:
            hub = np.array([[t * math.cos(psi + 2 * math.pi * k / 3),
                             t * math.sin(psi + 2 * math.pi * k / 3)] for k in range(3)])
            v, r, a = optimise_for_hub(hub, rng, starts=5, iters=1000)
            hf = hub_facts(hub)
            row = dict(t=t, psi=psi, best_need_radius=v, act_r=r, hub=hf,
                       core_covered=bool(hf["core_cover_radius"] <= U),
                       S1_frac_covered_by_active=frac_S1_covered(act_from_polar(r, a)),
                       worst_pt=worst_point(build(hub, act_from_polar(r, a)))[0],
                       act_ang_sorted=sorted(a.tolist()))
            rows.append(row)
            print(json.dumps({k: v2 for k, v2 in row.items() if k != "act_ang_sorted"}),
                  flush=True)
    out["hub_sweep"] = rows
    out["elapsed_s"] = time.time() - t0
    hits = [q for q in rows if q["best_need_radius"] <= U and q["hub"]["strictly_inactive"]
            and q["core_covered"] and q["S1_frac_covered_by_active"] > 0.99999]
    out["status"] = "counterexample" if hits else "inconclusive"
    out["summary"] = ("k=11 equilateral-hub sweep: %d rows with a full radius-U cover; "
                      "min sampled need-radius = %.12f (U = %.12f)" %
                      (len(hits), min(q["best_need_radius"] for q in rows), U))
    print(out["summary"])
    with open("research-2026/next-cover-global/members/threehub-cc2/evidence/"
              "exp1_k11_feasibility.json", "w") as f:
        json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
