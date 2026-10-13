# -*- coding: utf-8 -*-
"""
exp2_k11_need_radius.py -- members/threehub-cc2

MECHANISM TEST  For the k=11 branch (11 active centres with |c_i| >= 1-U, 3 hubs with
|h_j| < 1-U whose radius-U disks cover the core B(0,a), a = 1-2U):

    R11 := inf over such configurations of coverD = max_{theta} min_i |(cos,sin)t - c_i|

If R11 > U (with margin) the branch cannot be covered at radius U -> k=11 excluded,
and the number R11 is a lower bound on the n14 optimum contributed by this branch.

INSTRUMENT  coverD on 7200 S¹ points (clipped criterion; verified on the saved rational
construction, see calib2).  Interior audit only for final candidates.

CONTROLS
  * control A: start from the saved 14-centre rational construction, keep its 10 active
    + 4 hubs, run the SAME optimiser -> must return ~0.33173203 (instrument+optimiser
    can reach the known value).
  * control B: 3 centres equilateral, no activity constraint -> known r_3 = sqrt3/2? 
    (report only, marker: the optimiser's calibration factor ~ -4.5e-8 relative).
  * control C: k=11 forced near the saved construction (drop one hub, make its centre
    active) -> measures how much the activity split alone costs.

BUDGET 4 min single core.
"""
import json, math, time, sys
import numpy as np

U = 0.33173203427623414
A = 1.0 - 2.0 * U           # 0.33653593144753172
INACT = 1.0 - U             # 0.6682679657237659
NTH = 7200
TH = np.linspace(0.0, 2 * math.pi, NTH, endpoint=False)
CS, SN = np.cos(TH), np.sin(TH)

rng = np.random.default_rng(4242)


def polar(r, a):
    return np.stack([r * np.cos(a), r * np.sin(a)], axis=1)


def coverD(C):
    C = np.asarray(C, float)
    dx = CS[:, None] - C[None, :, 0]
    dy = SN[:, None] - C[None, :, 1]
    d = np.sqrt(dx * dx + dy * dy).min(axis=1)
    return float(d.max())


def core_cover_radius(hub, nth=180, nr=90):
    h = np.asarray(hub, float)
    th = np.linspace(0, 2 * math.pi, nth, endpoint=False)
    rr = np.linspace(A, 0.0, nr)
    TT, RT = np.meshgrid(th, rr)
    P = np.stack([(RT * np.cos(TT)).ravel(), (RT * np.sin(TT)).ravel()], axis=1)
    d = np.sqrt(((P[:, None, :] - h[None, :, :]) ** 2).sum(axis=2)).min(axis=1)
    return float(d.max())


def unpack(v):
    """v = [x1,y1,...,x11,y11, hx1,hy1,hx2,hy2, h3: (t,psi)]"""
    act = v[:22].reshape(11, 2)
    h1 = v[22:24]
    h2 = v[24:26]
    h3 = np.array([v[26] * math.cos(v[27]), v[26] * math.sin(v[27])])
    return act, np.vstack([h1, h2, h3])


def obj_k11(v, lam=50.0, ret_extra=False):
    act, hub = unpack(v)
    C = np.vstack([hub, act])
    c = coverD(C)
    cc = core_cover_radius(hub, nth=120, nr=60)
    pen = lam * max(0.0, cc - U) ** 2
    # keep activity split: active must be >= 1-U, hubs < 1-U
    na = np.linalg.norm(act, axis=1)
    pen += lam * float(((np.maximum(0.0, INACT - na)) ** 2).sum())
    nh = np.linalg.norm(hub, axis=1)
    pen += lam * float(((np.maximum(0.0, nh - (INACT - 1e-9))) ** 2).sum())
    if ret_extra:
        return c + pen, c, cc, na.min(), nh.max()
    return c + pen


def hill(v0, iters=20000, step0=0.12):
    v = np.array(v0, float)
    f = obj_k11(v)
    step = step0
    for it in range(iters):
        T = 0.004 * (1 - it / iters) + 1e-8
        v2 = v.copy()
        if rng.random() < 0.25:
            k = int(rng.integers(0, 11))
            ang = math.atan2(v2[2 * k + 1], v2[2 * k])
            rr = math.hypot(v2[2 * k], v2[2 * k + 1]) + step * rng.normal()
            rr = min(max(rr, INACT), 1.6)
            v2[2 * k], v2[2 * k + 1] = rr * math.cos(ang), rr * math.sin(ang)
        elif rng.random() < 0.85:
            k = int(rng.integers(0, 11))
            ang = math.atan2(v2[2 * k + 1], v2[2 * k]) + step * rng.normal()
            rr = math.hypot(v2[2 * k], v2[2 * k + 1])
            v2[2 * k], v2[2 * k + 1] = rr * math.cos(ang), rr * math.sin(ang)
        elif rng.random() < 0.6:
            k = int(rng.integers(22, 26))
            v2[k] += step * rng.normal()
        else:
            v2[26] = min(max(v2[26] + step * rng.normal(), 0.05), INACT - 1e-6)
            v2[27] += step * rng.normal()
        f2 = obj_k11(v2)
        if f2 < f - 1e-13 or rng.random() < math.exp(-(f2 - f) / T):
            v, f = v2, f2
        if it % 2000 == 1999:
            step = max(step * 0.75, 1e-4)
    return v, f


def hub_init(t, psi):
    return np.array([[t * math.cos(psi + 2 * math.pi * k / 3),
                      t * math.sin(psi + 2 * math.pi * k / 3)] for k in range(3)])


def make_v(hub, act):
    return np.concatenate([act.ravel(), hub[0], hub[1],
                           [math.hypot(*hub[2]), math.atan2(hub[2][1], hub[2][0])]])


def run_k11(t, psi, iters=20000, nmax=8):
    best = None
    for s in range(nmax):
        hub = hub_init(t, psi)
        if s % 2 == 1:
            hub = hub + rng.normal(scale=0.02, size=hub.shape)
        ang = np.sort((rng.random(11) if s else np.arange(11) / 11.0) * 2 * math.pi)
        rr = INACT * (1.0 + 0.25 * rng.random(11))
        act = polar(rr, ang)
        v0 = make_v(hub, act)
        v, f = hill(v0, iters=iters)
        c, cc, namin, nhmax, _ = obj_k11(v, ret_extra=True)
        if best is None or c < best[0]:
            best = (c, cc, namin, nhmax, v)
    return best


t0 = time.time()
out = {"schema": "mathlab-evidence/v1", "U": U, "a_core": A, "runs": []}

# ---- control A: same optimiser on the saved construction, with its activity split
print("=== control A: optimiser on the saved 14-centre rational construction ===")
from fractions import Fraction as F
d = json.load(open("research-2026/next-cover-global/lead/improved-upper-test.json"))
Csav = np.array([[float(F(x[0])), float(F(x[1]))] for x in d["centers"]])
print("  saved coverD =", coverD(Csav))
print("  (optimiser reachability control: 3 centres, unconstrained)")
v3 = np.concatenate([polar(0.6 + rng.random(3), np.sort(rng.random(3) * 2 * math.pi)).ravel(),
                     [0.3, 0.0, 0.3, 2.1, 0.4, 4.2]])
sys.stdout.flush()

# ---- control B: unconstrained n=3
def hill3(v0, iters=12000):
    v = np.array(v0, float)
    f = coverD(v[:6].reshape(3, 2))
    step = 0.2
    for it in range(iters):
        T = 0.005 * (1 - it / iters) + 1e-8
        v2 = v.copy()
        k = int(rng.integers(0, 3))
        ang = math.atan2(v2[2 * k + 1], v2[2 * k]) + step * rng.normal()
        rr = math.hypot(v2[2 * k], v2[2 * k + 1]) + (step * rng.normal() if rng.random() < 0.3 else 0)
        rr = min(max(rr, 0.1), 3.0)
        v2[2 * k], v2[2 * k + 1] = rr * math.cos(ang), rr * math.sin(ang)
        f2 = coverD(v2[:6].reshape(3, 2))
        if f2 < f - 1e-13 or rng.random() < math.exp(-(f2 - f) / T):
            v, f = v2, f2
        if it % 1500 == 1499:
            step = max(step * 0.7, 1e-5)
    return f, v[:6].reshape(3, 2)


b3 = min((hill3(polar(0.5 + rng.random(3), np.sort(rng.random(3) * 2 * math.pi)).ravel())
          for _ in range(10)), key=lambda z: z[0])
print(f"  n=3 unconstrained optimum found = {b3[0]:.9f}   (marker sqrt(3)/2 = "
      f"{math.sqrt(3)/2:.9f})")
print(f"  -> optimiser calibration factor = {b3[0]/(math.sqrt(3)/2):.12f}")
out["control_n3"] = dict(found=b3[0], marker=math.sqrt(3) / 2,
                         ratio=b3[0] / (math.sqrt(3) / 2))
sys.stdout.flush()

# ---- control C: k=11 but with hubs replaced by the saved 4 hubs' best 3 (forced split)
print()
print("=== control C: take the saved construction, force 11 active / 3 hubs ===")
# sort saved centres by norm; the 3 largest-norm among the 4 hubs become hubs
norms = np.linalg.norm(Csav, axis=1)
order = np.argsort(-norms)
act_sav = Csav[order[:11]]
hub_sav = Csav[order[11:]]
print("  forced split: active norms min =", np.linalg.norm(act_sav, axis=1).min(),
      " hub norms =", np.linalg.norm(hub_sav, axis=1))
print("  coverD with that split =", coverD(np.vstack([hub_sav, act_sav])),
      " core_cover_radius(hubs) =", core_cover_radius(hub_sav))
sys.stdout.flush()

# ---- main sweep
print()
print("=== k=11 sweep: hub triangle parameterised by circumradius t and rotation psi ===")
rows = []
for t in [0.34, 0.36, 0.38, 0.40, 0.42, 0.45, 0.50]:
    for psi in [0.0, 0.7]:
        c, cc, namin, nhmax, v = run_k11(t, psi, iters=12000, nmax=5)
        row = dict(t=t, psi=psi, best_penalised_cost=c, core_cover_radius=cc,
                   min_active_norm=namin, max_hub_norm=nhmax,
                   core_ok=bool(cc <= U + 1e-9),
                   active_ok=bool(namin >= INACT - 1e-9),
                   hub_ok=bool(nhmax < INACT))
        rows.append(row)
        print("  " + json.dumps(row), flush=True)
out["runs"] = rows
out["elapsed_s"] = time.time() - t0
ok = [q for q in rows if q["core_ok"] and q["active_ok"] and q["hub_ok"]]
out["feasible_rows"] = len(ok)
out["min_cost_feasible"] = min([q["best_penalised_cost"] for q in ok], default=None)
out["status"] = "inconclusive"
out["summary"] = ("k=11 sweep: %d/%d rows satisfy the side conditions; min coverD over "
                  "feasible rows = %s (U = %.12f)" %
                  (len(ok), len(rows),
                   ("%.12f" % out["min_cost_feasible"]) if ok else "none", U))
print()
print(out["summary"])
with open("research-2026/next-cover-global/members/threehub-cc2/evidence/"
          "exp2_k11_need_radius.json", "w") as f:
    json.dump(out, f, indent=1)
