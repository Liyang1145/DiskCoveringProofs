"""Step 3: bounded mechanism test of the relaxed value.

Relaxed problem (fixed anchors at the candidate angles):
    variables   sites C (14) and witnesses W for the KEPT faces only
    objective   f = max over retained constraints of |C_i - W_f|
    constraints (all must hold):
       kept face witness edges : |C_i - W_f| <= r, i in kept face f
       kept anchor edges       : |C_i - A_j| <= r, i in kept face f, A_j its anchor
       cut-site anchor edges   : |C_i - A_j| <= r for i in {8,9}, A_j in owners(i)
    Sites not appearing in any retained constraint are fixed to their candidate
    values (they are frozen, i.e. still present at their candidate positions).

If min f < r* then V_rel < r* and the relaxation kills the candidate radius
(numeric); if min f = r* then the relaxation leaves the candidate value intact.

Solver: Adam on a softmax-smoothed max (tau ramped down), several starts.
No scipy in this runtime; solver is written here and is *numeric only*.
"""
import json
import math
import numpy as np
from pathlib import Path
from fractions import Fraction

P = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\lead")
OUT = Path(r"C:\Users\袁力阳\Desktop\ai4math2\research-2026\next-cover-global\members\shared-radius-cc2\relaxed-value")
RD = json.loads((OUT / "relaxed_data.json").read_text())
D = json.loads((P / "improved-upper-test.json").read_text())
C0 = np.array([[float(Fraction(x)) for x in p] for p in D["centers"]])
A0 = np.array([[math.cos(math.radians(t)), math.sin(math.radians(t))]
               for t in RD["anchors_theta_deg"]])
r_star = RD["r_star"]
faces = RD["faces"]
kept = RD["kept_faces"]
owners = RD["owners"]
cut_sites = RD["sites_only_in_removed"]          # {8,9}
n = C0.shape[0]

# ---- retained constraint list (site index, partner index, kind)
cons = []
windex = {}
for f in kept:
    windex.setdefault(f, len(windex))
    w = windex[f]
    for s in faces[f]:
        cons.append(("w", s, w, f))
    for j, ow in enumerate(owners):
        for s in faces[f]:
            if s in ow:
                cons.append(("a", s, j, f))
for s in cut_sites:
    for j, ow in enumerate(owners):
        if s in ow:
            cons.append(("a", s, j, -1))

print("n retained constraints:", len(cons), flush=True)
nw = len(windex)
# variable vector: all sites (14) + kept witnesses (nw) -> 2*(14+nw)
NV = n + nw


def unpack(v):
    C = v[:2 * n].reshape(n, 2)
    W = v[2 * n:2 * n + 2 * nw].reshape(nw, 2)
    return C, W


def dists(v):
    C, W = unpack(v)
    d = np.empty(len(cons))
    for k, (t, s, j, f) in enumerate(cons):
        if t == "w":
            d[k] = np.linalg.norm(C[s] - W[j])
        else:
            d[k] = np.linalg.norm(C[s] - A0[j])
    return d


def smax(d, tau):
    m = d.max()
    return m + tau * math.log(np.exp((d - m) / tau).sum())


def smooth_obj(v, tau):
    return smax(dists(v), tau)


def grad(v, tau, eps=1e-6):
    g = np.zeros_like(v)
    for i in range(len(v)):
        vp = v.copy(); vp[i] += eps
        vm = v.copy(); vm[i] -= eps
        g[i] = (smooth_obj(vp, tau) - smooth_obj(vm, tau)) / (2 * eps)
    return g


def adam(start, steps=1500, lr=0.01, taus=(0.1, 0.03, 0.01, 0.003, 0.001, 3e-4, 1e-4)):
    v = start.copy()
    per = max(1, steps // len(taus))
    m = np.zeros_like(v); s = np.zeros_like(v)
    b1, b2, eps = 0.9, 0.999, 1e-8
    k = 0
    for tau in taus:
        for _ in range(per):
            k += 1
            g = grad(v, tau)
            m = b1 * m + (1 - b1) * g
            s = b2 * s + (1 - b2) * g * g
            v = v - lr * (m / (1 - b1 ** k)) / (np.sqrt(s / (1 - b2 ** k)) + eps)
    return v


def make_start(seed=None, jitter=0.0):
    v = np.zeros(2 * NV)
    v[:2 * n] = C0.ravel()
    C, W = unpack(v)
    # witness initial guess = circumcenter of the kept face's site triple
    for f, w in windex.items():
        a, b, c = (C0[faces[f][0]], C0[faces[f][1]], C0[faces[f][2]])
        M = 2 * np.array([b - a, c - a])
        rhs = np.array([b @ b - a @ a, c @ c - a @ a])
        O = np.linalg.solve(M, rhs)
        W[w] = O
    v[2 * n:2 * n + 2 * nw] = W.ravel()
    if seed is not None:
        rng = np.random.default_rng(seed)
        v = v + jitter * rng.normal(size=v.size)
    return v


def crop(v, r):
    """keep only sites participating in retained constraints"""
    return v

results = {}
# candidate start
v = make_start()
d0 = dists(v)
results["candidate_start"] = dict(max=d0.max(), argmax=int(d0.argmax()))
# optimize
steps = int(__import__("os").environ.get("STEPS", "600"))
lr = float(__import__("os").environ.get("LR", "0.02"))
best = None
starts = [("cand", make_start())]
for i, sd in enumerate([1, 2, 3]):
    starts.append((f"jit{sd}", make_start(seed=sd, jitter=0.05)))
for name, st in starts:
    v = adam(st, steps=steps, lr=lr)
    f = smooth_obj(v, 1e-5)
    d = dists(v)
    cand = dict(f=float(f), max=float(d.max()), argmax=int(d.argmax()),
                below_rstar=bool(d.max() < r_star - 1e-9))
    results[name] = cand
    if best is None or cand["f"] < best[1]["f"]:
        best = (name, cand, v)
print(json.dumps(results, indent=1), flush=True)
res = dict(r_star=r_star, results=results, nw=nw, n_cons=len(cons),
           cut_sites=cut_sites, kept=kept)
res["best"] = dict(name=best[0], **best[1])
np.save(OUT / "best_v.npy", best[2])
(OUT / "relaxed_test.json").write_text(json.dumps(res, indent=1))
print("BEST", best[0], json.dumps(best[1]), flush=True)
