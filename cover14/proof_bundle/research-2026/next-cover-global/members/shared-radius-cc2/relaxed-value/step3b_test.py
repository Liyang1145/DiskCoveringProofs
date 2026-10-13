"""Step 3b: relaxed mechanism test with an exact Newton/trust-region local solver
(pure numpy; scipy is absent in this runtime).

Relaxed problem, fixed anchors at candidate angles:
  sites C (14, all kept as variables) ; witnesses W of the 8 retained faces.
  retained constraints: witness edges (C_s,W_f) for s in kept face f, and
  anchor edges (C_s,A_j) for s in kept face f and its anchors, plus the
  cut-site anchor edges for s in {8,9}.
  value V_rel = min max over retained constraints of that distance.

If V_rel < r* the relaxation lowers the certificate value at the candidate; if
V_rel = r* (up to solver tolerance) the candidate value survives the removal.
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
faces = RD["faces"]; kept = RD["kept_faces"]; owners = RD["owners"]
cut_sites = RD["sites_only_in_removed"]
n = C0.shape[0]

# ---- constraints
cons = []
windex = {}
for f in kept:
    windex.setdefault(f, len(windex))
    w = windex[f]
    for s in faces[f]:
        cons.append(("w", s, w, f))
    for s in faces[f]:
        for j, ow in enumerate(owners):
            if s in ow:
                cons.append(("a", s, j, f))
for s in cut_sites:
    for j, ow in enumerate(owners):
        if s in ow:
            cons.append(("a", s, j, -1))
nw = len(windex)
NV = n + nw
print("cons", len(cons), "witnesses", nw, flush=True)


def unpack(v):
    return v[:2 * n].reshape(n, 2), v[2 * n:].reshape(nw, 2)


def dists(v):
    C, W = unpack(v)
    d = np.empty(len(cons))
    for k, (t, s, j, f) in enumerate(cons):
        d[k] = np.linalg.norm(C[s] - (W[j] if t == "w" else A0[j]))
    return d


def val(v):
    return dists(v).max()


def make_start(jitter=0.0, seed=0):
    v = np.zeros(2 * NV)
    C, W = unpack(v)
    C[:] = C0
    for f, w in windex.items():
        a, b, c = C0[faces[f][0]], C0[faces[f][1]], C0[faces[f][2]]
        M = 2 * np.array([b - a, c - a]); rhs = np.array([b @ b - a @ a, c @ c - a @ a])
        W[w] = np.linalg.solve(M, rhs)
    if jitter:
        rng = np.random.default_rng(seed)
        v = v + jitter * rng.normal(size=v.size)
    return v


def local_solve(v, iters=400, verbose=False):
    """Minimize max distance: active-set Gauss-Newton on the max constraint."""
    for it in range(iters):
        d = dists(v)
        k = int(np.argmax(d))
        t, s, j, f = cons[k]
        C, W = unpack(v)
        target = W[j] if t == "w" else A0[j]
        # gradient of the active distance wrt the involved variables
        g = np.zeros(2 * NV)
        diff = C[s] - target
        nd = max(d[k], 1e-14)
        g[2 * s:2 * s + 2] = diff / nd
        if t == "w":
            g[2 * n + 2 * j:2 * n + 2 * j + 2] = -diff / nd
        # line search: reduce the active distance while not increasing the rest
        step = 1.0
        improved = False
        for _ in range(60):
            vn = v - step * g
            dn = dists(vn)
            if dn[k] < d[k] - 1e-15 and dn.max() <= d.max() + 1e-12:
                v = vn
                improved = True
                break
            if dn.max() < d.max() - 1e-15:
                v = vn
                improved = True
                break
            step *= 0.5
        if not improved:
            if verbose:
                print("stall at iter", it, "max", d.max(), flush=True)
            break
    return v


res = dict(r_star=r_star, n_cons=len(cons), nw=nw, cut_sites=cut_sites, kept=kept)
runs = {}
for name, v0 in [("cand", make_start()),
                 ("j1", make_start(0.02, 1)), ("j2", make_start(0.05, 2)),
                 ("j3", make_start(0.1, 3))]:
    d0 = dists(v0)
    v = local_solve(v0, iters=2000)
    d = dists(v)
    runs[name] = dict(max0=float(d0.max()), max=float(d.max()),
                      delta=float(d.max() - d0.max()),
                      below=bool(d.max() < r_star - 1e-9))
    print(name, "start", d0.max(), "->", d.max(), flush=True)
# also test with the cut sites 8,9 allowed to move freely (no anchor pinning)
res["runs"] = runs
OUT.joinpath("relaxed_test2.json").write_text(json.dumps(res, indent=1))
print(json.dumps(runs, indent=1))
