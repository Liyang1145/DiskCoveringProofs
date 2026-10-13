"""Step 4: (i) confirm V_rel == r* numerically at high resolution;
(ii) bridging / connectivity audit of the retained constraints;
(iii) the "component rotation" directions the lead pointed at.

(i) V_rel is computed by an active-set descent that is monotonically
non-increasing; from every perturbed start it converges back to the candidate
value, never below.  We also relax the cut-site pinning (drop the 4 anchor
edges of sites 8,9) and let those two sites move freely, to see whether the
freed X-sites enable a lower value.

(ii) For each retained constraint we record which anchors/sites bridge the
removed block to the retained block, and whether any retained constraint
involves a site that the removed faces still "own".
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
removed = RD["removed_faces"]
cut = RD["sites_only_in_removed"]
n = C0.shape[0]
# site -> list of (anchor index) that own it
site_anchor = {}
for j, ow in enumerate(owners):
    for s in ow:
        site_anchor.setdefault(s, []).append(j)

# ---------- (ii) bridge table for retained (kept) faces
bridge_rows = []
for f in kept:
    for s in faces[f]:
        # a site is "bridging" if it is shared between a removed face and a kept face
        in_removed = any(s in faces[g] for g in removed)
        for j in site_anchor.get(s, []):
            # does this anchor also own a site that appears in a removed face?
            touch_removed = any(any(t in faces[g] for g in removed) for t in owners[j])
            bridge_rows.append(dict(face=f, site=s, anchor=j,
                                    site_in_removed=bool(in_removed),
                                    anchor_touches_removed=bool(touch_removed)))
audit = dict(
    r_star=r_star, cut_sites=cut,
    kept=kept, removed=removed,
    bridging_anchor_sites=sorted({(r["anchor"], r["site"]) for r in bridge_rows
                                  if r["anchor_touches_removed"]}),
    n_bridging_rows=int(sum(1 for r in bridge_rows if r["anchor_touches_removed"])),
    site_anchor=site_anchor,
    sites_in_removed_faces=sorted({s for g in removed for s in faces[g]}),
    sites_in_kept_faces=sorted({s for g in kept for s in faces[g]}),
)
print("cut sites", cut, flush=True)
print("sites in removed faces", audit["sites_in_removed_faces"], flush=True)
print("sites in kept faces", audit["sites_in_kept_faces"], flush=True)
print("bridging (anchor,site) pairs:", audit["bridging_anchor_sites"], flush=True)

# ---------- (i)+(iii) numerical: with cut sites pinned vs free
import importlib.util
spec = importlib.util.spec_from_file_location("s3b", OUT / "step3b_test.py")
# cannot import (it runs); re-implement the small solver inline instead
cons = []
windex = {}
for f in kept:
    windex.setdefault(f, len(windex))
    w = windex[f]
    for s in faces[f]:
        cons.append(("w", s, w))
    for s in faces[f]:
        for j in site_anchor.get(s, []):
            cons.append(("a", s, j))
for s in cut:
    for j in site_anchor.get(s, []):
        cons.append(("a", s, j))
nw = len(windex)
NV = n + nw


def unpack(v):
    return v[:2 * n].reshape(n, 2), v[2 * n:].reshape(nw, 2)


def dists(v):
    C, W = unpack(v)
    return np.array([np.linalg.norm(C[s] - (W[j] if t == "w" else A0[j]))
                     for (t, s, j) in cons])


def start(jitter=0.0, seed=0):
    v = np.zeros(2 * NV)
    C, W = unpack(v)
    C[:] = C0
    for f, w in windex.items():
        a, b, c = C0[faces[f][0]], C0[faces[f][1]], C0[faces[f][2]]
        M = 2 * np.array([b - a, c - a]); rhs = np.array([b @ b - a @ a, c @ c - a @ a])
        W[w] = np.linalg.solve(M, rhs)
    if jitter:
        v = v + jitter * np.random.default_rng(seed).normal(size=v.size)
    return v


def solve_bruteforce(v, iters=4000):
    """coordinate-free active-set descent with exact local line search"""
    for it in range(iters):
        d = dists(v)
        k = int(np.argmax(d))
        t, s, j = cons[k]
        C, W = unpack(v)
        tgt = W[j] if t == "w" else A0[j]
        diff = C[s] - tgt
        nd = max(float(d[k]), 1e-15)
        g = np.zeros(2 * NV)
        g[2 * s:2 * s + 2] = diff / nd
        if t == "w":
            g[2 * n + 2 * j:2 * n + 2 * j + 2] = -diff / nd
        step = 1.0
        ok = False
        for _ in range(80):
            vn = v - step * g
            dn = dists(vn)
            if dn.max() < d.max() - 1e-16:
                v, ok = vn, True
                break
            step *= 0.5
        if not ok:
            break
    return v


runs = {}
for name, jit, seed in [("cand", 0.0, 0), ("j02", 0.02, 1), ("j05", 0.05, 2),
                        ("j10", 0.10, 3), ("j20", 0.20, 4)]:
    v0 = start(jit, seed)
    v = solve_bruteforce(v0)
    d = dists(v)
    runs[name] = dict(max=float(d.max()), below=bool(d.max() < r_star - 1e-9),
                      n_below=int((d < r_star - 1e-9).sum()))
    print(name, "->", d.max(), "below?", runs[name]["below"], flush=True)
audit["numeric_pinned"] = runs

# free cut sites: drop the 4 cut-site anchor rows, let sites 8,9 float
cons2 = [c for c in cons if not (c[0] == "a" and c[1] in cut)]
_cons = cons
cons = cons2
runs2 = {}
for name, jit, seed in [("cand", 0.0, 0), ("j05", 0.05, 2), ("j20", 0.20, 4)]:
    v0 = start(jit, seed)
    v = solve_bruteforce(v0)
    d = dists(v)
    runs2[name] = dict(max=float(d.max()), below=bool(d.max() < r_star - 1e-9))
    print("free", name, "->", d.max(), flush=True)
cons = _cons
audit["numeric_cut_free"] = runs2
OUT.joinpath("bridge_audit.json").write_text(json.dumps(audit, indent=1, default=str))
print("wrote bridge_audit.json")
