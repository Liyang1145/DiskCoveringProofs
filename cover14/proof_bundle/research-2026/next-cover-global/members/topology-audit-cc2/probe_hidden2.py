"""Probe H: can the owner set grow when the radius grows, WITHOUT the active set growing?

This is exactly the sentence of lead/OWNER-COUNT-UNIFICATION.md §3 line 17:
  "Every hidden cell stays within D by §2 and has no new boundary ownership."
A hidden cell is a cell whose owned arc has length 0 (or is empty).  The claim says that
outward clipping (radius r -> r+e, domain D -> D_(1+e)) cannot turn such a cell into a
positive-length owner.  If it can, then the owner set at radius r+e (which is what the
whole no-chord measure argument is run on) strictly contains the owner set at r, and the
count q used by the argument is not the count of the original cover.

Method: one-parameter families + random families; for each configuration report
  A(r) = active sites, O(r) = positive owners,
  transitions O(r2) \ O(r1) with r2>r1 and A(r2)==A(r1).
"""
import json
import math
import random
from pathlib import Path

HERE = Path(__file__).resolve().parent
U = 0.33173203427623414


def dist(a, b):
    return math.hypot(a[0] - b[0], a[1] - b[1])


def scan_len(sites, r, samples=36000):
    """owned arc LENGTH per site (radians) by nearest-site sampling on S^1"""
    own = [0.0] * len(sites)
    for k in range(samples):
        th = 2 * math.pi * (k + 0.5) / samples
        x = (math.cos(th), math.sin(th))
        ds = [dist(x, c) for c in sites]
        m = min(ds)
        if m <= r:
            i = min(range(len(sites)), key=lambda j: ds[j])
            own[i] += 2 * math.pi / samples
    return own


def actives(sites, r):
    return [i for i, c in enumerate(sites) if math.hypot(*c) + r >= 1]


def family_ring(N, a, r_list, shrink, samples=36000):
    sites = [(a * math.cos(2 * math.pi * j / N), a * math.sin(2 * math.pi * j / N))
             for j in range(N)]
    sites[0] = (a - shrink, 0.0)
    rows = []
    prev = None
    for r in r_list:
        own = scan_len(sites, r, samples)
        O = frozenset(i for i, o in enumerate(own) if o > 1e-9)
        A = frozenset(actives(sites, r))
        rows.append(dict(r=r, nO=len(O), nA=len(A), O=sorted(O), A=sorted(A),
                         maxlen=max(own)))
    return rows


def family_ring_sweep():
    out = []
    for N in (11, 12, 14):
        for a in (0.86, 0.90, 0.94):
            for shrink in (0.0, 0.03, 0.08):
                r_list = [0.20, 0.24, 0.28, 0.32, U, 0.36]
                rows = family_ring(N, a, r_list, shrink)
                # look for O growth with constant A
                for i in range(len(rows) - 1):
                    g = set(rows[i + 1]["O"]) - set(rows[i]["O"])
                    lost = set(rows[i]["O"]) - set(rows[i + 1]["O"])
                    if g or lost:
                        out.append(dict(N=N, a=a, shrink=shrink,
                                        r1=rows[i]["r"], r2=rows[i + 1]["r"],
                                        gained=sorted(g), lost=sorted(lost),
                                        A1=rows[i]["A"], A2=rows[i + 1]["A"],
                                        A_same=(rows[i]["A"] == rows[i + 1]["A"])))
    return out


def random_families(trials=3000, m=14, seed=7):
    random.seed(seed)
    hits = []
    for t in range(trials):
        # clustered configuration: ring + jitter
        N = random.choice([10, 11])
        a = 0.85 + random.random() * 0.12
        sites = [(a * math.cos(2 * math.pi * j / N) + (random.random() - 0.5) * 0.04,
                  a * math.sin(2 * math.pi * j / N) + (random.random() - 0.5) * 0.04)
                 for j in range(N)]
        while len(sites) < m:
            rr = math.sqrt(random.random()) * 0.85
            th = random.random() * 2 * math.pi
            sites.append((rr * math.cos(th), rr * math.sin(th)))
        for r in (0.30, 0.315, 0.325, 0.3315, U):
            own = scan_len(sites, r, samples=7200)
            O = set(i for i, o in enumerate(own) if o > 1e-9)
            A = set(actives(sites, r))
            if A - O:
                hits.append(dict(trial=t, N=N, r=r, nonowner_active=sorted(A - O),
                                 nO=len(O), nA=len(A)))
    return hits


if __name__ == "__main__":
    rep = {}
    rep["ring_sweep_transitions"] = family_ring_sweep()[:40]
    rep["random_nonowner_active"] = random_families()[:40]
    (HERE / "evidence" / "probe-hidden.json").write_text(json.dumps(rep, indent=1),
                                                         encoding="utf-8")
    print(json.dumps(rep["ring_sweep_transitions"], indent=1)[:3000])
    print("random nonowner active hits:", len(rep["random_nonowner_active"]))
    print(json.dumps(rep["random_nonowner_active"][:10], indent=1)[:2000])

