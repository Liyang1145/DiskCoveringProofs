"""Owner-count vs active-count probes for the lead's OWNER-COUNT-UNIFICATION.md.

Object: D = unit closed disk; N=14 sites; radius r<=U=0.33173203427623414.
  active  = disk meets S^1 (|c|+r >= 1)
  owned positive arc J_i = {x in S^1 : x is strictly nearest to site i and |x-c_i|<=r}
For a site i with a NONEMPTY cell the owned arc is the S^1 part of its Voronoi cell W_i
(this is where the k10 chain and the unification both consume coverage).

Tests:
  T1  projection lemma: for any disk meeting D, the projected-centre disk contains
      D cap B(c,r); and for boundary-active centres the two roots give the same arc.
  T2  hidden-cell lemma (§2): W_i cap S^1 = {x} singleton => W_i subset D  (search).
  T3  ownership counts in explicit symmetric configurations: does an 11-active cover at
      r<=U exist whose positive-owner count q is 10 or 11?  Does q ever exceed the number
      of active sites, or does a positive-length owned arc exist with length > 2 asin r?
  T4  is the number of ACTIVE but NON-OWNING sites ever > 1 for a cover? (the unified
      claim needs the hidden cells to be non-owners at r)
"""
import json
import math
import random
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
R = 0.33173203427623414

random.seed(20260925)


def dist(a, b):
    return math.hypot(a[0] - b[0], a[1] - b[1])


def active(site, r=R):
    return math.hypot(*site) + r >= 1.0


def owners(sites, r=R, samples=200000):
    """returns per-site owned measure (fraction of S^1) by nearest-site sampling"""
    cnt = [0] * len(sites)
    for k in range(samples):
        th = 2 * math.pi * k / samples
        x = (math.cos(th), math.sin(th))
        best = None
        bi = -1
        for i, c in enumerate(sites):
            d = dist(x, c)
            if best is None or d < best - 1e-15:
                best = d
                bi = i
        if best <= r:
            cnt[bi] += 1
    return [c / samples * 2 * math.pi for c in cnt]  # owned arc LENGTH in radians


def coverage_radius(sites, samples=400000, lo=0.05, hi=0.6, tol=1e-12):
    """binary search minimal r covering D by disks of radius r around the IS projection of sites"""
    def covered(r):
        for k in range(samples):
            th = 2 * math.pi * k / samples
            x = (math.cos(th), math.sin(th))
            if all(dist(x, c) > r for c in sites):
                return False
        return True
    if not covered(hi):
        return None
    for _ in range(60):
        mid = (lo + hi) / 2
        if covered(mid):
            hi = mid
        else:
            lo = mid
    return hi


def T1():
    """projection lemma: centre outside D -> projected disk still contains D cap B(c,r)"""
    out = {"trials": 0, "violations": 0, "worst_margin": -1e9}
    r = R
    for _ in range(3000):
        th = random.random() * 2 * math.pi
        t = 1.0 + random.random() * r          # centre outside D, disk meets D
        c = (t * math.cos(th), t * math.sin(th))
        cp = (math.cos(th), math.sin(th))
        # sample D cap B(c,r)
        for _ in range(400):
            rr = math.sqrt(random.random())
            xx = (rr * math.cos(random.random() * 2 * math.pi),
                  rr * math.sin(random.random() * 2 * math.pi))
            if dist(xx, c) <= r:
                out["trials"] += 1
                marg = dist(xx, cp) - r
                out["worst_margin"] = max(out["worst_margin"], marg)
                if marg > 1e-12:
                    out["violations"] += 1
    # inner-root arc identity: same alpha, roots rho_pm, containment
    out2 = {"root_containment_violations": 0, "samples": 0}
    for _ in range(2000):
        alpha = random.random() * math.asin(r)
        disc = r * r - math.sin(alpha) ** 2
        if disc < 0:
            continue
        rp = math.cos(alpha) + math.sqrt(disc)
        rm = math.cos(alpha) - math.sqrt(disc)
        # x on the inner-root disk D cap B(rm u, r) must be in B(rp u, r)
        for _ in range(300):
            rr = math.sqrt(random.random())
            xx = (rr * math.cos(random.random() * 2 * math.pi),
                  rr * math.sin(random.random() * 2 * math.pi))
            if dist(xx, (rm, 0.0)) <= r:
                out2["samples"] += 1
                if dist(xx, (rp, 0.0)) > r + 1e-12:
                    out2["root_containment_violations"] += 1
    return {"T1a_projection": out, "T1b_roots": out2}


def T3_symmetric():
    """sites on a circle of radius a; report owner count and radii for k=10,11"""
    res = []
    for k in (10, 11):
        for a in (0.80, 0.90, 0.94):
            sites = [(a * math.cos(2 * math.pi * j / k), a * math.sin(2 * math.pi * j / k))
                     for j in range(k)]
            # minimal radius covering S^1 for this ring
            rr = math.sqrt(a * a + 1 - 2 * a * math.cos(math.pi / k))
            if rr > R:
                continue
            own = owners(sites, r=rr, samples=40000)
            res.append(dict(k=k, a=a, r_boundary_cover=rr,
                            owners=sum(1 for o in own if o > 1e-6),
                            max_owner_len=max(own), halfwidth_bound=2 * math.asin(rr),
                            all_active=all(active(s) for s in sites),
                            cover_D_radius=coverage_radius(sites, samples=20000)))
    return res


def T2_singleton_search():
    """sample 14-site configurations inside D; for each site with tiny owned measure report
    whether W_i has points outside D (owned measure ~0 but cell extends out)."""
    worst = []
    for trial in range(400):
        m = 14
        sites = []
        for _ in range(m):
            rr = math.sqrt(random.random()) * 0.99
            th = random.random() * 2 * math.pi
            sites.append((rr * math.cos(th), rr * math.sin(th)))
        own = owners(sites, r=R, samples=4000)
        # radial extent of each cell
        for i, c in enumerate(sites):
            if own[i] > 1e-9:
                continue
            out_count = 0
            for _ in range(300):
                rr = 1.0 + random.random() * 0.05
                th = random.random() * 2 * math.pi
                x = (rr * math.cos(th), rr * math.sin(th))
                di = dist(x, c)
                if di <= R and all(dist(x, c2) >= di - 1e-15 for j, c2 in enumerate(sites) if j != i):
                    out_count += 1
            if out_count:
                worst.append(dict(trial=trial, site=i, outside_hits=out_count,
                                  norm=math.hypot(*c), owned=own[i]))
    return worst[:10]


if __name__ == "__main__":
    rep = {}
    rep["T1"] = T1()
    rep["T3_symmetric"] = T3_symmetric()
    rep["T2_singleton_outside"] = T2_singleton_search()
    print(json.dumps(rep, indent=1))
    (HERE / "evidence" / "owner-probe.json").write_text(json.dumps(rep, indent=1),
                                                        encoding="utf-8")
