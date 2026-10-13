"""Decisive probes for the lead's OWNER-COUNT-UNIFICATION.md §2/§3.

Direction conventions (fixed after an earlier sign error in probe_owners.py):
  projection lemma: if the disk B(c,r) covers part of D, then for the inward projection
  c' = c/max(1,|c|) the containment that HOLDS is  D cap B(c',r) subset of D cap B(c,r)
  (the projected disk is the smaller one; it is still inside D).  A cover of D stays a
  cover after projecting centres in, because every point of D already has some centre of
  norm <= 1 within r.
  inner-root lemma: for a boundary-active centre at the OUTER root the containment that
  HOLDS is  D cap B(rho+ u, r) subset of D cap B(rho- u, r).
  outward clip: domain D_(1+e), radius r+e, same centres; owners / positive owners.

Probe Z (the decisive one): take an 11-active configuration at radius slightly above U
(so 11 disks really cover S^1 with each owned arc positive at that radius) and move one
centre inward until its own boundary arc has collapsed at r=U.  At each radius report
  * the owner set O(r) = sites with positive-length owned arc,
  * the ACTIVE set A(r) = sites with |c|+r >= 1,
  * whether some site is in O(r+e) but NOT in O(r) while A(r+e) == A(r),
  * whether a positive owner has length > 2 asin r,
  * whether two owned arcs can touch at a boundary triple point with the third site
    non-owning (the 'hidden singleton' of the unification).
This tests the exact sentence of §3 line 17 ('every hidden cell ... has no new boundary
ownership').
"""
import json
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent
U = 0.33173203427623414


def dist(a, b):
    return math.hypot(a[0] - b[0], a[1] - b[1])


def scan(sites, r, samples=72000):
    """nearest-site ownership on S^1 with tie detection (integer counters)"""
    own = [0] * len(sites)
    tie3 = 0
    tie2 = 0
    best_at_tie = []
    for k in range(samples):
        th = 2 * math.pi * k / samples
        x = (math.cos(th), math.sin(th))
        ds = [dist(x, c) for c in sites]
        m = min(ds)
        near = [i for i, d in enumerate(ds) if d <= m + 1e-12]
        if len(near) >= 3:
            tie3 += 1
            best_at_tie.append([i for i in near if ds[i] <= r])
        elif len(near) == 2:
            tie2 += 1
        if m <= r:
            own[near[0]] += 1
    return own, tie2, tie3, best_at_tie


def main():
    rep = {}
    # ------------------------------------------------------------------ probe Z
    # 11 disks on a ring of radius a; equal spacing covers S^1 at radius rb.
    # Move ONE centre inward (towards the origin) keeping its own tangent point.
    # Its arc at the original rb was positive (it 'owned' a sector); as its norm shrank
    # with rb fixed the arc shrinks towards the single tangency point.
    res = []
    for a in (0.90, 0.94, 0.97):
        k = 11
        rb = math.sqrt(a * a + 1 - 2 * a * math.cos(math.pi / k))
        for r in (rb, U, U + 5e-4, U + 1e-3):
            if r < rb - 1e-12:
                continue
            for shrink in (0.0, 0.002, 0.01, 0.03):
                sites = [(a * math.cos(2 * math.pi * j / k), a * math.sin(2 * math.pi * j / k))
                         for j in range(k)]
                # site 0 moved radially inward
                aa = a - shrink
                sites[0] = (aa, 0.0)
                own, tie2, tie3, tie3sets = scan(sites, r)
                pos = [i for i, o in enumerate(own) if o > 0]
                act = [i for i, c in enumerate(sites) if math.hypot(*c) + r >= 1 - 1e-15]
                lens = [o / 72000 * 2 * math.pi for o in own]
                res.append(dict(a=a, k=k, r=repr(r), shrink=shrink,
                                r_boundary_cover=rb,
                                active=len(act), owners=len(pos),
                                nonowner_active=[i for i in act if i not in pos],
                                max_owner_len=max(lens), bound_2asinr=2 * math.asin(r),
                                len_over_bound=sum(1 for o in lens if o > 2 * math.asin(r) + 1e-9),
                                triple_ties=tie3,
                                triple_sets=json.dumps(tie3sets[:3])))
    rep["Z_ring_shrink"] = res

    # ------------------------------------------------------- direction checks (fixed)
    # projection: D cap B(c',r) subset D cap B(c,r)
    r = U
    viol = 0
    tot = 0
    for i in range(200000):
        th = (i * 0.6180339887498949) % 1 * 2 * math.pi
        t = 1.0 + ((i * 0.7548776662466927) % 1) * r
        c = (t * math.cos(th), t * math.sin(th))
        cp = (math.cos(th), math.sin(th))
        rr = math.sqrt(((i * 0.5698402909980532) % 1))
        ph = ((i * 0.3819660112501051) % 1) * 2 * math.pi
        x = (rr * math.cos(ph), rr * math.sin(ph))
        if dist(x, cp) <= r:
            tot += 1
            if dist(x, c) > r + 1e-12:
                viol += 1
    rep["projection_containment_DcapBcp_subset_DcapBc"] = dict(samples=tot, violations=viol)

    # inner root: D cap B(rho+ u, r) subset D cap B(rho- u, r)
    viol2 = 0
    tot2 = 0
    for i in range(4000):
        alpha = ((i * 0.6180339887498949) % 1) * math.asin(r)
        disc = r * r - math.sin(alpha) ** 2
        if disc < 0:
            continue
        rp = math.cos(alpha) + math.sqrt(disc)
        rm = math.cos(alpha) - math.sqrt(disc)
        for j in range(40):
            rr = math.sqrt(((i * 0.7 + j * 0.13) % 1))
            ph = ((i * 0.37 + j * 0.29) % 1) * 2 * math.pi
            x = (rr * math.cos(ph), rr * math.sin(ph))
            if dist(x, (rp, 0.0)) <= r:
                tot2 += 1
                if dist(x, (rm, 0.0)) > r + 1e-12:
                    viol2 += 1
    rep["inner_root_containment"] = dict(samples=tot2, violations=viol2)
    (HERE / "evidence" / "owner-probe2.json").write_text(json.dumps(rep, indent=1),
                                                         encoding="utf-8")
    print(json.dumps(rep["projection_containment_DcapBcp_subset_DcapBc"]))
    print(json.dumps(rep["inner_root_containment"]))
    for row in res[:14]:
        print(json.dumps(row))


if __name__ == "__main__":
    main()
