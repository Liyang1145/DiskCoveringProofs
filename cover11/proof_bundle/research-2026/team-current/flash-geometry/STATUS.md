# flash-geometry STATUS — hub-free representation & core-hub domain audit

Owner: flash-geometry (independent analytic task). Write scope: this directory only.
Caliber: D = unit closed disk; 11 equal disks of radius r <= 19/50; positions in units
of the unit-disk radius; angles in radians. "Cover" = D subset of the union of the 11
closed disks. All statements are about *necessary* conditions unless marked proved.

## Current results

| # | Statement | Status | Scope | Evidence |
|---|---|---|---|---|
| A1 | Correct arc half-width of a radius-r disk covering bd(D): t(rho) = arccos((1+rho^2-r^2)/(2 rho)), maximised at rho = sqrt(1-r^2) with value **asin r**, and t <= asin r always | proved (elementary) | any r in (0,1); disk centre with 1-r <= rho <= 1+r | algebra: cos t >= sqrt(1-r^2) by AM-GM, equality iff rho = sqrt(1-r^2); `tools/geom.py:arc_halfwidth` |
| A2 | Consequently 9 ring arcs have total width <= 18 asin r; at r=.38 this is 7.016019 vs 2pi = 6.283185, i.e. **arc capacity has slack .732834** and is NOT the binding side | numeric-elementary (uses A1) | r=.38, 9 boundary disks | `tools/reform_calib.py` |
| A3 | Hub-free reformulation: an 11-disk cover at radius r exists iff 9 disks a_1..a_9 (the boundary disks) plus two disks of the same radius r cover D; the two extra disks are exactly the hubs and their positions enter only through the hole U = D \ union B(a_j,r). Necessary side: U must be 2-centre coverable at radius r, and bd(D) must be covered by the 9 rings | proved (elementary reduction; the "if" direction is a definition, the "only if" uses |h| < 1-r) | reduction C450/C451 | this file, section "hub-free" |
| A4 | `lead/CORE-TWO-HUB-DOMAIN.md` audited: (C1)-(C6) all correct; exact iff form of the arc criterion; product condition is sharp and is the best possible (s_1,s_2)-only consequence; r >= 1/3 necessary | proved (independent re-derivation + 300/300 random cross-check vs direct sampling + symbolic algebra) | two hubs, core disk B(0,1-2r) | `CORE-HUB-DOMAIN-AUDIT.md`, `tools/audit_core_hub.py` |
| A5 | Certified 9+2 object: min hub modulus .149428 lies strictly OUTSIDE the C450 |h| <= .14 domain but inside the new .294618 domain -> the extension is not vacuous | one object, r ~ .37998385 | `tools/audit_core_hub.py` last block |
| A6 | Certified object measure: the 9 ring disks alone already cover bd(D) (max over bd D of min over rings = .37998385311984 = the certified value, refined); exactly 2 centres have |c| < 1-r; both hubs satisfy 1-2r <= |h| <= 2r; the strict ring hole has radial depth function in [.3203,.6224] | numeric (grid + refinement), calibration only | `tools/hole_shadow.py`, `tools/check_cert_boundary.py` |
| A7 | 3-ring common point (O1) is NOT refutable by the pure-co-point capacity budget: grid max of the 3-arc union width under the co-point constraint vs threshold 2pi-12 asin r = 1.605630 | numeric, superseded by Lead's certified counterexample (margin -.0757) | exploration | `tools/o1_test.py` — do not use as evidence |
| A8 | Exact hub domain: Branch A `min s <= r-a`, or Branch B `s_j in [r-a,r+a] and delta >= 2pi-b_1(s_1)-b_2(s_2)`. The position-only product condition `s_1 s_2 <= r^2-a^2` is necessary but **not sufficient** (s_1=s_2=sqrt(r^2-a^2) with delta=0 fails). For r>1/3 the function b_j(s) is strictly decreasing on [r-a,r+a], from pi down to 0, with b_j = pi/2 exactly at s_j = sqrt(r^2-a^2). On the feasible region b_1+b_2 >= pi, so the required separation 2pi-b_1-b_2 lies in **[0,pi]**. | proved | two hubs, core B(0,a) | `CORE-HUB-DOMAIN-AUDIT.md`; `tools/audit_hub_domain2.py`, `tools/audit_core_hub.py` |
| A9 | **Two-convex-boundary lemma**: K closed convex bounded, C_1,C_2 closed convex, bd K subset C_1 u C_2  =>  K subset C_1 u C_2. Hence the hub-domain criterion for the core *circle* is an iff for the core *disk*, making (C3)+(C5)+(D1) the exact core obligation (necessary **and** sufficient). Fails for 3+ convex sets (verified control at r=.38: three disks of radius r at |c|=.42 spaced 120 deg cover bd B(0,.24) but not B(0,.24), since the origin is at .42 > r). | proved (elementary: strong separation + common descent ray; independently derived by the Lead) | any two closed convex sets, any closed convex bounded K | `CORE-HUB-DOMAIN-AUDIT.md` §(C7); claims C806 |

## Hub-free representation (A3) in bare form
D covered by 11 radius-r disks, 9 of them boundary disks (|a_j| >= 1-r) and 2 hubs
(|h_j| < 1-r) <==> bd(D) subset union_{j<=9} B(a_j,r)  AND  U := D \ union_{j<=9} B(a_j,r)
is contained in a union of 2 closed radius-r disks. Reason for the "only if": a hub
with |h| < 1-r satisfies |u-h| >= 1-|h| > r on bd(D), so hubs never cover bd(D); hence
the 9 ring disks must, and every remaining point of D (exactly U) is hub-only.
Payoff: all hub coordinates are eliminated from the covering statement; the hub side
becomes the 2-centre radius of an explicit planar set U built from the 9 rings. The
quantitative bottleneck then sits in T_2(U) <= r, not in arc capacity (A2).

## Discarded / corrected instruments (do not cite)
- `tools/check_cert_boundary.py`: printed "sum of arc widths = 9.018881" using the
  WRONG formula arcsin(r/rho). The correct one is arccos((1+rho^2-r^2)/(2rho)) (A1).
  The script's *other* output (boundary argmax .37998385311984 by direct distances) is
  unaffected and matches the certified value. The 9.018881 line is invalid.
- `tools/explore3.py`: near-root/far-root and "outside" orientation errors (Lead's
  reading). Exploration only, never load-bearing; superseded.
- `tools/reform_calib.py` "hole extreme points": the filter min_j |p-a_j| >= r is
  vacuous for pairwise circle intersections (they sit exactly at distance r from two
  rings). Equality points need the C458 accessibility test before they may be used as
  witnesses. Its T1/T2 numbers are therefore invalid.
- `tools/hole_of_object.py`, `tools/hole_meb.py`: O(n^3) exhaustive MEB on 10^6 grid
  points, timed out. Grid scans are not evidence here.

## Next obligation
One concrete open step in this line: T_2(U) <= r is a 2-centre condition on the hole of
9 boundary disks; the exact statement needs the strict-hole accessibility filter (C458)
so that equality/tangency points do not enter as witnesses. Next: state and prove the
strict version (U open, cl(U) = U-union of accessible equality points), and check
whether the C458 criterion simplifies for the ring-hole structure.
