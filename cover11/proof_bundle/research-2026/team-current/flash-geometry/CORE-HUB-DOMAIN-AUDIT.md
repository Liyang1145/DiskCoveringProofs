# Independent audit — `lead/CORE-TWO-HUB-DOMAIN.md`

**Verdict: file's claims are correct.** Re-derived and checked with a different
representation (direct dense sampling of the core circle; symbolic algebra; exact
rationals). One scope precondition must be stated explicitly (point 3 below).
Independent review pending; no novelty claim.

## Caliber / scope
D = unit closed disk; 11 equal disks of radius r; the C450/C451 reduction
(exactly 9 *boundary* disks with |a_i| >= 1-r, 2 *hubs* strictly interior
|h_j| < 1-r); a = 1-2r > 0; s_j = |h_j|; delta in [0,pi] = smaller angle between
h_1, h_2. All statements below are about *necessary* conditions for a cover.

## (C1) Core is hub-only
|x| < a and |a_i| >= 1-r give |x-a_i| >= (1-r)-|x| > r, so the 9 ring disks miss
the **open** core. The hubs' union is closed (finite union of closed disks) and
contains the open core, hence contains the closed core B(0,a). Correct.

## (C2) Branch A
s_j <= r-a  =>  |x-h_j| <= |x|+s_j <= a+s_j <= r for all |x| <= a, so that hub
alone covers the core. Correct (r >= 1/3 needed for branch A to be nonempty;
for r < 1/3 it is empty).

## (C3) Branch B — exact criterion, audited by independent representation
If neither hub alone covers the core then s_j in (r-a, r+a) and
`b_j = acos((a^2+s_j^2-r^2)/(2 a s_j))` in (0,pi) is the half-width of hub j's arc
on the core circle. Then

  the two closed arcs cover the whole core circle  <=>  b_1 + b_2 >= 2pi - delta.

(For r > 1/3, b_j is strictly decreasing in s_j on the admissible window and equals
pi exactly at s_j = r-a, which is the Branch A boundary; see the domain section.)

Derivation in complement form (cleanest, and it is what the inequality means): the
uncovered set is the intersection of the two complementary arcs, of half-widths
pi-b_1 and pi-b_2, whose centres are delta apart on the circle; that intersection is
non-empty iff (pi-b_1)+(pi-b_2) >= delta, i.e. iff b_1+b_2 <= 2pi-delta.
Covering the core *circle* implies covering the core *disk*: this is **not** the
one-disk convexity argument (the union of two disks is not convex and the naive
argument only covers one disk); it is proved in section (C7) below.
(Calibration only, not proof: 300/300 random (s_1,s_2,delta) agree with direct
evaluation of min(|u-h_1|,|u-h_2|) <= r on 2*10^5 points of the core circle, and
tangential stress cases flip exactly at the threshold.) **Scope precondition** the file
leaves implicit: the b_j formula presupposes the admissibility |a-r| <= s_j <= a+r; in
branch B it holds automatically (s_j > a+r means the disk misses the core entirely, so
the other hub must cover it alone; s_j < r-a is branch A).

## (C4) Product condition and its exact status — checked symbolically
 2 a s_1 s_2 (cos b_1 + cos b_2) = (s_1+s_2) (s_1 s_2 + a^2 - r^2).
Since b_1+b_2 >= pi <=> cos b_1 + cos b_2 <= 0 (monotonicity of cos on [0,pi]):

  b_1+b_2 >= 2pi-delta >= pi  =>  s_1 s_2 <= r^2 - a^2   (equivalently (s_1+s_2)(1-(r^2-a^2)/(s_1 s_2)) <= 0)

and with branch A (0 <= r-a <= sqrt(r^2-a^2) for r >= 1/3) this gives, after
relabelling, **min(s_1,s_2) <= sqrt(r^2-a^2) = sqrt((1-r)(3r-1))**.
*Structural remark:* the product condition is obtained from delta <= pi alone, so it
only uses the core constraint; the delta-dependence is exactly the (C3) criterion.
Therefore no further (s_1,s_2)-only improvement is available from the core
constraint — any improvement must use the hubs' remaining obligations.
*Sharp:* s_1 = s_2 = sqrt(r^2-a^2) with delta = pi gives b_1 = b_2 = pi/2 and the four
arc endpoints touch; direct sampling confirms the core circle is exactly covered.
So the bound is attained already in the core-only relaxation.
At r = 19/50 exactly: r^2-a^2 = 217/2500, bound = sqrt(217)/50 = .2946183972531247.

## (C5) r >= 1/3 is necessary — checked
For r < a a single radius-r disk covers an arc of the core circle of half-width
<= asin(r/a) < pi/2 (the max over s is at s = sqrt(a^2-r^2)). Two arcs covering the
circle need b_1+b_2 >= pi, hence some b_j >= pi/2, hence r >= a, i.e. r >= 1/3.
Consistent with the file's degenerate caveat.

## (C6) Calibration against the certified 9+2 object
`n11/upper/certified_object.json` hubs: s = (.149428, .272977), delta ~ pi,
b_1+b_2 = 4.351246 >= 2pi-delta = 3.141593, direct core-circle check passes,
min s = .149428 <= .294618.
**Load-bearing observation:** min s = .149428 > r-a = .14, so this object lies
strictly OUTSIDE the C450 |h| <= .14 domain while inside the new domain of radius
.294618. The domain extension is therefore not vacuous: a dual certificate on the
new domain cannot be a reuse of the C450 one.

## Exact hub domain (2D + angle), ready for a dual certificate
Everything above is exact; collected in the coordinates the dual work needs:
rotation sets h_1 = (s_1,0), so a hub pair is (s_1, s_2, delta) in
[0,1-r)^2 x [0,pi]. The core-covering constraint is **exactly**

  (D2) min(s_1,s_2) <= r - a                                  (Branch A), or
  (D3) s_j in [r-a, r+a] for both j  AND  delta >= 2pi - b_1(s_1) - b_2(s_2),
       with b_j(s) = acos((a^2+s^2-r^2)/(2 a s))               (Branch B).

The position-only consequence, free of delta, is the product condition

  (D1) s_1 s_2 <= r^2 - a^2,

and (D3) implies (D1) because delta <= pi forces b_1+b_2 >= pi. Shape of b_j on its
admissible window (r > 1/3): b_j(s) = acos((a^2+s^2-r^2)/(2as)) is **strictly
decreasing** in s because d/ds of the arccos argument equals (s^2+r^2-a^2)/(2as^2) > 0
for r > a; it runs from b_j(r-a+)=pi down to b_j(r+a-)=0, hitting pi/2 exactly at
s_j = sqrt(r^2-a^2). (Checked numerically at r=.38: 3.141442, 1.570796, 0.000071.)
For r < 1/3 (a > r) the window changes: the arccos argument is minimised at
s = sqrt(a^2-r^2) and b_max = asin(r/a) < pi/2, which is exactly why two radius-r
disks cannot cover the core when r < 1/3.

**Checked that (D1) alone is NOT sufficient**: s_1 = s_2 = sqrt(r^2-a^2) with delta = 0
satisfies (D1) (product = r^2-a^2 exactly, b_1 = b_2 = pi/2) yet the two coincident
hubs leave half the core circle uncovered; the same s with delta = 2.0 also fails,
while delta = pi works. So a certificate on this domain must carry the full angle
condition (D3), not just the position bound.
**(Corrected interval statement:** on the feasible region of (D3) one has
b_1+b_2 >= pi (forced by delta <= pi), hence the required separation 2pi-b_1-b_2 lies
in **[0, pi]**, below the cap delta <= pi; an earlier version of this file and my
message claimed [pi, 2pi), which was wrong.** The sampling in
`tools/audit_hub_domain2.py` is calibration of the criterion, not its proof.)

## (C7) Core circle covered by the two hubs <=> core disk covered (proof)
The criterion above is an iff for the core *circle*; upgrading it to the core *disk*
is done by the following lemma, stated in the general form (any closed convex bounded
body, any two closed convex sets). Independently derived by the Lead
(`lead/CORE-TWO-HUB-DOMAIN.md` follow-up); no sampling is used.

**Lemma (two-convex-boundary).** Let K be a closed convex bounded subset of R^2 and
let C_1, C_2 be closed convex sets with bd K subset C_1 union C_2. Then K subset C_1
union C_2. In particular, if two closed convex sets cover the circle bd B(0,a), they
cover the disk B(0,a).
*Proof.* Suppose x in K lies outside both. For i = 1,2 (C_i nonempty, x not in C_i)
let p_i be the point of C_i nearest to x and u_i = (p_i-x)/|p_i-x|. Strong separation
at positive distance: (y-x).u_i >= |p_i-x| > 0 for every y in C_i (for y in C_i and
t in [0,1], |x-(1-t)p_i-ty|^2 >= |x-p_i|^2; expand, divide by t and let t -> 0+).
Choose a nonzero v with v.u_1 <= 0 and v.u_2 <= 0: two closed half-planes through the
origin always share a nonzero vector (if u_1, u_2 are not antiparallel take v
perpendicular to u_1 on the side where v.u_2 <= 0; if u_2 = -u_1 take v perpendicular
to u_1). For every t > 0 the point x+tv lies outside C_i for both i: otherwise
y = x+tv in C_i gives t (v.u_i) = (y-x).u_i >= |p_i-x| > 0, contradicting v.u_i <= 0.
Since x lies in K, v is nonzero and K is bounded, the ray leaves K at a first time
t* > 0, and x+t*v is in bd K yet outside C_1 union C_2 — contradicting the
hypothesis. ∎
Consequence: covering bd B(0,a) by the two hub disks already forces covering the core
disk, so (C3)+(C5)+(D1) describe the core obligation exactly (necessary *and*
sufficient). Scope guard: the lemma is specific to *two* convex sets; three disks can
cover a circle and still leave a hole inside, so it must not be quoted for 3 or more
sets. Verified numerical scope control (a=0.24, r=0.38, three disks of radius r at
|c| = 0.42 spaced 120 degrees): max over the circle of the nearest-centre distance is
0.3650 <= r (circle covered) while the origin is at distance 0.42 > r from all three
centres (disk not covered).

## Not established here
Sufficiency for the full hole (the file does not claim it either); any improvement of
sqrt(r^2-a^2) from the core constraint alone (impossible, see C4); any certificate on
the 3D domain (s_2, delta) x rotation — still open.

Evidence / repro: `tools/audit_core_hub.py` (all checks PASS; random-seed 20260924).
