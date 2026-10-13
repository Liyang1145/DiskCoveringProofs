# r20-chain SCOPED REPORT — correction of the false L1–L4 entries, exact identities, and the outer-root geometry

Author: cline2-r20-chain (worker). Date: this session. Scope of everything below:
**q0(6,7) two-hub class** — unit closed disk `D`, `n = 11` congruent disks of radius `r = R`,
9 essential ring centres `c_i` with `1 - R <= |c_i| <= 1`, two hubs strictly inside `H = B(0,1-R)`;
the 9 ring edges (= consecutive pairs of the cyclic polar order) are served by the two hubs, so the
served sets are contiguous chains of sizes `k` and `9-k` (the chain sizes that arise are 4 and 5).
**No symmetry, no equal-angle, no saturation premise is used anywhere below.**

---

## 0. What was wrong (lead's objection, accepted in full)

| entry | verdict | why |
|---|---|---|
| **L1** "arc is covered by the hub disk iff the circle's pole w.r.t. the *origin* is covered" | **FALSE** | the critical points of `x -> |x-H|` on a circle are the arc endpoints and the phases of `H-C`. The origin-pole is the critical point of `|x|`, which is irrelevant unless `H=0`. Lead's counterexample is decisive: `R=1, C=(2,0), H=(1,0)` — the pole `(1,0)` is covered by `B(H,1)` but `(2,1)` on the same circle is at distance `sqrt2 > 1`. |
| **L1'** "(a-R)(b-R) = 1-R^2" | **FALSE / malformed** | verified only as a meaningless coincidence at one radius; discarded. |
| **L2** "the exposed rim endpoints of the two circles coincide" | **UNPROVEN** | I only ever sampled, never proved. Discarded as a stated fact. |
| **L3** "Helly gives `theta >= s_i + s_{i+1} - pi/2`" | **NOT PROVEN** | 3 disks with pairwise intersections do not give a triple intersection; I never produced the triple-disks argument. Discarded. |
| **L4** "summing L3 telescopes to `m*pi/2 + (s_k - s_l)`" | **FALSE as stated** | an artefact of the invalid L3 manipulation. The correct exact decomposition (F3 below) has a different form. |
| earlier `s_H(c) = arccos(|H-c|/(2R))` named the "spoke deficit" and used as a width bound | **WRONG SIDE** | `s_H(c)` is a MAX-type containment threshold; the chain imposes MIN-type width conditions. Mixing the two produced the `+18.6` slack in `out/final_bounded_experiment.txt` — that file certifies nothing. |

All of the above are now recorded as invalid; none of the numeric files that used them
(`corner_capacity.txt`, `cluster_criterion.txt`, `decisive_experiment.txt`,
`final_bounded_experiment.*`) may be cited.

---

## 1. Verified exact identities (the replacements)

### (F1) Single-arc identity — exact, verified
For `x(s) = C + R (cos s, sin s)` on the circle `Cc(C,R)`:
```
|x(s) - H|^2 = R^2 + |C-H|^2 + 2R (C-H)·n(s)          (affine in n(s))
=>  max_{s in arc} |x(s)-H| is attained at an endpoint of the arc
    or at a phase s = arg(H-C) + 2 pi k lying in the arc.
```
Consequently **arc ⊆ B(H,R) ⟺ max over {endpoints} ∪ {phases of H−C inside the arc} ≤ R**, which
is *necessary and sufficient* and finite. (Implementation `tools/arcs.py:maxdist_arc_exact`;
cross-checked against 8001-point sampling with no violation in 4000 random hub/arc pairs — the
earlier "violations" were my harness mishandling arcs of length > pi.)

### (F2) Single-triangle / circumradius identity — exact, verified
For a triangle with circumcentre `O`, circumradius `rho`, and `x = Σ λ_k v_k` in the triangle:
```
Σ_k λ_k |x - v_k|^2 = rho^2 - |x - O|^2 <= rho^2
=> min_k |x - v_k| <= rho.
```
Hence `rho <= R` ⟹ the triangle is covered by the three vertex disks; `rho > R` ⟹ the
circumcentre `O` is uncovered. **This is exactly the necessary-and-sufficient 3-disk (triangle)
unit** and replaces all earlier "circumradius criterion" hand-waving. (0 violations / 3000 random
triangles; `tools/identities2.py`.)

### (F3) Two-root factorisation — exact, verified
For ring sites `c_i, c_j` with `d = |c_i-c_j| = 2a`, midpoint `m`, unit normal `n`, `k = sqrt(R^2-a^2)`:
```
p_+ := m + k n ,  p_- := m - k n      (the two centres of radius-R circles through c_i, c_j)
rho(c_i,c_j,h) <= R  <=>  exactly one of  |h-p_+| <= R , |h-p_-| <= R,   for h OFF the radical line.
```
Verified: **0 mismatches in 30000 off-line cases** (`tools/outer_corrected.py`), and 0/20000 in
`tools/two_root.py`. On the line both or neither inequality holds and `rho > R` strictly.
This is the lead's (F3) and it is correct and usable. The hub is never on the line.

**Reading:** choose `p_in` on the hub's side; the chain constraint is
`|h - p_in| <= R` *and* `|h - p_out| >= R` for every chain edge. The inner inequalities alone are
a convex disk intersection; the outer ones are complements of disks.

### (F4) C879 variance identity — exact, verified
If `p_1..p_m` are all at distance `R` from `h*` and `h* = Σ λ_j p_j` with `λ_j >= 0, Σλ_j = 1`:
```
Σ_j λ_j |h - p_j|^2 = R^2 + |h - h*|^2      for every h.
```
So if in addition `h* ∈ conv{p_j}`, then a point `h` with all `|h - p_j| <= R` must satisfy
`h = h*`: the pin-disk intersection is a **single point** and the hub is rigid (the three-point MEC
case). When `h* ∉ conv{p_j}` this conclusion fails and the domain keeps its free lens.

**Calibration at the certified candidate** (`tools/c879_identity.py`):
* 4-edge chain (hub A, edges (4,9),(9,10),(10,3)): exactly **one** active pin (the (9,10) pin);
  the other two pins have margin `2.839e-3`.
* 5-edge chain (hub B): **three** active pins, each at distance `R = 0.379983853120` from `H_B`;
  their circumradius equals `R` (the pins and the hub are concyclic).
* **`H_B` is NOT in the triangle of the three active pins**: barycentric coordinates
  `[1.1195, -1.0226, 0.9031]` (one negative), and the LP for `H = Σλ p` with `λ >= 0` is
  infeasible. So the strong (`h = h*`) case does **not** occur; the pin-disk domains keep a
  genuine lens, exactly as the lead's calibration found.

### (F5) Outer-root geometry — corrected after AUDIT A/B (see `AUDIT-A-B.md`)
The hypothesis "`|p_out| >= 1` automatically, so the outer constraint is redundant and the chain
domain is a convex disk intersection" is **not automatic for an arbitrary legal-looking annulus
pair**: I exhibit a pair with `|c_i|,|c_j| >= 1-R`, `d <= 2R` and `|m+kn| = |m-kn| < 1`
(`0.4298`, `0.6108`; see `out/outer_corrected.txt`).

**However (correction of my own claim):** that pair **violates the interface hypothesis** of
`lead/R20-CHAIN-HUB-CONVEXIFICATION.md`. Computed on the pair:
* the covered unit-circle arc of `B(c_i,R)` has angular span `0.207562`, of `B(c_j,R)` `0.347863`,
  and their **intersection is empty** — so there is no common covered equal-distance point `U`;
* the radical-line unit-circle point `U = m + t₊ n` is at distance `1.5641` from both centres
  (> R), i.e. it is covered by neither disk;
* consequently the Lemma-1 inequality fails: `t₊ = 1.51996 > k = 0.09055` and
  `A² + t₊² = 2.44647 > R² = 0.14439`.
Hence the pair is **outside the domain** of the convexification, and my "the chain hub domain is
not convex" sentence must be **withdrawn as a statement about that domain**. What survives is the
weaker, correctly scoped statement: *the interface hypothesis is not automatic for arbitrary
annulus pairs, and when it fails `|p_out| < 1` is possible.*

On the **realised** chain of the certified object the interface hypothesis does hold and the
convexification's conclusion is confirmed by direct measurement: for each of the 9 chain edges the
inner pin satisfies `|H - p_in| = R` exactly (so `rho(c_i,c_j,H) = R`), while the outer roots give
`|H - p_out| >= 0.543 >> R`. So the lead's convexification is not affected by my counterexample.

### (F5') EXACT closed form for the two roots (verified, 0 mismatches in 13084 cases)
With `m`, `n`, `k`, `a = d/2` as in F3 and `p_± = m ± k n`:
```
|p_±|^2 = |m|^2 + k^2 ± 2 k (m·n)                                    (exact, elementary)
```
(the cross term is `2 (k n)·m`). Hence the outer root is the one with the **larger** magnitude,
`sign(m·n)` selecting it:
```
|p_out|^2 = |m|^2 + k^2 + 2 k |m·n| ,        |p_in|^2 = |m|^2 + k^2 - 2 k |m·n| .
```
Consequences:
* `p_in` and `p_out` are the two points of the perpendicular bisector of `c_i c_j` at distance `k`
  from `m` (this is what `m ± k n` means);
* `|m|^2 + k^2 = |m|^2 + R^2 - d^2/4 = L^2 + R^2 - d^2/2` for `L = |m|`;
* **the outer constraint is redundant for the pair iff** `|p_out| >= 1`, i.e. iff
  `|m|^2 + k^2 + 2k|m·n| >= 1` — a single checkable inequality on the four numbers
  `(|m|, d, k, the angle between m and n)`.
* (Correction of two earlier hand slips, both of which I verified numerically before recording:
  the sign of the cross term is PLUS for `|p_out|^2`, and the witness values below are consistent
  with that: `0.520299795^2 + 0.090551906^2 + 2(0.090551906)(0.520077613) = 0.373099563 =
  |p_out|^2`, so `|p_out| = 0.610818764`.)

**What is true at the optimum** (observation, not a theorem): for all eight adjacent pairs of the
*certified configuration*, `|p_out| = 1.000000000000` to machine precision, i.e. the identity
`|m|^2 + k^2 + 2k|m·n| = 1` holds exactly, while `|p_in| = 0.3960 ... 0.6229 < 1`. At this
configuration the exposed rim arcs' extreme points lie exactly on `∂B(H,R)`, so the pin disk's
boundary is attained: the optimum sits on the *boundary* of the outer constraint, and the
"`|p_out| = 1`" property is a codimension-one condition of the optimum, not a domain-wide identity.
(The natural guess `|m|^2 + R^2 = 1` is FALSE here: at the candidate `|m|^2 + R^2 - 1` ranges from
`-0.197` to `-0.371`.) The empirically clean description of the optimum is
```
|m| + k - 1 = 1.2e-3 ... 1.0e-2      (small but NOT zero; m and n are nearly antiparallel)
|m . n| + |m| = 4.8e-3 ... 3.8e-2    (same small quantity)
```
so at the optimum the outer root sits essentially on the ray from the origin through `m`
(`|p_out| = |m| + k` in the antiparallel limit), and `|p_out| = 1` is the residual equality after
the small tangential offset `delta = (1 - |m|^2 - k^2)/(2k)` is included:
`|p_out|^2 = |m|^2 + k^2 + 2k(|m| + delta) = 1`. Both forms are recorded; neither is yet a theorem.

**No counterexample was found** to this weaker, still-useful statement — recorded as an open
target, not as a claim:
> (T?) For every *legally realizable* chain (one that can actually be served by a single hub whose
> other obligations are met), `min_h |h - p_out| >= R`.

---

## 2. What survives and what is needed

**Survives (proved/verified):** F1, F2, F3, F4; the exposure of the L1–L4 errors; the exact
uncovered-rim-arc machinery (`tools/arcs.py`, cross-checked against 1.6M-point sampling to 1e-9 —
recovering the identity "the exposed rim arc of ring `i` has angular extent `2 s_i`" where
`s_i = arccos(|H-c_i|/(2R))` is the spoke deficit of `H` to `c_i`, exactly the `s` values of the
certified object); the `|p_out| = 1` calibration of the optimum.

**Route gap (honest statement).** The chain cannot be eliminated by a convex disk intersection on
the stated domain, because the outer-root constraint is not redundant. Two ways forward, both
scoped:
1. **Use the pair constraint directly** (no pole surrogate): for each chain edge keep
   `rho(c_k, c_{k+1}, h) <= R`; by F3 this is the two-sided condition
   `|h - p_k| <= R` AND `|h - q_k| >= R`. The chain domain is then a disk intersection minus a
   union of disks, and the global object is the intersection over the 4 or 5 edges **plus** the
   central two-hub/two-face coupling. The free cancellation of the outer constraints is *false*;
   the deficit it created in the earlier accounting was exactly the `0.1630`-scale slack seen at
   the candidate's `(5,7)`/`(8,6)` edges.
2. **Find the extra hypothesis that kills the counterexample family.** The counterexamples found
   all have `max(|c_i|,|c_j|)` near `1-R` (rings that barely reach `∂D`) *and* `d` near `2R`
   (tangent-ish ring disks). If a legal configuration forces at least one of the two rings of every
   chain edge to be far from `∂D` — e.g. because the *other* eight rings must cover `∂D` while the
   chain's rim arcs must stay exposed — then the degenerate family is excluded and (T?) becomes
   provable. This is a concrete, finite check on the ring parameters: maximize `|p_out|` over
   `{|c_i|,|c_j| >= 1-R, d <= 2R, both rings essential}` **plus** a quantified non-redundancy
   condition for the remaining seven rings.

---

## 3. Repro

```
cd research-2026/team-current/r20-chain/tools
py -3 identities2.py       # F1, F2 and the corrected arc/phase identity
py -3 two_root.py          # F3 factorisation (0/20000 mismatches)
py -3 outer_corrected.py   # F3 off-line verification + the counterexample pair
py -3 outer_decisive.py    # minimization showing the outer constraint is violated
py -3 c879_identity.py     # F4 variance identity + active pins of the candidate
py -3 arcs.py              # exact uncovered rim arcs (used by the above)
```
Outputs in `../out/`: `identities2.txt`, `two_root.txt`, `outer_corrected.txt`,
`outer_decisive.txt`, `c879_identity.txt`, `pout_exact.txt`, `pout_formula.txt`.

## 4. Open obligations (for the lead, not for me to self-certify)

* **O1** Decide between (1) and (2) of §2. My recommendation: (2), because the optimum's
  `|p_out| = 1` across all eight edges is strong evidence that the degenerate family is *not
  realizable*; proving that requires the non-redundancy of the remaining seven rings.
* **O2** Independent algebraic audit of F3's "off-line only" clause and of the counterexample pair
  (I verified numerically, not by hand; the lead should re-derive `p_out` for the witness).
* **O3** The `|p_out| = 1` property of the optimum should be tested against the *other* known
  critical configurations (the `C89` branch at `R = 0.385322908655`) — if it holds there too, it is
  a genuine optimality signature; if not, it is a coincidence of the record configuration.
