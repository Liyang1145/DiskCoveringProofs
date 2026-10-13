# Independent review of `team-current/lead/VORONOI-BOUNDARY-REDUCTION.md`

Reviewer: flash-structure (own tools only; no import of the lead's scripts).
Object reviewed: `research-2026/team-current/lead/VORONOI-BOUNDARY-REDUCTION.md` (33 lines, unregistered).
Scope of review: **analytic** (§1–§3 line by line) + numerical calibration on the record configuration
and on 42,000 random legal ledgers (own scripts, `tools/`, evidence `out/`).

## Verdict

**ACCEPT** the three sections and the stated payoff, with

* **two wording repairs** (R1a, R1b) that do not change the conclusions,
* **one load-bearing gap repaired** (R2: the degree-3 property of the nine boundary vertices),
* **one new lemma** proved here (N1) that strengthens §2's interface to the two-hub step,
* **one external lemma checked** (lead's NO-FOUR-RING-COMMON-POINT, verified independently below).

The scope caveats of the note (inner-root representative; all eleven centres distinct and in int D;
existential character of the reduction) are correct as stated and must be kept.

---

## §1 Each boundary disk owns exactly one connected nearest-centre boundary arc — ACCEPT (with R1)

Independently re-derived:

1. *No hub is nearest on ∂D*: for `u ∈ ∂D`, `|u-h| >= 1-|h| > r`, while some ring disk covers `u`
   with distance `<= r`. Correct (uses the strict interiority `|h|+r<1`).
2. *Privateness*: a point outside `I_i` has `|u-c_i| > r` and some covering centre at distance `<= r`,
   hence `c_i` is not nearest. Correct. Inside the private part of `I_i` only disk `i` covers.
3. *Overlap*: in `I_i ∩ I_{i+1}` only `c_i, c_{i+1}` can be nearest (multiplicity ≤ 2 of the arc ledger).
   The comparison is `f(u) = |u-c_i|^2-|u-c_{i+1}|^2 = 2u·(c_{i+1}-c_i) + (|c_i|^2-|c_{i+1}|^2)`,
   an affine function of `u` restricted to the circle; `c_i ≠ c_{i+1}` makes it non-constant.
4. **R1a (wording, conclusion unchanged).** The note justifies the strict endpoint signs with
   "each disk's actual arc has length less than π and the endpoints in this cyclic overlap are
   distinct". The real reason is: for a **positive-length** overlap `o_i>0` the endpoint
   `u(φ_{i+1}-t_{i+1})` of arc `i+1` lies in the **interior** of arc `i` (and symmetrically), hence
   `|u-c_i| < r = |u-c_{i+1}|` there, and likewise at the other end. Arc length plays no role.
5. **R1b (argument completed).** "an odd number of transverse intersections" needs the companion
   statement: `f` has **at most two** zeros on the whole circle (line ∩ circle). If both zeros lay in
   the overlap arc then `f` would have the *same* sign at its two endpoints, contradicting (4);
   hence exactly one zero. Tangency cannot occur (a tangent zero does not change sign). Correct as
   intended once R1b is added.
6. *Zero-length overlap*: the common endpoint of the two arcs is the unique tie (both distances `= r`;
   no third disk covers it by multiplicity ≤ 2). Correct.
7. *Nine distinct switches*: needs that the nine overlaps are pairwise disjoint — true because a common
   point of `O_i` and `O_j` would be a triple overlap. Should be said; the nine switch points are then
   distinct.
8. *Positivity of the nearest-arc length*: follows from the arc-ledger necessity (`ℓ_i = 2t_i-o_{i-1}-o_i > 0`),
   not from §1's argument. Dependency worth writing down.

⇒ exactly nine nearest-centre boundary switches, one connected closed nearest-arc per boundary disk.

## §2 Both complete hub Voronoi cells are bounded inside D — ACCEPT

Every step re-derived and correct:
`V_h` convex and `h ∈ V_h`; no `u ∈ ∂D` satisfies `|u-h| <= |u-c|` for all `c` (witness: a ring disk
covering `u`); convexity forbids points outside `int D` (segment to `h` crosses `∂D` inside `V_h`);
closed+bounded ⇒ compact; and `V_h ⊆ B(h,r)` because a covering disk at `x ∈ V_h ∩ D` whose centre is
not `h` already gives `|x-h| <= |x-c| <= r`. Correct, and the remark that this is about the **full**
(höchstens D-clipped) hub cell and not about "original ring adjacency ⇒ active Voronoi adjacency" is
important and correct.

## §3 Combinatorial count — ACCEPT **after R2**

* Euler for the disk subdivision: `V = v+9`, `E = e+9`, `F = 11` ⇒ `(v+9)-(e+9)+11 = 1` ⇒ `e = v+10`. ✔
  (verified separately on two toy subdivisions; `F = 11` needs all eleven centres in `int D`, i.e. the
  inner-root representative — the note states exactly that.)
* All eleven cells have nonempty interiors: after inward-root replacement every centre is in `int D`
  (`|c| <= sqrt(1-r^2) < 1`), all distinctness arguments are correct.
* Degree counting `2(e+9) >= 3v + 27` with `e = v+10` gives `v <= 11`, `e <= 21`. ✔
* High-order coincidences decrease the counts (a `k`-fold cocircular vertex replaces `k-1` trivalent
  vertices joined by zero-length edges): correct, zero-length edges are not counted.

**R2 (load-bearing).** The count uses that each of the nine boundary vertices has **degree exactly 3**
(two `∂D` edges + one interior Voronoi edge entering D). The note asserts this but does not prove it;
a degree-2 boundary vertex would only give `2(e+9) >= 3v+18`, i.e. the weaker `v <= 20`, `e <= 30`.
Proof supplied here (two lines):

* *Strictness at the switch point* (**corrected after lead review, item 1**). At the switch `t_i` the
  two adjacent centres are equidistant with common value `ρ_i <= r`; here `ρ_i = r` **iff** `o_i = 0`
  (touching arcs), while for `o_i > 0` the tie point lies in the interiors of both actual arcs and
  `ρ_i < r`. Every other centre is at distance `> r` strictly: a third boundary disk would be a triple
  overlap on `∂D` (excluded), and a hub satisfies `|u-h| >= 1-|h| > r`. So the two adjacent centres are
  *strictly* nearer than all others, and for `x` on the bisector line close to `t_i` they are still the
  two nearest centres (the strict margin persists by continuity). R2 never uses the equality case
  `ρ_i = r`, so the `<` version suffices.
* *The bisector meets int D.*
  `dist(0, bisector(c_i,c_{i+1})) = |(|c_{i+1}|^2-|c_i|^2)| / (2|c_{i+1}-c_i|) <= (|c_i|+|c_{i+1}|)/2
  <= sqrt(1-r^2) < 1` (reverse triangle inequality; inward-root representative). So the line has a
  direction entering `int D` at `t_i`, and therefore the Voronoi edge `(i|i+1)` really does enter `D`
  there. (Verified numerically on the record ring: max distance `= 0.232520 <= sqrt(1-r^2) = 0.924993`,
  `out/run5_analytic_checks.txt`.)

Consequently the boundary vertices are trivalent and the claimed `v <= 11, e <= 21` stand.

## New lemma N1 (proved here) — every hole point is nearest to a hub

**N1.** Let `H = D \ ∪_{i∈ring} B(c_i,r)`. Then for every ring index `i`, `H ∩ V_i = ∅`. Hence
`H ⊆ V_1 ∪ V_2` and (both `V_j` closed) `cl(H) ⊆ V_1 ∪ V_2`.

*Proof.* If `x ∈ H ∩ V_i` then `|x-c_i| <= |x-c|` for every centre `c`. As `x ∈ D`, some disk covers
`x`: `|x-c| <= r` for one `c` (necessarily `c ≠ c_i` would not matter). Hence `|x-c_i| <= r`, i.e.
`x ∈ B(c_i,r)`, contradicting `x ∈ H`. ∎

*Consequences (this is the interface the two-hub step needs).*
(i) The covering of `cl(H)` by the two hubs is **Voronoi-canonical**: every point of `cl(H)` lies in
the cell of `h_1` or `h_2`, and `V_j ⊆ B(h_j,r)` (§2), so the "separating line" of the two-hub
criterion is exactly the **hub bisector** `L`.
(ii) The tips of the hole, if they lie in `cl(H)`, are split by `L` into two classes that are
*hub cells* (not mere covering sets) — this is what makes the line-separable bisection class of the
two-hub criterion valid (see `NEXT-OBLIGATION-JOINT-REDUCTION.md`).
(iii) Numerically confirmed on the record configuration: 0 of 124,919 hole samples have a ring centre
as nearest (`out/run1_fammin_structure.txt`).

## Check of the lead's `NO-FOUR-RING-COMMON-POINT` (external, same round)

**Statement checked.** For `0<r<=19/50`, no four boundary disks have a common point.

*Proof (re-derived, with the `p ∉ D` case made explicit).* Let `p ∈ ∩_{i∈I} B(c_i,r)`, `|I| = 4`. Then
every point `u` of the arc `I_i` satisfies `|u-p| <= |u-c_i| + |c_i-p| <= 2r`, so `∪_{i∈I} I_i ⊆
∂D ∩ B(p,2r)`, an arc of half-width `h(a) = arccos((1+a^2-4r^2)/(2a))` at `a = |p|`. The maximum of
`h` over `a >= 0` is `asin(2r)` (at `a = sqrt(1-4r^2)`; `a > 1` is included and gives a smaller value),
so the four arcs have total length `<= 2 asin(2r)`, while the remaining five arcs have total length
`<= 10 asin(r)`. Covering `∂D` needs `2π <= 2 asin(2r) + 10 asin(r)`, i.e. `π <= asin(2r) + 5 asin(r)`.
The **right-hand side** `asin(2r) + 5 asin(r)` is strictly increasing in `r` (derivative
`2/sqrt(1-4r^2) + 5/sqrt(1-r^2) > 0`), so the worst case is the largest radius and it suffices to test
`r = 19/50` (**corrected after lead review, item 1**: it is `π − rhs` that decreases, not increases):
`asin(38/50) + 5 asin(19/50) = 2.8122945974 < π` (exact certificate: a rational upper
bound `2.82506254 < 3.14159265` is obtained from the Taylor series with geometric tail bound,
`out/run5_analytic_checks.txt`). Contradiction. ∎

*Scope and interface to the cellulation.* At an interior Voronoi vertex `x` of the cellulation of `D`
the cells meeting there are the centres nearest to `x`; `x ∈ D` is covered, say `|x-c| <= r`, so every
nearest centre satisfies `|x-c_k| <= r`: **all** disks whose cells meet at `x` share the point `x`.
Hence no interior vertex carries 4 or more **ring** cells; interior degrees lie in `[3,5]`
(at most 3 ring + 2 hubs). The bound `v <= 11, e <= 21` is unchanged — the lemma removes a degeneracy
class, it does not sharpen the count. It also shows that any interior vertex of degree `>= 4` must
involve at least one hub.

## Numerical calibration on the record configuration (`out/run1_fammin_structure.txt`)

* ledger reconstruction from `fammin_config.json`: exact; `o_i ≈ 1e-14` (touching), `Σt-π = +8.9e-16`,
  cover / only-adjacent / `ℓ_i>0` all pass; arc half-widths match the documented list.
* tips: closed form `|v|² = 2ρ_kρ_{k+1}cos γ_k + 2r² - 1` matches the numeric crossing to 9 digits;
  `|v_out| = 1` for all nine (`o = 0`), `|v_in| ∈ [0.396025, 0.622917]`;
  tips-lemma margin `min_{j∉{k,k+1}} |v_k-c_j| - r` has worst value `+0.2443`;
  all nine tips admit a radial-ray witness in `cl(H)`.
* Delaunay of the 11 centres: **21** edges `= 9` consecutive ring-ring `+ 1` hub-hub `+ 11` hub-ring;
  **0** non-consecutive ring-ring chords. (`21 = v+10` with `v = 11`: the record configuration
  saturates the Euler bound of §3.)
* hub cells (grid): `max|p-h| = 0.379629` and `0.379512 <= r = 0.379984` (close to §2's bound), and
  `max|p| = 0.6217 < 1` (inside D).
* hole: single component on a `1400²` grid; `cl(H) ⊆ conv(tips)` with the 9 tips as hull vertices;
  all 11 disks cover `D` (0 uncovered samples).

## Residual scope guards (not errors, but must not be dropped)

1. §3 is a statement about the **inner-root representative**; the count is not claimed for every
   representative (the reduction C464 is existential).
2. §1's "positive length" and N1's closure step use the arc-ledger necessity and multiplicity ≤ 2
   (both available unconditionally in the `r <= 0.38` branch).
3. The note's own payoff list is accurate: it does **not** give hub adjacency, ring-ring chord
   exclusion, trivalence, or any lower bound; `r_D(11) = R_stru` remains open.
