# INVALID — REJECTED BY LEAD 2026-09-24. DO NOT CITE.

**This document is retracted in full** (see INVALID.md for the itemised errors). It is kept
only as an audit record. Every statement in sections 2–4 is false; the root cause was using
the wrong ring-centre norm (I wrote \|c| = r\; the inward-root formula is
\|c| = sqrt(1-r^2)\), plus conflating the switch corner angle with the sector/arc measures.
Nothing below may be used, and the obligation (EX) must **not** be encoded anywhere.

---

# Sector height / degeneracy: analytic findings and the exact obstruction

Scope: 11-equal-disk cover of the unit disk D at radius `r ∈ [3/8, U]`, `U = 37999/100000`,
component `C840` (no 10-disk cover at `s = 19/50`), inward-root representative. **No
symmetry, no saturation, no positive-metric assumption.** Everything numeric is labelled;
the two things that are *proved* are flagged (P).

---

## 0. Answer to the question asked

* A **uniform positive lower bound on the sector height does not follow from the local
  sector data**, and there is no local inequality of the given shape that can yield one.
  The exact reason is an identity, not a gap in the estimates: the angle bound and the
  height are *not independent* — they degenerate together (1).
* The α→π limit is **not a family**: it is a single configuration up to the scale of the
  allowance (2). This is what makes the global interface attackable.
* The residual global obligation has an exact form: **one point** (the origin) is covered by
  exactly one disk, and the remaining ten disks of the same radius must cover `D` minus that
  point (3). No local bound on the other eight arcs can replace this, and the two hubs alone
  provably cannot either (4) — the second hub's angular placement relative to the *far-side*
  arcs is unavoidable input.

## 1. Why no local bound exists (exact, elementary)

Write the sector data as the lead's `P = (k,h)`, `Q = (k,-h)`, `c = (x,y)`, `H = k-x`,
`u = |c-P|`, `v = |c-Q|` and `α` the wedge angle at `P`. Two identities hold exactly:

**(1a) Height ↔ angle are the same datum.**
```
cot α = k/h - (1-|c|^2)/(2 h H)
```
so `α → π` forces `H → 0`, i.e. the height vanishes, and conversely `H → 0` gives `α → π`.
Consequently every bound of the form `α >= 2 atan(h/(k+sqrt(1-R^2)))` (lead) or
`α >= 2w >= g/2` (arc budget) is **vacuous in the limit**: the lower bound on `α` degrades
exactly as fast as `h → 0`.

**(1b) The arc budget has slack, not pinch.** With `w_i = arcsin(r/|c_i|) <= asin r`:
```
sum_i 2 w_i = 2 pi   and   w_i <= asin r
=>  slack  sum_i (asin r - w_i) = 9 asin r - pi
```
At `r = 0.38`, `9 asin r - pi = 0.3664` — of the same order as `pi` itself. The budget does
**not** pin the widths near their maximal value `asin r`; the sectors are free to shrink
their widths independently, which is exactly the direction that lowers every height.

**(1c) Consequence.** Any attempt to bound `sum_i h_i` or `min_i h_i` from below using only
(switch angles, arc widths, single-sector geometry) is defeated by the family member that
lets one sector saturate and absorbs the freed angular budget in the others. This is the
precise sense of "uniform height requires graph-global input".

## 2. The degenerate limit is one configuration, not a family

**(P) Necessity.** Suppose ring disk 0 owns the sector opposite it and is *doubly critical*
at its switch: its centre `c_0` satisfies `|c_0 - P| = |c_0 - Q| = r` for the two switch
points `P,Q ∈ bd D`. If additionally the covered arc is maximal, `w_0 = asin r`, then
`|c_0| = r` and, because `|c_0| ≥ 1-r` (ring), `r ≥ 1/2` is required — for `r < 1/2` the
saturated case is excluded. Hence within the feasible allowance the only degenerate
configuration is:

> `c_0` at distance exactly `r` from the origin (so the origin lies on `∂B(c_0,r)`, and
> `B(c_0,r)` is the **unique** disk covering the origin once `r > 1/3`, since all other
> centres have norm `> r`), and `c_0` owns the half-cone of directions pointing away from it.

**Normalisation (lead's interface).** Expressing lengths in fixed units `R0 = 38/100` and
keeping the *actual* allowance, the degenerate corner has `α → π` with `u = v = t := r/R0`
and `t ∈ [75/76, 1]`. Restricting to this 1D segment is legitimate for exclusion purposes;
since `α = π` forces `|c-P| = |c-Q| = r`, the two incident disks are **equal** (`u = v`), so
the second endpoint direction is not an extra degree of freedom: the wedge is isosceles.
That is the structural reason the fixed-`R0` dual bounds can be re-used without re-rooting.

## 3. The exact obstruction (global, one point)

At the degenerate corner the ten other disks have radius `r` and their centres satisfy
`|c_j| > r` (all but the pinned one miss the origin). Therefore:

> **(EX) the ten remaining radius-`r` disks must cover `D \ {origin}`.**

This is not a local statement about sector 0: the covering near the origin is decided by the
*hub* pair (the only sites that can sit close enough to the origin) together with the far
side of the boundary, i.e. by the global configuration. Two consequences:

* **(P) The corner is impossible at `r = s = 19/50`.** If the pinned configuration were
  feasible at radius `s` — ten radius-`s` disks covering `D \ {origin}`, with the pinned disk
  at distance exactly `s` from the origin so that it covers the origin — then re-adding the
  pinned disk gives an 11-disk cover of `D` at `s` whose **deletion** of that one disk gives a
  **10-disk cover of `D` at `s`**, contradicting `C840`. So the degenerate corner has no
  realisation at the top of the allowance. This closes exactly one radius value rigorously.
* **(N) The corner appears to miss the whole allowance — numerically only.**
  With the full critical set (all triple circumcentres in `D` plus all `C(11,2)` bisector
  points on `bd D`) and the pinned family `|c_0| = r`, bounded Nelder–Mead + Powell runs still
  report a positive violation at `r = 0.37999` and at `r = 0.40`, turning negative by
  `r = 0.42`. The bisection run exceeded the shell budget, so **no `r*` is claimed**; this is
  calibration only and must not be cited as a bound. Together with (P) it says the
  non-uniformity is confined to a thin range near the top of the allowance, consistent with
  attacking the corner on the lead's `t ∈ [75/76,1]` segment.

## 4. What the hubs alone can and cannot give (exact necessary condition)

Let `V_ε = B(0,ε)` with `ε ≤ r/3` (so that only the pinned disk and the two hubs can reach
near the origin). **Exact criterion.** A site at distance `h` from the origin is at distance
`≤ r` from **every** point of `V_ε` **iff** `h ≤ r - ε`. For two hubs at distances `h_1,h_2`
to cover `V_ε`, the ball-coverage part needs `h_j ≤ r - ε`, and the angular part is
equivalent to

```
cos α_j = (r^2 - ε^2 - h_j^2)/(2 ε h_j) =: γ_j ,     α_1 + α_2 ≥ π  ⟺  h_1 h_2 ≤ 2 r ε
```
(the last equivalence is the monotone identity `arccos γ_1 + arccos γ_2 ≥ π ⟺ γ_1γ_2 ≤
√((1-γ_1²)(1-γ_2²)) - 1`, whose right side collapses to `h_1h_2 ≤ 2rε`).

**This criterion is never binding.** On the allowed domain `ε ≤ r/3` one has
`h_j ≤ r - ε`, hence `h_1h_2 ≤ (r-ε)^2`; and `(r-ε)^2 ≤ 2rε` **iff** `ε ∈ [(2-√3)r, r]`,
i.e. for all `ε ≥ 0.2679 r` — in particular for the whole range `ε ∈ [(2-√3)r, r/3]`. Below
that the ball-coverage condition `h_j ≤ r-ε` is itself weaker than what the ring structure
already gives (`|c_j| ≤ sqrt(1-r²)`). Equivalently: at `r = 0.38` the numerical check gives
`α_1, α_2 ≈ 2.01 rad` with `α_1 + α_2 = 4.02 > π`, a wide margin.
**Therefore no bound derived from the hubs' coverage of `B(0,1-2r)` can exclude the corner**
(the hub route is not just unexploited, it is *insufficient*). This confirms the lead's
numerical diagnosis: the exclusion must use (EX) on the whole of `D\{origin}` — the far-side
arcs and the second hub's angular placement.

## 5. Verdict and interface to the certification

* **No derived exclusion from local geometry** — report as asked. The α→π corner is local-
  geometry-admissible; the exclusion must be global, and the global statement has the precise
  form (EX).
* **What is usable from here:** (i) the necessity in §2 (degenerate corner = pinned disk at
  `|c_0| = r` with `u = v = t ∈ [75/76,1]`), which turns the compactness problem into a 1D
  segment in the lead's normalisation; (ii) the identity (1a) which explains why no local
  α-bound can be uniform; (iii) the arithmetic slack (1b) showing the arc budget cannot
  substitute for the global argument.
* **Interface obligation for the certificate:** the fixed-`R0` dual route excludes the corner
  uniformly provided it is run over the whole 1D segment `t ∈ [75/76,1]` **and** the covering
  of `D\{origin}` is encoded (equivalently: the ten-disk configuration must include the
  origin-avoiding constraint). A corner exclusion at the single allowance `r = 0.38` does not
  by itself cover `r < 0.38` — as the lead's own scope note says.

## 6. Repro

```
py -3 -B -X utf8 tools/sector_angle_check.py    # switch angles, alpha at switch, width budget
py -3 -B -X utf8 tools/height_feasibility.py    # calibration: recovered cover radius = registered
py -3 -B -X utf8 tools/degenerate_threshold.py  # pinned-family violation vs r (TIMED OUT; partial)
py -3 -B -X utf8 tools/sector_height_probe.py   # critical-set machinery
```
`tools/degenerate_threshold.py` exceeded the 600 s shell budget; treat its output as absent and
do not cite an `r*` value. No further numeric runs on this line are requested or planned.
