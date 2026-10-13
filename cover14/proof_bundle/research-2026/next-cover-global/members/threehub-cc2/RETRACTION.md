# RETRACTION — members/threehub-cc2 round 1/2 (accepted Lead review)

## R0. What is withdrawn, in one line each

| item | verdict | root cause |
|---|---|---|
| **L2** ("active disks do not cover `\|x\|<1−2r`; hub disks do not cover `\|x\|>2r`") | **FALSE** | the "hub disks lie in `B(0,1)`" arrow is correct but the *reverse* arrow used in L4/L5 ("hubs inside `\|x\| ≤ 2r`") does not follow; and the active-disk inequality was used with the wrong direction |
| **L3** (`\|h_j\| ≤ U`) | **FALSE as proved** | a core point lying in a hub disk gives only `\|h\| ≤ a + U`; `\|h\| ≤ U` was inferred from the *convex cell contains a boundary point of the core* step, which is not enough. Non-equilateral triples can legally have a hub with `\|h\| > U`, so the universal quantifier was wrong too |
| **L4** (middle annulus is at distance `> r` from every hub) | **FALSE / VACUOUS** | domain `{2r < \|x\| < 1−2r}` is **EMPTY** at `r = U` (see R1); and the proof used `\|h\| ≤ r`, whereas only `\|h\| ≤ U` was (wrongly) claimed — `U > r` in general |
| **L5** (`Ā_r` must be covered by the 11 active disks) | **FALSE / VACUOUS** | inherits R1 (empty set has no covering obligation that constrains anything) |
| **`R(r)` experiment** (`py/rstar.py`, `evidence/rstar.{txt,json}`) | **INVALID** | measured a covering-radius function on an empty/near-empty domain; reported `R − r = +0.036` is the numerical fingerprint of exactly that sign error and was read as *confirmation* instead of a red flag |
| **`inner_circle.py` "inner-circle test holds at r=U with margin 3.7e−6"** | superseded | the test itself is an identity: `2r(1−r)cos(π/11) ≤ (1−r)² + 3r²` has discriminant `< 0` in `r`, so it holds for **all** `r` and excludes nothing |
| **`three-hub/INTERFACE-5D-EXPOSED.md §3` reference** | partially superseded | its `D5` closed-relaxation complaint stands, but my own replacement (L4/L5) is worse; the correct fix is to state an explicit closed relaxation with `≤` and include boundary degeneracies |

## R1. The decisive sign error (domain, not kernel)

`U = 0.33173203427623414`, so

    a = 1 − 2U = 0.3365359314475317   and   2U = 0.6634640685524683 .

The "middle annulus" I built in round 2 is `Ā_r = {2r ≤ |x| ≤ 1−2r}`, whose two radial
bounds cross inside the whole legal range: `2r ≥ 2·(something > 0)` and
`1−2r ≤ 1`, and at `r = U` the lower bound `2U = 0.6635` **exceeds** the upper bound
`1−2U = 0.3365`:

    Ā_U = {0.6635 ≤ |x| ≤ 0.3365} = ∅ .

The qualitative reading of the two regions is the opposite of the one I used:
`[a, 2U] = [0.3365, 0.6635]` is the annulus where hubs *can* reach (hubs have
`|h| < 1−U = 0.6683`, so hub disks reach inward over it), while `[2U, 1]` is the outer
part covered by active disks. My numerical validator even printed `R − r = +3.6e−2`
on a supposedly nonempty annulus — a symptom, which I misread as agreement.

## R2. The kernel error (the Voronoi/"far boundary point" step)

L3's proof tried to conclude `|h_j| ≤ U` from "the Voronoi cell of `h_j` contains a
point `p` on `|p| = a`, and `p` must be covered by some hub, so `|p − h_j| ≤ U`".
Two independent defects:

1. a core point lying in the disk `B(h_j,U)` gives only `|h_j| ≤ |p| + U ≤ a + U`,
   which is much weaker (and is the *inactivity* bound `1−U` after substitution, not
   `U`);
2. the cell-boundary assertion does not produce `|h_j| ≤ U`: for a hub with
   `|h_j| > U` the cell's far corner can be nearer than `|h_j|`, so the resulting
   constraint is on `√(a² + |h|² − a|h|)`-type quantities, not on `|h|`.

Consequently the quantifier in L3 ("**every** hub satisfies `|h_j| ≤ U`") is wrong;
only equilateral triples happen to attain it.

**Numeric bracket for the equilateral family** (3-decimal grid over `B(0,a)`,
`max_j` min-distance, `py/hubcore.py` and the final check run): with hubs equilateral
at distance `t`,
`C(t) = max(t, √(a²+t²−at)) − O(grid)`; the sampled values are `C(0.30) = 0.3197`,
`C(0.3317) = 0.3340`, so the equilateral legality threshold lies at
`t* ≈ (a + √(4U²−3a²))/2 ≈ 0.3268` (Lead's corrected arithmetic), **not** `U`.
So the equilateral family cannot be used to exhibit `t > U` hubs; the Lead's
non-equilateral example (`h₁ = (0.4,0)`, `h₂,₃` at `0.15` along `±120°`) is **not
verified by me** and must not be quoted as a counterexample or as proved.

## R3. What survives from this member's round (use only this)

* `U = 0.33173203427623414`, `a = 1−2U = 0.3365359314475317`, `1−U = 0.6682679657237658`,
  `2U = 0.6634640685524683 > 1−2U = a` (this last inequality is the fact that voids the
  whole annulus construction).
* **Activity counts (correct reading, cross-checked):** the saved rational
  construction `lead/improved-upper-test.json` has centre norms
  `0.326818 ×2, 0.388619 ×2, 0.780827 ×4, 0.891617 ×4, 0.943374 ×2`, i.e. with
  threshold `1−U = 0.6682679657` it is **10 active + 4 hubs** (an earlier line of mine
  claiming all four largest norms are `< 1−U` was a mislabelled threshold and is
  withdrawn; `evidence/diag3.txt`).
* Its covering radius, on both a 2D grid over `D` and a dense `S¹` grid, is
  `0.331732034276` — instrument re-checked in `py/crit_check.py` /
  `evidence/crit_check.txt`; the 2D grid is the correct criterion, since the `S¹`-only
  reading equals the covering radius of `D` **only** when every centre has `|c| ≥ 1`
  (which the saved construction does not satisfy).
* **L1 (kept, elementary):** a radius-`r` disk meeting `S¹` has centre norm in
  `[1−r, 1+r]`. Proof: `x ∈ S¹`, `|x−c| ≤ r` ⇒ `1 ≤ |c|+r` and `|c| ≤ 1+r`. ∎
* **Withdrawn member artifacts, listed so nobody reuses them:** `calib_ring_control.py`
  and the `1/(2cos(π/2n))` ring formula (wrong reconstruction of the literature entry);
  `exp2`–`exp5` (soft penalties drifting, `S¹`-only criterion, and the invalid
  "scale hubs about 0" projection in `exp4`, whose `core_radius = a` with all hubs at
  the origin is an artifact); `rstar.py`; the L2–L5 chain in `MEMBER-NOTES.md`.
* **Numerical observations that are NOT claims and are not to be used as candidates:**
  k=11 hill-climb readings around `0.3517` (`exp6`), the symmetric-family best `0.3734`
  (`sym11.py`). These come from an unconstrained 28-parameter hill-climb with no
  certified direction, and after the errors above I do not regard them as evidence for
  or against the k=11 branch.

## R4. Conclusion of this member's assignments

No structural new conclusion. In particular I did **not** produce a valid global bound
on a necessary condition, nor a verified feasible counterexample. The k=11 exclusion
obligation is exactly where it was before this round: it needs a legitimate closed
relaxation (explicit `≤`, boundary degeneracies included, `t = U` limit handled) and a
dual/capacity certificate on a **nonempty** region, which is not what L4/L5 provided.

Evidence paths: `evidence/diag3.txt` (activity counts),
`evidence/crit_check.txt` (criterion repair + saved covering radius),
`evidence/hubcore.txt` (equilateral `C(t)` readings),
`evidence/exp1..exp7_*`, `evidence/rstar.*`, `evidence/sym11.txt` (audit trail of the
withdrawn instruments).
