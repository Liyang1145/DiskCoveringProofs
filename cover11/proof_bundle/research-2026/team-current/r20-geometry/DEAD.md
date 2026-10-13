# r20-geometry — DEAD / withdrawn / method limits (this directory only; no claims registered here)

> Nothing in this directory registered a claim; all entries are review/audit artifacts of the lead's
> notes. "Withdrawn" = my own earlier text that was wrong and is corrected elsewhere; "method limit" =
> a computation whose stopping reason is the instrument, not the mathematics.

## Withdrawn (own text, corrected)

* ✗ **"`{R_c≤r}` is a union of two half-disk caps"** — wrong. By the product identity
  `4y²(R_c²−r²)=F_inF_out` the set is the **symmetric difference (two crescents)** of the two disks
  `B(p_in,r)`, `B(p_out,r)`. Corrected in `AUDIT-FAN-DISK-MECHANISM.md` §1/§3.3 and
  `AUDIT-CLOSED-H-AND-STRICT-HUB.md` §0.
* ✗ **"the outward tangency point `h★` is a spurious extra point"** — wrong; for `y_{h★}<0` it is a
  *legitimate inward* closed point (`R_c=r` exactly, inside the inner disk). The "18 spurious extras"
  scan line was the roundoff tail of the 2594 `y_{h★}>0` missed points. Withdrawn.
* ✗ **"the closed-domain mechanism region has no extra points at all"** — wrong at the base line
  `y=0`: there the mechanism region meets `|h|≤1−r` exactly in the degenerate stratum `h∈{a,b}`
  (ring centres), where the circumradius of `(a,b,h)` has no value (direction-dependent limit
  `d/(2|sinθ|)`). Corrected statement: no extras **off the base line**; the stratum lies on
  `|h|=1−r` and is excluded by strictness, so C879's strict statement is unaffected. See
  `AUDIT-CLOSED-H-AND-STRICT-HUB.md` Fix 3 and `STRICT-HUB-FINITE-DISJUNCTION.md` §0.
* ✗ **"the closed-domain `iff` patch is: add the ≤1 missed point per edge, nothing else"** — for an
  *iff* reading the two degenerate points `{a,b}∩∂B(0,1−r)` must also be named/excluded. Withdrawn as
  a complete patch statement (the "add the missed point" half remains correct).
* ✗ **"central coupling lives in `R⁴` as an intersection of balls (Helly-5, ≤4-active-ball finite
  candidates)" — WITHDRAWN (my own, lead-corrected).** Root cause: the fixed-disk centre `q` of the
  central crescent depends on the *other* hub, so when both hubs move the constraint is not an `R⁴`
  ball and the feasible set is not convex; a 2-D disk constraint lifted to `R⁴` is a **cylinder**, not
  a ball. Hence Helly number 5, convexity and the ≤4-active-ball candidate reduction all lose their
  basis. Replacement (valid): fix `a`; the `b`-fiber is a finite Boolean combination of disks in
  `R²`, the relaxed fiber is convex, **Helly-3** applies, and emptiness is the finite witness list
  H1–H6 as conditions on `a` (see `CENTRAL-COUPLING-NORMAL-FORMS.md` §2). Also: `C894` is retracted by
  `alternative` — **registered reason: reversed inclusion** (lead's original retraction reason; no other
  cause is asserted here) — and `C896` is numeric — neither may be used as a
  premise. Old "Theorem D" is downgraded to the generic compact-boundary fact (closedness is not
  automatic: the circumradius is undefined on the degenerate locus `a=b`, `c∈{a,b}`, `b∈line(a,c)`).
  `RADIAL-INWARD-LOCAL.md` §6 / `CENTRAL-COUPLING-NORMAL-FORMS.md` §0.

* ✗ **Box-level δ values for the distal-exclusion test — NOT certified (withdrawn from citation).**
  Lead (c498de5a) found float weights, a bbox-endpoint error and a `sqrt`-domain error in
  `alternative`'s `central_crescent_interval.py`; the old δ readings (`δ ≤ 1.872·10⁻³` etc.) must not be
  cited. Their repaired v2 reports `ε_A = 5.905046376·10⁻⁹`, `ε_B = 0.033062070669`, ranges
  `δ ≤ 1.8720480434·10⁻³` / `1.8200529466·10⁻³` (domain: C879-legal tuples only) — recorded here but
  **still uncited pending an independent audit**. What may be cited is only the *conditional* statement
  (if the far-disk separation holds then crescent = single disk on the box), never a numeric radius.
  See `CENTRAL-COUPLING-NORMAL-FORMS.md` §2.2.
* ✗ **My "tight triple" note claims — withdrawn (lead 78be2857).** (i) The line "max cyclic gap ≈ 189°
  > 180°" attached to a tight triple was a **wrong number copied from a different run**; the true gaps
  are 123.8°–170.0° (`≤ 180°`), and the criterion direction is: `gap ≤ 180°` ⟹ normals not in an open
  half-plane ⟹ no common strict inward direction ⟹ intersection = singleton; `gap > 180°` ⟹ interior.
  (ii) The claims "near-zero ⟹ exact saturation", "box sign change forced", "no direction to exploit"
  are **withdrawn**: near-zero readings (`~10⁻¹⁷`) are not certificates and imply no forced sign change.
  (iii) The `MEC` implementation is fine (obtuse ⟹ diameter branch) and is now calibrated on the lead's
  instance `(0,0),(2,0),(1,0.05)` (MEC = 1, diameter, bary `(100.25,100.25,−199.5)`); no mismatch was
  found — but the calibration is recorded in the script rather than assumed.
  See `GLOBAL-PARAMETER-COUNT-AND-COVERAGE.md` §4.
* ✗ **"triple intersection = singleton" conclusions from near-zero readings — withdrawn (lead 11dc6a88).**
  `ψ < r` with positive barycentric weights implies a small **interior** (MEC centre strictly inside all
  three disks), so the singleton reading is unjustified; the normal-cone criterion may be used only after
  an **exact** proof that all three boundaries pass through the point. The specific singleton claims are
  deleted; the conditional lemma is kept (see `GLOBAL-PARAMETER-COUNT-AND-COVERAGE.md` §4).
* ✗ **"Schur-energy stress maximum sits at simplex vertices (finite stress list)" — WRONG, retracted
  (lead fd64d79e).** Root cause: I used the *unreduced* sum `Σ α_e|edge_e|²`; the correct object is
  `E_α(U) = min over the free nodes`, an infimum of linear functions of `α` and hence **concave,
  generally nonlinear**. Concave maxima need not be at vertices: at a single-edge vertex the free
  endpoints coincide giving `E = 0`, while the two-edge path with weights `(a,1−a)` gives
  `E_a = a(1−a)|U−W|²`, maximised **interior** at `a = 1/2` with `|U−W|²/4 > 0`. The finite-vertex route
  and every downstream claim built on it are withdrawn; the corrected Lagrangian proof and the exact
  calibration are in `FIXED-SWITCH-QUADRATIC-STRESS.md` §5 / `schur_stress_calibration.out.txt`.
## Method limits (not disproofs)

* ✗ **Universal fixed-endpoint FAN saturation — dead (lead's counterexample, independently confirmed
  here).** Saturating a fan by moving the internal ring centre while hub and endpoints are held fixed
  is impossible in general: at `r=3/8`, `H=(1/2,0)`, `c0=(q,0)`, `c±=q(cos2A,±sin2A)` (`q=√55/8`,
  `A=asin r`) the gap endpoints `U±=(q,±r)` are `2r` apart, forcing the internal centre to be their
  midpoint, while `Rc² = 71/220 − 23√55/880 < 9/64` (both fans slack); the `ε`-family keeps this
  uniformly (`L_ε` shrinks to `{c0}`, `|c−(cos g,0)|² ≤ r²−sin²g`). Pointer: lead's
  `FIXED-ENDPOINT-SATURATION-COUNTEREXAMPLE.md`; my independent check
  `lead_counterexample_check.py/.out.txt`. **Do not use this normal form.**
  *Correction of scope (this directory):* the counterexample does **not** contradict the boundary-tie
  radial criterion B1–B3 (at `ε=0` the middle ring's `t_bdy=1` — no inward move — and for `ε>0`
  `t_bdy<1` while the fans stay slack: the two slack parameters are independent), and it does **not**
  block the **hub** min-norm move of `RADIAL-INWARD-LOCAL.md` §6 (in the same configuration
  `h → argmin_S|h| = (0.4056,0)` saturates **both** fans, still strict `|h|<5/8`).

* ⚠ **Fan-B singleton status is at the object's saturation level.** The certified object's hubs lie on
  the pin circles of 4/4 (fan A) and 3/5 (fan B) edges to ≤2e-18; whether these saturations are exact
  is **not** decided here. It does not affect the strict-hub verdict (margins 0.347/0.471), but any
  statement that *uses* the exact singleton (e.g. "no Slater point, exactly") carries this caveat.
* ⚠ **Interior stationary class — CLOSED for the tested configurations (Round 5c).** The earlier
  gap ("arc-interior stationary points of `t_-` not enumerated") is removed by the monotonicity
  lemma: `t_-=F(λ,φ)` increases in `λ` and in `|φ|`, so the maximum over `cl Q_i` sits at a crossing
  or a closed-form Pareto point (`λ'=0`: `c(1+r/|c|)`; `φ'=0`: radial tangency), plus crossing
  endpoints of constant-`F=1` pieces. What remains open is only the *uniform-over-ring-domain*
  version (all legal rings, not just the tested ones) and the iteration to simultaneous saturation.
* ⚠ **Naive angular-span criterion is FALSE** ("`|φ| ≤ φ_max` for all of `cl Q_i`"): off-span vertices
  exist (ring 6 at `r*`: `max|φ| = 0.544` vs `φ_max = 0.281`) but are inward/small-`λ`, so they cannot
  bind. Use the Pareto/monotonicity form, not the span form.
* ⚠ **One-ring-at-a-time only.** The radial-inward test moves one ring per evaluation; the iteration to
  simultaneous saturation of all nine seams (and its continuity) is not done.
* ⚠ **Tie-uniqueness hypothesis of C879** stays unproved here (bounded numeric search only,
  `audit_tie_uniqueness_fine.py`); no uniform margin exists (`|p_in| = 1 − Θ(d)`).
* ⚠ **`t_+=k`/`|p_out|=1` on all nine certified edges is exact for the object's *intended* design but
  only ~1e-17 in the stored rationals**; interval/exact arithmetic is required if a certificate is
  built directly on those equalities.
