> **STATUS: WITHDRAWN except section 0's convention note.  All monotonicity, ridge and
> active-set conclusions below are INVALID.  Do not use any result from sections 1-5.**
>
> The lead identified five independent defects, all confirmed here:
> 1. **Off-face formula error (mine, copied from r16b:86 into the report).** I wrote
>    `e2' = (X X' + Y Y')/(4 R sqrt(Q))`; with `e2 = sqrt(Q)/(2R)` the correct derivative is
>    `e2' = (X X' + Y Y')/(2 R sqrt(Q))`, i.e. **twice** what I wrote.  (The code path
>    `dQ/(2 sqrtQ)/(2R)` happened to evaluate correctly; the documented intermediate and the
>    report's formula were wrong.)  Validated independently in `r16q_validate_e.py`:
>    differencing `e2` itself agrees with the lead's formula to `6e-19`..`9e-19` at five
>    points, and is off by exactly a factor 2 from the halved form.
> 2. **Wrong ridge.** The ridge is `delta = b1 - b2` with `H = 2 r sin(b1+b2)`; `delta = b1`
>    is the **wedge edge** (A = 0), not the ridge.  Verified: at `delta = b1-b2`,
>    `H = 2r sin(2b1-delta) = 2r sin(b1+b2)` identically (checked at three triples).
> 3. **Wrong face intersection.** The two cap curves intersect at `delta = b1 - b2`, not at
>    `+- (b1-b2)/2`.
> 4. **Wrong root labels.** The plus norm root is `j=2` and the minus root `j=3` (my scan
>    called the plus root `j=3`).
> 5. **Wrong j=1 sign.** By the reflection `delta -> -delta, b1 <-> b2` the `j=1` branch
>    derivative is the **negative** of the `j=0` one, so a positive `j=1` slope was an
>    artefact.  My scan reported both branches "strictly increasing with min slope +0.1627"
>    and the "cap collar at `delta = +-(b1-b2)/2`" classification -- both withdrawn.
>    Note also that a direct bounded calibration with the corrected formula shows **both sign
>    signs on all four branches** (`j=0`: 8681 pos / 175 neg; `j=1`: 181 pos / 8675 neg;
>    `j=2`: 2902 pos / 2938 neg; `j=3`: 2884 pos / 2956 neg), so the monotone-arc picture of
>    section 1 does not hold as stated.
>
> Consistent with the lead's instruction, **no old monotonicity result from this file is
> usable**, and no interval certification was attempted on the corrected formula beyond the
> bounded calibration in `r16r_recalib.py` / `R16R-RECALIBRATION.md`.

# R16 — saturated-face branch derivative structure in delta *(WITHDRAWN below this line)*

Scope: own files only.  Read `lead/SATURATED-FACE-BOUNDARY-CHART.md` and the formulas in
`lead/interval_hub_saturated.py`.  Current coefficients
`lead/joint_nested_frozen.json` sha256 `5671967c5a3df341b068975b161900c8b7df4fd59298a4e4fb9f7210438221fb`.
Declared ranges: `b1, b2 ∈ [1, arccos r]`, `r ∈ [.375, .38]`; delta domain `[-b2, b1]`;
ridge is `delta = b1`.  No claim registered.

## 0. Conventions actually used (read off the sources)

`quad_range(a,b,x) = a*x^2 + b*x` (from `interval_joint_patch.py`), hence
`quad(beta,gamma,e) = beta*e^2 + gamma*e` with
`beta1 = -z[16] = +0.405431351`, `gamma1 = -z[78] = -0.870277865`,
`beta2 = z[20] = +0.400827103`, `gamma2 = z[82] = -0.86525597`.
Branch value as in `interval_hub_saturated.py:24-33`:
`V(delta) = (z3-z1) delta + H r (sin b1 sin A + sin b2 sin B) + Sum_i [a_i phi_i + quad(beta_i,gamma_i,e_i)]`
with `a1 = z1-z9`, `a2 = z3-z9`, `A = b1-delta`, `B = b2+delta`, and on the on-face index
`e = r sin(angle)/R`, `phi = b`; otherwise `e = |XY|/2/R`, `phi = atan2(Y,X)`.

Note: my first script used `quad(beta,gamma,e) = beta*e + gamma*e^2`.  That was wrong and
produced a spurious `j=3` interior *maximum*; with the correct convention the picture below
holds.  All numbers here use the corrected convention and closed-form `dV/ddelta`
(assembled by chain rule, `dV/dH`-free), cross-checked against finite differences.

## 1. The mechanism: which branch and which constraint

**(M1) The hub-position objective has no interior critical point on the stated range.**
Along a fixed branch the constraint is a one-dimensional curve in `(H, delta)`, and
`dV/dH = r(1 - cos(2H)) > 0` on `H ∈ (s-(1-r), 2r) ⊂ (0, pi/2)`; equivalently the tangent
parameter along the branch moves along `(0,1)` and `(1,2)` without vanishing.  So the hub
part is strictly increasing in the branch parameter and no stationary point of the hub term
survives in the interior of the cone; only the `delta`-weighted terms
(`(z3-z1) delta` and `(a2 cos delta - a1 sin delta)/2`) can create `delta`-stationary points.

**(M2) Branch-by-branch derivative structure** (852 profiles with a nonempty admissible set,
analytic derivative, refined roots to ~1e-15):

| branch | surface | admissible? | `dV/ddelta` sign changes | character |
|---|---|---|---|---|
| `j=0` | face-1 cap `H = 2r sin(2b1-delta)` | yes (294/294) | **0** | strictly increasing; min slope **+0.16266**, max **+0.39130** |
| `j=1` | face-2 cap `H = 2r sin(2b2+delta)` | yes (294/294) | **0** | strictly increasing (chart symmetry) |
| `j=2` | norm circle, negative root | **never** (0/294) | — | infeasible on the stated ranges |
| `j=3` | norm circle, positive root | yes (294/294) | **1** (294/294) | the unique interior critical point is a **minimum** |

No profile anywhere has its maximum at an interior critical point (0 of 852; also 0 of 240
in the refined-run census).  So the answer to the posed question is: **monotone arcs plus a
single minimum on the norm branch — there is no residual interior maximum** on the stated
ranges.

## 2. Where the maxima actually sit (active-set census)

Refined runs, `b1, b2 ∈ [1, arccos r]`, `r ∈ {.375, .376, .377, .378, .379, .38}`, 432
branch maxima for `j ∈ {0,1}`:

| active set at the maximum | count | condition |
|---|---|---|
| `face1-cap` only | 180 | `\|b1-b2\| ∈ [0.036, 0.186]` |
| `face1-cap & face2-cap` (both tight) | 36 | **exactly `b1 = b2`** in every case, at `delta = 0` |
| `face2-cap` only (branch `j=1`) | 216 | — |
| delta-domain end `delta = b1` | **0** | — |
| delta-domain end `delta = -b2` | **0** | — |

So on the stated ranges the maximum of the delta-profile is **always at the collar
`delta = ±(b1-b2)/2`**, i.e. the point where the second face cap starts to bite, never at the
domain ends and never at an interior stationary point.  When `b1 = b2` the two caps coincide
(`H = 2r sin(2b1+delta)` identically) and the collar collapses to `delta = 0`, which is the
only case where both caps are simultaneously active.

This is the precise sense in which the ridge/endpoint picture reduces: **on the stated
ranges the profile max is either (i) the face-cap collar — reducing to the endpoint/cap
intersection — or (ii) the ridge when the ridge itself is feasible.**  The ridge
`delta = b1` (A = 0) requires the hub to satisfy *both* face equations simultaneously,
which forces `sin(2b1) = sin(b1+b2)`, i.e. `b2 = b1` or `b2 = pi - 3b1`; with the hub-norm
condition this has **no solution in the stated ranges** (0 triples for every `r` scanned).
That is consistent with the lead's C860 finding that the global ridge is false at low
bearings: on this box the ridge is not merely inactive, it is infeasible.

## 3. Exact `delta = b1` identities (stated for the record)

At `delta = b1`: `A = 0`, so the face-1 chart gives `H = 2r sin(2b1)` and the edge length
`L1 = 2r sin A = 0`; the face-1 phi identity is `phi1 = b1` exactly.  The face-2 cap reads
`H = 2r sin(b1+b2)`.  Equalising the two gives the two ridges above; the `b2 = b1` branch has
`B = 2b1 = 2A + 2b1`, not a shared cap value, so it is not a "both caps tight" ridge either.
The `-2*z[72]`-type signed terms do not enter here: on all four branches the objective is the
one in `interval_hub_saturated.py:24`, with no eta term.

## 4. Scope, and what is missing

**Proved/established here (numeric, bounded scan; not a certificate):**
* the two face-cap branches `j=0,1` are strictly increasing in delta with margin
  `dV/ddelta ≥ 0.1627` over the scanned box;
* the norm branch `j=2` is infeasible on the box;
* the norm branch `j=3` has at most one interior `delta`-critical point and it is a minimum;
* every profile maximum is at the collar `delta = ±(b1-b2)/2` (838/852 in the full scan),
  at the domain end (0 cases), or at an infeasible-ridge exclusion.

**Not proved / missing implication:** nothing above is an interval certificate, and the scan
is a bounded parameter scan rather than a proof over the whole box.  Two gaps stand between
this readout and a usable branch reduction:
1. the monotonicity of `j=0,1` is verified by evaluating the derivative at ~294 parameter
   triples, not by an interval enclosure of `dV/ddelta` over the box — the margin observed
   (`≥ 0.1627`) is large but unproved;
2. the classification "feasible collar or infeasible ridge" must be shown to exhaust the
   box, i.e. an interval proof that `j=2` is empty and that `j=3`'s single root is a minimum
   for **every** `(r,b1,b2)` in the box, not just the scanned grid.
With those two, the hub-objective maximum on the stated ranges reduces to a finite
comparison of collar points (and the ridge, when feasible) — which is the reduction the lead
is looking for; without them the reduction is empirical only.

I did **not** extend to low bearings (`r < .375`, `b < 1`) and did **not** use the C860
counterexample region: on the stated ranges the ridge is self-excluded, so no ridge
assumption is being smuggled in.

## 5. Files

`r16b_analytic_deriv.py` (closed-form derivative + structural scan, `out/r16_deriv.json`),
`r16c_detail.py` (admissibility/feasibility census, `out/r16c_detail.json`),
`r16d_roots.py` (refined runs and roots, `out/r16d_roots.json`),
`r16e_classify.py`, `r16g_census.py` (active-set labels),
`r16h_final.py` (`out/r16h_endpoints.json`), `r16i_stats.py`.
Earlier `r16_branch_profile.py` used the wrong `quad` convention; its `j=3` "interior
maxima" are superseded by section 1 above.
