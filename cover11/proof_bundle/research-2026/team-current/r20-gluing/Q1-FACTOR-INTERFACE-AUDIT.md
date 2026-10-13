# Q1-FACTOR-INTERFACE-AUDIT — real cover ⇒ area factor identity, shared variables, moment dual signs, interval envelope

**Lane**: r20-gluing (cline2-r23-gluing), sole writer here. Read-only source audit of
`lead/Q1-BALANCED-EXCLUSION.md` and `lead/SHARED-MOMENT-DUAL.md` plus the three sources behind them
(`shared_moment_dual.py`, `certify_shared_moments_dense.py`, `check_quadratic_support.py`).
**No numeric re-run, no claim, no sub-agent.** Scope: only this interface, as instructed. C920/C921 are
not re-audited. Registered scope is *not* treated as proof of anything I did not check myself.

## 1. Real cover ⇒ factor identity: the only interface that must be one-way

The area bound uses C817's exact face/switch/sector decomposition (I did **not** re-derive it; it is an
inherited premise) and *adds* two families of constraints:

* **Side matching, first power:** two faces sharing an edge express that edge's length as
  `y_f sin A` resp. `y_g sin B`. For a genuine configuration the shared edge has **one** length, so
  `y_f sin A = y_g sin B` holds as an **equality** — hence both directions hold, and a *free* multiplier
  is legitimate; squaring gives the second-power identity, again an equality.
* **Radius copies:** a radius appearing in several factors is the same `ρ` in a genuine cover, so the
  first- and second-power copies are equalities as well.

Consequently, imposing both powers and both copies **cannot exclude a genuine cover**; it only shrinks
the decoupled relaxation, which is the stated purpose ("keeping both strengthens weak duality"). The
directions are therefore the safe ones. **Correction (lead).** Both powers of the shared side are
**equalities** (squaring an equality), so *both* get **free** multipliers — I had written the squared
ones as "nonnegative slacks", which is wrong. The only nonnegative slack in this family is the
**angle / Delaunay slack** (`kappa`-type), which is the one that is genuinely one-sided. `shared_moment_dual.py`
records the family split — `mu11, side21, endpoint18, nonnegative angle slack21, lambda, eta` — where the
21 angle slacks are the nonnegative ones and the side/copy multipliers are free; the generator adds the
corresponding columns before maximizing, so no constraint enters with a sign that a genuine cover could
violate. **Interface passes**, with the division of labour clear: the *identity* is C817's; the side/radius
rows are equalities (free multipliers, both powers); the angle slacks carry the one-sidedness; nothing
here needs moment realizability (as the note states).

## 2. Signs, cancellation, and the multiplier bookkeeping

The face factor is `linear angle part + Q(A,B)` with `B` = signed sum of the new side-first multipliers
times the sine of the opposite angle; the switch factor has `B = −(side-first)·sin b + two copy-first
terms`; ring factors add `−copy-left-first·u − copy-right-first·v`. These are exactly the first-power
shifts of the corresponding C817 atoms, with the *sign of the sine* carried by the geometry, so the
per-atom monomials cancel against C817's as claimed. That cancellation is not verified by inspection
here — it is delegated to `check_shared_moment_symbolic.py`, which assembles the formal atoms
independently and checks exact rational coefficient cancellation over **both** graph orbits
`{0,1,4,5}`, `{2,3,6,7}` (correspondingly `check_shared_moment_dense_symbolic.py` for the dense set). I
confirmed the schema (multiplier slices `z[73:94]` = 21 side-first, `z[94:112]` = 18 radius-copy, added
to the C817 dual with the constant unchanged) matches the family list in the module's header; the
*counts themselves* (21, 18) are checked by that symbolic control, not by me.

## 3. Interval maximizer envelope — verified, with one endpoint repair

The scalar support is `Q(A,B) = max_{0≤y≤1}(Ay²+By)`. The analytic case list used in the certificate
(endpoint values `0`, `A+B`, and the interior peak `−B²/(4A)`) is **correct**: for `A ≥ 0` the maximum is
at an endpoint; for `A < 0` it is at the endpoint or, iff `0 ≤ B ≤ −2A`, at the interior vertex. `Q` is
monotone in each coefficient (each `y², y ≥ 0`), the enclosure
`Q([a₀,a₁],[b₀,b₁]) ⊆ [Q(a₀,b₀), Q(a₁,b₁)]` follows, and the **maximizer** is nondecreasing in `(A,B)`
`because A(y₂²−y₁²)+B(y₂−y₁)` increases in both coefficients for `y₂>y₁`; ties are bounded by a full
enclosing maximizer interval. The generator implements this: radius intervals are built from the corner
maximizers (`interval(max(0,lowarg.a), min(1,hiarg.b))`), the centered mean-value form is taken at a
fixed radius inside that interval, and the result is intersected with the direct enclosure
(`interval(max(direct.a, mean.a), min(direct.b, mean.b))`) — a sound intersection of two valid
enclosures; boundary-crossing boxes fall back to the direct one. Danskin's envelope gradient at a
singleton argmax plus the local Lipschitz bound at ties covers the mean-value step.

**Finding — WITHDRAWN (my misread).** I flagged the peak branch's missing `B ≥ 0` condition as
producing a non-rigorous *lower* endpoint. That was wrong: (i) `scalar_quad` has an early
`if b.b <= 0: return zero` (line 23) — the case `B < 0` never reaches the peak branch at all, and the
parent `quad` calls `scalar_quad(A.a,B.a)` / `scalar_quad(A.b,B.b)` with **exact dyadic singleton
endpoints**, not with intervals straddling zero; (ii) `arg_at` carries the same guard (line 48). So the
lower endpoint I complained about is unreachable, and no fix or warning is warranted. The analytic
support list itself (endpoints `0`, `A+B`, and the interior peak under `0 ≤ B ≤ −2A`) remains correct —
it is the universal argument, while `check_quadratic_support.py` is only its instrument calibration.

## 4. What the interface does *not* cover (recorded, no claim)

* **Ring factors remain global 3D suprema** inside the interval subdivision; only the face/switch
  factors get the envelope treatment. The module itself flags that "ring radius grids are NOT global
  certificates", and the pilot's coarse-grid failures (`start2 = 3.164374 > π`), the improved ear
  capacity (`R+ρ_ear`) and the 8/24-slice ear tests are recorded as **honest failures of those
  coefficient sets / grids, not as disproofs**. The final numbers quoted in the note
  (`start0 < 3.135494`, `start2 < 3.139813`, tolerance `4e-5`) are **readings of the certificate
  outputs**, and this audit neither recomputed them nor certifies them; the two independent controls I
  inspected are a 3000-box `Fraction` calibration of the support formula (`check_quadratic_support.py`,
  explicitly *not* the universal argument) and the formal-atom cancellation checks.
* The note's own scope is correct and I keep it: excluding the balanced q1 graphs at `R = 19/50` says
  nothing yet about the sharp optimum, and the q0 degrees `(4,9),(5,8),(6,7)` remain.

**Verdict.** The real-cover ⇒ factor-identity interface is one-way in the safe direction — side and
radius-copy rows are **equalities in both powers** (free multipliers), the one-sidedness sits in the
**angle / Delaunay slacks** (the only nonnegative family), and the sign bookkeeping matches the family
list — and the maximizer envelope is analytically justified with the `B ≤ 0` guard in place. My earlier
"peak-branch lower endpoint" finding is **withdrawn** (§3) and no repair is needed. Nothing here is
promoted to a claim, and no global statement is made.
