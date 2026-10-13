# CLASS-COMPLEMENT AUDIT — the q0(6,7) class complement

**STATUS: `initial_invalid`; §4/§5 sentences RETRACTED.** The transfer section of
this report contained unproved and wrong statements and is superseded by the lead's
note **`lead/RADIUS-TRANSFER-MOMENT-DUAL.md`**, which is the source-based proof. Do
not use my §4/§5 as evidence.

What I got wrong (retracted):

1. I claimed all four kernels **assert `z[eta] == 0`**. That holds for the three
   q0-family scripts (`certify_q0_moments.py` line 12, `certify_q0_closure.py`
   line 12, `certify_q0_lower375.py` line 12) but **not for q1**:
   `certify_shared_moments_dense.py` has **no** such assertion, and in the saved
   vectors `z[71] = 0`, `z[72] = 0.4374583364682675` (orbit A) and
   `1.3576794611063165` (orbit B) — so for q1 the slot-72 multiplier is `eta` and is
   strictly positive.
2. Hence my "the constant is radius-independent" is **wrong for q1**: with
   `z_eta > 0` the piece `+2 z_eta·asin(2R)` is radius-dependent and **increasing**.
   The correct sufficient statement is only: **`eta ≥ 0` makes the constant
   non-decreasing in `r`** (as the lead's note proves); my §4 term-by-term radius
   dependences remain valid as supporting detail.
3. The closure kernels' added `(hl + hr)·w/2` **requires `hl + hr ≥ 0`** for
   monotonicity. I listed it as radius-dependent only through `w` without proving
   that coefficient's sign; the lead's note supplies the closure positivity, and I
   do not re-derive it.
4. **`qmin` is not documentary.** In the closure kernels
   `qmin = 4 sin(π − 8 asin R)²/R²` is a **domain cut that moves with `r`**, so the
   transfer needs a nesting proof (the lead's note: `qmin` monotone decreasing on
   `sin(π/9) ≤ r ≤ 0.38`). My "taken as given" label is withdrawn.
5. **Area reading.** `2 r² Π sin` in the moment dual is the **area** (as the lead
   states), not twice the area; my attempted extra-factor-2 derivation is withdrawn.

Everything below is my earlier text; the unaffected parts (domains as supersets,
degenerate limits, graph enumeration, term-by-term radius dependences, the `C ≥ 0`
values) are supporting detail only, not the transfer proof.

Independent audit of the **class-complement** evidence for the global fixed-graph
reduction: the claims that leave `q0(6,7)` as the only surviving class for
`r ≤ 19/50`, namely C818 (all `q1`), C819 (`q0(4,9)`), C820 (closure identity,
used by k3/k4) and the two closure certificates
`q0_closure_dual_certificate_0_3.json` (k3 = `q0(5,8)` at `R = 19/50`) and
`q0_lower375_dual_certificate_0_4.json` (k4 = `q0(6,7)` at `R = 3/8`).

Scope per instruction: **not** a ledger restatement; the question is whether the
domains of the excluded classes really include the non-acute / degenerate /
low-bearing cases, whether the domains are the compatible legal ones, and whether
any numeric premise should be upgraded to **gap**. The fixed-oracle interface
(`closure-geometry/GLOBAL-ORACLE-INTERFACE-AUDIT.md`) stays **conditional**; nothing
here declares the whole chain sound. Only this report is written; the invalid
scratch scripts are quarantined in `closure-geometry/scratch-scaletest/`.

---

## 0. Answer in one paragraph

The exclusions are **over-approximations in the safe direction**: every factor
domain used is a superset of the images of the real (including non-acute,
degenerate and boundary-touching) configurations, infeasible combinations only
weaken the bound, and the degenerate limits (`α = π`, `α = 0`, `u = 0`, `v = 0`,
`b = 0`, `b = π/2` as a **domain box**, `q = 0`, zero circum-radius) lie in the
closed domains. Graph enumeration is anchored (each script asserts its face/edge
list against a reconstructed expected list). **The certificates are evaluated at a
single radius** (`R = 19/50`, or `3/8` for k4) while C818/C819/k3 claim
`r ≤ 19/50`; **the transfer is nevertheless immediate, because for each kernel every
radius-dependent term is non-decreasing in `r` and the constant term is
radius-independent** — this is the correct replacement for my earlier (invalid)
`−2πz_λ r` reading, and it is proved in §4. Consequences: C818/C819/k3/k4 keep
their status; the only items I would still label **gap** are documentary
(the `(71,72)` slot semantics differ between the two kernel families, and the
monotonicity argument, though one line, is nowhere written). The domain-superset
part is verified in §2 and holds for non-acute, degenerate and low-bearing cases.

---

## 0.1 Corrections (superseded by the status block above; kept for the record)

1. **Constant term — RETRACTED AGAIN.** There is indeed no `r`-multiplied penalty.
   But my claim that "`z[eta] == 0` is asserted in all four kernels" is **false for
   q1** (`certify_shared_moments_dense.py` contains no `z[eta]` assertion at all;
   its saved `z[71] = 0`, `z[72] = 0.4374583364682675` / `1.3576794611063165`), and
   therefore the constant's piece `+2 z_eta·asin(2R)` is radius-dependent and
   increasing for q1. The sufficient statement is **`eta ≥ 0`**, not `eta = 0`.
2. **Monotonicity direction.** I had written `dV/dr ≤ 0`; the correct requirement
   for an upper bound at `R` to dominate smaller `r` is `dV/dr ≥ 0`.
3. **Area formula — RETRACTED.** `2 r² Π sin` in the moment dual is the **area**
   (per the lead), not twice the area; my factor-2 derivation is withdrawn.

   The formula as it appears in the code is `2*R2*sn[0]*sn[1]*sn[2]` with the
   angles the three face angles and `x ∈ [0,1]` an independent relaxation scale
   (`shared_moment_dense.py` line 20); no factor `2` beyond the one written is
   asserted by me. The ring atom carries the moment terms `−x sin²(angle)` (and
   `−√x sin(angle)`) through the per-side `M[:,side+ee]` / `lin` slots.
4. **The `b`-domain.** `sin 2b ≤ 1` gives only `b ∈ [0, π/2]`, which **is** the
   script's box; it does **not** by itself imply the sharper covering bound
   `b_j ≥ acos(r)/2`. That sharper bound, if used, must come from the covering
   argument (a radius-`r` disk covers a unit-circle arc of length `≤ 2 asin r`, so
   the cone half-angle obeys `tan b ≥ r`); I have **not** verified that the
   certificates rely on it, and the switch factor's `x`-cap relaxation
   (`x ≤ min(1, cos²b/R²)` in the LP sampler; `[0,1]` in the interval kernel) is
   the only place the two could interact.

---

## 1. What each exclusion actually consumes

| class | claim | certificate file | evaluation radius | domain |
|---|---|---|---|---|
| all `q1` | C818 | `shared_moment_dense_certificate_0_4.json`, `..._2_4.json` | `R = 19/50` | faces (2 angles in `[0,π]`² with `α+β ≤ π`), 9 switches `b ∈ [0,π/2]`, 9 rings `(a,u,v) ∈ [0,π]×[0,1]²`; **no `eta` assertion** — `z[72] = 0.4374583365` (A), `1.3576794611` (B) is the `eta` multiplier |
| `q0(4,9)` | C819 | `q0_moment_dual_certificate_0_2.json` | `R = 19/50` | same factor shapes; **this** kernel asserts `z[eta] == 0` (`z[71] = 0.4828122595` carries the ring `w`-coefficient) |
| `q0(5,8)` = k3 | C820 + dual | `q0_closure_dual_certificate_0_3.json` | `R = 19/50` | face `(a,b)` with `a,b,c ≥ 0`, `Σ = π`; switch `b ∈ [0,π/2]`; ring `(a,u,v)`, `q ≥ qmin`; **no** `eta = 0` assumption needed — the added `(hl+hr)w/2` needs `hl + hr ≥ 0` (see the lead's note) |
| `q0(6,7)` at `r ≤ 3/8` = k4 | C820 + dual | `q0_lower375_dual_certificate_0_4.json` | `R = 3/8` | as k3 |

Recorded strict conclusions: `3.13549360...`, `3.13981254...`, `2.97871288...`,
`3.09579300...`, `3.10878894...`, all `< π`; the weakest is the q1 branch span 2 at
`3.1398125442` vs `π = 3.1415926536` (relative gap `5.7e-4`).

---

## 2. Domain audit — non-acute, degenerate, low-bearing

**(a) Non-acute faces.** Quotients are built from the *area/moment* identity
(equivalently `area = (R sin α)(R sin β)(R sin γ)/(4R)`), applied through the sine
factors `sin α sin β sin γ`; nothing uses `MEC = circumradius` (which needs
acuteness). The factor is a function of the two free angles with the third pinned by
`α+β+γ = π`, and the box admits `α+β ≤ π` — a superset that includes obtuse and
right triangles and the degenerate limit `α+β = π`. **Non-acuteness is covered.**

**(b) Degeneracies.** I evaluated the kernel independently
(`scratch-scaletest/check_scale_kernel.py`, 25-digit interval) at the limiting
points: ring atom `(α,u,v) = (π,1,1) → 0.1972901033`, `(0,1,1) → 0.0`,
`(π,0,0) → 0.0`, `(0,0,1) → 0.0326715807`; the `α = 0` and `u = v = 0` cases are
exactly `0`, consistent with `S = R²uv sinα/2 + (w−sin w)/2 + Cw`. The declared
domains include `α = 0`, `α = π`, `u = 0`, `v = 0`, `b = 0`, `b = π/2`, `w = 0`,
`2β = π` (switch), and the script's own `assert z[kap:lam].a >= 0` and its
`None`-on-negative-argument handling mean discarded boxes are simply never counted
against the total — the bound only weakens. **Degenerate cases are in the domain
and were spot-checked; no exclusion of a physically real degenerate configuration
was found.**

**(c) The one relaxation that is genuinely a superset.** In the switch factor the
admissible `x` (`x = sin² b` scaled) is enlarged from its actual cap to `[0,1]`;
the code says so, and this is a valid global relaxation. **This makes the bound
weaker, not wrong.**

**(d) Low-bearing.** The bearing parameter `b` is the *site-pair half-angle at the
switch*. What the certificate actually uses is **only the box `b ∈ [0,π/2]`** (the
scripts declare `(0, upperfloat(pi/2))`), and **nothing in the covering argument
justifies a narrower box of that form**: `sin 2b ≤ 1` bounds `b` above by `π/2`,
and the sharper covering fact that a radius-`r` disk covers a unit-circle arc of
length `≤ 2 asin r` (equivalently `tan b ≥ r`) bounds `b` **below** — it does not
produce an upper bound other than `π/2`. So the box `[0,π/2]` is a genuine
superset of the legal bearing range (`b > acos r/2` with the sine condition), and
using it is a safe relaxation: no spurious bearing premise is introduced, and the
high-bearing split (`b_j ≥ 1`, C848/C849/C861/C862) belongs to the *oracle* side
and is not consumed here. **Caveat:** because the box is a superset, these
certificates say nothing about whether the sharper legal bearing/sine constraints
would have sufficed; that is a strength question, not a soundness one.

---

## 3. Graph enumeration

* `shared_moment_dense.py` and `certify_shared_moments_dense.py` assert the
  face/edge lists against a reconstructed expected list, and the saved graph
  (`shared_moment_dense_0_4.json`) has 11 faces / 21 edges with the ear
  `(0,1,2)`, hubs 9,10, core `[0,2,3,4,5,6,7,8]` — matching the two `q1` orbits
  `{0,4}` and `{2,4}` referenced by C818. The ear is `(0,1,2)` and core
  `[0,2,...]`, so the two representatives do occur. **Enumeration is anchored.**
* `certify_q0_moments.py` asserts its graph is the k-fan form
  `(9,k,k+1),(10,k,k+1),(9,10,0),(9,10,span)` and that `z[η] == 0`; the saved graph
  for `(4,9)` is the `k=2` fan, as C819 states.
* The q0 **closure** scripts are a different kernel type (face `(a,b)` domain,
  switch/ring as above, `qmin` present), so their graph is consumed through the
  `h_i`-augmented formal assembly (`check_q0_closure_symbolic.py`), which I did not
  re-derive.

---

## 4. The transfer: pointwise monotonicity in `r` (proved)

**Setup.** Each interval script fixes `R` (`iv.mpf(19)/50`, or `iv.mpf(3)/8` for k4)
once and evaluates every factor box at that `R`; the conclusion is `total < π`. The
claims read `r ≤ R` (C818/C819/k3) or `r ≤ 3/8` (k4). The needed step is

```
   (T)   [ total(R) < π ]   =>   [ total(r) < π  for every 0 < r <= R ] .
```

**(T) holds, by pointwise monotonicity.** I read each kernel line by line. In each
kernel the reference radius enters **only** through the following terms; everything
else in the script (`z` values, node parameters `b`/`(a,u,v)`, all multipliers) is
radius-independent.

| kernel | radius-dependent terms | all other terms |
|---|---|---|
| `certify_q0_moments.py` (q0(4,9)) | `2*R2*sin(a)*sin(b)*sin(c)` (face); `R2*sin(2*b)/2` (switch); `w = 2*asin(R*sqrt(q)/2)` inside `quad(v, ...)` and `(w−sin w)/2 + C*w` (ring); constant `pi*(…) + 2*z[eta]*asin(2*R)` | radii, angles, `z`, `q`, `C` |
| `certify_shared_moments_dense.py` (q1 A/B) | identical list (line 42, 71, 81–84, 98) | same |
| `certify_q0_closure.py` (k3) | identical list (line 42, 74, 84–86), plus the **domain guard** `qmin = 4 sin(π−8 asin R)²/R²` (line 82) | same |
| `certify_q0_lower375.py` (k4) | identical list with `R = 3/8` | same |

**Line-by-line radius dependences and their signs.** For `0 < r₁ ≤ r₂ ≤ R`:

1. **Face.** `2 R2 sin a sin b sin c = 2 r² sin a sin b sin c` with
   `sin a sin b sin c ≥ 0` on the box `{(a,b) : a,b ≥ 0, a+b ≤ π}`; so it is
   non-decreasing in `r`. All other face terms (`sum(co[k]*ang[k])`,
   `sum(dd[k]*sin²)`, `sum(ll[k]*sin)`, and the `quad` bounds) contain no `r`.
2. **Switch.** `v = R2*sin(2b)/2 − d*sin²b + e` with `sin(2b) ≥ 0` on
   `b ∈ [0,π/2]`; the increase of `v` in `r` propagates through
   `quad(v, g sin b + h) = max(0, min(1, arg))²·v + (that arg)·(g sin b + h)`,
   which is **non-decreasing in its first argument** for fixed `(A,B)`
   (both `v ↦ (arg)²v` and the `max(0,·)`, `min(1,·)` operations are monotone).
3. **Ring.** `w = 2 asin(r √q /2)` is non-decreasing in `r` (the box enforces
   `r√q/2 ≤ 1`, i.e. `q ≤ 4/r²`, and `q ≤ 4` from the declared box), and
   `w ↦ (w − sin w)/2` has derivative `(1 − cos w)/2 ≥ 0`, so both `w`-terms are
   non-decreasing. The further terms `R2*u*v*sin(a)/2` (non-negative because
   `a ∈ [0,π]`, `u,v ∈ [0,1]`) and `C*w` with **`C ≥ 0`** are non-decreasing. The
   remaining terms `−mu*a − d u² − e v² − dl u − el v` are radius-independent, and
   for the closure kernels the added `β`-terms `(hl−hr)β − hr a + hr π + (hl+hr)w/2`
   depend on `r` only through the non-decreasing `w`.
4. **Constant.** `pi*(sum z[:9] + 2 sum z[9:11] + sum z[kap:lam] − 2 z[lam] − 2 z[eta]) + 2 z[eta]*asin(2R)`
   (and `− pi*sum(z[cl:])` for the closure kernels).
   **RETRACTED as written:** I claimed `z[eta] == 0` is asserted by every kernel.
   That is true only for `certify_q0_moments.py`, `certify_q0_closure.py` and
   `certify_q0_lower375.py` (line 12); the q1 kernel
   `certify_shared_moments_dense.py` makes **no** such assertion. What is actually
   needed and sufficient is **`z[eta] ≥ 0`**: then `2 z[eta]·asin(2R)` is
   non-decreasing in `R` along with everything else, which is what the lead's note
   `lead/RADIUS-TRANSFER-MOMENT-DUAL.md` proves. The q1 saved values
   (`z[72] = 0.4374583365`, `1.3576794611063165`) are positive, so they satisfy
   this; the earlier "the constant is radius-independent" sentence is withdrawn.
5. **`C ≥ 0`.** `C = z[71] + (z[72] if i ≥ 3 else 0)`; values from the saved
   vectors: `q0(4,9)`: `z[71] = 0.4828122594968165`, `z[72] = 0`;
   `q1 A`: `z[71] = 0`, `z[72] = 0.4374583364682675`;
   `q1 B`: `z[71] = 0`, `z[72] = 1.3576794611063165`;
   k3 and k4: `z[71] = z[72] = 0`.
   So `C ≥ 0` in all four kernels, with equality allowed and harmless (the `Cw`
   term is then absent). The scripts additionally assert `z[kap:lam] ≥ 0`.
   **Caveat added:** for the closure kernels the extra `(hl+hr)w/2` needs
   `hl + hr ≥ 0`, which I do **not** prove here (the lead's note supplies the
   closure positivity).

**Conclusion.** Every summand of the total is a non-decreasing function of the
reference radius, and the per-box upper-bound function used by the branch-and-bound
is non-decreasing in `r` **on the same box** (the boxes are radius-independent:
they are the declared domains `[0,π]²`, `[0,π/2]`, `[0,π]×[0,1]²`). Therefore

```
   total(r) <= total(R) < π      for every 0 < r <= R ,
```

so the certificates' strict inequalities transfer to the full claimed range, and
C818/C819/k3/k4 keep their status. **No downgrade.**

**One caveat that must be stated (closure kernels only).** In
`certify_q0_closure.py` / `certify_q0_lower375.py` the domain guard
`if q.b < qmin.a: return None` has `qmin = 4 sin(π − 8 asin R)²/R²`, which **does**
depend on `R`; a discarded box is omitted from the heap rather than evaluated. This
does not affect the transfer of the *bound* as long as `qmin` is a valid necessary
cut for the true class: for the real configuration at radius `r` one has
`w ≥ 2π − 16 asin r` (the owned widths sum to `2π` with all owned widths
`≤ 2 asin r`), and `w = 2 asin(r√q/2)` together with `q ≥ qmin` is the kernel's
encoding of that. Since `qmin` is monotone in `R` (it decreases as `R` grows) and
the certificate is run at `R = 19/50`, the guard is applied at the weakest radius,
which is the direction that keeps the largest set of boxes — i.e. it can only cost
efficiency, not soundness. **What I did not re-derive is the `qmin` algebra itself**
(that `q ≥ 4sin²(π−8asin r)/r²` really is the exact translation of the width
bound); that belongs to the closure certificate's own kernel audit
(`CLOSURE-KERNEL-ANALYTIC-AUDIT.md`), and I flag it as the residual documentary
gap in this family.

**Remaining documentary gaps (not mathematical):**

1. the `(71,72)` slot semantics differ between the two kernel families
   (`certify_q0_moments.py` uses `C = z[71] + (z[72] if i≥3 else 0)` and asserts
   `z[72] == 0`; `certify_shared_moments_dense.py` uses `C = z[72]` with no
   `i≥3` restriction). Both readings give `C ≥ 0` and a radius-independent
   constant here, so the conclusion is unaffected — but the convention should be
   written down once.
2. the one-line pointwise monotonicity argument of this section is nowhere stated
   in the audited notes; it is what makes the single-radius evaluation of C818,
   C819, k3 and k4 sufficient for their stated `r`-ranges.
3. the `qmin` translation (above) is taken as given.

**Invalid diagnostics.** The earlier `scaletest_*` / `SCALETEST_*` runs in
`closure-geometry/scratch-scaletest/` must not be cited: they re-used multipliers
fitted at `R = 19/50` at other radii (where dual feasibility is not certified) and
were motivated by my incorrect constant. They are retained only to document the
error.


---

## 5. Bounded audit of the single most dangerous dependency

**Choice: the `r`-transfer of `q0(4,9)` (C819) together with the `C ≥ 0` input it
shares with the q1 pair.** Rationale for choosing it: C819 is the exclusion that
leaves `q0(5,8)`/`q0(6,7)` as the only survivors, and its kernel is the only one
whose ring `w`-coefficient is carried in slot 71 (`C = 0.4828122594968165`)
rather than slot 72 — i.e. it is the family where a slot misreading would change
the conclusion, and it is also the family whose multiplier is farthest from zero.

What I did (bounded, no history re-read):
(i) read `certify_q0_moments.py` lines 8–12, 30–32, 34–66, 68–75, 76–97 and 99
line by line; (ii) transcribed the exact constant from line 99 and confirmed
`z[eta] == 0` is asserted; (iii) confirmed `C = z[71] + (z[72] if i≥3)` with
`z[71] = 0.4828… > 0` from the saved vector, and the same check for the other
three kernels; (iv) verified each radius-dependent term's sign as listed in §4.
**Outcome: no gap in this dependency's transfer; the constant has no `r`-factor
and `z[eta] = 0` makes it radius-independent.** The residual items are the
documentary gaps of §4 (`(71,72)` slot semantics; the monotonicity argument not
being written down; the `qmin` translation not re-derived). My earlier claim that
this dependency needed a new argument rested on a misread constant and is
withdrawn.

---

## 6. Itemised status

| # | item | status |
|---|---|---|
| 1 | factor domains are supersets of the real (non-acute, degenerate) class domains | interface-level verified |
| 2 | degenerate limits lie in the closed domains and give finite, consistent values | verified at spot points (§2b) |
| 3 | no high-bearing premise is used by these certificates | verified (§2d) |
| 4 | graph enumeration + orbit coverage `{0,4},{2,4}`, k-fan forms | verified in scripts + saved graphs |
| 5 | infeasible combinations only weaken the bound (`None`-handling, `x`-cap relaxation) | verified in code |
| 6 | bound `< π` **at `r = 19/50`** for q1 (both orbits), `q0(4,9)`, k3; `< π` at `r = 3/8` for k4 | **proved-interval** (scripts + saved certs) |
| 7 | **transfer to `r ≤ R`**: every radius-dependent term non-decreasing in `r`; constant non-decreasing because `z[eta] ≥ 0` | **proved in `lead/RADIUS-TRANSFER-MOMENT-DUAL.md`** (my §4 has the term-by-term dependences but the `z[eta] = 0` claim inside it is retracted) |
| 8 | `C ≥ 0` for the ring `w`-coefficient in all four kernels | verified: `z[71] = 0.4828122595` (q0(4,9)); `z[72] = 0.4374583365`, `1.3576794611` (q1 A/B); `0,0` (k3,k4) |
| 9 | `(71,72)` slot semantics identical across kernels | **GAP (documentation)**: `q0_moment*` uses `C = z[71] + (z[72] if i≥3)`, `shared_moment*` uses `C = z[72]`; both give `C ≥ 0` |
| 10 | pointwise-monotonicity argument written down in the notes | **closed by `lead/RADIUS-TRANSFER-MOMENT-DUAL.md`** |
| 11 | the `qmin` algebra (`q ≥ 4sin²(π−8asin r)/r²` = width bound) **and its `r`-nesting** | **NOT documentary**: the cut moves with `r` and needs a nesting proof (monotonicity of `qmin` on `sin(π/9) ≤ r ≤ .38`); addressed in the lead's note, and the object identity is the subject of `QMIN-OBJECT-IDENTITY.md` in this directory |
| 12 | C820 closure identity used by k3/k4 | reviewed earlier (C820 review history on this id); its exactness at degenerate/boundary ties was checked then |


---

## 7. Files

**Transfer proof (authoritative): `lead/RADIUS-TRANSFER-MOMENT-DUAL.md`** — the
constant's `eta ≥ 0` monotonicity, the closure `z` positivity, and the `qmin`
monotonicity on `sin(π/9) ≤ r ≤ 0.38` are proved there; my §4/§5 sentences are
retracted in favour of it.

Audited here: `certify_shared_moments_dense.py`, `certify_q0_moments.py`,
`shared_moment_dense.py`, `shared_moment_dense_certificate_0_4.json`,
`shared_moment_dense_certificate_2_4.json`, `q0_moment_dual_0_2.json`,
`q0_moment_dual_certificate_0_2.json`, `q0_lower375_dual_certificate_0_4.json`
(plus the `q0_closure` certificate totals), `Q1-BALANCED-EXCLUSION.md`,
`SHARED-MOMENT-DUAL.md`, `Q0-DEGREE4-EXCLUSION.md`, `Q0-CLOSURE-EXCLUSIONS.md`,
`CLOSURE-KERNEL-ANALYTIC-AUDIT.md` (totals only); claims C818, C819, C820 read in
full via `claim_get`.

My diagnostics (not evidence): `closure-geometry/scratch-scaletest/` — the scaled
copies `scaletest_*.py`, their `SCALETEST_*.json` totals, and
`check_scale_kernel.py`, `check_monotone_r.py`, `check_zsigns.py`.

No claims registered; no subagents; no lead file modified (the scaled copies and
their outputs were written to `closure-geometry/scratch-scaletest/`).
