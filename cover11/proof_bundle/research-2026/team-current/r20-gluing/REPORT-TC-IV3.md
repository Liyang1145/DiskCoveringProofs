# R20-TC-IV3 — independent full-12D interval enclosure of the symmetric TC KKT root
### (r20-gluing, cline2 / DS v4.1f · own file set · **no claim registered** · no lead/historical file touched)

Supersedes the enclosure *reading* of `r20_tc_iv2.py` on four load-bearing points (box endpoints,
recorded precision, π-mapping shape, endpoint-comparison semantics). The iv2 script itself is left
in place as history; nothing in it is deleted or rewritten.

---

## 0. Answer to the instruction (short)

| question asked | finding | evidence |
|---|---|---|
| does `lambdify` handle **rational constants** as enclosures? | In the compiled family they never become floats: all rational coefficients in the 285 trees are **dyadic** (no 1/3-type constant anywhere), and Python 3 prints them as `(1/2)`, `(1/4)`, i.e. exact binary. Zero `Float` nodes in the trees. | probe Q1 (`r20_tc_iv3_probe.json`) |
| does it handle **π** as an enclosure? | For *these* expressions π **never reaches the backend**: 0 of 285 generated sources mention `pi` (SymPy folds `sin(π−2σ)→sin 2σ`, `cos(π−2σ)→−cos 2σ`, and `ρ₄=cos a₄−√(R²−sin²a₄)` → `−cos2σ−√(R²−sin²2σ)`). The mapping that *would* be used is nevertheless the wrong shape: `iv_modules()['pi']` is a **0-arg function**, while the printer emits the bare name `pi` — a control expression with a surviving π raises `NotImplementedError` (fail-loud, no silent wrong value). Fix: map `'pi' → iv.pi` (scalar, correctly rounded outward). | probe Q2/Q3 |
| is the constant slip load-bearing? | **For the object: yes.** Variant model with π replaced by binary64 3.141592653589793 shifts `F(c)` by **4.71e-15** — 4.7× the size of the residuals themselves (~1e-15) — and moves `Q` in the 7th digit. **For the inclusion: no** (the variant still certifies; slack is 1e-9). So exact π/rational handling is required to certify the *intended function*, not to make the inclusion work. | probe Q3, iv3 `control_engines.wrong_pi` |
| iv2 box endpoints | **Confirmed defective (lead's reading).** iv2 built `mpf(c_hex)±mpf(rad)` at the *default* `mp.dps = 15`, i.e. rounded mpf arithmetic, not iv: per-coordinate defect up to **2.72e-17 outward / 5.26e-19 inward** (5.3e-10 of the 1e-9 radius). Rebuilt with iv-only ops (`iv.mpf(float.fromhex(hex)) + iv.mpf([-rad,rad])`): defect **exactly 0** at dps ∈ {25,30,40}, verified in exact rational arithmetic. | iv3 `box` |
| endpoint accessor semantics | `ivmpf.a`/`.b` are **degenerate ivmpfs**, not mpf; `mpf()` of a non-degenerate interval raises; comparisons on non-degenerate intervals can return `None` (silently falsy). iv1/iv2's diagnostics happened to be on degenerate endpoints, so they were not numerically wrong — but every comparison in iv3 extracts endpoints from `_mpi_` into `Fraction`s instead. | probe Q4 |
| recorded precision | iv2's JSON says `iv_dps: 30` while its box/J arithmetic ran at 40 (the value was read back *after* importing `tc_s33_kkt`, which sets `iv.dps = 30`). iv3 sets `iv.dps` after all imports and records the precision that actually produced the certificate. | iv3 `iv_dps_primary` |

---

## 1. What is certified, and at which level

**Object.** `F : R¹² → R¹²`, `x = (a₀,a₁,a₂,a₃,y₀,y₁,R, λ₀…λ₄)`:
`F = ( f₀…f₄ , δ_{i,6} − Σ_m λ_m ∂f_m/∂x_i )`, with `f_m` the 5 independent TC residuals
(`tc_s32_kraw.res5`, C366) re-derived from the explicit geometry in `r20_tc_iv1.symbolic_res5`.

**Box.** the lead's `repaired_tc_krawczyk.json` centre hex / radius hex reused verbatim
(`radius_hex = 0x1.12e0be826d695p-30`, exact value 4835703278458517 / 4835703278458516698824704
≈ 1.0000000000000000623e-9); **not enlarged**.

**Theorem used (one-box Krawczyk).** If `J(U)` encloses `F'(U)`, `Y` is any fixed real matrix,
`Q := ‖I − Y J(U)‖_∞ < 1` and `K := c − Y F(c) + (I − Y J(U))(U − c) ⊂ int(U)`, then `F` has
exactly one zero in `U`, and it lies in `K` (proof: `g(x)=x−YF(x)` is a `Q`-contraction mapping
`U` into `K`; `Q<1` makes `YJ(U)` invertible, hence `Y` nonsingular, so zeros of `F` in `U`
coincide with the unique fixed point of `g`).

**Verified hypotheses (all exact-rational comparisons).**

| quantity | value | status |
|---|---|---|
| box ⊇ exact box `[c_i−rad, c_i+rad]` | defect **0** (exact) | ✔ |
| all 10 sqrt arguments `R²−sin²a_k`, `R²−d²` > 0 on `U` | min `1.0931e-3` | ✔ (⇒ `F ∈ C¹` near `U`) |
| **5 outer-distance radicands** `dx²+dy²` (4 corner rows + waist) | strict rational lower bounds `0.14438765239459 … 0.14438772446269`, `min = 0.14438765239459 ≈ R²−O(1e-9)`; independent lead reading `> 0.14` (`lead/tc_root_geometry.json`) | ✔ (added 20:18; `C¹` item) |
| `Q` | `3165917149883075392461318896747212561595468071 / 730750818665451459101842416358141509827966271488` = **0.004332416836240972** < 1 | ✔ |
| `K − c ⊂ int(−rad, rad)`, all 12 coords | max `‖K−c‖_∞ = 4.3324275e-12` (0.43 % of the radius); **min slack = 9.9566757e-10** = 99.57 % of the radius, with the **corrected** exact-rational definition `min(rad + lo, rad − hi)`; the withdrawn definition `min(rad − lo, rad − hi)` gives the same `slack_min` and overestimates by at most `3.486e-17` (report bug only). New self-check `slack_i > 0 ⟺ inclusion on coordinate i` holds for all 12 | ✔ |
| same verdict at `iv.dps = 30` and `25` (same box, same `Y`) | Q and all slacks identical to 10 digits | ✔ not a precision artifact |
| instrument calibration: lead `J12_iv` + lead `Y` → my `Q` pipeline | `0.0043719716217` = their reported value | ✔ (known-answer check) |

**Controls that must fail** — both fail: λ₀ shifted by +1e-2; `F(c)` shifted by 1e-3 in one row.
Diagnostic: radius × 4 ⇒ `Q = 0.0173296813` (contraction grows as it must).

**Evidence level: `proved-interval`** — no conditional leg left for the source identity:
* rigorous: box containment, `J(U)` enclosure (tree-walk interval arithmetic with exact rationals,
  `Pi = iv.pi`, `Float` = hard error), `Q<1`, `K ⊂ int U`, sqrt-positivity (10 original arguments
  **plus** the five outer-distance ones added in the 20:18 revision), the Banach argument;
* source identity: `r20_tc_iv1.symbolic_res5` **is** `tc_s32_kraw.res5` — proven at the
  *assignment* level by the lead in `lead/TC-ROOT-SOURCE-IDENTITY.md` (same a₄ = π−2Σ, same
  reflected-9-angle table, same ρ/θ two-stage recurrence, same C/U definitions, same five output
  rows; the only textual difference is kraw's `half = mpf('0.5')` versus iv1's `(y0+y1)/2`, and
  that `half` is exactly the dyadic `1/2`). The former "checked-numeric (**not** a proof)"
  wording is therefore retired; this round did **not** re-prove the identity by CAS. The numeric
  agreements (point agreement to 4.3e-50, interval overlap with the lead's `J12_iv` **35/35**
  first order / **49/49** second order, `F(centre)` within 6.1e-40) are now supporting controls
  only.

**Two engine representations** (same model, different evaluation path): hand-written strict
tree-walk vs `lambdify` with the fixed scalar-π mapping — overlap **35/35** and **0/49**
second-order non-overlaps, max endpoint spread 1.84e-40.

**`Y` — honest note (corrected after direct check).** `Y` was recomputed from my own midpoint
Jacobian (own derivatives, `mp.dps = 60`; `cond₂ = 1433.8`). Compared with a lead-style `Y`
(their AD): scripted comparison at `mp.dps = 65` gives **0.0** entry difference; an alternative
evaluation route (mpf-tree at the point, then float) gives ≤ **1.1e-15**. So the two preconditioners
are the same matrix up to rounding, and this leg adds **no** independence — stated explicitly
rather than claimed as independent. It is not needed either: `Q < 1` proves `Y` nonsingular by
itself (`‖I − YJ(U)‖_∞ ≤ Q < 1` ⟹ `YJ(U)` invertible ⟹ `det Y ≠ 0`).

**Instrument calibration on a known answer.** Feeding the **lead's** `J12_iv` (with their box λ) and
their `Y` through my exact-rational `Q` pipeline reproduces the lead's reported contraction:
`0.0043719716217` vs their `0.00437197162167…`. With my tree-walk `J(U)` the same pipeline gives
`0.004332416836240972` (**0.91 % tighter**). The difference is therefore attributable to the
`J(U)` enclosure (dependency in the AD form; second-order block centres agree to 1.9e-11), **not**
to `Y` — with the lead's `Y` on my `J(U)`, `Q = 0.004332416836240972` (12th-digit change).

**Root data reproduced.** `R = 0.3799838531198386897222616061360932143087189561522153170163879`
(C249-consistent), and the certified enclosure `c + K` has half-width ≤ 4.34e-12.

---

## 2. Scope guards (what this does **not** say)

* One box only; **no** multi-box / branch-and-bound, no global rank or independence statement.
* **No** covering-radius, no optimality, no statement about `r_D(11)`; the unconditional n=11
  global problem stays open — a local root certificate is not a completion.
* No geometry/gluing claim beyond the explicitly written 12D system; C408's old withdrawal stands.
* `r20_tc_iv2.py`'s numeric readings (Q = 0.00433242…, `K−c`≈4.3e-12, `F(center)` 5.7e-40) are
  *reproduced* by iv3, but iv2's **box**, **recorded precision** and **π-mapping** statements are
  superseded by §0 — do not re-cite them.

## 3. Repro / paths

```
py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_iv3_probe.py   # source+constant audit (~7 s)
py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_iv3.py         # the enclosure (~24 s)
```
Evidence: `r20_tc_iv3.json` (certificate + exact `Q` rational + controls + hashes),
`r20_tc_iv3.log`, `r20_tc_iv3_probe.json`. Model source: `r20_tc_iv1.py` (hash recorded).
Read-only inputs: `team-current/lead/repaired_tc_krawczyk.json`, `lead/repair_tc_krawczyk.py`,
(`tc_s33_kkt.J12_iv` only as a control).
