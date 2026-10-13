# Audit — lead/certify_middle_inward.py (C844 filter, corner formula, storage)

Read-only audit. No lead file modified. Checked against the running objects
(`middle_inward_frozen.json`, sha256 `17a0225e7fc329b54c78e5dab04b7f1dff30c61c721f81659d6c92aee4ad139d`)
and the per-factor outputs `middle_inward_bound_*.json`.

## Verdict

* **Filter (lines 15-17): sound.** No defect found.
* **Raw/full-box return and storage (lines 18, 30-46): sound.** No defect found.
* **Corner formula (lines 20-23): NOT a valid upper bound for factor 22 as used.**
  One concrete discrepancy, quantified below. This is the item to act on.

## 1. Concrete discrepancy — the corner is not a bound for the 3-D factor

`factors[22]` is overwritten (line 23) by the 1-D formula
```
corner(t) = (w−sin w)/2 − z[2]·π − (z[36]+z[37])·t² − (z[98]+z[99])·t + (z[71]+(z[113]+z[114])/2)·w,
            w = 2·asin(R·t),   domain [75/76, 1].
```
**Its coefficients are correct**: I verified index-by-index that `z[2]`, `z[32+2i]=z[36]`,
`z[33+2i]=z[37]`, `z[94+2i]=z[98]`, `z[95+2i]=z[99]`, `z[71]`, `z[113]`, `z[114]` are exactly the
quantities the kernel's ring-2 functional uses (`mu,d,e,dl,el,C,hl,hr` with the kernel's own
index map). On the slice α = π, u = v = t the corner value **equals** the ring functional
(checked: max difference 0; e.g. t = 1: corner = −2.708925639, ring22(π,1,1) = −2.801821339 —
and the corner is *above* it, so it is a valid slice bound).

**But the bound actually stored is the wrong endpoint of that slice.** The script's B&B maximises
`corner` over `t ∈ [75/76, 1]`, and `corner` is decreasing in `t`:

```
stored bound for factor 22 (middle_inward_bound_22.json) = −2.708920648   (= corner(1))
max_t corner(t) on [75/76,1]                             = −1.552226299   (= corner(75/76))
```

The factor that is actually being certified is the **3-D** ring-2 residual, because the filter
only deletes boxes that are *entirely* infeasible; it never restricts `α`. Numerically the
supremum of the ring-2 residual over the admissible domain (C844 constraint satisfied) is

```
sup over admissible domain = −1.087632095   at (α, u, v) ≈ (0.5952, 0.1927, 0.2175)
stored bound               = −2.708920648
stored − sup               = −1.621289      -> the stored value is below an attained value
```

Even on the *looser* domain "filter does not delete the box" the sup is ≈ −1.09; even without the
filter the sup is ≈ −0.070. So the stored per-factor bound is lower than achievable values of the
ring-2 residual by **≈ 1.62**.

**Effect on the total:** the assembly is `constant + Σ per-factor uppers` with
`constant = 2.455913155`. Summing the 29 values recorded in
`middle_inward_exchange_refined_history.json` (round 14, `factor_values`) gives 0.685316884, and
`2.455913155 + 0.685316884 = 3.141230033` = the reported numeric total. Using sound per-factor
uppers instead (replacing factor 22's −2.7089 by the admissible sup ≈ −1.0876, and noting that
rings 20/24 ended on the 200 000 budget) the total is **larger** than 3.141230033, i.e. the
numeric total is not reproducible once factor 22 is bounded correctly. In particular
`2.455913155 + 1.353699551` (sum of the 25 actually-written bounds) = **3.809612706 > π**.

**Action required:** factor 22 must be bounded on the full 3-D domain (i.e. keep the ring-2
functional and let the C844 filter prune), or the corner must be combined with a proof that the
admissible domain collapses to the slice `{α = π, u = v = t}` (it does not: the filter's condition
`uv(k sin α − h cos α) ≥ max((75/76)²,u²,v²)·h` holds on a 2-parameter family, see the argmax
above with `α ≈ 0.595`). Using the *slice value at the correct endpoint* (−1.5522) would be a
valid slice bound but is still below −1.0876, so it is not sufficient either.

## 2. Filter soundness (lines 15-17) — checked, no defect

* `q` uses the cancellation-free form and is clipped to `[0,4]`; on `α∈[0,π], u,v∈[0,1]` this is
  lossless (it clips only outside the box).
* `h = R√q/2`, `k = √(1−h²)` are monotone/valid because `h ≤ R < 1`.
* `lhs = u·v·(k sin α − h cos α)` is evaluated as a full interval product, so
  `lhs.b ≥ max` of lhs over the box. It is **not** monotone in `h` for all `α`
  (`∂lhs/∂h = −uv cos α` changes sign), so an endpoint-only evaluation would have been wrong —
  the interval product used here is the safe route. ✔
* `m = I(max((tmin·tmin).a,(u·u).a,(v·v).a), max(...b))` is a valid enclosure of
  `max((75/76)², u², v²)`, and `(m·h).a ≤ min over the box of max(...)·h` since `h ≥ 0`. ✔
* Discarding only when `lhs.b < (m·h).a` means: no point of the box satisfies the necessary
  condition `lhs ≥ max(...)h`, so no admissible point is lost. ✔ The strict `<` is the safe
  direction.
* Consistency with `INWARD-SECTOR-COUPLING.md` lines 11-15: `pq sin α ≥ r² sin(w/2)` gives
  `uv(k sin α − h cos α) ≥ (r/R0)²h`, and `r ≥ max(p,q)`, `r/R0 ≥ 75/76` give the RHS bound.
  Note `(75/76)² = 5625/5776 = 0.9738573407202216 = (0.375/0.38)²` **exactly**, so the
  `(75/76)²` slack is used up entirely at `r = 0.375`; the filter stays sound but has no margin
  there.
* One soft spot: the filter's necessary condition also needs `sin(α − w/2) ≥ 0`, which holds on
  admissible points because `w < α`. The filter does not enforce it, but it is only used as a
  *necessary* condition, so this does not weaken soundness. Recorded for completeness.

## 3. Full-box raw return, storage, budget exit — checked, no defect

* `filtered` returns `raw(box)` untouched when the box survives, so the raw objective still
  encloses the **full** box (its own `qmin` test is the only internal rejection). Partially
  infeasible boxes are therefore still bounded, as intended ("return full box raw even on
  partially infeasible boxes"). ✔
* `upper = max(discarded, live heap max)` (line 46): every discarded leaf had
  `upper < lower` at discard time, and `lower` is a feasible point value, so
  `max(discarded, live)` still bounds every leaf of the final cover. ✔
* Budget exit: the `while` condition carries `count < 200000`, so exhaustion leaves the heap
  intact and line 46 returns a sound (loose) upper bound with `budget_ended: true`. ✔
  Currently `ring0` and `ring4` both exited on budget (200001 evaluations), so their stored
  uppers are loose.
* Outward float handling (`upperfloat`/`lowerfloat`) and the digest guard on re-entry (line 27)
  are fine.

## 4. Secondary observations (not defects)

* The filter leaves the box `[0, π] × [0, 1]²` in place, so for the ring factors the derivative
  clip at the kernel's line 91 (inherited via the truncated source) is still evaluated on boxes
  where `|∂w/∂α|` can exceed `L = R/√(1−R²)` (up to ≈1.18 at `α≈0.1225, u=v=1, q≈qmin`). My
  box-level tests (box widths 1e-3…5e-2) showed the returned interval still enclosed the true
  pointwise sup because the direct enclosure dominates, but this is worth an explicit lemma if
  the corner/ring certificate is to rest on the clipped gradient.
* `corner` hard-codes `i = 2` and the domain `[(lf(tmin), 1)]`, so re-running the script for a
  different factor index would silently keep the ring-2 corner. Add an index argument or an
  assertion if the script is reused.
* `middle_inward_frozen.json` carries `numeric_total = 3.14123003341214`, which matches the
  round-14 `continuous_numeric` in the exchange history; both are built from the *optimizer's*
  per-factor values, not from the interval bounds in `middle_inward_bound_*.json`, so the file's
  total should not be read as a certified value.

## Repro

```
cd research-2026/team-current/cline2-closure-kernel
py -3 middle_inward_audit.py        # corner vs 3-D sup, assembly
py -3 corner_soundness_quant.py     # sup over the filtered domain vs corner
py -3 ring2_bound_vs_sup.py         # tight sup (−1.0876) vs stored (−2.7089)
py -3 assemble_middle.py            # constant + Σ written bounds = 3.8096
```
