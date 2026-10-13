# R17 source audit — ridge rank-one tangent certificate (C867)

Read-only. No lead file modified. Scope: `RIDGE-RANK-ONE-COUPLING.md`,
`ridge_tangent_jet.py`, `certify_ridge_tangent.py`, `patch_smooth_jet.py`,
`ridge_split_control.json`, `ridge_tangent_certificate.json`.

## Verdict

**Approve with scope.** No algebraic flaw found in the decomposition, the tangent direction, or
the component interface. Two language/coverage caveats are recorded below. My earlier numeric
probe failures were **my own interface errors** (`old.objective(box).b` on a `Jet`; then
`I(str(r))`), not kernel defects — the lead's 30-point calibration plus the module identity check
already cover that interface.

## 1. Decomposition — correct, including the coefficient swap

`G = K(r) + F1 + F2 − r² sin(2T)`, `T = b1+b2`, with the swap (`b1` gets `z3−z9`, `z20`, `z82`;
`b2` gets `z1−z9`, `−z16`, `−z78`) is exactly what `ridge_tangent_jet.component` implements:

* `j=0`: `bb,gg,aa = z[20], z[82], z[3]−z[9]`
* `j=1`: `bb,gg,aa = −z[16], −z[78], z[1]−z[9]`

and the trig identity that produces the swap,
`4 sin(b1+b2) sin b1 sin b2 = sin 2b1 + sin 2b2 − sin 2(b1+b2)`, is asserted exactly
(`sympy.trigsimp(..., method='fu') == 0`) in `check_ridge_split.py:10`. The hub-angle terms
cancel against the δ-linear term as the note states.

**Verified independently:** for 40 random legal points (r∈[0.375,0.38], b∈[1,acos0.375],
w∈[0.66,0.76]) I evaluated `patch_ridge_jet.objective` and
`constant(r) + component(·,0) + component(·,1)` and found
`worst |split − old_ridge| = 3.35e-17` — the identity holds to rounding, not merely up to the
`±inf` interval bracket that `check_ridge_split.py` asserts.

## 2. Tangent direction — correct

`h(T) = −sin 2T` on `T ∈ [2, 2acos(0.375)] = [2, 2.372799104599]`, so `2T ∈ [4.0, 4.745598]`
⊂ `(π, 2π)` and

```
h''(T) = 4 sin 2T ;  grid min −4.000000000, grid max −3.027209981   (strictly NEGATIVE)
```

so `h` is strictly **concave** there — the note's claim is right. With `τ = 87/40` (exact
rational, `2τ = 4.35`, `cos 2τ = −0.354509065048`, `h'(τ) = +0.709018130096`):

```
max_T [ h(T) − (h(τ) + h'(τ)(T−τ)) ] = −7.76e-13 ≤ 0
```

i.e. the tangent line lies **above** `h` (it only touches at τ; at the ends the gap is
−5.42e-02 and −7.58e-02). Hence the kernel's gap
`g = r²[h(τ) + h'(τ)(T−τ) − h(T)] ≥ 0` and subtracting it — as
`constant + Σ components` does — is the **correct direction** for an upper bound. The sample
gaps in `ridge_split_control.json` are all strictly positive (0.000152…0.001661), consistent.

**Exact-bearing-gap.** The one place the certificate leaves slack is this tangential gap:
`g` is non-negative, so the certificate bounds `G` from above but the tangential slack is
real. Sampled magnitude of `g = r²·Δ(T; τ)` with `Δ ∈ [0, 7.58e-02]` and `r² ∈ [0.1436, 0.1444]`:
**at most ≈ 1.09e-02** over the ridge domain, vanishing at `T = τ` (which is why the search
around `T ≈ 2.175 = τ` is where the certificate is tightest and where any true maximum must be
sought). At the report's own margin `28.107045 − 28.106900595 = 1.44e-04`, the tangential slack
is ~76× the available margin, so **tightening τ (or infimising over τ) is the natural next
lever** if the ridge certificate ever needs to sit closer to the target.

## 3. Component AD interface — sound as a full-extension MVT

* `patch_smooth_jet.Jet` carries value + 7 first derivatives; `component` builds jets only for
  `(r,b,w)` with identity derivatives for those three coordinates and zero elsewhere, so the
  gradient columns used in the MVT are exactly `∂/∂(r,b,w)` of the component — the other
  physical coordinates enter only through the fixed relation `H = 2r sin(b1+b2)` and
  `δ = b1−b2`. ✔
* **No physical clip touches the derivative path.** Lines 15 clamp only `den.v` and `q.v`
  (`I(max(den.v.a, gap.a), den.v.b)` and likewise `q.v`), never `den.d`/`q.d`; the derivative
  slots are built from the unclipped analytic expressions. Same pattern in
  `patch_smooth_jet` (its `objective` raises `Unsafe` when `den.v.a <= 0` rather than clipping
  the derivative). This is precisely the stated "full analytic extension for MVT, never physical
  clipping in derivatives". ✔
* `bound` guards are necessary condition only: `cos b ≥ r` (line 25) is the high-bearing
  condition `b ≤ acos r`; `(q.v − r²).a > 0` rejects only when the whole box violates `q ≤ r²`
  (the inradius constraint `u ≤ r`). Both are correct necessary filters. ✔
* `min(uf(f.v), uf(mv))` takes the smaller of the direct enclosure and the MVT enclosure; both
  are upper bounds, so the minimum is one — sound, and it explains why `upper` for the
  components is negative while the true component maximum is positive (the tangent split
  supplies the positive part through `constant`). ✔

## 4. Assembly and pins

* `certify_ridge_tangent.py:28`: `total = uf(constant(I(*dom[0])) + Σ I(component uppers))`.
  `constant` itself is an interval; the certificate stores it as a string interval
  `[28.199958585, 28.201563872]`, sum of component uppers `−0.094663277`,
  `constant_lo + Σ = 28.105295307`, certificate `upper = 28.10690059505904`.
  Margin to 28.107045: **1.44e-04** (lead's assembled margin 0.0001448207 — consistent, the
  small difference is which endpoint of the constant interval is folded in).
* Source pins all **match on disk**: `ridge_tangent_jet.py 28c32cfbf731`, `certify_ridge_tangent.py
  298bed95f61e`, `patch_smooth_jet.py 0ea533809a58`, `interval_joint_patch.py 274749214594`.
* `coefficient_sha256` `5671967c5a3df341…` = current `joint_nested_frozen.json`. ✔
* Components: `j=0 count=817 live=0 upper=−0.047821`, `j=1 count=831 live=0 upper=−0.046842`.
  Zero live boxes ⇒ these are valid **upper bounds** on the components over the covered boxes
  (not attained maxima) — same language caveat as C863.

## 5. Caveats (scope / language only)

1. **Scope.** Ridge only (`δ = b1−b2`, `H = 2r sin(b1+b2)`), high-bearing `b1,b2 ≥ 1`,
   `r ∈ [0.379,0.37999]`. The note itself states it does **not** assert all maxima lie on the
   ridge (C867's own next obligation is the non-ridge part). C868's new face stationary
   counterexample affects the face closure obligation, not this certificate — agreed.
2. **Zero live boxes ≠ attained maximum.** As with C863, `live=0` shows the search terminated
   with every remaining box below the component threshold; the numbers are upper bounds.
3. My probe scripts (`r17_final_check3.py`, `r17_search_fixed.py`, `r17_concise.py`) are
   **not** evidence: the first two fail on my own Jet/interval misuse and the third was stopped
   on instruction. Recorded as instrument failures, not theorem flaws.

## 6. Exact statements I will stand behind

* Decomposition identity `constant + Σ component_j = G_ridge + g` with `g ≥ 0` — exact
  (trig identity + numeric check at 3.3e-17).
* `h` strictly concave on the range; tangent lies above `h` (`max residual −7.8e-13 ≤ 0`);
  bounded tangential gap `≤ 1.09e-02` in magnitude over the ridge domain.
* Pins and constants as in §4.
* Nothing here is a statement about non-ridge maxima or about the target 28.107045 being reached.
