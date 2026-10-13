# C450-KERNEL-SCOPE-AUDIT — atom → (10+1) exclusion scope, and both kernels' scan/prune coverage

Assigned obligation: (a) audit the passage from the **single-disk capacity atom** to the
**(10 boundary + 1 hub) exclusion** at every radius `≤ 0.38`, including the **scaling**
step and the **centre bound `e ≤ 7/50`**; (b) audit the **A/B kernels themselves** for
empty-branch / pruning coverage. Sources read directly:
`solo-20260922/M10-038-EXCLUSION.md` (§1–§4),
`solo-20260922/certify_directional_dual.py` (kernel A core, 78 lines),
`solo-20260922/certify_directional_dual_t.py` (kernel A driver, 56 lines),
`solo-20260922/verify_directional_fixed.py` (kernel B, 135 lines),
`solo-20260922/check_directional_instrument.py`, plus the manifest and its checker.
**The original `DUAL-MANIFEST.json` is NOT modified**; the stale-hash finding from my
previous audit is carried here and its correct value recorded in §4.

---

## 1. Atom → (10+1) exclusion: is the scope uniform in `r ≤ 0.38`?

**The scaling step is what makes it uniform, and it is present in §1 (verified
verbatim).** M10's hypothesis is `r ≤ R = 19/50` with eleven disks of common radius `r`;
§1 reduces it to the *exact* radius `R` by **enlarging every radius to R with centres
unchanged**:

> "反设 `r≤R=19/50`。把全部半径扩大到 `R`。原十个边界盘仍接触且覆盖 `∂D`；十一盘仍覆盖 `D`。
> 今后 `r` 不再自由，所有 `R` 为精确 `19/50`。"

Enlargement is monotone for coverage, so after it the hypothesis holds at the single
scale `R`; the whole certificate is then evaluated at `R` only. **Therefore the atom
bound `Q < B/10` proved at `R` applies to the `r ≤ R` statement without any
interpolation between radii** — there is no "does it hold at smaller r" gap, because
smaller `r` is only the hypothesis, never the point of evaluation.

**The centre bound `e ≤ 7/50` (checked exactly).**
`B(0, 1−2R) ⊂ B(h,R)` together with `1 − 2R ≤ R` (true iff `R ≥ 1/3`, and `19/50 > 1/3`)
gives `e + (1−2R) ≤ R`, i.e. `e ≤ 3R − 1`. Exact rational check:
`3·(19/50) − 1 = 7/50` ✔ (the numeric coincidence I first suspected,
`7/50 = 196/625`, is **false** — `196/625 = 0.3136`, and the correct value
`0.14` is `7/50`; the hub-cell step uses `1 − 2R = 6/25 = 0.24`, a *different*
constant). The certified `e`-range reaches exactly `7/50`:
`directional_e_cover.json`'s last interval is `[0.136, 0.140]`, and the exact-rational
checker `audit_dual_manifest.py` asserts `edge == F(7,50)` for **both** kernels, which
I re-ran: **contiguous coverage to `7/50`, no gaps, both kernels**.

**Domain of the atom vs. the disks actually admissible in the 10+1 hypothesis.** M10 §3
uses `c = ρ(cos φ, sin φ)` with `0 ≤ t ≤ asin(R)` and
`ρ = cos t ± sqrt(R² − sin² t)`. Every disk of radius `R` meeting `S(0,1)` has centre norm
`ρ ∈ [1−R, 1+R] = [0.62, 1.38]` and half-width `t` satisfying `R² − 2ρcos t + ρ² − 1 = 0`,
whose two roots in `ρ` are exactly the two signs — so the §3 scan is **equivalent** to
"all disks of radius R meeting `S(0,1)`" and, in particular, is a superset of the ten
boundary disks' after enlargement (each of which touches `∂D`). Both kernels implement
exactly this: kernel A over `(ρ, φ, e)` with `ρ ∈ [0.62, 1.38]`, `φ ∈ [0, π]` after the
reflection symmetrisation, `e ∈ [e0,e1]`; kernel B over `(t, v, e, sgn)` with
`t ∈ [0, TMAX]`, `v ∈ [−1,1]`, `for sgn in [-1,1]`.

---

## 2. Kernel A (`certify_directional_dual.py` + `_t.py`) — coverage and pruning

| aspect | line | finding |
|---|---|---|
| full domain | `_t.py` 28: `stack=[(mpf([0,A.b]), mpf([-1,1]), mpf([e0,e1]), sign, 0) for sign in [-1,1]]` | `t ∈ [0, asin R]`, `v ∈ [−1,1]`, `e` = the job's interval, **both roots** |
| pruning | `_t.py` 33: `if val.b < target.a: leaves+=1; continue` | prunes only when the **upper** bound of the atom is below the **lower** bound of `B/10` — outward sound |
| fail-loud guard | `_t.py` 34–36: midpoint evaluation; `if midval.a > target.b: fail` | a genuine counterexample would be *recorded as a failure*, not silently pruned. **No run in the 36 segments carries a failure record** |
| budget guard | 37–38 | exhausting `maxboxes`/`depth` sets `pass=False`; all 36 runs report `pass: True` |
| inner-term skip (**CORRECTED — see the retraction below**) | `_t.py` **21**: `if ell.a >= (2*R).b: return out` | `_t.py` **20** computes `ell = iv.sqrt((rho-e)**2 + 2*rho*e*(1-v))` with **no clip at all**; the gate skips the hub term only when the box's **lower** bound of `ell` already exceeds `2R`. Otherwise lines 22–24 compute the hub term. Conservative in the correct direction: it may compute a term that is truly absent, never omits one that is present |
| ell in `_t.py` | `_t.py` 20 | exact identity, no clipping. The parameterisation is `(t, v, e, sgn)`, **not** `(ρ, φ, e)`, so the `ell²`-clip issue does not arise in this driver at all |
| ell in `_dual.py` (a **different** atom) | `_dual.py` 41: `sqrt(clip(rho^2+e^2-2*rho*e*cp, '0.2304','3'))`, gate at 42: `if lo(ell) >= hi(2*R): return out` | domain floor `0.2304` is exactly the true minimum of `ell²` at `(ρ,e,cos φ) = (0.62,0.14,1)` — valid and tight; the upper clip `3` **is** binding (true max `ell² = 2.3104` at `ρ=1.38, e=0.14, cos φ=−1`, since `ρ²+e²+2ρe = 1.9044+0.0196+0.3864`), and it only loosens the interval |
| reflection symmetrisation | `_dual.py` 25–31 | the saved weights are exact rationals; `coeff()` averages over `φ → −φ` so the odd (sine) terms drop, and it **asserts** `a_j0 ≥ Σ_{k≥1}|a_jk|` (nonnegativity) on the *resulting* coefficients |

**Retraction (my error, corrected here).** My earlier version of this table claimed
that "because `3` clips the top, `ell² > 2.02 > 4R²`, so `lo(ell) ≥ hi(2R)` always holds
and the inner term is *never* computed in kernel A", and derived from that the
"caveat" that kernel A does not verify the hub-arc term. **That finding was false and is
withdrawn.** Two distinct errors:

1. I attributed the `ell²`-clip line to the file that does not have it. The clip at
   `clip(..., '0.2304','3')` is in `certify_directional_dual.py` line 41, whose atom is
   parameterised in `(ρ, φ, e)`. The driver actually used for the certified rows,
   `certify_directional_dual_t.py`, computes at line 20
   `ell = iv.sqrt((rho-e)**2 + 2*rho*e*(1-v))` with **no clip**, and gates at line 21
   with `if ell.a >= (2*R).b: return out`; every other box proceeds to the hub term at
   lines 22–24.
2. An upper clip does **not** force the lower bound above the threshold: clipping
   `ell² ∈ [0.2304, 3]` gives `ell ∈ [0.48, 1.732]`, and `lo(ell) = 0.48 < 0.76 = 2R`,
   so the gate does **not** fire. I had wrongly inferred "always skipped" from the clip.

**Point check (the lead's example), computed with the atom formula of `_t.py` 11–24 for
`e = 0, t = 0, sign = −1, v = 1`:**

```
  sin t = 0, cos t = 1, sqrt(R² − sin²t) = 0.38
  rho = cos t + (−1)·sqrt(R² − sin²t) = 0.62   <  2R = 0.76
  ell = sqrt((rho−e)² + 2·rho·e·(1−v)) = 0.62  <  2R  ⟹  gate does NOT fire
  ⟹ the hub term is computed at lines 22–24 and is genuinely nonzero.
```

So the hub-arc capacity is present in kernel A's evaluated expression, and my
"conservative/under-counting" reading of kernel A is withdrawn.

**Why the direction of the concern matters (and why kernel A is nonetheless sound).**
The lead's point is the right one: the gate `ell.a >= (2R).b` is a *lower*-bound gate, so
it skips only when skipping is provably harmless; when the box straddles the threshold
the hub term *is* computed. Omission of a nonnegative contribution would be unsound
because it **under**-estimates the upper bound and could wrongly prune a box (the code
maximises per box, so a too-small upper bound can fall below the target and eliminate a
genuine near-violation). With the hub term present this cannot happen; the remaining
over-estimation risk (the over-estimate `4ρe ≤ 4·1.38·0.14 = 0.7728` in a straddling box)
is handled by the fail-loud midpoint test at `_t.py` 34–36, which records a failure
instead of pruning.

---

## 3. Kernel B (`verify_directional_fixed.py`) — coverage and pruning

| aspect | line | finding |
|---|---|---|
| full domain | 106: `stack=[(I.raw(0,TMAX.b), I(-1,1), E, sgn, 0) for sgn in [-1,1]]` | `t ∈ [0, TMAX]` with `TMAX = 0.3897962964742606`; line 87 `assert sin(TMAX).a > R.b` ⟹ `TMAX > asin R` so the domain is a strict superset; `v ∈ [−1,1]`; `e` = `I(*row['e_interval'])`; both roots |
| root geometry | 90: `rho = clip(cs + sgn*sqrt(clip(R*R-sn*sn,0,R*R)), '.62','1.38')` | identical parameterisation to §3; the clip matches `[1−R, 1+R]` exactly |
| pruning | 111: `if val.b < target.a: continue` | same outward-sound rule as kernel A |
| budget guard | 112: `assert d<70 and count<300000` | a budget failure would **raise**, not silently pass; no such exception in the 36 certified runs |
| inner-term skip | 94: `if ell.a >= (2*R).b: return out` | conservative, same as kernel A |
| `ell` enclosure | 93: `ell = sqrt((rho-e)**2 + 2*rho*e*(1-v))` | **no clipping**; the minimum over the domain is the same `0.2304` (verified separately over the `(t,v,e,sgn)` parameterisation, attained at `sgn=−1, t=0, ρ=0.62, e=0.14, v=1`) |
| `beta` guard | 96: `assert b.a >= I('.6').b` | **checked to be non-vacuous and safe**: `b = clip(ell/(2R),0,1)`, and `ell ≥ sqrt(0.2304) = 0.48` while `2R·0.6 = 0.456`, so `b ≥ 0.6` holds on the entire domain; the assertion cannot fire on admissible boxes, and the run history confirms it never did |
| trig enclosures | 49–82 | `sqrt` integer `isqrt`; `sin`/`cos` alternating Taylor with explicit next-term remainder; `acos` via `2 atan(sqrt((1−x)/(1+x)))` with `x` clipped to `[0.6,1]` so the `atan` argument is `≤ 0.25 ≤ 0.5` as `atanpoint` requires; `PI` by Machin with an independent enclosure assertion (line 85) |
| exact weight handling | 102–104 | weights read as `Fraction`s from the A-side rows, nonnegativity asserted, target `PI*(c[0][0]+c[1][0])/10` |

**No empty-branch or pruning defect found in kernel B.** Counts: 36 runs,
`sum(boxes) = 198152`, matching the manifest's declared `kernel_B_boxes`.

---

## 4. Manifest status (unchanged file; audit result recorded here)

Per instruction the source manifest is **not** modified. The defect I found earlier
stands as a provenance item only:

```
DUAL-MANIFEST.json  (written 17:29:12)     files['directional_fixed_all.json']
   stored  hash: d89e2aef567c073da1835542bcb6046d8168f1806424c9713b10e2556ec165b8
current hash: 04a76a473cab61f98ed35333501ac1154f501d00dc49fcf719a544b0a3c2a829
```

Cause: that file was re-written at 21:10:01 (post-manifest) in the split shape
(`directional_fixed_all.json` = 34 runs `[0.0071,0.14]`, `directional_fixed_low.json` =
2 low runs `[0,0.004],[0.004,0.0071]`). I re-ran the manifest **checker** on the present
files: **36 runs / 198152 boxes per kernel, identical `e`-intervals and weights across
kernels, all `pass` true, contiguous coverage to `7/50`, declared box counts
reproduced.** So the certificate's content is intact; only the hash string is stale.
Recommended action (for the lead, not done here): re-run `audit_dual_manifest.py` to
refresh provenance.

---

## 5. Verdict

| question | answer |
|---|---|
| does the atom bound transfer to every `r ≤ 0.38`? | yes — via §1's uniform enlargement to `R = 19/50`; the certificate is evaluated at `R` only, and no between-radii interpolation is involved |
| is the centre bound `e ≤ 7/50` derived correctly? | yes — `e ≤ 3R − 1 = 7/50` from `B(0,1−2R) ⊂ B(h,R)` and `1−2R ≤ R`; the `e`-range is covered contiguously to exactly `7/50` in both kernels |
| does the atom domain cover the admissible disks? | yes — `(t,ρ)` with both roots is *equivalent* to "radius-`R` disks meeting `S(0,1)`", a superset of the ten enlarged boundary disks |
| kernel A pruning/coverage (**corrected**) | sound. The certified driver `certify_directional_dual_t.py` computes `ell` at line 20 **without any clip** and gates at line 21 on `ell.a >= (2R).b`, so the hub term of lines 22–24 **is** evaluated whenever the box attains `ell < 2R` — including the lead's point `(e,t,sign,v) = (0,0,−1,1)` where `ρ = ell = 0.62 < 0.76`. My earlier claim that the inner term is always skipped is withdrawn (see the retraction in §2) |
| kernel B pruning/coverage | sound; full domain including both roots, exact `Fraction` weights, integer outward arithmetic, non-vacuous `beta` guard verified to hold on the whole domain, no failure records, boxes match the manifest |
| defects | one provenance defect (stale hash); **no mathematical defect**. The "kernel A omits the hub term" remark I previously raised here was false and is withdrawn |

No claim registered; no subagent; no lead file modified; the source manifest was not
modified (its correct current hash is recorded above).
