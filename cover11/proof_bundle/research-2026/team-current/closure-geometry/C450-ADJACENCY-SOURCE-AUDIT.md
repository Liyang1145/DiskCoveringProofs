# C450-ADJACENCY-SOURCE-AUDIT — per-disk capacity domain and the `S(h,R)` use

Assigned source audit of the dependency chain
`lead/HUB-ADJACENCY-DUAL.md` (HAD) ⟶ `solo-20260922/M10-038-EXCLUSION.md` (C450).
Two questions only: (i) does C450's **per-disk capacity** cover all of `e ∈ [0,7/50]`,
all disk positions and **both radial roots**? (ii) is HAD's use of the circle
`S(h,R)` inside the original capacity quantifier? Source/interface and manifest
integrity only — no long certificates re-run (I ran only the manifest checker and the
instrument control, both seconds-scale).

---

## 1. What C450's capacity actually quantifies over

From `M10-038-EXCLUSION.md` §1–§3 (read directly):

* **§1 confines the hub**: assuming `r ≤ R = 19/50`, all radii are enlarged to `R`;
  then `B(0, 1−2R) ⊂ B(h,R)` forces `e = |h| ≤ 3R − 1 = 7/50`, and a rotation puts
  `h = (e, 0)`; the certificate covers **all** `e ∈ [0, 7/50]` with no appeal to
  rotation-symmetry theorems (§1 says so explicitly).
* **§2 the two necessary circles**: the outer `∂D` is covered by the ten ring disks;
  for each `R < q < 1 − e` the inner circle `S(h,q)` is inside `D` and outside the hub
  ball, hence must be covered by the ring disks; taking `q ↓ R` is legitimate (arcs
  converge continuously, tangency has zero angular measure) and **"直接把闭圆边界称为
  未覆盖是错误解释，不是本证明"** — i.e. `S(h,R)` itself may be covered by the hub, and
  the capacity uses the *outer limit*, which is the correct direction.
* **§3 the per-disk formula**: for a single disk, write `c = ρ(cos φ, sin φ)`, `t` its
  half-width on `∂D`:
  `0 ≤ t ≤ asin(R)`, `ρ = cos t ± sqrt(R² − sin² t)` — **both signs enumerated, the
  outer root not deleted** — and `v = cos φ ∈ [−1,1]`; then
  `ℓ² = (ρ−e)² + 2ρe(1−v)`, `cos ψ = (ρv−e)/ℓ`, and on the inner target circle
  `b = acos(ℓ/(2R))` if `ℓ < 2R`, else `b = 0`. The two-circle weighted integral is
  `Q` and the demand is `B = π(a_00 + a_10)`, with the requirement
  **`Q < B/10` for every single disk**, weights fixed per `e`-segment.

**So the quantifier is**: *every* radius-`R` disk that has a nonempty arc on `∂D`
(i.e. every disk meeting `S(0,1)`), for every `e ∈ [0,7/50]`, with both roots, all
half-widths and all azimuths, against one nonnegative weight pair per `e`-segment.

**Containment check (the direction that matters).** C450 needs the bound only for the
**ten ring disks that cover `∂D`**: a disk covering part of `∂D` meets `S(0,1)`, so its
`ρ ∈ [1−R, 1+R]` and it lies inside the quantified class. In the other direction C450
quantifies over a *superset* of those ten (every disk meeting the circle, including
those whose inner arc is empty and for which `Q = 0 < B/10` trivially). **The
quantifier is correct and complete for the use made of it.**

---

## 2. Verified in the two independent kernels (interface only)

`verify_directional_fixed.py` (kernel B, integer fixed point `10^-28`, outward
rounding, no mpmath/numpy/scipy, no import from the producing certifier — read
directly, lines 1–135):

| item | code location | check |
|---|---|---|
| `t` full domain | line 86 `TMAX=I('0.3897962964742606')`, line 106 `I.raw(0, TMAX.b)` | `assert sin(TMAX).a > R.b` (line 87) confirms `TMAX > asin(R)`; so `[0, TMAX]` ⊇ `[0, asin R]` |
| both roots | line 106 `for sgn in [-1,1]`; line 90 `rho = clip(cs + sgn*sqrt(clip(R²−sn²,0,R²)), '.62','1.38')` | `sgn = ±1` implements ρ = cos t ± sqrt(R² − sin²t); the clip is exactly `ρ ∈ [1−R, 1+R] = [0.62, 1.38]` |
| `e` domain | line 105 `E = I(*row['e_interval'])` | the interval handed in by the coverage files; `t`-box is the block `[0, asin R]` |
| azimuths | line 106 `I(-1,1)` for `v = cos φ`, line 83 `cheb(v) = [∖, v, 2v²−1, 4v³−3v]` | `v ∈ [−1,1]` = all azimuths |
| inner target | line 93–99 | `ℓ² = (ρ−e)² + 2ρe(1−v)` (matches §3); `b = clip(ℓ/(2R),0,1)`, `beta = acos(b)`, `cos ψ` via `cheb(clip((ρv−e)/ℓ,−1,1))` |
| nonnegativity | line 103 `assert all(a[0] >= sum(abs(x) for x in a[1:]) for a in fs)` | `a_j0 ≥ Σ_{k≥1}|a_jk|` on **every** segment |
| demand | line 104 `target = PI*(c[0][0]+c[1][0])/10` | `= B/10` |
| positive control | `check_directional_instrument.py`, run: `PASS 20 independent quadrature comparisons; genuine regular cover r=s saturates weighted demand` | independent direct `mp.quad` of the weight over each arc matches the atom, and a **genuine 10-ring cover saturates the demand exactly** — the instrument does not falsely exclude true covers |

Kernel A (`certify_directional_dual*.py`, used to *propose* the weights) is a different
implementation; the manifest asserts the two kernels' weights and endpoints agree.

---

## 3. Manifest integrity — one concrete defect, content unaffected

I re-ran the manifest **checker** (not its writer) and hashed all ten files:

```
DUAL-MANIFEST.json: status PASS, intervals 36, kernel_A_boxes 198152, kernel_B_boxes 198152,
                    weights_and_endpoints_equal true, files: 10 hashes
hash verification:  directional_low_cover.json OK | directional_e_cover.json OK
                    directional_fixed_low.json OK | directional_fixed_all.json ** MISMATCH **
                    certify_directional_dual.py OK | certify_directional_dual_t.py OK
                    verify_directional_fixed.py OK | verify_directional_fixed_low.py OK
                    directional_instrument_control.json OK | M10-038-EXCLUSION.md OK
stored  hash: d89e2aef567c073da1835542bcb6046d8168f1806424c9713b10e2556ec165b8
current hash: 04a76a473cab61f98ed35333501ac1154f501d00dc49fcf719a544b0a3c2a829
```

**Cause (established from mtimes):** `directional_fixed_all.json` was written at
**21:10:01**, while `DUAL-MANIFEST.json` was written at **17:29:12**; the current file
carries `{"status":"PASS completed rows","kernel":"independent integer fixed point 1e-28
with outward rounding","runs":[34 runs]}`, and its sibling `directional_fixed_low.json`
(17:21:11, unchanged, hash OK) holds the remaining 2 runs. So the file was re-run in a
**split-format shape** after the manifest was generated, and the manifest's hash for it
is **stale**, not evidence of tampering.

**Why the mathematics is unaffected — I verified the checker's own assertions on the
current files:**

```
kernel A: 36 runs / 198152 boxes   kernel B: 36 runs / 198152 boxes
e-intervals identical between kernels: True
weights identical between kernels:    True
every run's pass flag true:           True
contiguous e coverage [0, 7/50] with no gaps/overlaps, both kernels: True
manifest's declared box counts match the recomputed ones: True
```

So `audit_dual_manifest.py`'s chain-of-custody claim (`weights_and_endpoints_equal`,
36 exact intervals, box counts) **re-verifies on the present files**; only the stored
hash string is out of date. `directional_instrument_control.json` is likewise
post-manifest (21:14:40) and its hash matches, so the manifest writer's file list is
internally consistent. *Recommendation (not a mathematical gap):* re-run
`audit_dual_manifest.py` to refresh the hash, since its own header is the provenance
record.

**One boundary-file note for downstream readers:** `directional_fixed_all.json` and
`directional_e_cover.json` store 34 runs (`[0.0071, 0.14]`) and
`directional_fixed_low.json` / `directional_low_cover.json` store the 2 low runs
(`[0, 0.004], [0.004, 0.0071]`); in the manifest-era files the split was 2 + 34 the same
way, so the pairing is unchanged.

---

## 4. Is HAD's `S(h,R)` inside the capacity quantifier? — Yes

HAD (lines 21, 25–29) argues: the nine ring disks, **enlarged to radius `R` with their
centres unchanged**, cover the circle `S(h_1,R)` as well as `S(0,1)`; then
"C450's finite dual is stronger than its original covering formulation: for each
`e ∈ [0,7/50]`, its saved nonnegative angular weights satisfy, for **every single**
radius-`R` disk meeting `S(0,1)`, `Q(c;e) < B(e)/10` … **This is exactly
M10-038-EXCLUSION.md §§3–4, independent of how the inner circle was produced.**"

Checked point by point against §1–§3:

1. **Are the nine centers admissible disks?** Each ring disk meets `∂D` (they cover it),
   so its centre has norm `∈ [1−R, 1+R]` after enlargement; the quantified class is
   exactly "radius-`R` disks meeting `S(0,1)`". ✔ (This is also why C450's §3 keeps the
   **outer** root: the ring centres are not constrained to the inner-root circle.)
2. **Is the inner target circle the same object?** C450 §2 uses `S(h,R)` with
   `h = (e,0)` after rotation; HAD uses `S(h_1,R)` with `h_1 = (e,0)` by the same
   rotation freedom, `e = |h_1| ≤ 7/50` from HAD's own step (line 7). Same object. ✔
3. **Does the bound hold per disk or only for covers?** It is a **per-single-disk**
   bound (`Q(c;e) < B(e)/10` for every admissible disk); HAD's sentence "independent of
   how the inner circle was produced" is exactly this: the capacity does not encode the
   *covering* configuration, only the disk class. ✔
4. **Is the sum step legitimate?** HAD needs `Σ_{i≤9} Q(c_i;e) ≥ B(e)` for nine disks
   covering both circles and `Σ Q < 9B/10` from the per-disk bound. The capacity
   statement "cover ⇒ `Σ_i Q ≥ B`" is the necessary direction; HAD's nine disks do cover
   both circles (by its facet lemma), so the hypothesis is met. ✔
5. **Weights are per-`e`-segment and nonnegative**; HAD fixes `e` and uses the weights
   saved for that segment. ✔ (Both kernels assert `a_j0 ≥ Σ|a_jk|` per segment.)
6. **One formal caveat, already handled by C450:** calling `S(h,R)` "must be covered" at
   exactly `q = R` would be the mistaken reading that §2 warns against ("直接把闭圆边界
   称为未覆盖是错误解释"); the correct statement is the outer limit `q ↓ R`, and any
   discrepancy is confined to a point set of zero angular measure. HAD's usage does not
   rely on the closed-circle reading — it only needs the weighted integral over the
   circle, which the certificate computes as that limit. ✔

**Conclusion of this item: HAD's `S(h,R)` use is inside the C450 per-disk capacity
quantifier; no extra hypothesis is smuggled in.**

---

## 5. Summary

| item | verdict |
|---|---|
| per-disk capacity covers `e ∈ [0,7/50]` without gaps | yes — 36 exact rational `e`-intervals, contiguous, both kernels (`audit_dual_manifest` assertions re-verified) |
| all disk positions (`ρ ∈ [1−R,1+R]`, all azimuths) | yes — code line 90's clip and `v ∈ [−1,1]` |
| both radial roots | yes — `for sgn in [-1,1]`, with the outer root explicitly retained |
| `t` full domain `[0, asin R]` | yes — `[0, TMAX]` with `sin(TMAX) > R` asserted |
| weight nonnegativity per segment | yes — asserted in the verifier and in the manifest checker |
| instrument computes the intended quantity | yes — 20 independent quadrature comparisons + a genuine cover saturating the demand |
| manifest integrity | **one defect: stale hash for `directional_fixed_all.json`** (post-manifest re-run; content checks all pass, box counts and cross-kernel agreement intact) |
| HAD's `S(h,R)` inside the quantifier | yes — per-disk, disk-meets-circle class, same `e`-domain, outer-limit reading |

No mathematical gap found in the C450 → HAD dependency. The only actionable item is
refreshing the manifest hash. No claim registered; no subagent; no lead file modified.
