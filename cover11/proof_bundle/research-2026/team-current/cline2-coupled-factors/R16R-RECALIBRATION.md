# R16R — corrected bounded calibration of the saturated-face branch derivatives

Supersedes the withdrawn `R16-SATURATED-FACE-DERIVATIVES.md` results.  Own scope, current
coefficients only (`lead/joint_nested_frozen.json` sha256 `5671967c…21fb`), no new
coefficients, no interval certification attempted here.

## Corrections applied (each verified in `r16q_validate_e.py`)

| # | defect | correction | evidence |
|---|---|---|---|
| 1 | off-face derivative written `(X X'+Y Y')/(4R√Q)` | `e2 = √Q/(2R)` ⇒ **`e2' = (X X'+Y Y')/(2R√Q)`** | finite-differencing `e2` at 5 points matches the corrected form to `6e-19…9e-19`; the halved form is off by exactly 2 |
| 2 | "ridge = delta = b1" | ridge is **`delta = b1 − b2`, `H = 2r sin(b1+b2)`**; `delta = b1` is the wedge edge (A = 0) | `2r sin(2b1−(b1−b2)) = 2r sin(b1+b2)` verified at 3 triples |
| 3 | face intersection at `±(b1−b2)/2` | intersection is at **`delta = b1 − b2`** | equalising the two sine arguments |
| 4 | plus norm root called `j=3` | **`j=2` is the plus root**, `j=3` the minus root | `interval_hub_saturated.py:19` |
| 5 | `j=1` reported "strictly increasing, slope +0.16" | by `delta → −delta, b1 ↔ b2` the `j=1` derivative is the **negative** of `j=0`; measured `j=0` min/max `−?…+`, `j=1` mirrored | sign census below |

The `quad` convention used throughout is `quad_range(a,b,x) = a x² + b x`, i.e.
`quad(β,γ,e) = β e² + γ e` with `β1 = −z16 = +0.405431351`, `γ1 = −z78 = −0.870277865`,
`β2 = z20 = +0.400827103`, `γ2 = z82 = −0.86525597`.

## 1. Validation of the repaired derivative

`dV/ddelta` assembled from the corrected formulas, compared against central differences of
`V` itself (`h = 1e-11`, 30 dps):

```
j=0 (0.379,1.02,1.02,-0.45): dV=+0.180941994  fd=+0.180941994  |diff|=1.89e-19
j=1 (0.379,1.02,1.02,-0.45): dV=-0.279640620  fd=-0.279640620  |diff|=2.71e-19
j=2 (0.379,1.02,1.02,-0.45): dV=+1.214584155  fd=+1.214584155  |diff|=7.08e-19
j=3 (0.379,1.02,1.02,-0.45): dV=-0.263877846  fd=-0.263877846  |diff|=2.96e-19
```

(and likewise at four further triples; all four branches agree to `<1e-18`).

## 2. Calibration at the distinguished deltas (corrected)

```
   r     b1     b2 |  j     delta        point         dV/ddelta        H
 0.375 1.050 1.050 |  0  0.000000   ridge b1-b2        +0.110534    0.647407
 0.375 1.050 1.050 |  1  0.000000   ridge b1-b2        -0.114301    0.647407
 0.375 1.050 1.050 |  2  0.000000   ridge b1-b2        -0.009197    -
 0.375 1.050 1.050 |  3  0.000000   ridge b1-b2        -0.000733    -
 0.375 1.050 1.050 |  0  1.050000   wedge edge          +0.431590    0.650567
 0.375 1.050 1.050 |  1  1.050000   wedge edge          -0.270667    (B=0)
 0.375 1.100 1.050 |  0  0.050000   ridge b1-b2        +0.141203    0.627674
 0.375 1.100 1.050 |  1  0.050000   ridge b1-b2        -0.133755    0.627674
 0.380 1.020 1.100 |  0 -0.080000   ridge b1-b2        +0.119955    0.648235
 0.380 1.020 1.100 |  1 -0.080000   ridge b1-b2        -0.143706    0.648235
 0.380 1.020 1.100 |  2 -0.080000   ridge b1-b2        +0.356932    -
```

Observations that survive this calibration:
* at the ridge `delta = b1-b2` both face branches are admissible and their derivatives are
  **equal in magnitude and opposite in sign** (`+0.1105 / −0.1143`, `+0.1412 / −0.1338`,
  `+0.1200 / −0.1437`) — consistent with correction 5;
* `j=0`'s derivative at the ridge is positive in every sampled triple, `j=1`'s negative;
* the wedge edge `delta = b1` has `B = 0` (degenerate) and is not a maximum or ridge of
  interest; `j=1` there has `H < 0` on the sampled triples, so nothing is inferred from it.

## 3. Sign census on the corrected formula (bounded: 6×6×6 triples × 41 deltas)

```
j=0 : 8681 positive,  175 negative, 0 zero
j=1 :  181 positive, 8675 negative, 0 zero
j=2 : 2902 positive, 2938 negative, 0 zero
j=3 : 2884 positive, 2956 negative, 0 zero
```

Consequence: **the monotone-arc picture of the withdrawn report does not hold.**  `j=0` and
`j=1` are *sign-definite on the sampled set* (opposite signs, as the reflection requires) but
with a small fraction (≈2%) of the opposite sign; the two norm branches have both signs in
comparable proportion.  Any certification attempt must handle those sign changes rather than
assume monotonicity, and the earlier `j=0` monotonicity target ("certify `dV/ddelta >= 0.15`")
is not achievable as stated on this sampled set — the observed `j=0` values go below 0.15
(e.g. `+0.083337486` at `(0.375, 1.02, 1.10, −0.30)`) and even below zero.

## 4. Scope and missing implication

* What is established: the repaired formula is correct (validated against finite differences
  of `V` to `<1e-18` on all four branches); the ridge/face-intersection/root-label corrections
  are algebraically verified; and the sign census above is a bounded empirical statement.
* What is **not** established: any monotonicity, any interval certificate, and any reduction
  of the hub-objective maximum to ridge-minus-endpoint.  In particular the earlier claim that
  the profile maximum sits at a cap "collar" is withdrawn, and the certification target
  `j=0 ⇒ dV/ddelta >= 0.15` is false on the sampled set (minimum observed `j=0` value is
  negative), so that target must be re-scoped before any interval work resumes.
* No claim registered; nothing here is a bound.

Files: `r16q_validate_e.py` (formula validation + ridge algebra), `r16r_recalib.py`
(corrected calibration + sign census), logs in `out/r16q.log`, `out/r16r.log`.
