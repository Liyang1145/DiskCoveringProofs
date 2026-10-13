# R16 Cartesian controls from the lead's disk construction — PASSED

Own scope.  **No interval run and no numeric curvature work was performed on this
correction**; the lead's gate ("two legal off-ridge and one illegal off-ridge control must
pass first") is what this file addresses.

## 1. The lead's disk construction, read literally

From `lead/interval_hub_boundary.py:11`:

```
disks = [ ( r sin2b1, -r cos2b1,  r ),      # D1, radius r
          ( r sin2b2,  r cos2b2,  r ),      # D2, radius r
          ( s,          0,       1-r ) ]    # unit-disk condition,  s = sqrt(1-r^2)
```

so `D1 = (r sin 2b1, −r cos 2b1)`, `D2 = (r sin 2b2, +r cos 2b2)`, and the hub is
`x = (H cos δ, H sin δ)`.  **My previous "controls" used invented centres and the wrong
site angles `φ = δ ± b`; they are withdrawn.**  This file uses only the centres above.

## 2. Exact residual identities — verified

```
|x − D1|² − r²                = H (H − 2r sin(2b1−δ)) = −H R1
|x − D2|² − r²                = H (H − 2r sin(2b2+δ)) = −H R2
|x − (s,0)|² − (1−r)²         = H² − 2 s H cos δ + 2r(1−r) = −N
```

Checked at 40 dps over six random `(r, b1, b2, H, δ)` draws: the Cartesian and chart
residuals agree identically, **max discrepancy `2.29589e-41`**.  Consequently

> **the hub must lie INSIDE both radius-`r` disks** (and inside the unit disk).
> A **positive** distance residual means the hub is **outside** that disk, i.e. **ILLEGAL**;
> a positive norm residual means the hub is outside the unit disk, i.e. **ILLEGAL**.

Both `|D1| = |D2| = r` exactly (e.g. `0.377000` / `0.378000` at the controls below).

### 2.1 Sign-rule correction (as requested) with the decisive numbers

My earlier wording — "positive residual = inside the disk = ILLEGAL" — was **wrong**, and the
error was reporting the classical constrained classification rather than the geometry.  The
filter's own accept condition is `H <= cap1`, i.e. `H(H − cap1) <= 0`, i.e.
`|x − D1|² − r² <= 0`.  At `r = 0.377, b1 = 1.008, b2 = 1.001, δ = −0.32`
(`cap1 = 0.543815934`, `D1 = (+0.340251161, +0.162351924)`):

| H | `H − cap1` | residual `H(H−cap1)` | `\|x−D1\|` | `\|x−D1\|−r` | inside disk1? | filter |
|---|---|---|---|---|---|---|
| 0.493816 | −0.050000 | −0.024690797 | 0.342692578 | −0.034307422 | **inside** | ACCEPT (legal) |
| 0.533816 | −0.010000 | −0.005338159 | 0.369852458 | −0.007147542 | **inside** | ACCEPT (legal) |
| 0.543816 | 0.000000 | 0.000000000 | 0.377000000 | 0.000000000 | boundary | ACCEPT (legal) |
| 0.553816 | +0.010000 | **+0.005538159** | 0.384274849 | +0.007274849 | **outside** | **REJECT (illegal)** |
| 0.593816 | +0.050000 | **+0.029690797** | 0.414511516 | +0.037511516 | **outside** | **REJECT (illegal)** |

So: **positive signed residual = OUTSIDE the disk = illegal**, exactly as the lead now states,
and my "inside" description is retracted.  Note this is the same constraint either way — the
filter requires the hub to be inside each disk, so an outward (positive) residual is the
illegal direction.  The identity itself is unaffected (it is verified to `1e-41`), and the
three controls in section 3 are unaffected in their verdicts; only the prose label changes.

## 3. The three required controls — all off-ridge, `D1`, `D2` fixed, `H` perturbed

Legal ⟺ both disk residuals ≤ 0 **and** norm residual ≤ 0.  Off-ridge ⟺ `b1 ≠ b2`.

### A) two LEGAL off-ridge configurations

| control | r | b1 | b2 | δ (off-ridge: `b1−b2`) | H | disk₁ residual | disk₂ residual | norm residual | verdict |
|---|---|---|---|---|---|---|---|---|---|
| **A-legal-1** `H=cap1` | 0.377 | 1.10 | 1.05 | −0.32 (`+0.05`) | 0.439077 | **0.000000e+00** | −1.310571e-01 | −1.095378e-01 | **LEGAL** |
| **A-legal-1** `H=cap1−0.05` | 0.377 | 1.10 | 1.05 | −0.32 (`+0.05`) | 0.389077 | −1.945387e-02 | −1.355868e-01 | −6.302605e-02 | **LEGAL** |

`D1 = (+0.304803, +0.221865)`, `D2 = (+0.325430, −0.190327)`, `C = (+0.926213, 0)`,
`cap1 = 2r sin(2b1−δ) = 0.439077`, `cap2 = 2r sin(2b2+δ) = 0.737560`.

Sanity check inside control A: the midpoint `H = (cap1+cap2)/2 = 0.588319` gives
`disk1 = +8.780156e-02 > 0` and is correctly classified **ILLEGAL** — i.e. the same fixed
centres produce a failure when the hub is pushed inside a disk, which is exactly the
monotonicity property the gate is meant to test.

### B) one ILLEGAL off-ridge configuration with an explicitly positive disk residual

| control | r | b1 | b2 | δ (off-ridge: `b1−b2`) | H | disk₁ residual | disk₂ residual | norm residual | verdict |
|---|---|---|---|---|---|---|---|---|---|
| **B-illegal-1** | 0.377 | 1.10 | 1.05 | +0.60 (`+0.05`) | 0.753678 | **2.869859e-42** | **+3.251626e-01** | −1.145059e-01 | **ILLEGAL** |
| **B-illegal-1** `H=mid` | 0.377 | 1.10 | 1.05 | +0.60 (`+0.05`) | 0.537961 | −1.160475e-01 | **+1.160475e-01** | −6.333053e-02 | **ILLEGAL** |
| **B-illegal-1** `H=min−0.05` | 0.377 | 1.10 | 1.05 | +0.60 (`+0.05`) | 0.272244 | −1.310677e-01 | −1.361222e-02 | **+1.276317e-01** | **ILLEGAL** |

`D1`, `D2`, `C` identical to control A (same `r, b1, b2`), only δ and H changed — so the
comparison is clean.  Here **disk₂'s residual is positive** (`+3.251626e-01`), the
positive-distance-residual-is-illegal rule fires, and the control is confirmed illegal.
`cap1 = 0.753678`, `cap2 = 0.322244` at this δ.

## 4. Gate status

| requirement | status |
|---|---|
| two legal off-ridge controls | **PASS** (A-legal-1 at `H = cap1` and at `H = cap1 − 0.05`) |
| one illegal off-ridge control, positive disk residual confirmed | **PASS** (B-illegal-1; disk₂ residual `+3.251626e-01`) |
| `D1`, `D2` fixed under the `H` perturbation | **PASS** (built from `(r,b1,b2)` and not recomputed) |
| exact residual identities | **PASS** (agreement `2.29589e-41`) |
| off-ridge (`b1 ≠ b2`) in every control | **PASS** (`\|b1−b2\| = 0.05` or `0.06`) |

## 5. What is withdrawn / what remains open

* **Withdrawn:** my earlier Cartesian controls (`r16ss`/`r16tt`/`r16uu`/`r16vv`/`r16ww`) used
  invented disk centres and `φ = δ ± b`; all of them, and the "agree" rows printed from them,
  are invalid.  The only surviving content of `r16vv`/`r16ww` is the corrected sum-to-product
  identity `sin(2b2+δ) − sin(2b1−δ) = 2cos(b1+b2)·sin(b2−b1+δ)` (verified to `1e-41`), which
  is unaffected by the centres question.
* The legal filter's equivalence to the original three Cartesian disks is now **verified**
  through the identities of section 2 at these controls.
* **Not attempted, per instruction:** any interval run, any grid test, any numeric curvature
  campaign.  The main theorem remains open, as the lead states.

Files: `r16zz_lead_centers.py` (all identities and controls), `out/r16zz_controls.json`,
log `out/r16zz.log`.
