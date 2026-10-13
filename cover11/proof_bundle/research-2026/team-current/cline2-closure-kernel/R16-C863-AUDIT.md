# R16 audit — C863 high-bearing norm-boundary exclusion (independent interfaces, own scope)

Read-only. No lead file modified. Sources hashed; certificates re-checked arithmetically.

## Verdict

**No bearing counterexample. The certificate arithmetic, pins and bookkeeping check out; the
exclusion is accepted for the stated norm-saturated scope only.**

**Correction applied (lead, R16 follow-up):** `liveboxes=0` with `budget_ended=false` does **not**
prove the stored number is the attained maximum. It proves the search terminated with every box
already under the termination threshold, so the returned value is a legitimate **upper bound** on
the maximum over the covered boxes — possibly strict. Language in this report is corrected
accordingly.

**L1 is CLOSED** by the lead's chart definition — see §3. The polar chart is the same norm circle
the Cartesian control sweeps, and both roots are retained. The former L1 is withdrawn as an
obstruction (it was my error: `t = s sin δ` instead of `t = H sin δ`).

## 1. What I verified independently (no defect)

| # | Check | Result |
|---|-------|--------|
| V1 | Source hash pins in `patch_outer_norm_boundary_certificate.json` (9 files) and `norm_cartesian_control_certificate.json` | **all match** the files on disk |
| V2 | `coefficient_sha256` pin | both certificates and `joint_nested_frozen.json` = `5671967c5a3df341…` ✓ |
| V3 | frozen row structure | `len(z)=121`; `all(z[50:73]==0)` ✓ (the assert in the kernels passes) |
| V4 | certificate bookkeeping | polar: `evaluations=51`, `liveboxes=0`, `budget_ended=false`; Cartesian: `45`, `0`, `false` → valid **upper bounds** over the covered boxes (not attained maxima) ✓ |
| V5 | domains | both certificates carry `[[0.37499999999999994,0.38],[1,1.1863995522992576],[1,1.1863995522992576]]`; `1.1863995522992576 = acos(0.375)` ✓ (broad `v` handled inside as `[.3,.76]` per `interval_hub_boundary.setup`) |
| V6 | margins | `28.107045 − 28.103151732510888 = 0.00389… > 0`; `28.107045 − 28.104759566903198 = 0.00228… > 0` ✓ |
| V7 | assembly `assemble_norm_boundary.py` | `const = π(Σz[0:9] + 2Σz[9:11] − Σz[112:121])`; `ids = 29 \ {1,2,12,13,21,22,23}` = **22 complement factors**; per-file hash asserts on digest and `q['coefficient_sha256']==digest`; final `assert total.b < iv.pi.a` — so the two printed assemblies are genuine, not clamped ✓ |
| V8 | kernel self-consistency at fixed outer points (`interval_hub_norm_only.bound` on a degenerate box) | `(r,b1,b2)=(0.376,1.05,1.05)` → 28.025550871; `(0.375,1,1)` → 28.042642456; `(0.38,1.1,1.1)` → 28.017295052; `(0.377,1.02,1.08)` → 28.031848718; `(0.379,1.18,1.02)` → 28.028033345 — all below the certified 28.1031517, and below the target 28.105 ✓ |

## 2. Structure of the bound as coded (matches the documentation)

`interval_hub_norm_only.bound` returns `K + Σ width-uppers + max(branch uppers)`; the branches at
`j=2,3` are the two polar roots, taken as a **maximum**, so if only one root is active the other
contributes `-inf` — visible in V8 (`normbranches uppers: [-inf, …]`). The `j=2,3` branch also
applies `clip(H, s-(1-r), 2r)` and the two face caps `H ≤ 2r sin(b+angle)`, i.e. necessary
constraints only, and rejects a box only when a necessary predicate is violated
(`rad.b<0`, `(H−2r sin)·a>0`, face-disk containment). That is the correct discard convention.

## 3. L1 — CLOSED (my error, corrected by the lead)

The correct chart is **`v = H cos δ`, `t = H sin δ`** (never `t = s sin δ`). Substituting

```
v = H cos δ,  t = H sin δ,  H = s cos δ ± sqrt((1−r)² − s² sin² δ)
```

into the norm distance from `(s,0)` gives, exactly,

```
(H cos δ − s)² + (H sin δ)² = H² − 2 s H cos δ + s² = (1−r)²,
```

the second equality being the root quadratic `H² − 2 s cos δ · H + (s² − (1−r)²) = 0`, whose
discriminant is `s² cos²δ − s² + (1−r)² = (1−r)² − s² sin²δ` — the code's radicand. Reported
numerically: worst `|lhs − (1−r)²| = 4.44e-16` over `r ∈ [0.375,0.38]`, `δ ∈ [−0.5,0.6]`; worst
`| norm-distance − (1−r) | = 2.22e-16` over both roots. So the polar family **is** the norm circle
the Cartesian control sweeps, both roots are the `H_max`/`H_min` pair from the quadratic formula,
and `δ ∈ [−b₂,b₁]` is the bearing interval. My obstruction came from using `t = s sin δ`.
**Withdrawn.**

**L2 (shared infrastructure) — stands as an honest limitation.** The Cartesian control reuses
`interval_hub_boundary.setup` (widths) and `interval_patch_delta` envelopes, as the note itself
says. It is therefore an independent check of *domain/branch/objective geometry*, not of the
shared width/MVT machinery. The interval-projection and mean-value-guard arguments in
`INTERVAL-PATCH-KERNEL-SCOPE.md` (guard proves all clips inactive on the segment before using the
analytic center; otherwise raw) are the load-bearing shared part and were not re-derived here.

**Language fix (lead).** `liveboxes=0` does not prove the stored numbers are attained maxima; it
shows the search exhausted the domain under the termination threshold. Every stored per-factor
number in this C863 family is a valid **upper bound** on the corresponding maximum, and the
assembly is an upper bound on the seven-factor objective over the covered boxes.

**Explicit scope (as the note states).** Norm-saturated hub only: interior hub points, face-only
boundary points, the complement covers, the two face arcs (C861), and the C862 asymmetric
larger region are **not** covered. The `.379..37999` restriction is applied only in the assembly
stage, not in the 7-factor certificate.

## 4. Minor code notes (not defects)

* `assemble_norm_boundary.py` line 6: `assert len(files)==1` — if a re-run leaves two matching
  files for the same index the assembly aborts rather than silently mixing. Fine, but a duplicate
  `*_bound_21.json`-style name collision would be a hard stop; worth knowing when re-running.
* `certify_patch_norm_boundary.py` uses `target=28.105` purely for pruning and stores
  `terminal_upper` separately; `liveboxes=0` and `budget_ended=false` make the returned
  `upper` the true maximum over the covered boxes. ✓
* The kernel docstring says `maxeval=129`; the outer B&B used 51 evaluations total with the
  tolerance path, so no inner envelope was truncated without being reported (`-inf` only where a
  branch is genuinely inactive).

## 5. Repro

```
cd research-2026/team-current/cline2-closure-kernel
py -3 r16_pins.py                 # V1-V3, manifest
py -3 r16_kernel_vs_pointwise.py  # V8 (imports the lead kernels read-only)
py -3 r16_coverage_test.py        # L1 experiments
```
