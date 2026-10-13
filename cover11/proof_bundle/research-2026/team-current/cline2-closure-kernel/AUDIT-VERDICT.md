# cline2 — closure-kernel audit verdict (q0(5,8), span 3, R=19/50)

Auditor: cline2. Lead files were **read only, never modified** (probes re-execute only
lines 1-108 of the kernel in my own namespace; the branch-and-bound body never runs there).
Subject: `lead/certify_q0_closure.py` (sha256 `901dca3e9c87c8dc6950ec90c5f300fd8ce62ff9341bbab932fb65e2de913e69`)
and `lead/q0_closure_dual_certificate_0_3.json`.

## Verdict

**No soundness defect found in the kernel's construction.** Every per-factor certified upper
exceeds the supremum of the module's own closure on its own domain; the certified total
re-assembles exactly from the kernel's own coefficients; every interval operation I could
stress is sound, including the two I initially suspected (`quad`/`scalar_quad`, and the
line-91 derivative clip). **The q0(5,8) continuous interval bound may be promoted as a
computational-interval result, conditional on the geometric reduction (item U1 below).**

## Corrected index map (factual; supersedes my earlier E9/E11 text)

Verified by comparing the *running bytecode* against formulas built from the source literals,
and by the module's own value at b=0 (`switch0` fixes `h` away from the alternative reading):

```
face t    : co_k = -z[i_k] - z[50+ee_k],  dd_k = ±z[11+ee_k],  ll_k = ±z[73+ee_k]
switch bi : c = z[i] + z[j] - z[50+ee] + 2*z[112+bi]      (i=bi, j=(bi+1)%9)
            d = z[11+ee],  e = z[32+2i+1] + z[32+2j]
            g = -z[73+ee]
            h = z[73+21+2i+1] + z[73+21+2j]               <-- source line 70 literal
ring i    : mu = z[i],  d = z[32+2i],  e = z[32+2i+1],  C = z[71] + (z[72] if i>=3)
            dl = z[73+21+2i],  el = z[73+21+2i+1]
            hl = z[112 + (i-1)%9],  hr = z[112 + i]
closure   : extra = (hl-hr)*beta - hr*a + hr*pi + (hl+hr)*w/2      (lines 98, 105)
```
Evidence: `kernel_source_index_crosscheck.py` — module vs formula over 300 random domain points,
`max|Δ| = 0 or ~1e-16` for all faces, all rings, and 7/9 switches; `switch4/7` differ by
9.8e-6/3.9e-6, which is the `quad` endpoint artifact on those flat factors (the code returns the
upper endpoint of the interval maximum; the pointwise maximum is what the check compares), not a
formula mismatch. My earlier claim that `h` used consecutive indices `z[73+2i+1]+z[73+2j]`
rested on a mislabeled probe and is **withdrawn**.

## Evidence

| # | Check | Result | Artifact |
|---|-------|--------|----------|
| E1 | Total re-assembled independently (mpmath, 60 digits) from the certificate's own 9-digit coefficients + per-factor uppers | `3.0957930091218027303549533069` ⊂ certified interval; `π − total = 0.04579964446799051` | `q0_closure_kernel_audit.py`, `kernel_audit.log` |
| E2 | Exact-rational coefficient part | `−322509177/125000000`; `Σ uppers = 17.349997125736046`; `constant = −14.254204117` | same |
| E3 | Kernel's own graph assertion (`expected` triangles, 21 edges, `z[72]==0` exact) | all pass | same |
| E4 | **Per-factor soundness**: pointwise max of the module's own closure over its own domain vs the certified upper, all 29 families (20k-67k points/family) | **0 violations**; tightest margins ≈9.6e-4 (ring3), ≈1e-3 (faces) | `kernel_pointwise_check.py`, `pw.log`, `kernel_pointwise_check.json` |
| E5 | `quad`/`scalar_quad` semantics | sound **upper** envelope: 0/20000 sampled point values exceed the returned upper endpoint; vertex branch `-b²/4a` present where needed | `kernel_final_checks.py` |
| E6 | Sector derivatives as coded (lines 90, 101) vs central differences | worst `|FD−analytic| = 3.9e-9` (FD floor at q≈2e-3); formulas exact | `kernel_derivative_formula_check.py` |
| E7 | `qmin` window | kernel uses `qmin = 4sin²(π−8asinR)/R² = 0.0149357`; admissible rings have `α ∈ [0,π]`, so this is the same window for every ring; the filter discards a box only when `q.b < qmin.a`, i.e. only boxes with no admissible point | same |
| E8 | Derivative clip `[-L, L]`, `L = R/√(1−R²) = 0.410817` | verified valid on the admissible set: `max|w_α| = 0.379 < L` and `max(|w_u|,|w_v|) = 0.41065 ≤ L` on a dense admissible scan; box-level enclosure spot checks (h = 1e-3 … 5e-2) all OK, 0 violations | `clip_window_test.py`, `clip_window_test.json` |
| E9 | Closure-term accounting | `ring_i` reads `hl=z[112+(i−1)%9]`, `hr=z[112+i]`; `extra` places `−hr` on α, `hr` on π, `(hl+hr)/2` on w — consistent slot by slot with the kernel's `T_i`/`L_i` decomposition; `switch_i` gets `2z[112+i]` on `b_i` | `kernel_final_checks.py` §2 |
| E10 | B&B bookkeeping | terminal ub = max(discarded_upper, live heap max) ≥ every leaf ub; leaves ≤ parent; sampled sup 3.96e-6 ≪ terminal 9.836e-4; outward `nextafter` on float endpoints | `kernel_final_checks.py` §3 |
| E11 | `check_q0_closure_symbolic.py` source inspected | closure terms **were** genuinely added (lines 25-27: `pi ← −Σz[112:]`, `b_i ← 2z[112+i]`, `base-left/right`, `width ← (h_{i−1}+h_i)/2`; lines 46-47 mirror it in the `E` assembly). Its `hl`/`hr` sit on swapped sides relative to the kernel (both are correct labelings; the object is an identity, so this is immaterial). Control ran: `q0_closure_symbolic_control.json`, 218 formal atoms, `exact_identity: true` | read of `lead/check_q0_closure_symbolic.py` |

## Retractions of my own intermediate findings (do not cite)

* `module_closure_min.py` / `kernel_feasibility_audit.py` "negative residuals" / "1e154 optimizer
  points" — artifacts of (a) minimising the code's *max* form and (b) unconstrained optimisers
  escaping the domain through float overflow. **Withdrawn.**
* My mid-audit `quad`/`scalar_quad` "unsoundness" alarm — **withdrawn**; E5 shows the helper is a
  sound upper envelope for the concave radial maximum, and the lead's `Q(A,B) = max_{0≤y≤1}(Ay²+By)`
  reading is the correct one.
* The `h = z[73+2i+1]+z[73+2j]` claim — **withdrawn** (see corrected map above).
* My earlier statement that rings 3-8 admit `α` up to `2π` — **withdrawn**; the kernel's ring domain
  is `α ∈ [0,π]` for every ring (line 108).

## Unresolved / obligations

1. **U1 (geometry, outside this kernel).** The kernel certifies
   `constant + Σ sup(factor) ≤ 3.09579… < π` for its box model. Promotion still needs
   *actual configuration ⇒ a point of the admissible state domain*, with `u,v ∈ [0,1]` from
   `ρ ≤ R` and `q ≥ qmin` from the width/closing constraint (lead's C820 half-plane input). I did
   not re-derive that implication.
2. **U2 (semantics of the assembled dual).** That the assembled object majorises the cover area
   (positive triangle areas tiling the target, no inclusion-exclusion needed per lead) is the
   geometric step; `check_q0_closure_symbolic.py` checks only the *coefficient identity* of the
   assembled dual against a formal residual dictionary. Verified genuine (E11), but it is an
   identity check, not a geometric proof.
3. **U3 (`tol = 0.001`).** Pinned per-factor uppers; the tightest margin is 9.6e-4 on `ring3`, and
   the total's margin to π is 0.0458 (≈4.5%). The tolerance is not binding; this is a note, not a
   gap.
4. **U4.** This is a computational-interval certificate, not a proof. No promotion to `proved`
   without U1/U2 (analytic enclosures + the geometric reduction).

## Repro

```
cd research-2026/team-current/cline2-closure-kernel
py -3 q0_closure_kernel_audit.py            # E1-E3
py -3 kernel_pointwise_check.py             # E4 (a few minutes)
py -3 kernel_final_checks.py                # E5, E9, E10
py -3 kernel_derivative_formula_check.py    # E6, E7
py -3 kernel_source_index_crosscheck.py     # corrected index map
py -3 clip_window_test.py                   # E8
```
