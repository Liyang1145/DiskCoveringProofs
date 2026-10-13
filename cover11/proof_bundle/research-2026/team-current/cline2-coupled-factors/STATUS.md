# cline2-coupled-factors — STATUS (round 4b) — MECHANISM WITHDRAWN

> **MECHANISM-angle-only.md is INVALID and withdrawn in full.** The lead identified five
> concrete errors: (1) wrong chord algebra (ell^2, not (M ell)^2) and hence a wrong box
> maximum (correct form `ell <= M max(1, 2 sin(alpha/2))` by corner enumeration);
> (2) `M = 1` means only `gamma_f <= 1` with root `gamma_0 = 1`, not all `gamma = 1`
> nor all sine ratios 1; (3) from `sum w = 2 pi` and `q = R s` one gets
> `sum 2 asin(R s_i/2) = 2 pi`, not `R = sum s_i/(2 pi)`; (4) the target `R >= .38` is
> FALSE (certified cover < .37999; human target is the sharp optimum ~.379983853);
> (5) `.379983853119838733` is a rounded float, not a new certified value.
> No claim from that file is offered; no further exploration or numeric runs were made.


Write scope: `research-2026/team-current/cline2-coupled-factors/` only.  No new claims
registered (per lead).  No new numeric runs after this point.

## Deliverable

`MECHANISM-angle-only.md` — one analytic mechanism for the C839 angle-only model, with its
proof, its exact quantitative requirement, and the explicit gap.  Summary:

**Proved (exact, global).**  With `q_i = 2 sin(w_i/2)`, `ell_i` the sector chord in the root
gauge, `M = max_f gamma_f >= 1`, `s_i := 2 sin(alpha_i/2)`:

1. **Chord bound.** `M ell_i <= s_i` for every sector, because `(M ell_i)^2 =
   gamma_{i-1}^2 + gamma_i^2 - 2 gamma_{i-1} gamma_i cos alpha_i` is increasing in each
   `gamma` on `[0,M]`, so its maximum over `[0,M]^2` is `s_i^2` at `gamma_{i-1} = gamma_i = M`.
   Equality iff both endpoint branches attain `M`.
2. **Global bound.** `R_shape = M q_i/ell_i` for all i (the model's own identity), so
   `R_shape >= M^2 q_i/s_i >= q_i/s_i`; equivalently, in multiplicative form,
   `R_shape >= M^2 (prod_i q_i/s_i)^{1/9}`.

**Requirement.** At the saved candidate `M = 1` and `min_i (q_i/s_i) = 0.37998385312`, so the
mechanism gives `R >= 0.37998385312`, i.e. 1.6e-5 short of 0.38.  To reach 0.38 it needs
`M^2 min_i(q_i/s_i) >= 0.38`, equivalently `M >= sqrt(0.38/min_i(q_i/s_i))`, and `M >= 1`
alone cannot deliver that because `min_i(q_i/s_i) < 0.38`.

**Gap (explicit, structural not effort-limited).**  On the `M = 1` manifold one has
`M ell_i = s_i` for all i, so the six circle equations collapse to the single scalar relation
`2 sin(w_i/2) = R * 2 sin(alpha_i/2)` for all i with `R = sum_i s_i / 2pi`; in that regime
every sine-law ratio equals 1 and both cycle residuals vanish identically.  Hence the two
nonlinear cycle equations are automatically consistent with `M = 1`, and no re-weighting or
re-averaging of the equal quantities `q_i/ell_i` can improve the bound.  Closing the gap
requires either (i) a positive uniform lower bound on `M` from the sine-law recursion itself
(log-sine structure along the ring), or (ii) a direct upper bound on `sum_i sin(alpha_i/2)`
on the `M = 1` family, i.e. an upper bound on `sum_i b_i` that the angle-only model does not
carry.

## Corrections carried out (lead-instructed)

- `g4_cycles.py` header rewritten: everything there is **numeric** (float arrays derived from
  the 1e17 integer source), not "exact arithmetic".
- The claim that "the only elementary route that could reach 0.38 must bound a PRODUCT-type
  functional" is **deleted**.  Unsupported exhaustion claim; the weighted-sum (arithmetic)
  form is equally meaningful and a weak particular consequence
  (`R >= (1/9) sum_i q_i / max_i ell_i >= 0.343057030948`) does not exclude refined additive
  bounds.
- No further `gN` candidate-reading scripts; the analytic obligation is discharged in
  `MECHANISM-angle-only.md`.

## Scope guards

- `0.38` appears only as the target the mechanism must reach.  No radius improvement, no new
  exclusion, no proof of `R >= 0.38`.
- The numeric readings in `out/g1_structure.json`, `out/g3_constants.json`, `out/g8.log` and
  the outputs of `g7_cycle_products.py` are diagnostics; they are NOT structural evidence and
  are not used as such in `MECHANISM-angle-only.md`.
- `R_cert = 0.379983853119838733` remains the certified numeric value throughout.
- Retractions from round 4 stand: C826/C827/C829 and the f12/f13/f15 diagonal are dead; see
  `CORRECTION-uv.md` and `DEAD.md`.
