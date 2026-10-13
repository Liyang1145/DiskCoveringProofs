# root-cc2 DEAD: failures, invalid artefacts, method limits (not disproofs)

Separated from the log: nothing here is evidence against a mathematical proposition
unless stated as a counterexample.

## False claims I made and retracted (registered)

* **C1160 (retracted, was "proved"):** I claimed `r^2-(A-z)^2 = r^2-z^2` because
  "`A - z = r - sqrt(r^2-z^2)`". The true relation is `A - z = (s-z)/2`, and at the root
  `A - z = 0.3082777942140979` vs `r - sqrt(r^2-z^2) = 0.2748453717541834`. The
  radicands differ (`0.0150109441595389` vs `0.0032360923728978`), so `sigma_B` is an
  independent branch condition and the candidate file's original text was right. My
  quoted sympy expression is the *non-zero difference* (`-0.2965…`), i.e. a constraint,
  not an identity. Root cause: asserted a geometric relation from a mis-remembered
  formula instead of substituting `A = (s+z)/2`, and wrote the numeric check so that it
  compared `B`'s radicand with itself and could not falsify the claim.
* **C1161 (retracted, was "numeric"):** (i) I claimed the lead's linear solve returns
  the *lower* circle-circle intersection `(0.3082777942, 0.5111378551)` and called it a
  unit-circle contact; its norm is `0.5969062785`, i.e. it is not on `S^1`, while the
  upper point `(0.6187591879, 0.7855807198)` has norm `1.0` and *is* what the solve
  returns. (ii) I claimed `F` is a sum of two non-negative terms; the coded second term
  `|p1-S1|^2 - r^2` is signed. Root cause: I computed the correct numbers, then stated a
  different (false) statement, and never tested the statement against its own numbers.
* Related to the same episode: the audit text that reported "radicand agreement 1e-62"
  in `audit01_root.txt` is invalid as a witness (it compared the wrong pair). The file is
  kept for traceability, and the corrected numbers are in `evidence/diag_disputed.txt`.

## Interface / precision care items (fixed, not errors of rigor)

* The coded `F` equals `e(e+1)` with `e = |p1|^2-1` (exact, since `p1.S1 = v1` is
  enforced), and my kernel's `F_tilde` is the same expression (verified at 200 digits to
  `7.3e-203`). The alternative normalization `det^2 e` (with `h = |p^2|/det^2 = 6.17465845489`)
  is a *different* function and is not what the certificate evaluates.
* The certificate's box is declared as the exact mpf/dyadic interval it is; the mpf of a
  decimal literal is exact (not rounded) while the *decimal* literal sits ~6e-92 outside
  the dyadic endpoints, which is 86 orders below every margin. No decimal-box claim is made.

## Invalid artefacts (do not use)

* `evidence/audit02_contacts.txt`, `evidence/audit03_coverage.txt` — contact/coverage
  portrait computed from the **incomplete** 10-centre free D2 family (I forgot the two
  fixed x-axis orbit-2 pairs), so `R_cover = 0.5827` at `(-1,0)` was an artefact of the
  missing sites, not a hole of the configuration. Additionally the OLD-hprec side used
  `json['centers']` (float64) instead of the exact `json['th']` literals; per the lead's
  instruction that old-roof portrait is invalid and no conclusion uses it.
  Superseded by `evidence/audit04_contacts_corrected.txt`.
* `members/candidate/THREE-EQ-AND-NEW-ROOT.md` §1 sentence that `sigma_B` is not forced
  by `sigma_t` and that both are "genuine branch conditions" — wrong: with
  `A - z = (U-z)/2 > 0` one has `A - z = r - sqrt(r^2-z^2)`, hence
  `r^2 - (A-z)^2 = r^2 - z^2` identically and `sigma_B = sigma_t` is forced. Its
  numbers are fine; only that algebraic claim is wrong. (Not used by the certificate,
  which evaluates the branch directly on the box.)
* `members/candidate/THREE-EQ-AND-NEW-ROOT.md` §5 "the contact structure changed" —
  index-label artefact; see `REPORT.md` §4 / `evidence/audit04_contacts_corrected.txt`.

## Method / implementation failures (mine)

1. Gradient slots holding **plain intervals** instead of derivative-carrying objects:
   products of gradients silently collapsed to scalar interval arithmetic, so `J`'s
   gradient came out identically 0. Caught by calibration check (3) (compare against
   exact sympy), not by inspection.
2. **Nested `Jet` objects** for gradient/Hessian slots: `Jet.__init__` allocating zero
   Jets recursed until `RecursionError`.
3. **Level-tagged** jet scheme with a "level-0 factor" conflation: the chain rule
   applied to the *variables* made the second-order term `F_{zk}` vanish, giving
   `dJ = 0` again.
4. **"Unit-direction" Val coordinates** with the perturbed *value* (`x_k + 1`): radicands
   like `r^2 - z^2` became negative and `sqrt` correctly refused. Fix: keep values at the
   true point and carry the direction in the derivative slot only — hyper-dual
   (`d^2 = e^2 = 0`, mixed `d*e` coefficient = second derivative) does exactly this.
5. `mpmath` interval traps: `iv.mpf([1,2])` builds a **thin** interval at 1 (use
   `iv.mpf([mp.mpf(1), mp.mpf(2)])`); `mp.mpf(iv)` fails on non-degenerate intervals
   (use `x.a.a` / `x.b.b`); `iv.sqrt` of an interval straddling 0 raises; division by an
   interval straddling 0 silently yields `[-inf, +inf]` (guard added).
6. Krawczyk bookkeeping: `ok_i1` initially required `K.lo < X.lo` (backwards) and the
   face-margin diagnostic had the wrong sign, so a passing certificate printed FAIL for
   two runs. Fixed; the containment condition is `X.lo < K.lo` and `K.hi < X.hi`.

## Budget / scope stops

* The old-hprec branch portrait was abandoned on the lead's instruction (float centres,
  not an input to the certificate). No further effort spent there.
* No global grid, no k11 work, no optimality claim: out of scope for this assignment.
