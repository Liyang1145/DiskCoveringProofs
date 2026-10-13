# root-cc2 anchor-value-branch: numeric structure diagnostic of the fixed-anchor value V
# (see "Corrections" below: the previous version of this file mis-stated what the ranks mean)

Scope `members/root-cc2/anchor-value-branch/` (only). Lead artifacts read-only.
**No claim registered**; `lead/` untouched. Numeric diagnostic only.
Evidence: `evidence/validation01.txt`, `evidence/kkt02.txt`, `evidence/null01.txt`,
`evidence/rank02.txt`, `evidence/active01.txt`.

## Corrections to my previous version (all six accepted)

1. **The assembled matrix is the PRIMAL active-constraint Jacobian**, not a full KKT
   system: 62 rows x 61 columns = 28 site + 32 witness + 1 radius columns, one row per
   active constraint. It contains no stationarity rows and no multiplier variables. My
   script labels it "KKT"; that label was wrong. (Confirmed in `py/validation01.py` (0).)
2. **Full column rank of the site/radius submatrix does not mean the sites are pinned**
   when witness motion is allowed. My own null vector is the counterexample: it has a
   nonzero site part (sites 8, 9, 10, 11) together with a nonzero witness part. Restricting
   to those columns is a **column restriction, not a projection and not an elimination**;
   I withdraw the "projection/elimination" language and the "sites pinned" inference.
3. **`x_2 = x_7 = 0` are normalised angular deficits**, not site coordinates, and there is
   no "x-axis site with x = 0": the x-axis sites are 8, 9 (their `y = 0`), while the sites
   with x-coordinate 0 are 12, 13. The `x -> x^2` non-invertibility inference is deleted;
   nothing here depends on it.
4. **IFT non-singularity is sufficient, not necessary.** A singular Jacobian proves neither
   that `V` is non-differentiable nor that no explicit branch exists. The only correct
   statement is that the raw IFT applied to this active set is unproven. That is all the
   nullity number supports.
5. **Zero-multiplier faces are tight at the candidate**, so demanding strict slackness over
   the whole domain already fails at the candidate; and a **lower bound does not need their
   inactivity at all** — one may simply **drop** those constraints, obtaining a convex
   relaxation whose value is `<= V`. My "(S)" formulation (uniform slackness separation of
   the zero-multiplier faces) was over-demanding and unnecessary; it is withdrawn. The
   usable route is to build the lower bound/branch on the **relaxed problem after deleting
   the zero-stress faces**, keeping the possibly degenerate X pair.
6. **A rank-2 witness block is only relevant for faces with positive multiplier.** At
   `lambda = 0` the KKT/adjoint system and the constraint rank differ, so my sentence "every
   witness block has rank 2, hence no witness is under-determined" does not apply to
   inactive/zero-multiplier faces. Withdrawn as stated (it remains true per-face as a
   statement about the three constraint gradients alone).

## What the diagnostic actually shows (nothing more)

Setup: the calibration's own primal point of the fixed-anchor SOCP for q10/879
(`lead/fixed-anchor-convex-probe.json`), `r = 0.33173203427623366`; unknown vector =
14 sites (28) + 16 witnesses (32) + radius (1) = 61; one row per active constraint.

* Anchor-owner incidences: **20 of 20 active**.
* Face-site incidences: **42 of 48 active**; faces 14 `[4,6,12]` and 15 `[5,7,13]` are
  slack by `1.1e-2` at the candidate.
* A least-norm multiplier solution gives **zero multiplier on faces
  `1, 4, 7, 10, 12, 13`** and positive multiplier on `0, 2, 3, 5, 6, 8, 9, 11`
  (`+0.0336` / `+0.0758`), matching the lead's force-cascade statement. Numeric only: the
  multiplier vector is not unique and I do not claim an exact zero set.
* The primitive active-constraint Jacobian has numeric rank 56 / nullity 5. The null space
  consists of 4 directions supported only on the two slack witnesses, and **1 direction
  with a nonzero site part on sites 8, 9, 10, 11 (pure x-motion) plus a witness part on
  exactly the six zero-multiplier faces**. All ranks are diagnostics, not exact statements.
* Dropping the six zero-multiplier faces leaves a 44-row Jacobian (8 faces x 3 incidences +
  20 anchor incidences) with numeric rank 41 / nullity 3: deleting those faces removes the
  mixed site/witness direction, but the relaxed Jacobian is **still numerically singular**,
  so the relaxed system is not immediately non-singular either and needs its own exact
  treatment.

## The route this leaves (no new computation)

* A lower bound on `V` may be taken from the **convex relaxation** that deletes the
  zero-multiplier (zero-stress) face constraints: for that relaxation the deleted faces'
  witnesses separate and impose no coupling, so the relaxed value is `<= V`. No statement
  about those faces becoming inactive is needed.
* The relaxed problem **retains** the possibly degenerate X-site pair rather than assuming
  it away. Whether it admits an explicit active-branch representation is exactly the open
  question this note does **not** settle: the diagnostic only shows that the raw active set
  at the candidate gives no IFT branch and that merely deleting the six faces does not,
  numerically, repair singularity.
* C1355's effective constant is the existing quantitative input. The lead's framing — can
  the zero-`lambda` constraints be relaxed away to obtain an easily analysable branch — is
  the correct next obligation, and it requires an **exact** dependency or a positive
  separation argument, not a numeric rank.

## Scope

Finite diagnostic of the active set at the candidate. No optimiser run, no grid, no claim,
no modification of lead files. Every rank in this note is explicitly a numeric diagnostic.
