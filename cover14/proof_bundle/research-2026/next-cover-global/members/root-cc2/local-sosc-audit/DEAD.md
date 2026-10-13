# root-cc2 / local-sosc-audit: DEAD entries (errors and method limits)

Scope `members/root-cc2/local-sosc-audit/`. Local-only, no global content.

## DEAD-1: my "rank <= 4 versus invertible 5x5" objection (WITHDRAWN, elementary error)

**What I claimed.** That the proof's rank-<=4 premise and the certificate's invertible
5x5 system are mutually exclusive, and that the published weights therefore cannot
satisfy stationarity.

**Why it is dead.** Rank 4 of the 28x5 equilibrium matrix describes its *row space* (or
equivalently the null space of the multiplier vector); invertibility of the 5x5 built from
four selected rows plus the normalization row describes those five rows being independent.
Appending the normalization row to a rank-4 28x5 matrix gives a rank-5 29x5 system — the
lead's example `M = [[1,-1],[0,0]]` (rank 1) plus the row `[1,1]` (rank 2, positive null
vector `(1/2,1/2)`) is the exact analogue. Retracted; nothing was registered from it.

## DEAD-2: swapped C-orbit ordering in my scripts (ROOT CAUSE of every disagreement)

**What went wrong.** In `iface05`–`iface09` (and the geometry scribbles) I built the centre
list as `(+c,-d), (+c,+d), (-c,-d), (-c,+d)`. `local_sosc_certificate.py` builds
`(sx*c, sy*d)` for `sx in (-1,1) for sy in (-1,1)`, i.e.
`(-c,-d), (-c,+d), (+c,-d), (+c,+d)`. The two halves were swapped.

**Consequences (all artefacts).** Wrong physical sites in every contact → contact values
not equal to `r^2`; a spurious "6 slack faces at `R^2-r^2 = 0.207204`" (there are no
such slack faces; all 24 contacts are tight, and the two genuinely slack faces are not in
`g['faces']`); a nonzero `s`/`z` column; rank 5 instead of 4; residuals 4-9% for the
published weights; a different 5x5 solution with negative entries.

**Fix / verification.** `py/fix10_corrected_calibration.py`: with the certificate's
ordering, all 24 contacts equal `r^2` (<= 9.7e-62), the rebuilt 28x5 matrix matches the
lead's published `lead-kkt-matrix-control.json` to 4.4e-17 over all 140 entries, its rank
is 4, `[A; normalization]` has rank 5, and the published weights give
`max |A^T w| = 4.4e-18`.

## DEAD-3: "finite differences prove the vanishing columns" (overclaim, not an error of fact)

A finite-difference residue of `1e-36` is not a proof of an exact zero. The vanishing of
the `s`/`z` columns is analytic (document section 2); my numerics only support it.

## DEAD-4: mixed conventions in `iface02`–`iface07`

Those drafts differentiate a *family parameter* (which moves several sites at once)
instead of a single *site coordinate*. Both are legitimate objects, but only the
site-motion convention matches the certificate's gradient rows. Superseded by
`fix10_corrected_calibration.py`.

## Method limits (kept, not errors)

* My checks evaluate the box midpoint; the rank decision there is not delicate (four
  singular values >= 0.35 against a ~1e-36 remainder), but the trusted object for exact
  signs remains the interval computation.
* I did not re-derive C1173's stationary contact curve, and I did not read or run the
  explicit-box certificate (`LOCAL-EXPLICIT-BOX.md`,
  `local_neighborhood_certificate.py`); the box part of C1182 is outside my review.
