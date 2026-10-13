# root-cc2 / local-sosc-audit status  (CORRECTED)

Scope `research-2026/next-cover-global/members/root-cc2/local-sosc-audit/` (only). Lead
artifacts read-only. One source re-run; one comparison against the lead's
`lead/local-kkt-matrix-control.json`. **No claim registered by me** (lead instruction).

## Verdict on the assigned obligation

**The exact-KKT/SOSC interface closes.** My first draft's "rank <= 4 versus invertible
5x5" objection was an elementary linear-algebra misreading and is retracted. After fixing
a centre-ordering bug in my own scripts (C orbit halves swapped), my independent
reconstruction reproduces the lead's published 28x5 matrix to 4.4e-17 over all 140
entries, and:

* all 24 contacts equal `r^2` (deviations <= 9.7e-62);
* rank of the 28x5 equilibrium matrix = **4** (singular values 1.1430, 0.96294, 0.55898,
  0.35861, ~1e-36);
* rank of `[A; normalization]` (29x5) = **5** — compatible, exactly as the lead said;
* the published weights annihilate all 28 rows (max `|A^T w| = 4.4e-18`), are all
  positive, and sum to 0.27173765101674;
* the `s`/`z` columns vanish (analytically proved in the document; my finite differences
  show ~1e-36);
* the interval-LDL pivots are all strictly positive with min lower bound
  0.06386145383348588, so the penalized matrix is positive definite and the SOSC holds on
  the critical subspace (a valid strengthening of SOSC).

## Root cause of my earlier disagreement (single bug)

In every script after the first calibration I built the centre list as
`(+c,-d), (+c,+d), (-c,-d), (-c,+d)`, whereas `local_sosc_certificate.py` uses
`(-c,-d), (-c,+d), (+c,-d), (+c,+d)` (i.e. `C[i] = (sx*c, sy*d)` with
`sx in (-1,1) for sy in (-1,1)`). With the halves swapped, every downstream quantity
referred to the wrong physical sites: contact values, slack/tight labels, the vanishing
columns, the rank and the weights. `py/fix10_corrected_calibration.py` is the corrected
object and is calibrated against the lead's published matrix before any further check.

## Scope reviewed for C1182 (requested)

Reviewed, for C1182: the exact-KKT interface, the rank argument, the
D2-orbit structure and the support (18 contacts in 5 orbits, 6 zero multipliers), and the
28x28 penalized-Hessian SOSC reasoning. **Not reviewed (declared excluded):** the explicit
coordinate box and its convex-penalty certificate (`LOCAL-EXPLICIT-BOX.md`,
`local_neighborhood_certificate.py`, `local-neighborhood-certificate.json`); I did not run
or read those. So my review covers C1182's local strict-optimality-modulo-rotations
content with the box part carried explicitly as unverified by me.

## Evidence / repro

```
cd research-2026/next-cover-global/members/root-cc2/local-sosc-audit
py -3 -B py/fix10_corrected_calibration.py     # 24-contact calibration + 28x5 matrix
                                              # + comparison with the lead's control
```
Output: `evidence/fix10_corrected_calibration.txt`. Superseded drafts (wrong ordering or
mixed conventions) kept for traceability: `iface01`–`iface09`, `rank01_28x5`,
`leadmatrix01`, `diag_contact_values`. Write-up: `AUDIT.md`.

## Next executable step

None for this obligation. Remaining scope notes (row-space versus column-space wording in
the proof's section 2; midpoint versus interval in my checks; the six zero-multiplier
faces being tight contacts) are cosmetic or already consistent. Global content, C1173's
curve derivation and C1177/q11 are outside this audit.
