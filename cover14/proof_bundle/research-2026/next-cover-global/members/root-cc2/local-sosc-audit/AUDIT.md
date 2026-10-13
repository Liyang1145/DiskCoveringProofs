# root-cc2 local-sosc-audit: interface audit of lead/LOCAL-SOSC-PROOF.md +
# local_sosc_certificate.py  (CORRECTED version, supersedes the first draft)

Scope `members/root-cc2/local-sosc-audit/`. Lead artifacts read-only. One source re-run
plus one comparison against the lead's published control matrix
(`lead/local-kkt-matrix-control.json`). **No claim registered** (lead instruction).

## Verdict

**The interface closes.** My first draft reported a "rank <= 4 versus invertible 5x5"
objection; that objection was an elementary linear-algebra misreading on my part and is
**retracted** (section 4). With the centre ordering corrected in my own scripts (the
lead's diagnostic: I had the C orbit's two halves swapped), my independent reconstruction
of the certificate's 28x5 equilibrium matrix agrees with the lead's published matrix to
**4.4e-17 over all 140 entries**, and every structural statement of the certificate checks:

| statement | my independent value |
|---|---|
| all 24 contacts equal `r^2` at the candidate | deviations <= 9.7e-62 (all OK) |
| the two vanishing columns (`s`,`z`) | ~1e-36 by finite differences; proved analytically in the document |
| rank of the 28x5 equilibrium matrix | **4** (singular values 1.1430, 0.96294, 0.55898, 0.35861, ~1e-36) |
| rank of `[A; normalization]` (29x5) | **5** |
| published weights annihilate all 28 rows | max `|A^T w| = 4.4e-18` |
| published weights | all positive, sum 0.27173765101674 |

The rank argument is exactly the lead's: rank(A) = 4 gives a 1-dimensional null space for
the multiplier vector; appending the normalization row makes the system rank 5, hence the
weights are determined and strictly positive. There is no incompatibility between
"rank 4" and "invertible five-row system": `M = [[1,-1],[0,0]]` has rank 1 and becomes
rank 2 when the row `[1,1]` is appended, with positive null vector `(1/2, 1/2)`.

## 1. Calibration performed first (per instruction)

`py/fix10_corrected_calibration.py` -> `evidence/fix10_corrected_calibration.txt`:

* centre ordering taken from the certificate itself: `C[i] = (sx*a, sy*b)` for
  `sx in (-1,1) for sy in (-1,1)`, then `(sx*c, sy*d)` the same way, then the six axis
  sites `(-s,0), (s,0), (z,0), (-z,0), (0,-t), (0,t)`;
* **24-contact calibration**: every contact value equals `r^2` to <= 9.7e-62;
* the rebuilt 28x5 matrix reproduces the lead's published rows; selected rows
  `[normalization, 0, 1, 8, 9]` agree entry-by-entry (row 0: `0.3635107036,
  -0.01871109738, 0, -0.2529825653, -0.2491780426`; row 1: `-0.1444704299,
  0.3794859696, 0, 0.04403469447, -0.09903108376`; row 8: `0, 0.2793173356,
  -0.291941119, 0.006991608566, 0`; row 9: `0, -0.04861858177, 0.1575326176,
  -0.1417991314, 0`).

## 2. What the certificate establishes (my reading)

Rank 4 of the equilibrium matrix plus a positive normalized multiplier vector, supported
exactly on the five orbits, gives exact KKT for minimising `R` subject to `f_k(C) <= R`;
the penalized 28x28 matrix being positive definite (interval LDL, all pivots strictly
positive, min pivot lower bound 0.06386145383348588) gives `v^T H v > 0` on every
direction that annihilates the positive-multiplier gradients and the rotation gauge. The
critical cone of the relaxation lies inside that subspace, so this is a valid (strictly
stronger) SOSC and the direct Taylor argument of the proof's section 4 follows. Scope
stays local modulo rotations, not global.

## 3. Interface points worth stating (not defects)

* The document's section-2 sentence "the full stationarity matrix has rank <= 4, they span
  all its rows" concerns the **row space** of the 28x5 system (the four selected physical
  rows span it, so all 28 coordinate equations are satisfied). True here; it is not a
  column-space statement. This is exactly the distinction that produced my false
  objection.
* My checks use the box midpoint, so my near-zero singular value is ~1e-36 while the
  lead's exact-integer computation reports ~1e-17. Both are numerical zero against the
  other four (>= 0.35), so the rank decision is not delicate; the trusted object remains
  the interval computation.
* The six zero-multiplier faces are **tight** contacts (`f_k = r^2`) outside the KKT
  support, at flattened indices 11, 14, 17, 20, 22, 23; the two genuinely slack faces are
  not in `g['faces']` at all. My first draft's slack/tight labelling was wrong because of
  the swapped C ordering (it resolved each face record to the wrong physical triangle);
  corrected above.

## 4. My errors (corrected; the false objection is withdrawn)

1. **False "mutual exclusion" objection (retracted).** I claimed "rank <= 4" and
   "the selected 5x5 is invertible" cannot both hold. They concern different objects: rank
   4 of the 28x5 matrix describes its row space / the multiplier null space, while
   invertibility of the 5x5 built from four selected rows plus normalization describes
   those five rows being independent. A rank-4 28x5 gains a full-rank 29x5 when the
   normalization row is appended. Nothing was registered from the objection.
2. **Swapped C-orbit ordering in my scripts.** I wrote the C orbit as
   `(+c,-d), (+c,+d), (-c,-d), (-c,+d)` instead of the certificate's
   `(-c,-d), (-c,+d), (+c,-d), (+c,+d)`. Every check downstream of that list
   (`iface05`–`iface09`) consequently used the wrong physical sites: wrong contact values,
   wrong slack/tight labels, a nonzero `s`/`z` column, rank 5 instead of 4, and residuals
   of 4–9% for the published weights. After the fix all of those become exact. This single
   list was the root cause of my entire disagreement.
3. **Finite differences quoted as "exact".** I wrote that a 1e-36 finite-difference
   residue "is exact". The vanishing of the `s`/`z` columns is an analytic fact (document
   section 2) that my numbers support but cannot prove. Wording corrected.
4. I also mixed the *family-parameter* and *site-motion* conventions in
   `iface02`–`iface07`; the current scripts use the site-motion convention (the
   certificate's) and are calibrated against its published matrix.

## 5. Scope

Local strict-optimality-modulo-rotations only. Not audited: C1173's contact-curve
derivation, the relaxation-to-covering interface, and the C1177/q11 item (out of scope).
