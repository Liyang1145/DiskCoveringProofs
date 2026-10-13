# Cosine-envelope cell: independent kernel audit (node 26) - corrected

Artifacts audited: lead/certify_cosine_envelope_cell.py, lead/certify_energy_cell.py,
lead/cosine_envelope_cell_certificate.json. Independent instrument: cosine_cell_audit.py
(no lead helper import). Reproduction: py -3 -B -X utf8 cosine_cell_audit.py

## (S) Exact Schur identity - hard-asserted, exact Fraction, zero residual
For each of the 3 fields: alpha is a positive probability vector over the 51 carrying edges
(the assert is len(alpha) == len(edges), which is 51 here), the 36 stored pairs are in the
canonical order with positive weights, and with M_ij = -w_ij (i != j), M_ii = sum_{j != i} w_ij
the exact identity Laa - M == Laf . Lff^{-1} . Lfa holds with residual EXACTLY ZERO
(Fraction Gauss-Jordan for Lff Y = Lfa). All asserted; no printed-only quantity.

## (M) Whole-arc minorants - interval Taylor, expanded arcs, shifted target
Every stored minorant line is checked on the WHOLE arc with an INTERVAL Taylor bound
(h(z) = 1 - cos z - s z, h(z) >= h(m) - |h'(m)| r - r^2/2), cos/sin evaluated with iv on I(F(.))
inputs, radius inflated outward, and the comparison is lo(bound) >= hi(intercept) - 1e-6.
The arcs are the stored decimal endpoints EXPANDED to also enclose my own interval vertex ranges.
Result, asserted: all 73 lines proved, worst subdivision depth 9. No asin, no sin-monotonicity,
no tangent-only argument.

## (V) My own interval vertex bound ON THE SAME OBJECT
The bound is recomputed with every intercept shifted by -1e-6, i.e. exactly the object that (M)
proved, with the mixture weights W_k = sum_f beta_f * 2 w_k^{(f)} >= 0 checked against the recorded
per-pair weights, beta a checked probability vector, per-pair gamma summing to 1 with nonnegative
entries. Asserted results:

    energy lower  = 0.147772046945512182
    radius lower  = 0.384411299190739425  >  0.38   (asserted)

The stored 0.3844117100697405393769... refers to the UNSHIFTED interception; it is a DIFFERENT
quantity and is not claimed to be reproduced here. That gap is the 1e-6 shift, as intended.

## Factor bookkeeping (corrected wording)
The certified energy form is E = sum_k W_k (1 - cos z_k) with W_k = sum_f beta_f * 2 w_k^{(f)}:
the factor 2 lives inside W_k (twice the Schur weight per field), so writing
sum_k W_k * 2 (1 - cos z_k) would double count. In certify_energy_cell.py the per-pair factor
2 * w appears inside the sum over pairs, consistent with W_k as defined here.

## Limits and remaining structure (not "only global far")
Audited: cell-26 kernel only (Schur exactness, minorant validity with the 1e-6 object, mixture
weights, own interval vertex bound). NOT audited: (a) the derivation of the cosine energy form from
the Schur matrix (modelling step); (b) the cell splitting/coverage logic and the 131-leaf pilot;
(c) the class-complement cover -> oracle interface, which still needs its own audit (this is a
separate outstanding obligation, not part of "global far"); (d) any global claim (artifact scope:
node26 only, NOT global).

## Full-interval rewrite: RESOLVED (2026-09-25)

The earlier revision of this audit used high-precision `mp` scalars with endpoint extraction, which is
not an interval certificate. With the interface fix provided by the lead the check now runs in genuine
interval arithmetic end-to-end:

* exact Fraction endpoints from the raw dyadic tuples: `dyadic(t) = (-1)^sign * man * 2^exp`;
* `taylor_ok` works only with Fractions (`mF = (aF+bF)/2`, `rF = (bF-aF)/2`), converts to intervals via
  `I(F)` (never `mp.iv.mpf(F(...))`), and proves `bound_iv = hm - abs(hp)*I(rF) - I(rF)**2/2
  >= I(intercept - 1/10^6)`;
* arcs are the exact Fraction hull of my interval vertex ranges and the stored endpoints, with explicit
  containment asserts `I(aF) <= z`, `I(bF) >= z` for every vertex interval (no padding, no guess);
* the final comparison is an interval comparison `iv.sqrt(...) > I(F(19,50))`.

Readings with this revision (all asserted, no printed-only quantity):
Schur residual exactly zero for all three fields (exact Fraction); **73/73 minorant lines proved**,
worst subdivision depth 9; shifted-object **energy lower 0.147772046945512182**, **radius lower
0.384411299190739425 > 0.38**. The stored `0.3844117100697399...` remains the *unshifted* object and is
not claimed to be reproduced.

Cause of the earlier failure (recorded for accuracy): a real traceback in `mpmath` interval
construction when an interval was passed where a scalar was expected (`ctx_iv.convert_mpf_`), fixed by
using the raw dyadic accessor `_mpi_` with exact Fraction conversion. This was a local interface error
in my code, not a defect of the mpmath interval interface as a whole.
