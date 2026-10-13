# C922 root-threshold: independent audit (r20-rigidity)

Objects: `lead/contract_exact_root_threshold.py`, `lead/exact_root_threshold.json` (claim C922).
Scope: inclusion logic, constants, precision and interface of this contraction; no lead edits.

## Inclusion logic (verified sound)

The script contracts the known C891 root box with a Krawczyk-type step and *preserves inclusion* of
the already-proved root:

* `f0 = system(c)` is the interval enclosure of `f` at the **fixed dyadic centre** `c`;
* `Y` is a numeric inverse of the midpoint Jacobian, wrapped as an interval matrix. This is only a
  **proposal** for a preconditioner: because the root is *already known* (C891), the inclusion identity
  below holds for **any real matrix `Y` whatsoever** — no invertibility, no conditioning, no rank
  assumption is needed, and neither the float inversion nor its accuracy is load-bearing for soundness.
  (Invertibility would only be needed if the same step had to *prove existence/uniqueness*; here it must
  only *preserve inclusion* of the known root.);
* at each iteration the Jacobian enclosure is taken over `hull(c, X)` (coordinatewise
  `[min(lo), max(hi)]`), not over `X`. This is the correct MVT domain: after the first intersection the
  fixed centre `c` is generally **outside** `X`, and the segment from `c` to any `x ∈ X` lies in the
  hull. The script's comment states exactly this; the implementation matches;
* `K = c − Y f(c) + (I − Y J(hull))(X − c)` satisfies the identity
  `x* = c − Y f(c) + (I − Y J̄)(x* − c)` with the **integrated Jacobian**
  `J̄ = ∫₀¹ J(c + t(x* − c)) dt` along the segment from `c` to `x*`. Two points of care: (i) the vector
  mean value theorem does *not* provide a single point `ξ` that works for all twelve equations, so the
  integrated (or rowwise) form is the correct one; (ii) `J̄` is enclosed by the interval matrix
  `J(hull(c, X))` because every argument `c + t(x*−c)` lies in the hull and intervals are convex, so
  integrating an interval-valued enclosure stays inside it. Hence `x* ∈ K(X)` whenever `x* ∈ X`,
  for any real `Y`. Intersecting `X_new = X ∩ K(X)` therefore
  keeps `x* ∈ X_new`; the `assert lo <= hi` only guards non-emptiness of the intersection, while the
  containment itself comes from this identity, not from the assert. Induction over the six iterations
  gives `R* = x*_7 ∈ X_new` at the end, i.e. the *original* C891 root, never a different numeric root.

## Threshold and constants

* `T = 3799838531198387090485182/10^25`, formed as `iv.mpf(int)/10**25`. Both the integer and `10**25`
  are exactly representable at `dps = 90`, so `T` is a tiny interval around the exact rational; the
  assertion used is `X[6].b < T.a`, i.e. the **upper** endpoint of the root enclosure below the
  **lower** endpoint of `T` — conservative with respect to the exact rational, hence sound.
* Reported `gap_T_minus_R_lower = lo(T − X[6]) = 1.9326256593863664...e-17` is a valid *lower* bound of
  `T − R*` for the same reason. Hand check: `T = 0.3799838531198387090485…`,
  `X[6] ≈ [0.379983853119838689722261606135,…]`, difference `≈ 1.93e-17`, consistent with the printed
  value; the second assertion `X[6].b < 19/50` is a weaker companion.
* The exact bearing objects are the **dyadic rational endpoints** `R_exact_rational_enclosure`,
  produced from the internal `_mpf_` (sign, man, exp) as exact fractions — no decimal round trip.
  The `gap_...` and `radius` fields are decimal renderings of interval endpoints and should be read as
  diagnostics only; the assertions in the script are what carries the bound.

## Precision / interface notes (no defect found, but read them as such)

1. **The iteration stalls by construction.** Iterations 5 and 6 have the same width to all printed
   digits (`≈ 9.7282e-28`); this is the documented effect of keeping the centre `c` fixed while it
   leaves `X` (the hull stays larger than `X`), not a precision failure. More iterations would not
   shrink the enclosure materially; the threshold `T` is far above the stall width anyway
   (`1.9e-17 ≫ 9.7e-28`), so the stalling costs nothing for this claim.
2. **Uniqueness is a premise, not re-proved.** The docstring says existence/uniqueness come from C891;
   the script only propagates inclusion. That is the honest interface; C922 should not be quoted as
   independently re-proving the root's existence.
3. **`X[6]` is the R\* coordinate** in the C891 parametrisation; the audit relies on that indexing
   being the same as in the earlier certificates (it is, per the shared `center_hex` layout).
4. **The float inverse `np.linalg.inv` is not a constant of the certificate.** It only proposes `Y`;
   the stored JSON does not need to pin it (unlike, e.g., `basis_R_floathex` elsewhere). If
   reproducibility across BLAS builds is wanted, `Y` should be emitted as floathex; currently the
   recipe is "any real Y at all", which is fine mathematically but makes bitwise replay environment
   dependent.
5. `iv.dps = 70`, `mp.dps = 90` are adequate for the asserted inequalities: the assert compares
   quantities separated by `~1.9e-17` with enclosure widths `~1e-27`, a margin of ten orders of
   magnitude.

## Verdict

Inclusion logic, MVT hull handling, threshold orientation and the exact-endpoint export are all
correct as written; the C922 gap `> 1.9326e-17` follows from the printed assertions. The notes above
are interface/precision remarks, not defects. No claim added.
