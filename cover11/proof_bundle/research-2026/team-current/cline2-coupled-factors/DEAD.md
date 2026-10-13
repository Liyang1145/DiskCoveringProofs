# cline2-coupled-factors — DEAD / method limits

## Mathematical negatives
- **`u_k = v_k` is FALSE** (lead's C821 certified unequal-switch counterexample). A switch is
  equidistant from two neighbouring SITES; a site is not equidistant from two neighbouring
  SWITCHES. The equality holds on the saved candidate only because all nine switches are
  saturated there. **No dual/relaxation may restrict the sector domain to the diagonal
  u = v.** `f13_diagonal.py`, `f15_argmax.py` diagonal columns: invalid.
- The draft diagonal kernel form `S(alpha,1) = R^2 alpha/2 + (w - sin w)/2` was wrong (it
  drops the chord correction); the correct diagonal form is
  `R^2(alpha - sin alpha)/2 + (w - sin w)/2`. Dead twice over (the diagonal itself is invalid).
- No moment-impossibility statement is claimed. The unbounded LP readings for the
  first-moment and product-partner rows are construction defects (unpinned nonnegative
  coefficient blocks), not mathematical obstructions.

## Method limits (implementation and calibration, not mathematics)
- **Mixed-radius hazard.** The dual is built at R = 19/50, so every standardized radius is
  rho/R with the same R in the prefactor. Standardizing the candidate's radii by R_cert
  while multiplying by R^2 inflates face/ring terms by (R/R_cert)^2 - 1 = 8.4987e-5 and
  produced the spurious 2.451e-4 "forced slack". Use the lead's own machinery rather than a
  second assembly: `f29_final_eval.py` executes the scalar identity from
  `q0_exact_closure_radius.py` from the **repo root** (it resolves a relative
  `n11/upper/certified_object.json` path).
- **Float agreement is not certification.** Reproducing 3.175702557547944 to 1e-15 is a
  cross-check of the lead's proposer, not evidence. No proved label is justified without
  rational/symbolic or interval control.
- **Sampled domains are not certificates.** All maxima here are over finite grids.
- **Slot labelling.** In `q0_closure_dual_0_4.json` the ring labels 0..8 are *cyclic slots*,
  not physical site indices: slot k is site [4,9,10,3,5,7,1,8,6][k]; labels 9,10 are hubs 0
  and 2. Reading the labels as site indices silently corrupts every angle/edge lookup (this
  produced my earlier 6e-2 "identity violation").
- `scipy.spatial.Delaunay` on the saved coordinates does NOT return the q0(6,7) graph (it
  picks the other diagonal of the two quadrilateral patches). Take the graph from
  `lead/q0_graphs.json`.
- Superseded files: `f1_dual_probe.py`, `f2_arch_audit.py`, `f7_realized.py`,
  `f7b_realized.py`, `f9_slack.py`, `f12_identity.py`, `f13_diagonal.py`, `f16_decomp.py`,
  `f18_bounded_L.py`, `f20_product.py`, `f23_clean_moments.py`, `f25_joint_product.py`,
  and the diagonal column of `f15_argmax.py`.

## Scope guards
- C831 is a single-realization float evaluation at the saved candidate; it bounds nothing.
- C832(i) is an identity check at one configuration; C832(ii) is a sampled argmax table.
  Neither is a certificate and neither implies an exclusion.
