# cline2-coupled-factors — round 4 report (post-correction)

Scope: q0(6,7) k4, the lead's closure/shared-radius factor dual, calibrated on the saved
certified candidate. Numeric diagnostics and reconstructions only — **no proved labels**.

## 0. Corrections requested by the lead, carried out

1. **C826 retracted** (by the lead): float agreement is not certification. The from-scratch
   reproduction of 3.175702557547944 is kept as a *numeric* cross-check of the lead's own
   proposer, not as evidence of anything exact.
2. **C827 retracted** (by the lead, reproduced here): my "forced slack 2.451e-4" was a
   mixed-radius artifact. `f9_slack.py` standardized the candidate's radii by
   R_cert = .379983853119838733 while multiplying by R^2 = (19/50)^2. The correct
   standardization is rho/R with the same R in the prefactor:
   * switch radius: rho/R_cert gives (rho/R_cert)^2 = 1.000000000000 (what I used, wrong);
     rho/R gives (rho/R)^2 = 0.999915018226 — which is exactly the lead's
     `max_normalized_radius` 0.9999575082101021 for rho/R in `q0_closure_scalar_control.json`.
   * Corrected evaluation via the lead's own machinery (`f29_final_eval.py` executing the
     scalar identity from `q0_exact_closure_radius.py`):
     area - pi = 0.0, sum(ws) - 2pi = 0.0, closure residual = 0, channel split
     (0.0, 0.0, 1.9e-16), and **D = 3.141592653589793 with D - pi = +0.0e+00**.
   So there is **no forced slack at the candidate**, and the whole 0.034110 gap between pi
   and the sampled bound 3.175702558 is in principle recoverable. The lead's
   `check_q0_closure_scalar.py` control agrees (scalar identity error 4.44e-16).
3. **C829 retracted**: the unbounded readings came from moment LPs whose coefficient blocks
   were not pinned. The lead correctly refuses to draw any moment-impossibility inference
   from them, and I withdraw that inference.
4. **The u_k = v_k claim is retracted** in full (see `CORRECTION-uv.md`); the lead's C821
   certified unequal-switch counterexample settles it, and the diagonal restrictions in
   `f13_diagonal.py` / `f15_argmax.py` are invalid.

## 1. What is actually preserved (numeric, scoped)

**(A) Full-domain argmax diagnostic of the lead's span-4 dual** (`f15_argmax.py`, `full`
column only — the diagonal column is invalid). The sampled dual value 3.175702558 is
assembled as const.z = -5.615541133 plus face maxima 5.160601204, switch maxima
0.091959701, ring maxima 3.538682786. The maximizers sit at:

| factor | argmax | value |
|---|---|---|
| face1 (9,1,2) | angles (0.0873, 0.0000, 3.0543), x = 1 | 0.633869 |
| face2 (9,2,3) | angles (0.0873, 3.0543, 0.0000), x = 1 | 0.633866 |
| face3 (9,3,4) | angles (2.7925, 0.3491, 0.0000), x = 0.871 | 0.508207 |
| face0, face5, face7, face8, face9, face10 | mixed, most at x = 1 | 0.17–0.53 |
| face6 (10,6,7) | angles (0.0000, 0.5236, 2.6180), x = 0 | 0.488795 |
| rings 1,2,3,6,7 | at the u = v = 1 boundary of the sector domain | 0.52–0.69 |
| rings 5,8 | at u = 0 boundary slices | 0.26 |
| switch1, switch2, switch6 | at interior b ~ 0.86–0.95, x = 1 | 0.012–0.053 |

Reading: the dual's value is carried by **degenerate face angle triples** (one angle -> 0,
another -> pi, i.e. nearly collinear delivered site triples) and by boundary faces of the
sector domain. Those are not realizable configurations.

**(B) Exact shared-side identity on the saved candidate** (`f22_side_identity.py`): with the
correct slot map the identity rho_f sin A_f = rho_g sin B_g holds on all 12 internal edges,
worst discrepancy 2.776e-16. (My earlier reading of 6e-2 came from using the wrong opposite
angle; discarded.)

**(C) Reconstructed realized angle diagram** (`f8_realized2.py`, `out/realized.npz`):
slot -> site [4,9,10,3,5,7,1,8,6]; widths sum to 2pi exactly; the closure equation
T_k + L_{k+1} + 2 b_k + (w_k + w_{k+1})/2 = pi holds to 8.9e-16; the endpoint copies
u_k = v_k = 1 to 3.3e-16 **because all nine switches are saturated at R_cert** (a property
of this object, NOT a constraint); min(pi/2 - b_k) = 0.520117984. The chord relation
|P_k P_{k+1}| = 2 sin(w_{k+1}/2) was verified exactly, which is what fixed b_k.

## 2. Honest status of my assigned mechanism (grouped/moment couplings)

Dead ends, each with its reason:
* **first-moment adjoint rows** (+-sqrt(x) sin A): the block is unpinned, the LP walks
  away from the useful region (bounded-box optima 3.1325 / 3.1065 / 3.0630 / 2.9631 for
  caps .25/.5/1/2, all below pi) and is unbounded without a box. This is a construction
  defect of my extension, but it also means the extension as formulated cannot help.
* **product-partner rows** (+sin^2 A_f in one face, +sin^2 B_g in the other): same defect,
  unbounded (LP -4.6156 at every cap). A correct version needs the joint pinning
  s_f s_g <= K_e^4 between two different factor maxima, which is not a linear LP row; I did
  not complete it (f25 is abandoned mid-implementation).
* **endpoint relations on u,v**: my u = v theorem was wrong; there is no free equality row.
* **sector center-norm / closure / switch cap**: the lead's, and the ones that actually move
  the bound (3.1757 -> 3.1693 for the center-norm filter).

## 3. What the corrected numbers say about where to look

Since D(candidate) = pi exactly, the dual is a support functional of the area form at the
candidate, and the entire 0.034110 of `ub(z0) - pi` is the price of the dual attaining its
maxima at the unrealizable points listed in (A). Any sharper coupling therefore has to
exclude **near-collinear delivered triples** (face angles (eps, ~0, pi-eps)) at the
standardized radii the dual needs, keeping the dual above pi. That is the mechanism class
worth attacking — position/rigidity, not the moment hierarchy.

Recommended concrete experiment (bounded, calibrated on the same point): take the face
maxima in (A), extract the (site-triple, radii) they imply, and test whether the lead's
closed-cover / switch-cap / center-norm conditions can hold there at all. If they cannot,
the recovered slack is exactly the 0.028–0.034 the lead has been chasing.

## 4. Files

Load-bearing (numeric): `f22_side_identity.py`, `f15_argmax.py` (full column),
`f8_realized2.py`, `f29_final_eval.py` (correct radius discipline),
`f28_scalar_replica.py`, `f26_redo_radii.py`, `f27_rootcause.py`.
Superseded / do not cite: `f1_dual_probe.py`, `f2_arch_audit.py`, `f7_realized.py`,
`f7b_realized.py`, `f9_slack.py`, `f12_identity.py`, `f13_diagonal.py`,
`f15_argmax.py` diagonal column, `f16_decomp.py`, `f18_bounded_L.py`, `f20_product.py`,
`f23_clean_moments.py`, `f25_joint_product.py`.
`REPORT.md` (this file), `STATUS.md`, `DEAD.md`, `CORRECTION-uv.md`.
