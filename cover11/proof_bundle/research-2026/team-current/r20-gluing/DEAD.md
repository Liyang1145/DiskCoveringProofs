# r20-gluing — DEAD / 勿重复 (round 20)

## 2026-09-24 TC derivative audit — do not repeat these (already settled)

13. **`res5` derivative representations agree — but only POINTWISE, and that is settled.**
    `r20_tc_audit*.py` re-derived the 5 residuals in SymPy from the explicit geometry and compared
    against `tc_s33_kkt.f5_nested` **at the threshold point**: gradient diff 0, Hessian diff
    4.3e-50 over all 5x7x7 entries; sqrt-circle residual f5 full 7-gradient and 7x7 Hessian
    identical; joint 12-vector `max|f5| = 6.7e-51`. This is numerical agreement at a point, NOT a
    symbolic identity — do not call it an identity.
    The interval version is now done (`r20_tc_iv1.py`, `r20_tc_iv2.py`): every interval Jacobian
    entry overlaps the lead's `J12_iv` (35/35 first-order, 49/49 second-order), and an independent
    one-box Krawczyk inclusion reproduces `F(center)` to 5.7e-40 and `K(c,U)-c` to 1.0e-13, with
    `Q = 0.0042710 < 1` and strict containment. **Do not redo either.**
14. **Audit gate confirmed discriminating.** Mutating the sqrt derivative `1/(2 sqrt x)` ->
    `1/(3 sqrt x)` shifts the gradient by `9.15e+00`; the lead's λ-shift negative control also
    fails to certify. Reproduce with `r20_tc_audit4.py` / the lead certificate.
15. **Pointwise scope of the rank statement.** The 5x7 Jacobian has rank 5 at the threshold point
    (singular values 34.03, 11.41, 3.955, 1.965, 0.666) — a POINTWISE statement. **Do not turn it
    into an interval rank test**: 12D invertibility is already guaranteed by the contraction. This
    audit says nothing about the Krawczyk interval branch-and-bound, the `float` Y-inverse wrapping
    (reused, not re-audited), the covering radius, or C408 (old withdrawal stands).
16. **Reading the dual coefficients.** With the repo's residual sign convention `|.| - R`, the
    threshold condition is `e_R = sum lam_i grad f_i` with all `lam_i` NEGATIVE (equal sign), and
    an independent least-squares solve reproduces them to `8.3e-17`. Do not "fix" the sign by
    flipping lam.
17. **Krawczyk box/inverse pitfalls — both hit, both fixed (do not regress).**
    (a) building the box from `float(c +- rad)` gives outward-rounded endpoints that do NOT enclose
        the true box; build it as `[exact_mpf(center_hex) - rad, exact_mpf(center_hex) + rad]` over
        ALL 12 coordinates (hex -> float -> Fraction -> mpf, exact);
    (b) the Hessian block must multiply the BOX lambda coordinates `U[7+m]`, never the point values
        `numeric_root[7:]`; otherwise the assembled matrix is not a full-12D enclosure.
    With both fixed: `Q = 0.00433242 < 1`, strict inclusion on all 12 coordinates, `K-c` within
    `+-4.34e-12` of the 1.0e-9 box. The earlier "proved-interval" reading of the buggy version is
    withdrawn; the corrected numbers are in `r20_tc_iv2.json`.
18. **Any fixed dyadic Y is legal — do NOT add an inverse-enclosure step.**
    `||I - Y J(U)||_inf < 1` already implies `Y J` invertible and hence `Y` invertible; enclosing
    the true inverse is useless work.
19. **Mixed-partial enclosure equality is a self-check, not a cross-check.** "max endpoint spread 0"
    for `H[i][j]` vs `H[j][i]` compares the same expression twice; do not cite it as independent
    evidence.
20. **Overlap is a control, not a certificate.** The interval `J12` control only says the two
    enclosures intersect at every entry; interval equality is neither expected nor claimed.
21. **Vocabulary discipline: there is no "pointwise-exact".** Pointwise derivatives agree
    numerically at 50-60 digits; interval statements are separate. Use `numeric` / `proved-interval`
    correctly and never claim an identity from a point comparison.

## 2026-09-24 successor: quarantined interfaces (root causes, do not repatch)

4. **Wrong caliber: R = 19/50 with the candidate tuple.** At 19/50 a strict cover exists
   (r = 0.3799838531198388), so the sharp-area support question is not even well posed there and a
   negative reading is meaningless. Every result must state R = r_cand.
5. **69-parameter "family" = silently shared copies.** The producer family
   (`lead/q0_lower375_dual.py`) has 11 faces x (a,b,y) + 9 switches x (b,y) + 9 rings x
   (alpha,u,v) = **78** independent parameters. Tying the switch radius to two ring copies changes
   the object and makes a single factor's derivative rows meaningless. `r20_kkt_active.py`,
   `r20_kkt_system.py`, `r20_kkt_global.py` and the first Farkas scripts are quarantined.
6. **Homogeneous stationarity.** f_k = v_k(pi) + M_k(pi).z makes the condition
   `v' + M'.z = 0`; dropping the `v'` (b) term gave a reported control of 0.371 which was a FAILURE.
   Recalibrated in `r20_producer_family.py` (1e-10).
7. **Reversed boundary signs.** Upper closed-domain endpoint => inward is a decrease =>
   `v' + M'.z >= 0`; lower => `<= 0`. Toy gates: `r20_toy_calibration.py`.
8. **Improvised sign cone.** mu `[0:11]` and closure `[112:121]` are **FREE** in the producer;
   only `z[50:71] >= 0`, `z[71] >= 0`, `z[72] = 0` are asserted. Also ETA is fixed 0 by the
   producer and the ear-capacity (kappa) family has no constraint in q0.
9. **Finite competitor sampling cannot certify a support; and do NOT chase it with 78D BnB.**
   The 29 factors are independent, so factor-wise maximisers are separate 1D/2D/3D problems; a
   joint 78-parameter search is unnecessary and was already refuted as a method. Measured here:
   with up to 10 competition exchanges (cuts from true factor-wise maximisers) at scopes
   `|z|inf <= 3`, `1e3`, `1e6`, the LP stays feasible but no witness closes — worst factor excess
   +8.9e-2 / +7.6e-2 / +2.6e-2 respectively (decreasing, not closed). Verdict: **numerically
   inconclusive, leaning no-support**; not a disproof. Evidence `r20_exch2.json`, `r20_exchange.json`.
10. **The sampled LP dual is not a certificate here.** `|sum lam G|_inf / |lam h| ~ 1.0`, so the
    attempted exact Farkas certificate for the family is withdrawn as non-bearing.
11. **Do not read a fixed-z failure as a family obstruction.** `max` over tuples is not `min` over
    z: the predecessor's `V = 1092` for one witness refutes that witness only. Likewise a random
    tuple with `V(z_c825;X) = 10.90` proves nothing — that tuple violates the constraint families
    (e.g. `sum w = 2pi`), and `V(z) >= pi` is asserted only on the feasible set.
12. **ETA belongs to the family as identically 0.** Producer line 15 `const[eta]=0`, line 44
    `bounds[eta]=(0,0)`, certifier asserts `z[eta]==0`. The earlier probe
    (`r20_factor_probe.Model.ring_coefs`) adds `+z[eta]` for rings i>=3 — a DIFFERENT family; the
    predecessor report's "ETA firing on rings 3-8" is withdrawn. `r20_prod_check.py` verifies 0
    ETA coefficients in the producer-faithful construction.

## Method limits (measured, not mathematical disproofs)

1. **`lead/joint_nested_frozen.json` is not a pure 29-factor dual.** Its 7-atom block
   {1,2,12,13,21,22,23} is joint by construction; maximising its 29 factors independently gives
   total **57.64** at R = 19/50. Do not use it for factor-wise residual restoration.
   Falsified implicitly; evidence `r20_factor_probe.json`.
2. **Single-coupling repair of the 29-factor gap is exhausted at the C825 solution z\***:
   four separately measured upper bounds on the gain of imposing one coupling each —
   sector-chain radius sharing ≤ 1.8e-5, cyclic closure ≤ 4.2e-4, side-matching holonomy
   ≤ 3.4e-5, 11 site angle sums ≤ 5.3e-3 — against a total gap of 4.72e-2.
   Scope: **at z\*** with the C825 coefficients, R = 19/50 (allowed: the mechanism could still be
   live for a re-optimised `z`). Do not re-run these four tests as if untested.
3. **First version of the holonomy test is withdrawn (implementation).** Leaving the third face
   angle free in the constraint while the objective computed it as `π−a−b` let the solver satisfy
   the holonomy at zero cost (defect 1e-13 at unchanged value). Corrected version ties
   `c = π−a−b` in both; recorded in `r20_holonomy_test.py`.
   (Same failure family as DEAD.md's "direction/label/interface" discipline entries.)

## Scope guards

* All numbers are calibrated numerics (grid + deterministic pattern search; identity checks at
  1e-15). No proof, no claim registered, lead kernel untouched.
* The frontier leg is evaluated at `R = 19/50`, where a genuine cover exists
  (r = 0.3799838531198388), so **no** relaxation of this type can go below π there; a "gap" is
  expected and its size is not by itself evidence of a defective dual.
* The four coupling tests bound the gain of *one* coupling at a time; their union is not bounded
  above by the largest of them.
