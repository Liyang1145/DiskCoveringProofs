# r20-rigidity — STATUS (2026-09-25, continuation; cline2 DS v4.1f, no delegation)

Write scope: this directory only. **No claim registered here** (lead owns registration); the
entries below are internal working records with evidence paths and repro commands. Read
`R20-RIGIDITY-LOCAL-STRUCTURE.md` for the full narrative.

## Objects

| id | object | source | status |
|---|---|---|---|
| `x*` | saved certified upper object (22 ints/1e17), radius `C529 = 0.37998385311983870904851817957342985381159790…` | `n11/upper/certified_object.json` | proved-interval (registered) |
| `X60` | registered mirror-symmetric 1e-60 object, radius `R_stru = 0.3799838531198386897222616061360932143087189561…` | `research-2026/session2/n11alg/cert_sym60.json` | registered |
| `X_f` | 17-digit truncation of the same symmetric configuration | `n11/kkt2/frozen.json` | registered |

## AUDIT DOWNGRADE (2026-09-25, lead review) — raw readings kept

* **W5 is downgraded**: `X60` is *not* an "exact stationary root". The `7.78e-61` spread on a
  `1e-60` rational grid is **grid-scale stationarity only**; `sigma_min = 1.7e-51` is a
  finite-difference floor and a small singular value is **not** rank deficiency. Raw readings kept.
* **W6 is downgraded**: only **first-order non-rigidity** is supported. "No local uniqueness" is
  withdrawn — a first-order kernel direction can be a strict second-order minimum.
* **W7 is numeric, not a certificate**: complete over directions *given* the finite-difference
  Hessians; the Hessians themselves are not certified.
* **Local optimality: corrected and conditional on `C_3`.** The `max_i`-form certificate is
  insufficient (counterexample in `R20-MINIMAX-SUFFICIENT-THEOREM.md` §0), but the **weighted**
  K-restricted average holds at `X60`: `Q^T M_u Q` eigenvalues `0.1649, 0.2217, 0.2550, 0.2813`
  (numeric), and the corrected split-proof theorem gives `gamma - gamma* >= 0.0206·dist(x,O)^2`
  for `dist <= ~9e-7`. Remaining: `C_3`, exact (H1)/`Lambda`, interval Hessians.
* **Gap accounting**: to the target `3/8` the gap is `R_stru - 3/8 = 4.98385e-3`; `8.99e-5` is only
  the certification gap to the numeric lower bound `0.3798939830`; proved lower bound `0.3709`
  gives `3/8 - 0.3709 = 4.1e-3`.
## Working records (numeric unless noted)

### W1 — objects are the same shape up to rotation  [numeric]
`max_i min_j |x*_i - R(271.337645738°) X60_j| = 1.7712707e-9`; identical radius multisets;
correspondence `X60 -> x*` = `[2,0,7,1,8,6,4,9,10,3,5]`.
Evidence `r20_rigidity_decisions.json` (Q1), `r20_target_objects.json`. Repro `r20_rigidity_decisions.py`.

### W2 — candidate is 18/20 radius-active, not fully saturated  [proved-exact on the saved rationals]
20 critical points, 18 tight (`9` V3 + `9` V2b), 2 at `gamma* - 1.1526819e-3` (`V3(0,3,10)`, `V3(0,4,9)`
in x*-labels); equivalently 18 of the 20 angle-model local radii saturate. Same at `X60`.
Evidence `r20_calibration.json` §C, `r20_mixed_tangent.log` B1, `r20_second_order_certificate.json`.

### W3 — `C249` upper bound is **not** the exact `rstar`  [numeric]
Independent 120-dps radius of `cert_sym60.json`: `0.379983853119838689722261606136093214308718956`
(matches the registered `RD_interval` lo to `9.7e-81`); registered `T_cert` exceeds it by `≈ +8.5e-46`.
`C529 - R_stru = +1.9326257e-17`. Keep `C529`, `R_stru`, `T_cert` strictly separate.
Evidence `r20_target_objects.log` §B, `r20_second_order_certificate.log` C0.

### W4 — `x*` is NOT a local minimum; correct descent model  [numeric, high precision]
18 tight values at `x*` differ by up to `7.86e-17`; the local model is
`gamma(x*+d) - gamma* = max_i[-δ_i + ∇f_i·d] + O(|d|²)`. Along the direction to rotated `X60`
the descent runs at `7.1743e-9` per unit distance (the argmax function `V2b(1,7)`), total
`-1.9326e-17` at the ideal object. The interrupted "thin descent cone `tau = 3.7e-9`" reading is
**incorrect as a bound on `gamma`** (it bounds only the simultaneous decrease of all 18).
Evidence `r20_direction_audit.json/.log`, `r20_rigidity_decisions.log` (Q3,Q5).

### W5 — `X60`: grid-scale stationarity of the 18-pinned system  [numeric; downgraded]
18 values equal to `7.8e-61`; `rank(J18) = 17`, `sigma_min = 1.7e-51` (FD floor), `sigma_2 = 0.0584199083`;
`0 ∈ ri conv{∇f_i}` with `u > 0`, `min u_i = 9.8947e-3`, `‖J^T u‖_inf = 2.2e-52`.
Evidence `r20_second_order_certificate.json/.log` (C0–C2).

### W6 — rigidity table (first-order non-rigidity only)  [numeric; downgraded]
`dim ker(J18) = 5` (rotation in ker); `rank(J18|Sym) = 9/11`, `rank(J18|Anti) = 8/11`;
`dim(ker ∩ Sym) = 2`, `dim(ker ∩ Anti) = 3`.
So: *first-order non-rigidity only* — the linearisation has a 4-dimensional flat space mod rotation
(2-dimensional even on the fixed mirror locus). This is **not** a statement about uniqueness of a
local minimiser and it uses an unproved exact rank.
Evidence `r20_second_order_certificate.json` (`rank_Sym`, `rank_Anti`, `ker_*`).

### W7 — second-order min-max over all flat directions  [numeric; FD Hessians, not certified]
`c_k = max_{λ∈simplex} λ_min(Q^T Σλ_i H_i Q) = 0.25550766818243037826` (dim 4, `Q` = `ker/rotation`),
certified input `c₀ = 0.255507667182`. Sub-values: symmetric part `0.3219144793`,
antisymmetric part `0.3035345293`. Transverse rate
`mu = min_{v ⊥ ker, ||v||=1} max_i ∇f_i·v = 0.0014325394911` (complete vertex enumeration).
Evidence `r20_second_order_certificate.json` (C6–C9).

### W8 — Danskin-average Hessian and remainder diagnostic  [numeric]
`H̄ = Σ u_i H_i`: `rot^T H̄ rot = -8.8e-19`; spectrum on `rot^⊥` has two negative eigenvalues
(`-3.28e-2`, `-1.32e-2`) ⇒ the average form alone is insufficient; on the flat space
`[0.1649, 0.2217, 0.2550, 0.2813]`. Third-order remainder scale estimate `≈ 1.68` (diagnostic only).
Evidence `r20_error_bound.json/.log`.

### W9 — independent geometry assembly for the repaired TC root  [interval, structure-derived]
`R20-TC-ROOT-COMPLETENESS.md`, `r20_tc_root_independent.py/.json/.log` (reads
`../lead/repaired_tc_krawczyk.json` read-only; no SciPy, no new optimisation).
Derived from the res5 reflection structure: the 7 active fan equalities are exactly
`|U_k - H|^2 = R^2` (4 equations + 3 reflections), the 2 central equalities are the fifth res5
equation + reflection (hub-distance identity `(m-y_i)^2 + h^2 = R^2` is algebraic), and the 9
boundary ties are at distance `R` by the defining relation of `rho_k`; boundary arcs tile because
`sum a = pi` identically. Face list assembled from the structure and verified combinatorially
(no hull algorithm): `V=11, E=21, F=11, V-E+F=1`, hull edges in exactly 1 face, 12 interior edges
in exactly 2, all sites used, `3F = 2E - 9`. Delaunay criterion verified with strict margins
(`min empty-circle margin 1.5050e-1`, all 11 circumcentres inside `D` by `>= 0.612`), so the list is
the unique Delaunay triangulation and its circumcentres are all Voronoi vertices; branch margins all
`>= 1.09e-3` versus box radius `1e-9`; the two slack faces have `circumradius^2 - R^2 in
[-8.747e-4, -8.746e-4]` (no saturation assumed). With the boundary/vertex max argument this gives
`R_D(root configuration) = R` exactly, i.e. `r_D(11) <= R` (upper bound only).
Scope guard: root existence/uniqueness is the read-only Krawczyk certificate; the active equalities
are its equations, not interval containment of zero; the global lower bound is untouched. My first
circumcentre routine added the base site twice (bug found by comparison with the pin, fixed; see
the log) — recorded so the artifact is not read as a geometric obstruction.
### W10 — independent geometric assembly for the repaired TC root, audited  [interval, structure-derived]
`R20-TC-ROOT-COMPLETENESS.md` (claim) + `R20-TC-ROOT-AUDIT.md` (audit), instruments
`r20_tc_root_independent.py` (re-run after the fix), `r20_tc_box_audit.py`,
`r20_tc_delaunay_completeness.py` (all with `.json`/`.log`).
* **Defect A fixed**: the box was built with rounded float endpoints (`iv([c-rad, c+rad])`);
  measured defect `<= 2.723e-17` per coordinate. Now `iv(c) + iv([-rad,rad])` (the lead's kernel
  construction), certified box contained with `0` defect; all readings unchanged. Positivity now
  decided on exact interval endpoints (`min empty margin = 0.1504954350807983567`,
  `min (1-|cc|) = 0.61197353225160098382`, conservative thresholds `0.15`, `0.61`).
* **Defect B fixed (inference)**: "no margin is zero ⇒ no four cocircular sites" is invalid and
  false. All 330 quadruples were tested by the translated circle determinant: 324 are certified
  non-cocircular on the whole box (`|det| >= 5.6e-8`), the remaining **6 are exactly cocircular**
  (the mirror-symmetric quadruples `{C0,C1,C7,C8}`, `{C0,C2,C6,C8}`, `{C0,C3,C5,C8}`,
  `{C1,C2,C6,C7}`, `{C1,C3,C5,C7}`, `{C2,C3,C5,C6}`; two mirror pairs are cyclic by the exact
  reflection). Each of the 6 is **strictly non-empty** (a site lies inside its circle by
  `>= 0.61070938122121436004`), which is what unique Delaunay needs; "no 4 sites cocircular" is
  false and is not used.
* Two further findings: `(C4,H0,H1)` is **exactly collinear** (`theta_4 = 0`; harmless: no
  circumcircle, not a supporting line); the reflection symmetry is **exact** at parameter level
  (palindromic `a`, `theta_{8-k} = -theta_k`), the `2e-7` readings being interval slack only.
* Completeness (new instruments, all positive on the corrected box): F1 210 edge pairs
  non-crossing; F2 88 (face, site) pairs (no site in another face); F2b 231 (edge, site) pairs (no
  site inside an edge); F3 55/55 face pairs with certified disjoint interiors; F4 hull orientation
  margin `5.402e-2`; F5 `V=11,E=21,F=11,Euler=1,2E-9=33=3F` ⇒ the listed triangles are exactly the
  bounded faces; plus G (no empty cocircular quadruple). Hence the Delaunay subdivision is a
  triangulation equal to the face list, its Voronoi vertices are the 11 circumcentres, all strictly
  inside `D` ⇒ `R_D(root configuration) = R`, i.e. `r_D(11) <= R` (**upper bound only**).
* Controls: Cramer circumcentre vs structure prediction `<= 4.7e-7` (active), `1.690e-3` for the
  slack faces matching `r - R = -1.151e-3`; incircle-determinant control agrees in sign for all 88
  pairs (max signed value `-0.0463 < 0`); angle sums (interior `2*pi`, hull = nonagon angle) and
  area sum of the 11 triangles vs hull area are consistent within `9.2e-7` (consistency only, the
  proof of completeness is F1–F5).

### W11 — TC chart: rank 5 + rank 7, analytic pivots  [proved (analytic pivots) / box-verified]
`R20-TC-CHART-RANK-AUDIT.md`, `r20_tc_chart_rank.py/.json`. Audits the lead's
`TC-BOUNDARY-CHART-RANK.md` and answers obligation 1 of `TC-TO-PHYSICAL-KKT-LIFT.md`.
* Radial facts (L1): `a_rho = (1-R^2-rho^2)/(2 rho^2 sin a) >= 9.786e-2 > 0`,
  `a_R = R/(rho sin a) >= 1.1247 > 0`, `1-R^2-rho^2 >= 5.90e-2`, `R^2 - sin^2 a >= 1.093e-3` on the box;
  the exact identity `1-R^2-rho^2 = 2 rho (cos a - rho)` is the clean proof of the sign.
* Rank 5: the lead's radial 5x5 orbit minor has determinant `2 d_0d_1d_2d_3d_4` with
  `d_k = a_rho(rho_k) > 0` (pivot `>= 1.477e-2`); refinement R1: the reduction needs the
  orbit bookkeeping (`sigma(k) = 8-k` on radii, `tau(i) = 7-i` on gaps), and invertibility of `I+S`
  on `R^9` alone does not imply invertibility of the 5x5 block. Independent second minor (4 rotation
  directions + `R`): pivot `2(beta_0+beta_1+beta_2+beta_3)+beta_4 >= 12.936 > 0`.
* Rank 7 immersion: diagonal `sin a_k rho_k / sqrt(R^2-sin^2 a_k)`, pivot `>= 13.249 > 0`.
* L5 proportionality `dg_i = mu_i d(t_i-R)`, `mu_i = a_{i,R}+a_{i+1,R} > 0` (box `[2.309, 3.448]`),
  independently reproduced by the gap/radius route `dv/dg in [0.2900, 0.4332] > 0`; reciprocity
  `(dv/dg)*mu = 1` to `3.2e-6`. Far radical-line point uncovered by the pair by `>= 1.314`.

### W12 — interior residual conversion incl. the central waist  [proved-exact + interval signs]
`R20-TC-CHART-RANK-AUDIT.md` §5 (audit of `TC-BOUNDARY-CHART-RANK.md` §"Interior residual conversion").
* Exact: `4 y^2 (Rc^2-R^2) = F_in F_out`; at `F_in = 0`, `d(Rc-R) = [F_out/(4y^2)] df`. Re-derived
  from scratch; calibrated on 120 box points (residuals `7.2e-62` central, `3.9e-61` fan).
* Central waist (chord = hub segment, third vertex `C_6`, `W_+ = (m,+h)`, `h = sqrt(R^2-(chord/2)^2)`):
  exact algebra `2 c_y (rho_c^2 - R^2) = (s+h)·F_in` with `s` the circumcentre height; `F_out >= 0.8774`
  (interval) and `>= (c_y+h)^2 - R^2 >= 0.8763` (analytic), `c_y >= 0.6944`, branch factor
  `(s+h)/(2c_y) in [0.454882, 0.454883] > 0`. Notation warning (R2): the lead's `d` in `sqrt(R^2-d^2/4)`
  is the **chord length**; the audit scripts use `d` for the half-chord.
* Fan: `F_out > 0` by interval (`>= 0.4248` on all four active orbits) and by the triangle inequality
  (`|H| <= 0.272978`, `|B_k| = 1` ⇒ `|H-B_k| >= 0.727022 > R`, margin `0.347`).

### W13 — local minimax weighted-H theorem: gap inventory  [audit note]
`R20-MINIMAX-SUFFICIENT-THEOREM.md` §2-§4 audited (see the note in this directory): the slice/orbit
lemma only needs `dist(x,O) <= ||s||` (always true), not equality; the radius formula must also carry
the fourth-order condition `L A^2 ||d||^2 <= c/16` (non-binding at `X60`: `|d| <= 1.19e-5` vs
`9.0e-7`); the hypotheses must be stated on the **active** set with `u > 0` there. `C_3` is not the
only gap: also exact (H1), exact (H3‡)+interval Hessians, the `Lambda = {u}` rank reading, the
`gamma(x*) = R_D(x*)` model-completeness interface, and `rho_0`.

### W14 — physical 18-branch architecture, KKT common-gradient kernel, anti block  [proved lemmas + numeric readings]
`R20-PHYSICAL-KKT-KERNEL.md`, `r20_physical_kkt_kernel.py/.json/.log` (dps=60, no finite
differences; anchor = the lead's root box, read-only). Lead split: sym 2x2 is the lead's
(`TC-SYMMETRIC-SECOND-VARIATION.md`); this entry owns the anti 8x11 / rotation quotient / anti block.
* Branch catalogue (explicit finite formulas in the 22 centre coordinates, differentiated by
  second-order jets): 11 face circumradius branches + 9 boundary-tie branches; 18 active
  (9 faces = 7 fan + 2 central, 9 ties), 2 slack faces. Values: active `max|f-R*| = 4.7e-59`,
  slack `R*-f = 1.152681921e-3` (matches W2), ties `<= 7.8e-62`; chart coincidence fans/pins 9.5e-59,
  ties/`B_k` 1.6e-61, central/`(m,+-h)` 5.5e-62; critical-set cross-check 20/18. FD control 4.9e-31;
  the exact-formula singular values reproduce `r20_second_order_certificate.json` `sigma_Sym/sigma_Anti`
  to all printed digits and the positive centred spectrum `[0.16490, 0.22167, 0.25496, 0.28133]`.
* **Kernel (analytic).** `T = ker J_A x {0}` in `R^23` under `sum w_i grad f_i = 0`, `sum w_i = 1`;
  rotation field is an exact kernel direction (equivariance); weighted Hessian annihilates it.
  Numeric: `rank J_A = 17`, `dim ker = 5 = 2 Sym + 3 Anti`, mod rotation 4 = 2+2; `|J rot| = 6.8e-62`.
* **Anti block.** `A_anti` (8 orbit-representative rows) has `sv = .7755..0.0413` (rank 8), witness
  minor cols (2,3,4,5,7,8,9,10) `det = -7.0679e-5`; kernel dim 3 by two independent routes
  (minor-null and mpmath SVD) with residuals 1.7e-62 / 2.2e-61; `|A_anti rot_a| = 7.2e-62`;
  quotient 2D. Weighted (canonical Danskin weight, `min 9.8947e-3`, `|sum w_i grad f_i| = 1.8e-59`,
  reflection-symmetric 2.1e-61): anti 3x3 `{0, 0.1649026928, 0.2549598729}`, anti quotient 2x2 the
  two positives, sym 2x2 `{0.2216701155, 0.2813311259}`, max-form `0.3066 > 0`.
* **Reflection blocks.** `|[SIG,HW]| = 2.8e-61`, mixed `max|BS^T HW BA| = 1.8e-61` (**exact 0**, from
  branch equivariance + `w` invariance — structural, not neglected).
* **Gauge lemma (proved).** `G = kappa f`, `f|_T = df|_T = 0` ⇒ `d^2G|_T = kappa d^2f|_T`; off the
  kernel `d^2G - kappa d^2f` is the `df (x) dkappa` cross term. Fan `(2,3,H0)`:
  `kappa = Fout/(4y^2) = 0.4187003705`; kernel identity to 2e-63 / 1e-61; transverse gap 2.5e-2.
* **Metric lemma (proved).** `grad W = 0` ⇒ pullback `d^2(W o Psi)|_{T_z} = Y^T d^2W Y` (verified vs
  7D jets to 2.4e-55); inertia transfers, eigenvalues do not (physical sym `{0.2217, 0.2813}` vs
  chart-z `{0.4081, 0.7504}`, per-mode ratios 1.84/2.67). Angle-model spectra
  (`stress` V0 `{.0443,.0564,.0588}`, lead's `{.0413..0590}`) must not be equated with these.
* **Interface calibration.** With `c_i = 4y_i^2/Fout_i`, `b_j = a_{j,R}+a_{j+1,R}` computed here,
  `w_i c_i` is orbit-constant to 6.9e-61 and `w_j b_j` to 1.6e-61 ⇒ the lead's physical weight formula
  `mu_i c_i`, `nu_j b_j` holds numerically (18 -> 10 factorisation); the certified version needs
  `r20-stress`'s exact `nu` (not duplicated here).
* Calibration note: the old FD read of the negative full-space eigenvalues (`-3.28e-2, -1.32e-2`)
  is not reproduced in magnitude by the exact formulas (`-7.95e-2, -1.84e-2`); sign structure same.

### W15 — anti 8x11 rank + anti quotient interval certificate  [interval; PD conditional on stress weights interface]
`r20_anti_block_interval.py/.json/.log`, `R20-PHYSICAL-KKT-KERNEL.md` §0/§8. No SVD, no numeric
rank, no eigen/Gram arithmetic in the claim.
* Rank: explicit 8x8 witness minor (cols 2,3,4,5,7,8,9,10) has **interval determinant
  `[-4.00004e-4, -3.99635e-4]` ∌ 0** over the lead's box ⇒ `rank(A_anti) >= 8`; `rank <= 8` on the
  symmetric slice structurally (2 self-reflected branches with `sigma`-invariant gradients ⇒ zero
  anti part; 16 rows in 8 conjugate pairs) ⇒ rank = 8, anti kernel dim 3, rotation inside
  analytically.
* Kernel: explicit null vectors from the minor (interval Gauss-Jordan, fixed pivot order from the
  centre; **pivot guards**: every pivot excludes 0 — `p_lo*p_hi > 0` — is finite, and `det` is
  finite, else FAIL); rotation **kernel coefficients** `c* = rot_a[FREE] = (0.29837, -0.76471,
  0.59861)` (identity from the unit free block of KV, no least-squares in the certificate path);
  `j* = 1`, transversality by the exact **sign test** `c_lo > 0 or c_hi < 0` (a `min(|lo|,|hi|) > 0`
  margin does NOT exclude 0: `[-1,2]`), margin 0.7647; complement `(KV[0], KV[2])`.
* Tie interface (frozen TIEPICK ⇒ C892 boundary tie, interval over the box): A1 `max |p - B_k| <=
  3.73e-7`; A3 `min (other-site dist^2 - f^2) >= 0.4248 > 0`; A2 `inf |p* - p_other|^2 >= 3.783737`
  (equals stress's independent A2); A4 other-branch nearest-pair **failure** margin `>= 2.773827 >
  0` (squared-distance form of stress's A4).
* Weights: `r20-stress/weights_interface.py::physical_weights()` (interval, 18/18 strictly positive,
  sum contains 1; my numeric Danskin λ lies inside every interval ⇒ mapping/orbit convention
  verified; FACE_MAP from `face_labels`).
* **Certificate (Sylvester on interval endpoints):** `B11 in [0.450451, 0.450475] > 0` and
  `det >= 0.217798969238 > 0`; **merged verdict** = (minor det ∌ 0) ∧ (pivot guards) ∧
  (transversality sign test) ∧ (Sylvester) = True ⇒ the weighted form is PD on the complement for
  every configuration in the box and every weight in the interval enclosure. Controls: point mode
  reproduces the exact-formula spectra `{0.164903, 0.254960}` (22D orthonormal quotient) and
  `{0, 0.164903, 0.254960}` (3D kernel pencil) — rotation is the exact zero direction. The `[A6]`
  eigenvalue/Gram number is a *diagnostic only* and must not be compared with cross-basis spectra.
* Fixes recorded: `IVJ.__truediv__` had a corrupted Hessian slot (now `_recip` + multiplication,
  with a 1/x, x/y, sqrt jet self-test at 1e-60); integer anti basis + diagonal Gram
  `diag(2x8,1x3)` used in every inner product; `np.linalg.eigvalsh(G^{-1}B)` replaced by
  `scipy.linalg.eigh(B, G)` (the old call silently read one triangle of a non-symmetric matrix).
  With the corrected solver the chart-metric sym block reads `{0.3976, 0.7609}`, matching the lead's
  independent TC-chart eigenvalues.
* Scope: PD is **conditional on** (i) the lead's box/Krawczyk certificate, (ii) the geometry and
  branch interfaces (C892, boundary-switch margins), (iii) the stress weights interface (C897).
  Global far-region optimality untouched.

### W16 — C902 → quantitative neighbourhood: corrected design + scalar lemma  [design; corrected 2026-09-25 after lead audit]
`R20-QUANTITATIVE-NEIGHBORHOOD.md` (rewritten; §6 lists the retractions), `r20_quant_pilot.py/.json/.log`
(numeric, uncertified, kept only as readings).
* **Retracted after lead audit:** (a) the box is **not** the 12D symmetric box — the neighbourhood must
  be the unrestricted 22-direction product box `Sym(11+1) x Anti(11)`; (b) "mixed Hessian = 0" holds
  only at the exact σ-fixed point and only for the Sym/Anti split — for the `T/T^⊥` split the mixed
  term exists and is carried by a constant `M`; (c) the pilot `ρ` is **not** usable for a global
  argument (numeric, uncertified, and it assumed `|t| = |v|`).
* **Scalar lemma proved** (no optimization, all directions):
  with `v = k + t`, `η = min(1, λ/(8M))`,
  `ρ = min(1, 2μη/L2, 9λ/(8L3))`, `c = min(μη/(2ρ), 3λ/32)`,
  `F(x*+v) − R* ≥ c|v_quot|²` for `|v| ≤ ρ`, using
  `max_i∇f_i·v ≥ μ|t|`, `(1/2)v^TH_Wv ≥ (λ/2)|k_quot|² − M|k||t| − (M/2)|t|²`,
  and remainders `(L2/2)|v|²`, `(L3/6)|v|³`; case split `|t| ≥ η|v|` vs `<`.
  **RETRACTED 2026-09-25 (lead audit, three errors):** `2μη/L2` only gives non-negativity at the
  endpoint (the `μη/2·|v|` form needs `|v| ≤ μη/L2`); `η = min(1, λ/(8M))` is inadmissible (`η = 1`
  ⇒ `1−3η < 0`, no positive kernel bound); `|k_quot|` does not control `|k|` on `R^22`.
* **Corrected scalar lemma (uniform (Hλ), no side conditions — lead's simplification):** in the fixed
  physical slice `S = rot(x*)^⊥` (21D, no chart/`R` residue), `K = T ∩ S` (4D), `v = k + t` with
  `t ∈ S ∩ K^⊥` (17D); `η = min(1/4, λ/(16M))` and (Hλ) `(λ/2)(1−η²) − Mη − Mη²/2 ≥ λ/3` holds
  **unconditionally**: `η ≤ 1/4`, `Mη ≤ λ/16`, `Mη²/2 ≤ λ/128` ⇒ `15λ/32 − λ/16 − λ/128 = 51λ/128 > λ/3`;
  `ρ = min(1, μη/L2, λ/(2L3))`, `c = min(μη/(2ρ), λ/4)` ⇒ `F(x*+v) − R* ≥ c|v|²` for `0 < |v| ≤ ρ`
  (case A: `μη|v| − (L2/2)|v|² ≥ (μη/2)|v|` for `|v| ≤ μη/L2`; case B: bracket bound then
  `−(L3/6)ρ|v|² ≥ −(λ/12)|v|²` from `ρ ≤ λ/(2L3)`).
* **Operator bounds (executed: `r20_operator_bounds.py/.json/.log`):** margins over the box
  `det_min ≥ 0.30784`, `d_min ≥ 0.45110`, `rad_min ≥ 0.94594`; **naive** worst-case numerator
  substitution is vacuous: `L2_face ≈ 1.93e7`, `L3_face ≈ 1.40e11`, `η ≈ 2.6e-10`, `ρ ≈ 2e-20`.
  Diagnosis (recorded in design §5.1): the exponents `det_min^{-2,-3,-4}` are right, the **coefficients**
  are not — `w = P/(2 det)` is homogeneous of degree 1 and `Dw` of degree 0, so the bounds must be
  scale-separated: `|Dw| ≤ N₁/sinθ`, `|D²w| ≤ N₂/(|g| sin²θ)`, `|D³w| ≤ N₃/(|g|² sin³θ)` with
  dimensionless `N_k` and `sinθ = det/(|g₁||g₂|)`. Tie side loses only ~10×; face side ~1e6×.
* **ANCHOR IDENTITY (resolves the rank-18/rank-17 cross-member discrepancy, 2026-09-25):** all
  computations in this directory are anchored at the lead's **exact** C891/C892 root
  (lead/repaired_tc_krawczyk.json, Newton limit 62 digits; "not the printed centers" per the
  assembly note). At that object the exact-jet J (dps=50/60) has sigma_18 ~ 6e-17 (kernel dim 5 =
  2 Sym + 3 Anti), left null vector all-positive (min 9.8947e-3), i.e. the exact positive-weight
  relation (H1)/(C897) holds. The rank-18 readings (sigma_18 = 2.4e-9, (H1) failing, "v18 soft
  direction") belong to the **rounded saved object** 
11/upper/certified_object.json (17 digits),
  where the same symmetry is broken at the 1.77e-9 noise level; they are not statements about the
  exact root. Same for X60 (cert_sym60.json): rank 17, (H1) exact -- consistent with this anchor.
* **sigma_17 interval lower bound from a 17x17 square minor of the physical J (20_anti_sigma_interval.py/.json/.log):** 22D hull box of the chart image (superset of the symmetric slice, widths <= 1.99e-7); interval 18x22 physical gradient map with all-direction iv jets; 17x17 minor (rows/cols 0..16) inverted by interval Gauss-Jordan with pivot guards (no bad pivots, min|pivot| >= 7.9853e-3, no non-finite entries); ||M^{-1}||_F <= 4.459317e2 => sigma_min(M) >= 2.242496e-3, hence sigma_17(J) >= 2.242496e-3 (square-minor route, no sqrt; true value 5.841991e-2, loss 26x). With the stress interface endpoint w_min = 0.0098946876 this gives the chain-margin candidate mu = w_min*sigma/2 >= 1.109440e-5 (LP value 1.43254e-3, loss 129x) - an interval lower bound on sigma, conditional on the branch-choice and w_min interfaces; no claim added.
* **RETRACTED 2026-09-25 (lead audit): the "certified coarse λ and μ / true certificate" wording of
  this entry.** The Schur/trace ratio is not a valid eigenvalue lower bound in general; `σ₁₇`, the
  symmetric metric factor `1/3` and the `L2/L3` coefficients are numeric/unchecked. Read the entry as
  **conditional bound candidates only** (no claim added). Safe replacement for the anti side:
  `det(B)_lower/(tr(B)_upper·tr(G)_upper) = 0.217799/(17.4352·73.59) = 0.000170`; with the numeric
  `σ₁₇` and metric factor the conditional chain gives `η = 5.48e-13`, `ρ = 3.86e-24`, `c = 4.24e-5` —
  candidates, **not** certificates. The analytic `μ`/minor-bound interface is being supplied by the
  chain and must be substituted. (Original entry text kept in the repo history below.)
* **~~Certified COARSE positive λ and μ~~ (superseded text, kept for the record):**
  `λ_anti ≥ [B11⁻ − (|B12|ᵐᵃˣ)²/B22⁻]/(G11⁺+G22⁺) = 0.029554` (invalid-Schur version),
  `λ_sym ≥ (1/4)·(1/3) = 0.083333` (metric factor numeric) ⇒ `λ ≥ 0.029554` (point value 0.164903);
  **`μ ≥ w_min·σ₁₇/√18 = 1.362469e-4`** with `w_min = 0.0098946876` (stress interface) and
  `σ₁₇ = 0.0584199083` (numeric; LP value 1.43254e-3). Derivation of the μ formula: for unit `v ∈ K^⊥`,
  `‖Jv‖ ≥ σ₁₇` ⇒ some `|∇f_i·v| ≥ σ₁₇/√18`; if it is positive the max bound follows, otherwise the
  weighted identity (perturbed by `(1−w_{i*})max_j∇f_j·v ≥ w_{i*}σ₁₇/√18`) gives the same.
  With the current crude `L2/L3` this yields `η = 9.5e-11`, `ρ = 6.7e-22`, `c = 7.4e-3`.
  **`μ ≥ w_min·σ₁₇/√18 = 1.362469e-4`** with `w_min = 0.0098946876` (stress interface) and
  `σ₁₇ = 0.0584199083` (LP value 1.43254e-3). Derivation of the μ formula: for unit `v ∈ K^⊥`,
  `‖Jv‖ ≥ σ₁₇` ⇒ some `|∇f_i·v| ≥ σ₁₇/√18`; if it is positive the max bound follows, otherwise the
  weighted identity (perturbed by `(1−w_{i*})max_j∇f_j·v ≥ w_{i*}σ₁₇/√18`) gives the same.
  With the current crude `L2/L3` this yields `η = 9.5e-11`, **`ρ = 6.7e-22 > 0`**, `c = 7.4e-3`:
  a *genuine* (if tiny) quantitative certificate — the constants are now the optimisation target.
  Remaining inputs to certify: `σ₁₇` interval minor bound, the `L2/L3` coefficients (symbolic check),
  the metric factor 1/3.
* **Constants (five):** `μ`, `λ` (C893 + C901 + pointwise Sym/Anti mixed = 0), **`M` (mixed term)**,
  `L2`, `L3` (all-direction box suprema from *closed forms*: face branch via `det = 2 area` and the
  strict-empty margin; tie branch via `|d|` and `1 − |A0|²` radical margins).
* **Pilot readings kept as readings only:** `μ = 0.00143254`, centre-kernel spectrum
  `{0.164903, 0.221670, 0.254960, 0.281331}`, `max_i‖H_i‖₂ = 4.572`, sampled directional third
  derivatives (max 2.29) — explicitly **not** an `L3` bound.
* Next: closed-form `L2_i`, `L3_i` over the box, then the uniform `(ρ, c)`; no interval work before
  that, no global claim.

## Gaps / limits

1. **Hessians are finite differences** (120 dps, `h = 1e-16`, Richardson `≤ 4e-31` on spot entries):
   the certificate is numeric. The planned interval-arithmetic upgrade requires
   (a) non-degenerate interval inputs, (b) exact simplex normalisation of `λ` — both identified,
   neither used in the reported number.
2. **Cubic remainder bound and the radius `ρ`** of the local error bound are not certified.
3. **Far-region separation is open**, and per `lead/R21-NO-FIXED-FINITE-SHARP-WITNESS.md` it cannot
   be obtained from any frozen finite witness set; moving witnesses / the full `R_D` derivative
   structure are required. No global bound is claimed or improved here.
4. The `Q5`-style segment evaluation must keep recomputing the configuration-determined critical set
   (it does); do not carry the 18 (or 20) points along a motion.

## Repro

```
py -3 -B -X utf8 r20_second_order_certificate.py     # C0-C9, writes r20_second_order_certificate.json
py -3 -B -X utf8 r20_error_bound.py                  # W8
py -3 -B -X utf8 r20_rigidity_decisions.py           # W1
py -3 -B -X utf8 r20_direction_audit.py              # W4
py -3 -B -X utf8 r20_mixed_tangent.py                # W2/W5 partial record
py -3 -B -X utf8 r20_tc_root_independent.py          # W10 (re-run after the box fix)
py -3 -B -X utf8 r20_tc_box_audit.py                 # W10 box defect + exact endpoints + 330 circle determinants
py -3 -B -X utf8 r20_tc_delaunay_completeness.py     # W10 F1-F5 triangulation + G non-empty cocircular quadruples
py -3 -B -X utf8 r20_tc_chart_rank.py                # W11/W12 chart rank, conversion factors, central F_out
py -3 -B -X utf8 r20_physical_kkt_kernel.py          # W14 physical 18 branches, KKT kernel, anti block
py -3 -B -X utf8 r20_anti_block_interval.py          # W15 interval anti rank + quotient certificate
R20_POINT=1 py -3 -B -X utf8 r20_anti_block_interval.py   # W15 point-mode controls
py -3 -B -X utf8 r20_quant_pilot.py                  # W16 quantitative-neighbourhood pilot constants
```
(`R20_FORCE=1` rebuilds the Hessian cache `r20_hess_cache.npz`.)

Notes: `r20_tc_root_independent.py` was re-run *after* the box fix, so its log/JSON in this directory
are the corrected ones; `R20-TC-ROOT-AUDIT.md` states exactly which claims changed. All new scripts
use the corrected box `iv(c)+iv([-rad,rad])` and decide positivity on exact interval endpoints.

### W17 - operator bounds, scale-separated step  [in progress; candidates only]
20_operator_bounds.py/.json/.log now uses the scale-separated form (no homogeneity-as-conditioning):
face |Dw| <= N1/(g_min sin_min), |D2w| <= N2/(g_min^2 sin_min^2), |D3w| <= N3/(g_min^3 sin_min^3)
with sin_min = det_min/4 = 0.076960, g_min = 0.30 (conservative floor), N_k = 12, 48, 192 (crude,
symbolic check PENDING); tie branch unchanged (4/|d|, 16/|d|^2, 64/|d|^3 and sqrt(rad_min) factors).
Readings: L2_face = 8.01e5 (dominated by dw^2/f_min, dw = 519), L2_tie = 1.33e3,
L3_face = 1.36e9, ho = 1.14e-17 (was 2e-20 with the naive det_min^{-2,-3,-4} form).
Branch validity on the ball is NOT certified here: the 22D hull is only a coordinate envelope of the
chart image and must not be used for the ball statement (lead); the perturbative det/adical
Lipschitz route is the pending replacement. Remaining lever: a genuine symbolic derivation of N_k
(the current values lose ~500x) and a tighter g_min/sin_min pair.
Also recorded: determinant provenance block in R20-QUANTITATIVE-NEIGHBORHOOD.md section 8 (witness
minor -4.0e-4 vs certificate 0.2178 vs B2 pencil det 9.2819, three different bases) for the lead's
whole-matrix diff; the obsolete REPORT.md in this directory is not mine and its float-matrix
rational-determinant rank claim is not accepted.

### W18 - operator bounds: exact recurrences only, then pause  [paused per lead]
Docs: `R20-QUANTITATIVE-NEIGHBORHOOD.md` sections 9-11; check script `r20_recurrence_check.py/.json/.log`.
* Face branch: exact recurrence from `A w = b` (`A = [g1^T; g2^T]`, `b = -(1/2)(|g1|^2,|g2|^2)^T`):
  `Dw = A^-1(Db - (DA)w)`, `D^2w = A^-1(D^2b - 2(DA)Dw)`, `D^3w = A^-1(-3(DA)D^2w)`, with
  `||A^-1|| <= ||A||_F/|det A| <= 2 sqrt2/|det A|`. Identity verified against the exact jets at the
  root (implementation check only, 9 faces x 6 directions, rel. err. 4.24e-16 / 1.63e-15).
* Safe constants ONLY (sharpness claims withdrawn, lead audit): `|b| <= 2 sqrt2`, `|Db| <= 4`,
  `|D^2b| <= 2 sqrt2`, `|D_v g_i| <= sqrt2`, `||DA|| <= 2`. The earlier `|Db| <= 2 sqrt2`,
  `|D^2b| <= 2` and the "sharp 3/sqrt2" are retracted; `max |v_a - v_b|^2 = 2` (v_a = e/sqrt(2),
  v_b = -e/sqrt(2), v_c = 0), so no sharp version exists from that route.
* `f >= R* - rho` is WITHDRAWN (circumradius not globally 1-Lipschitz). `f_lo`, `|d|_lo`,
  `(1-|A0|^2)_lo` must come from interval lower bounds over the domain, separately from any rho.
* Tie branch: exact identity form (section 11): `p` solves `d.p = kappa_d` and `|p|^2 = 1`; the
  derivative recurrence is the 2x2 system `M D_v p = rhs` with `M = [d^T; p^T]`, `det M = t|d|`,
  `||M^-1|| <= sqrt(|d|^2+1)/(t|d|)`, and the nonlinear second/third-order terms
  `p.D^2p = -|Dp|^2`, `p.D^3p = -3 Dp.D^2p`, and (corrected, lead audit) the LINE side is
  `d.p' = kappa' - d'.p`, `d.p'' = kappa'' - 2 d'.p'`, `d.p^(k) = -k d'.p^(k-1)` for k >= 3, with
  `kappa'' = |D_v c_b|^2 - |D_v c_a|^2 != 0` (the earlier omission of kappa'' at k = 2 is retracted).
* PAUSED: no quantitative rho reported, no bound assembly; outstanding = plain-algebra audit of the
  interface factors, interval domain lower bounds for `f_lo, |d|_lo, (1-|A0|^2)_lo`, perturbative
  Lipschitz step for the ball version. Open question for the lead: whether to optimise constants at all.
