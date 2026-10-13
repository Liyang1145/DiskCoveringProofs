# Physical 18-branch architecture, KKT common-gradient kernel, reflection blocks, and the
# KKT-kernel invariance (gauge + metric) lemmas

Scope: `research-2026/team-current/r20-rigidity/` only. Instrument: `r20_physical_kkt_kernel.py` ->
`r20_physical_kkt_kernel.json` / `.log` (mpmath dps=60, **no finite differences**). Anchor (read-only):
`../lead/repaired_tc_krawczyk.json` (the 12D symmetric TC root box, radius
`0x1.12e0be826d695p-30` = 1e-9 exact with `iv(c)+iv([-rad,rad])`; centre = exact binary64s;
Newton limit 62 digits). Geometry root interface: `lead/STRICT-EMPTY-FACET-COMPLETENESS.md`
(strict-empty facets ⇒ the 11 Delaunay faces), used as an interface, not re-audited.
No claim is registered here (lead owns registration); the candidate claims are listed in §9.

Division of labour taken from the lead's 2026-09-25 messages: the **symmetric 2x2 block** (free
`(y0,y1)` graph basis, interval Gauss) is the lead's (`lead/TC-SYMMETRIC-SECOND-VARIATION.md`,
`certify_tc_symmetric_hessian.py/json`); this note owns the **anti 8x11 rank**, the **rotation
quotient (3 -> 2)** and the **anti physical Hessian block**. Certified anti weights need
`r20-stress`'s exact `nu`; everything numeric here uses the canonical Danskin weight.

---

## 0. Summary of readings (all at the lead's root box, dps=60)

| object | reading |
|---|---|
| branch catalogue | 11 faces + 9 ties; **18 active** (9 faces = 7 fan + 2 central, 9 ties), 2 slack faces |
| active values | `max abs(f_i - R*) = 4.7e-59`; slack `R* - f = 1.152681921e-3` (both orbits) |
| chart coincidence | fans vs pins `U_k` 9.5e-59; ties vs `B_k` 1.6e-61; central vs `(m,+-h)` 5.5e-62 |
| critical set (cross-check) | 20 points, 18 at radius `R*` (matches W2's 9 V3 + 9 V2b; the 2 slack are V3) |
| jet vs FD control | `max |FD(1e-15) - jet| = 4.9e-31` (6 branches x 3 coordinates) |
| `sv(J\|Sym)` (18x11) | .9394 .9035 .8012 .6717 .5658 .5288 .4211 .2830 .1808, then 0, 0 |
| `sv(J\|Anti)` (18x11) | 1.0967 .9485 .8383 .7305 .6172 .5006 .2508 .0584, then 0, 0, 0 |
| ranks | `rank(J\|Sym) = 9`, `rank(J\|Anti) = 8`; gaps 1.5e57 / 2.3e59 |
| anti 8x11 | orbit-representative rows; `sv` .7755 .6707 .5928 .5165 .4364 .3539 .1773 .0413; best minor (cols 2,3,4,5,7,8,9,10) `det = -7.0679e-5` |
| anti kernel | dim 3; two independent routes (minor-null vs mpmath SVD) agree (rank of combined basis 3); residuals 1.7e-62 / 2.2e-61 |
| rotation | `|A_anti rot_a| = 7.2e-62`; inside the kernel span to 1.5e-61 |
| `lambda` (Danskin) | `min 9.894700e-3`, `max 1.270147e-1`, `sum 1`; `|sum lam_i grad f_i| = 1.8e-59`; reflection-symmetric to **2.1e-61** |
| mixed block | `max |BS^T HW BA| = 1.8e-61` (**exact 0**); `|[SIG,HW]| = 2.8e-61` |
| rotation | `|HW rot| = 7.4e-60` (**exact kernel direction of the weighted Hessian**) |
| **anti block** | 3x3 eigenvalues `{0.0000000000, 0.1649026928, 0.2549598729}`; quotient 2x2 = the two positive values; anti max-form value `0.3066 > 0` |
| sym block (calibration; lead owns) | 2x2 eigenvalues `{0.2216701155, 0.2813311259}` (physical metric) |
| gauge conversion | fan `(2,3,H0)`: `kappa = Fout/(4y^2) = 0.4187003705`; kernel identity `d2G = kappa d2f` to **2e-63**, off-kernel gap **2.5e-2** |
| interface calibration | `w_i c_i` orbit-constant to 6.9e-61 (faces), `w_j b_j` to 1.6e-61 (ties) |
| chart transfer | pullback (7D jets) vs chain `Y^T HW Y`: **2.4e-55**; chart-z vs physical sym eigenvalues `{0.3976, 0.7609}` vs `{0.2217, 0.2813}` |

**Interval certificate (this directory, `r20_anti_block_interval.py`, box mode):** with
`r20-stress/weights_interface.py::physical_weights()` (interval KKT weights, all 18 strictly
positive, sum contains 1) and the lead's 12D root box:

* witness minor interval determinant `[-4.00004e-4, -3.99635e-4]` **excludes 0** ⇒
  `rank(A_anti) >= 8` on the whole box (no SVD, no numeric rank);
* rotation coefficients inside the 3D kernel: `|rot_a| = (0.2984, 0.7647, 0.6736)`, so with
  `j* = 1` the pair `(KV[0], KV[2])` is an explicit rotation-free 2D complement;
* Sylvester on interval endpoints: `B11 in [0.45045, 0.45047] > 0` and
  `det >= 0.217798969238 > 0` (exact-endpoint comparisons, no eigenvalue/Gram arithmetic in the
  claim) ⇒ the weighted form is **positive definite on that complement for every configuration in
  the box and every weight in the interval enclosure**;
* controls (point mode): the 22D orthonormal-quotient route gives `{0.164903, 0.254960}`, matching
  the exact-formula numeric run, and the 3D kernel pencil gives `{0, 0.164903, 0.254960}` (rotation
  as the exact zero direction).


---

## 1. The physical branch catalogue and its finite formulas

Configuration: 11 sites `c_1..c_11` in `R^2` (9 ring `C_0..C_8` + hubs `H0,H1` at the candidate),
`x in R^22`; radius variable `R`. Two branch types (both smooth on the candidate's open
neighbourhood, and **rotation-equivariant**):

* **face branch (V3)** for a noncollinear triple `(a,b,c)`: `p` = circumcentre, `f = |p - c_a|`.
  With `g_1 = c_a - c_b`, `g_2 = c_a - c_c`, `w = p - c_a`:
  ```
  M w = beta,   M = [g_1^T; g_2^T],  beta = -(|g_1|^2, |g_2|^2)^T / 2,   M = [[g1x,g1y],[g2x,g2y]]
  ```
  (the code uses the equivalent Cramer form). Directional derivatives are **finite**:
  ```
  M dw = d(beta) - (dg_1.w, dg_2.w)^T,      d(beta) = -(g_1.dg_1, g_2.dg_2)^T
  M d^2w = -(dg'_1.dg_1, dg'_2.dg_2)^T - (dg'_1.dw + dg_1.dw', dg'_2.dw + dg_2.dw')^T
  df     = what_a . dw
  d^2f   = what_a . d^2w + [ dw.dw' - (what_a.dw)(what_a.dw') ] / f
  ```
* **tie branch (V2b)** for an adjacent pair `(k,k+1)`: `p` = perpendicular bisector
  `{p : p.d = kappa}`, `d = c_{k+1} - c_k`, `kappa = (|c_{k+1}|^2 - |c_k|^2)/2`, intersected with
  the unit circle on the near side, `f = |p - c_k|`:
  ```
  p = A0 + s t n,  A0 = (kappa/|d|^2) d,  n = d^perp/|d|,  t = sqrt(1 - |A0|^2),  s = +-1
  ```
  (an explicit rational-plus-one-sqrt expression; the code differentiates it by second-order jet
  arithmetic, i.e. exactly, including the sign branch, which is fixed by the nearest-two-site test).

The **implementation** is a 3-field second-order jet `(v, g in R^22, h in R^{22x22})` with
`+,-,*,/,sqrt,cos,sin` (all closed-form propagations); the branch code is shared between the
numeric and jet evaluations, so the same expression is evaluated and differentiated. This is the
"finite formula directly on the physical branches" asked for: no angle chart, no finite differences.
The jet chain is controlled against high-precision central differences (`max |FD - jet| = 4.9e-31`)
and — independently — reproduces the previously registered FD-based readings:
`sv(J|Sym) = [0.93945, 0.90354, 0.80116, 0.67166, 0.56581, 0.52877, 0.42108, 0.28302, 0.18084]`
and `sv(J|Anti) = [1.09666, 0.94851, 0.83833, 0.73047, 0.61718, 0.50056, 0.25079, 0.05842]`
agree with `r20_second_order_certificate.json` (`sigma_Sym`, `sigma_Anti`) to all printed digits,
and the positive centred spectrum `[0.16490, 0.22167, 0.25496, 0.28133]` reproduces W8's
`[0.1649, 0.2217, 0.2550, 0.2813]`. Calibration note: the *negative* full-space eigenvalues read
by the old FD route (`-3.28e-2, -1.32e-2`) are **not** reproduced in magnitude (exact formulas:
`-7.95e-2, -1.84e-2`); the sign structure (two negative directions outside the kernel) is the same
and the exact-formula values should be used downstream.

## 2. KKT setting and the common-active-gradient kernel (analytic)

Minimise `R` subject to `F_i(x,R) = f_i(x) - R <= 0`, `i in A` (`|A| = 18`). Suppose a positive
weight `w` on `A` with
```
(T1) sum_i w_i grad f_i = 0   and   sum_i w_i = 1
```
(the normalisation `sum w_i = 1` is exactly the R-component of stationarity; the lead's lift gives
`w_i = mu_i c_i` on faces, `w_j = nu_j b_j` on ties — see §5).

**Lemma 1 (kernel and the R-direction).** Let `T = {(dx,dR) : dF_i(dx,dR) = 0 for all i in A}`.
Under (T1), `T = ker J_A x {0}` where `J_A = (grad f_i)_{i in A}`, and
`dim T = 22 - rank J_A`. Proof: `dF_i(dx,dR) = df_i(dx) - dR`, so summing with weights gives
`0 = sum_i w_i df_i(dx) - dR = -dR` for any `dx` in `ker J_A`; conversely any `(dx,dR) in T` gives
`0 = sum_i w_i df_i(dx) = dR`, hence `dx in ker J_A`. QED

So the second-order object lives in the 22 centre coordinates; the constraint curvature of the
`R`-equation is zero and no auxiliary angle equality enters.

**Lemma 2 (rotation).** Every branch function is invariant under simultaneous rotation of all
centres about the origin (faces: the circumcentre rotates with the triple; ties: the unit circle and
the bisector are rotation-invariant). Hence `J_A rot = 0` identically, i.e. the rotation field is an
**exact** kernel direction. Verified: `max |J rot| = 6.8e-62`, `|P_Anti rot| = 1` (the rotation field
is purely anti-invariant), `|P_Sym rot| = 0`.

Numeric dimension chain at the anchor (numerical rank — no exact rank statement is claimed here):
`rank J_A = 17`, `dim ker J_A = 5` = 2 (Sym) + 3 (Anti), and mod the rotation direction `4 = 2 + 2`.
The Sym side is the lead's chain (`rank J_{5x7} = 5` deduced from the certified 12x12 KKT Jacobian
non-singularity ⇒ `dim = 7 - 5 = 2`); the Anti side is the explicit 8x11 minor below.

## 3. The anti block: 8x11 rank and the rotation quotient (this directory's obligation)

Reflection `sigma : (x,y) -> (x,-y)` acts on `R^22`; `R^22 = Sym(11) + Anti(11)` exactly (bases built
in closed form, `|SIG^2 - I| = 3.1e-61`). The 18 active branches form **10 reflection orbits**
(8 paired + 2 fixed: the self-reflected fan `(8,0,H1)` and the self tie `B_8`). The 2 fixed
branches are `sigma`-invariant, so their gradients are `sigma`-invariant and their **anti parts
vanish**; hence the anti-projected gradient map is supported on the 8 paired orbits:

* `A_anti` = the 8x11 matrix whose rows are the anti parts of one representative per paired orbit
  (faces `(1,2,H1),(2,3,H0),(3,4,H0),(2,H0,H1)` and ties `B_0..B_3`).
* `sv(A_anti) = .7755 .6707 .5928 .5165 .4364 .3539 .1773 .0413` (**all nonzero**: `rank = 8`);
  explicit witness minor on columns `(2,3,4,5,7,8,9,10)`, `det = -7.0679e-5` (60-digit value
  `-7.0678782569e-5`). The row space of `A_anti` equals the row space of `J|Anti` (same rank, rows
  contained), so `ker A_anti = ker (J|Anti)` = the 3D anti kernel.
* The kernel is computed by **two independent routes**: (a) null space via the explicit minor
  (exact linear solve), (b) mpmath SVD of `J|Anti` (rows 8..10). Residuals `1.7e-62` and `2.2e-61`;
  the combined 6-vector basis has rank 3, i.e. the two routes span the *same* 3D space. This is the
  "8x11 rank" obligation: rank 8 with an explicit minor, kernel 3, no 22x22 floating null space used.
* **Rotation quotient.** `|A_anti rot_a| = 7.2e-62` and `rot_a` is inside the kernel span to
  `1.5e-61`; the remainder is 2-dimensional. So `3 = 1 (rotation) + 2`.

## 4. Reflection block decomposition and the weighted Hessian

Let `w` be the canonical Danskin weight (T1) and `H_W = sum_i w_i H_i`. Since every branch is
`sigma`-equivariant (`J_{sigma(r)} = J_r SIG` to 1e-16 in the earlier run; here the exact statement is
`f_{sigma(i)}(x) = f_i(sigma x)`) and `w` is `sigma`-invariant (**verified 2.1e-61**), `H_W` commutes
with `sigma`:

* `|[SIG, H_W]| = 2.8e-61`, `max |BS^T H_W BA| = 1.8e-61`.
* The mixed Sym x Anti block is therefore **exactly zero** — not "neglected": the only inputs are
  (i) `sigma`-equivariance of the branches, (ii) `sigma`-invariance of the weight vector. Both are
  structural, and (ii) is a consequence of the lead's reflection lift (`w_{sigma(i)} = w_i`).
* **Lemma 3 (rotation nullity).** If `W = sum_i w_i f_i` has `grad W = 0` at `x*` and is
  rotation-invariant, then `H_W rot = 0` (differentiate `W(g_t x) = W(x)` twice and use
  `grad W = 0`). Verified: `|H_W rot| = 7.4e-60`, `rot^T H_W rot = 1.6e-60`. Consequently the anti
  3x3 block is singular with the rotation as an exact kernel vector, and the quotient (2x2) carries
  the physical second-order information.

**Anti block readings** (physical metric, orthonormal basis; `w` = numeric Danskin weight):
```
anti 3x3 eigenvalues        { 0.0000000000, 0.1649026928, 0.2549598729 }
anti quotient 2x2 eigenvalues { 0.1649026928, 0.2549598729 }        (positive)
sym 2x2 eigenvalues (calibration, physical metric) { 0.2216701155, 0.2813311259 }
anti max-form value  min_v max_i v^T H_i v = 0.3066 > 0   (necessary-condition side, float64)
```
So the weighted second-order form is positive definite on the centred common kernel in the physical
metric: anti quotient margin `0.165`, sym margin `0.222`, cross block `0`. The margins are `O(0.1)`,
i.e. this is not a borderline reading.

## 5. Interface calibration: the weight factorises as (orbit multiplier) x (conversion factor)

Using the lead's conversion factors (`c_i = 4 y_i^2 / Fout_i` for face `i`, `b_j = a_{j,R}+a_{j+1,R}`
for tie `j`) computed here from the anchor geometry:
```
face c_i : 2.231568 2.388343 2.977926 2.977926 2.388343 2.231568 2.614933 3.245038 3.245038
tie  b_j : 2.765683 3.448380 3.140160 2.308616 2.308616 3.140160 3.448380 2.765683 2.547066
```
The canonical weight satisfies, to 60-digit accuracy,
```
w_i * c_i   orbit-constant (spread 6.9e-61 over the 5 face orbits)
w_j * b_j   orbit-constant (spread 1.6e-61 over the 5 tie orbits)
```
i.e. `w_i = mu_k c_i`, `w_j = nu_j b_j` with one multiplier per orbit — exactly the lead's
"Physical radius branch weights" interface (`lead/TC-TO-PHYSICAL-KKT-LIFT.md`). This is a
**numerical 18 -> 10 factorisation check** of that interface (it does not certify the multiplier
*signs*, which is `r20-stress`'s obligation). Implied orbit multipliers at this anchor:
`mu = [0.2834, 0.0731, 0.0295, 0.1357, 0.0942]`, `nu = [0.1679, 0.2105, 0.2508, 0.1303, 0.0992]`
(per-branch normalisation; the orbit-sum convention is the lead's).

## 6. Gauge conversion: `d^2G` vs `kappa d^2f` (the cross terms) and the kernel identity

For the fan face `(2,3,H0)`: `G = Rc - R` (radius excess of the circumradius branch) and
`f = |U_inner - H0| - R` (chord-circle inner-pin residual). The lead's exact identity
`4 y^2 (Rc^2 - R^2) = F_in F_out` gives `G = kappa * f` with `kappa = Fout/(4y^2)` (positive,
`Fout > 0`), here
```
Fout = 0.7092308604852 ,  y = -0.65074695417736 ,  kappa = 0.418700370469513017
(calibrated independently by the limit face-excess / pin-residual -> 0.41870037)
```
**Lemma 4 (gauge/kernel invariance).** If `G = kappa f` with `kappa > 0` smooth, `f(x*) = 0` and
`df|_T = 0` (`f` is one of the tied residuals), then on `T`
```
dG|_T = 0   and   d^2G|_T = kappa(x*) d^2f|_T ,
```
while in the full space `d^2G = kappa d^2f + df (x) dkappa + dkappa (x) df + f d^2kappa`, so
`d^2G != kappa d^2f` off the kernel. Proof: differentiate the product identity; the cross terms
contain `df`, which vanishes on `T`, and the last term contains `f(x*) = 0`. QED

Readings: on the two anti-quotient kernel directions `(d^2G, kappa d^2f, gap) =`
`(0.0018124012916162, 0.0018124012916162, 2e-63)` and
`(0.19017496360743, 0.19017496360743, 1e-61)`; along a transverse direction the same comparison
gives `d^2G = 1.0260297539447` vs `kappa d^2f = 1.0511732941401`, **gap 2.5e-2**. This is exactly the
warning "cannot simply use `H_G = kappa H_f` in the whole space" together with its resolution on the
common kernel.

**Consequence (used by the lead's weight formula):** the weighted form may be evaluated either with
the radius branches and weights `mu_i c_i` (resp. `nu_j b_j`), or with the pin/gap residuals and
weights `mu_i` (resp. `nu_j`) — the two agree on `T` exactly, by Lemma 4 applied branchwise. So the
lead's second-order weight formula `mu_i c_i`, `nu_j b_j` is *consistent* with the physical branch
Hessians, and no angle-manifold curvature (the `sum mu_j grad^2 c_j` normal correction of
`r20-stress/PHASE3-LAMBDA-HESSIAN.md`) appears in the physical formulation: the physical constraints
are `f_i - R <= 0`, whose `x`-curvature is exactly `H_i` and whose `R`-curvature is zero.

## 7. Metric / congruence transfer — why angle-model eigenvalues may not be equated

**Lemma 5 (congruence transfer).** Let `Psi` map a second chart (angles, graph coordinates, ...) to
the centre coordinates, `Y = DPsi` at the base, and let `W = sum_i w_i f_i` be a weighted branch sum
with `grad W = 0` at the base (true here by T1). Then for `v,w in ker(DPsi) = T_z`:
```
d^2(W o Psi)|_{T_z} = Y^T d^2W|_{T_x} Y      (no chart-curvature term survives, because grad W = 0).
```
Verified against the lead's 7D TC chart (`z = (a0..a3,y0,y1,R)`, `Psi` = the chart map):
pullback computed by 7D jet arithmetic vs chain rule `Y^T H_W Y` agree to **2.4e-55**, and
`|grad_{22D} W| <= 1.8e-59`, `|grad_{7D}(W o Psi)| <= 4.4e-58`.

Consequences (this is the "kernel-invariance lemma" asked for):

1. **Inertia and sign conditions are chart-independent** (Sylvester's law of inertia); *eigenvalues
   are not*. At the same base point, the sym 2x2 block reads `{0.2217, 0.2813}` in the physical
   metric but `{0.3976, 0.7609}` in the chart-`z` (generalized) metric; the per-mode ratios
   (1.7938, 2.7045) are **not** equal, so the change is a genuine metric congruence, not a rescaling.
   A controlled random linear chart preserves the inertia `(19 pos, 2 neg)` while moving the
   spectrum (`-0.0795, -0.0184, 0` as the smallest three values). Calibration note: the chart-metric
   numbers here are computed with `scipy.linalg.eigh(B, G)`; an earlier reading of this pair used
   `numpy.linalg.eigvalsh(G^{-1}B)`, which silently reads one triangle of a non-symmetric matrix and
   is not admissible — the corrected values (0.3976, 0.7609) agree with the lead's independently
   computed TC-chart eigenvalues `[.3976, .7609]`, which is an external control of the transfer.
2. **Per-branch positive factors and monotone reparametrisations** (`f_i -> kappa_i f_i`,
   `gamma_i -> log gamma_i`) preserve the *sign* of every `v^T H_i v` on `T` and hence the sign of
   the max-form condition `min_v max_i v^T H_i v >= 0` (each term is multiplied by a positive
   number). So the physical, pin-residual, gap and log-radius formulations all carry the same
   second-order sign information on the common kernel.
3. **What does NOT transfer:** numeric spectra. The angle-model readings
   (`r20-stress/PHASE3-LAMBDA-HESSIAN.md`: `V0` 3x3 `{0.0443247, 0.0564136, 0.0588168}`; lead's
   centred dim-4 `{.0413, .0499, .0568, .0590}`) live in a 42-angle model with its own auxiliary
   equalities, its own metric and the `log gamma + log(q0/ell0)` normalisation; they must **not** be
   equated with the physical `{0.16490, 0.22167, 0.25496, 0.28133}`. Only signs, inertia,
   dimensions and the (sign of the) max-form condition are shared. Likewise the lead's certified
   symmetric block reads `G00 in [.5782,.5898]`, `G01 in [-.3142,-.2984]`, `G11 in [.965,.9867]`,
   `det > .4593`, eigenvalues `> 1/4` in the **hub-coordinate graph metric** — a congruent, not
   equal, representation of the same physical block.
4. **Therefore the future interval LDL can be run directly on the physical branches** (finite
   formulas of §1, no angle manifold, no auxiliary constraint curvature): positivity of
   `sum_i w_i H_i` on `T` is a metric-free statement on the subspace `T = ker J_A x {0}`. What must
   be certified are the ingredients that are not metric-free: the branch formulas, the rank/kernel
   chain, and the weights `w_i` (via the lead's `mu, nu`).

## 8. Local theorem interface (what the anti block feeds into)

Assembly reference: `lead/LOCAL-CERTIFICATE-ASSEMBLY.md` (objects C891/C892/C893/C897) and the
lead's `FINITE-MINIMAX-QUALITATIVE-SUFFICIENCY.md`. The chain is now:
1. **Model completeness (lower bound + equality):** near the base, `R_D(x) >= max_{i in A} f_i(x)`
   (C892 + the boundary-switch interval margins: at each tie every other site keeps squared
   distance minus `R^2 > .01` over the box), with equality at the base; locality of the active
   branches is guaranteed by the registered strict margins. No active-set stability for the two
   slack faces is needed.
2. **First order:** `0 in ri conv{grad f_i : i in A}` with positive weights (C897; stress's
   interval weights give 18/18 strictly positive and `sum = 1`, confirmed here).
3. **Second order on the common kernel** (`T = ker J_A x {0}`, rotation in `T` analytically):
   * Sym 2x2: lead's interval-certified block (C893).
   * Anti 2x2 quotient: **interval-certified here** (witness minor rank, explicit rotation-free
     complement, Sylvester `B11 > 0`, `det > 0`).
   * Mixed Sym x Anti: **exactly 0** (Lemma: `sigma`-invariance + equivariance).
   * Rotation: exact kernel direction of the weighted Hessian (Lemma 3), so the statement is
     "PD mod rotation".
4. The qualitative Taylor/compactness argument (lead) then gives a strict local minimiser of
   `max_{i in A} f_i` mod rotation, hence of `R_D` mod rotation, with `cover(x) >= R* + c
   dist(x, orbit)^2` nearby.
5. **Still open:** the global far-region quantitative cover (no remote asymmetric configuration with
   smaller radius is excluded), and — as noted in the assembly doc — the local theorem does not
   upgrade to the original global target.

## 9. Candidate claims for the lead to register (statements + evidence)

* **A. (proved, analytic)** Common-active-gradient kernel identity: under a positive weight with
  `sum w_i grad f_i = 0`, `sum w_i = 1`, the tied tangent space is `T = ker J_A x {0}` in
  `R^23`; the rotation field is an exact kernel direction; the weighted Hessian annihilates the
  rotation field. Evidence: this file §2-§4 (proofs) + `r20_physical_kkt_kernel.json`
  (`kernel`, `blocks.hw_rot_max`, `gradient_maps.rotation_equivariance`). Status: proved / numeric
  for the residual readings.
* **B. (proved, analytic)** Gauge/kernel invariance `d^2G|_T = kappa d^2f|_T` for `G = kappa f`,
  `f|_T = 0`, `df|_T = 0`; and the exact-zero mixed reflection block. Evidence: §4, §6 (proofs) +
  JSON (`gauge.kernel_pairs`, `blocks.mixed_max`).
* **C. (interval, unconditional rank + conditional-on-weights PD)** Anti block: the explicit 8x8
  minor has interval determinant excluding 0 over the whole box ⇒ `rank A_anti >= 8`; on the
  reflection-symmetric slice `rank <= 8` structurally (the two self-reflected branches have
  `sigma`-invariant gradients, their anti parts vanish, and the 16 remaining rows form 8 conjugate
  pairs) ⇒ `rank = 8` and the anti common-gradient kernel is exactly 3-dimensional, with the
  rotation inside analytically. With r20-stress's interval weights (all 18 strictly positive, sum
  contains 1) the weighted form on the explicit rotation-free complement `(KV[0], KV[2])` satisfies
  `B11 > 0` and `det >= 0.217798969238 > 0` (Sylvester on interval endpoints) ⇒ PD mod rotation.
  Evidence: JSON `certificate`, `minor_det`, `rotation_coeffs_abs`;
  `R20_POINT=1` controls reproduce the exact-formula spectra `{0.164903, 0.254960}` and
  `{0, 0.164903, 0.254960}`.
* **D. (numeric, high precision)** Weight factorisation `w_i c_i`, `w_j b_j` orbit-constant
  (6.9e-61 / 1.6e-61) — interface calibration of the lead's `mu, nu` weight formula; the certified
  weights themselves are r20-stress's (`weights_interface.py`, C897).

## 10. Repro

```
py -3 -B -X utf8 r20_physical_kkt_kernel.py        # -> r20_physical_kkt_kernel.json / .log  (~1 min)
py -3 -B -X utf8 r20_anti_block_interval.py        # interval anti certificate -> r20_anti_block_interval.json
R20_POINT=1 py -3 -B -X utf8 r20_anti_block_interval.py   # point-mode controls (spectra vs the numeric run)
```
Read-only inputs: `../lead/repaired_tc_krawczyk.json`, `../r20-stress/weights_interface.py`
(hashes recorded in the JSON output). No scipy in the branch/jet/kernel chain (scipy is used only
for float64 diagnostics). The sym-side interval block is not recomputed here (lead's
`certify_tc_symmetric_hessian.py`, C893).
