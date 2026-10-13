# root-cc2 report: radical-branch / geometry audit + interval root certificate

Scope: `research-2026/next-cover-global/members/root-cc2/` only. Old n11/n12 assets read
read-only; no other member's files touched.
Repro (all from this directory):
* `py/audit01_root.py`      -> `evidence/audit01_root.txt`      (branch + geometry audit)
* `py/audit04_contacts_corrected.py` -> `evidence/audit04_contacts_corrected.txt` (contacts)
* `py/calib01_kernel.py`    -> `evidence/calib01_kernel.txt`    (kernel calibration)
* `py/cert01_krawczyk.py`   -> `evidence/cert01_krawczyk.{txt,json}`  (**the certificate**)
* `py/verif01_krawczyk_independent.py` -> `evidence/verif01_krawczyk.txt`
Run with `py -3 -B` (no bytecode is written into the workspace).

## 1. Main result: the local root certificate (the one requested obligation)

**Claim (proved-interval, local).** With
`Phi(z,C,r) = ( F, G, F_z G_C - F_C G_z )`, where `F`, `G` are the two contact
equations of the D2 family as defined by `lead/root_scout.py` and independently
re-derived here, the box

```
X = [0.326813068949914, 0.326823068949914]
  x [0.291936118964939, 0.291946118964939]
  x [0.331727034276234, 0.331737034276234]
```

(declared as the exact mpf/dyadic interval above — the object every test uses — with
half width `5e-6`; the lead's reported root lies strictly inside with distance `5.0e-6`
to every face) contains **exactly one** zero of `Phi`, established by two finite
interval computations at 90-digit working precision:

| test | value | verdict |
|---|---|---|
| Krawczyk existence `K(X) = m - Y Phi(m) + (I - Y M)(X - m) subset int(X)` | smallest face margin `4.35e-6` | PASS |
| contraction `rho = || I - Y M ||_inf` (uniqueness) | `0.129212276185 < 1` | PASS |
| interval `det(DPhi(X))` (invertibility on the box) | `[4.0739, 4.4207]`, excludes 0 | PASS |

with `m` the rational midpoint, `Y` the exact-rational numeric inverse of `DPhi(m)`
(`det = 4.2457427127457716829`), and `M = DPhi(X)` an interval matrix.
`Phi(m) = (5.60e-16, 5.28e-18, 1.21e-15)`; the lead's own point has residuals ~1e-61,
i.e. the same zero.

Uniqueness is the standard argument: for any two zeros on `X`,
`Y Phi(x) - Y Phi(x') = int_0^1 (I - Y DPhi(x'+t(x-x'))) dt (x-x')` and every
`|| I - Y DPhi(.) ||_inf <= rho < 1`, so `x = x'`.

Legality of the branch on the whole box (so the statement is about the legal branch):
`r^2 - z^2 >= 3.23e-3`, `r^2 - (A-z)^2 >= 1.50e-2`, `r^2 - C^2 >= 2.48e-2`,
`1 - r^2 >= 0.8899`, `r - A <= -0.3033` (so `A - z = r - W` and `sigma_B = +`),
`det = A D - B C >= 0.4024` (each read off at the box corners; for these monotone
radicands the corner minimum is the box minimum). `|p1| = 1` is only *sampled* at the
corners (`1.9e-5`); no interval bound on `|p1|^2 - 1` is claimed, and none is needed —
`F` itself carries that term.

Interfaces: input = the audited definition of `(F,G)` and the algebraic combination
`J`; output = existence + local uniqueness of one zero of `Phi` on a rational box;
carried premise = the definition of `Phi` itself (if the lead's `J` convention changes,
the box constants and the whole `M`/`rho` table must be recomputed).
**Not covered:** optimality, the covering property of the 14-centre configuration,
global n=14, and any k11 statement.

## 2. Radical-branch audit — RETRACTED CLAIM (my error), corrected

Independent recomputation at the lead root `(z,C,r) = (0.3268180689499140633…,
0.2919411189649396619…, 0.3317320342762341226…)`, 90/200 digits:

* residuals reproduce `root-scout.json` (max deviation `7.0e-63`), i.e. the input
  coordinates are consistent with the reported system;
* `s = sqrt(1-r^2) = 0.94337365737810…`, `A = (s+z)/2 = 0.63509586316401…`,
  `t = r + sqrt(r^2-z^2) = 0.38861869679828…`,
  `B = r + sqrt(r^2-(A-z)^2) = 0.45425119261295…`,
  `D = 1 - sqrt(r^2-C^2) = 0.84246738235353…`; each `+` branch reproduces the
  `a_b_c_d_s_z_t_r` block of `root-scout.json`;
* **branch status (corrected).** `A - z = (s-z)/2 = 0.3082777942140979`, while
  `r - sqrt(r^2-z^2) = 0.2748453717541834`: the two are *different*. Hence
  `r^2 - (A-z)^2 = 0.0150109441595389` and `r^2 - z^2 = 0.0032360923728978` differ by
  `0.0117748517866411`, and `B = 0.4542511926129566 ≠ t = 0.3886186967982857`.
  So `sigma_B` **is** an independent branch condition selected by the data, exactly as
  `members/candidate/THREE-EQ-AND-NEW-ROOT.md` originally stated; my earlier "force
  sigma_B = sigma_t" claim (registered as C1160, now retracted) was wrong, and the
  sympy expression I quoted, `r^2-(A-z)^2-(r^2-z^2) = -(s-z)(s+3z)/4 = -0.2965…`, is
  the non-zero *difference*, i.e. a constraint, not an identity. `sigma_D = -` is
  likewise genuine. The reason the original numerical "agreement" of 1e-62 was
  spurious: the audit script compared `B`'s radicand with itself.
* `det = A D - B C` is bounded away from 0 on the certificate box: interval enclosure
  `[0.4024036932, 0.4024622069]`.
* Registered claims: C1160 and C1161 were **retracted**; no replacement claims were
  added (lead instruction). The corrected statements live here and in DEAD.md.

## 3. F / G geometry audit (rewritten)

* **The coded `F` and the algebraic contact condition.** `lead/root_scout.py` codes
  `F = (|p1|^2 - 1)^2 + (|p1 - S1|^2 - r^2)` with `p1 = M^{-1} v`, `M = [[A,D],[C,B]]`,
  `v = (v1,v2)`, `v1 = (1+|S1|^2-r^2)/2`, `S1 = (A,B)`, `S2 = (C,D)`. The linear solve
  enforces `p1.S1 = v1` identically, so with `e := |p1|^2 - 1` the identity
  `|p1-S1|^2 - r^2 = e` holds **exactly** (from `|p-S1|^2 = |p|^2 + |S1|^2 - 2p.S1`),
  and therefore
  ```
  coded F  =  e^2 + e  =  e(e+1) .
  ```
  My kernel's `F_tilde = e^2 + (|p1-S1|^2 - r^2)` is the *same expression*: verified to
  200 digits, `F_kernel - F_coded = 7.3e-203`, ratio `1.0`
  (`evidence/verif03_interface_highprec.txt`). Hence my root kernel is a legitimate
  representation of the lead's contact equation, and `F = 0 ⇔ e = 0` holds on the box
  because (i) `|p|^2 = e+1` is strictly positive there — interval `[0.9995226, 1.0004776]`
  — and (ii) `det ≠ 0` there (`[0.4024037, 0.4024622]`).
  Caution: the lead's message described the alternative normalization "`F = det^2 e`"
  (`h = |p|^2/det^2 = 6.17465845489`); that is a *different* function from the coded one
  and is **not** what the certificate uses. The certificate evaluates the coded `F`
  directly, so no normalization hypothesis is needed for C1164.
* **F is a boundary two-site switch on `S^1`** — with the branch *measured*, not assumed:
  the two intersections of the radius-`r` circles about `S1`, `S2` are
  `(0.3082777942140979, 0.5111378551350082)` with `|p| = 0.5969062785375325` (not on
  `S^1`) and `(0.6187591879148537, 0.7855807198314828)` with `|p| = 1.0` (28+ digits).
  The lead's solve reproduces the **second** one, i.e. the genuine contact point with
  `|p1 - S1| = |p1 - S2| = r`; my earlier claim that it returns the lower point
  (registered as C1161, now retracted) was a plus/minus labelling error in my own script.
* **G is the interior three-site circumradius condition** — `G = l1 l2 l3 - 4 r^2 cross^2`
  with `l_i` the squared side lengths of `S1, S2, S3 = (0,t)` and `cross = 2[area]`, so
  `G = 0 ⇔ R_circum = r` (with `cross ≠ 0`). Verified at the root:
  `R_circum = 0.33173203427623… = r`. Thus the system couples one **boundary** two-site
  contact to one **interior** three-site contact, matching 3 free parameters minus one
  stationarity condition.

## 4. The "contact structure changed" claim is an indexing artefact

`audit04_contacts_corrected.txt`. The free D2 family of `root_scout.py` produces only
**10** centres (3 orbits of 4, one of which folds to 2); the full 14-centre object
keeps the two fixed x-axis pairs. Rebuilding the *same physical* slot configuration at
the new root (slot deltas `3.2e-10` for the A-orbit, `1.2e-9` for the B-orbit,
`2.3e-10` for the near x-axis pair, `1.3e-9` for the y-axis pair) and enumerating
nearest-site-filtered Voronoi vertices gives **the identical contact structure in both
objects**:

* tight vertices at radius `r`: `(0,6,12) (0,8,11) (0,11,12)` and the D2 images —
  all 12 of them plus the two 2-site vertices `(10,11,12)`, `(10,11,13)` (14 tight);
* the same slack pair: `(4,6,12)` and `(5,7,13)` at radius `0.3208208546053816835…`
  (identical to 20 digits in both objects);
* `R_cover = max_D min_i |x - P_i| = r = 0.331732034276234122557815548802` for the
  rebuilt new-root configuration (restricted numerical computation; not a certificate).

Therefore the candidate's claim that "the contact structure changed" is a labelling
artefact: the two configurations are the same physical configuration up to ~1e-9 and
cannot have different contact combinatorics. Their `Jdet` difference (a factor ~66.8
in their own text) is likewise a normalization difference and does not affect the root
set — `F`/`G` multiplied by a non-zero factor have the same zeros.

## 5. Corrections to the record (mine, kept honest)

* My first contact reconstruction (`audit02`/`audit03`) used the **incomplete**
  10-centre family and reported `R_cover = 0.5827` at `(-1,0)`; that was my error (the
  boundary reference point is covered by the *fixed* x-axis pair, which I had left
  out). Superseded by `audit04`. The old-hprec side of `audit02/03` additionally used
  `json['centers']` (float64) instead of the exact `th` literals — per the lead's
  instruction that portrait is **invalid** and was not used for any conclusion.
* `audit01` initially mislabelled the old point's free coordinates; the lead's
  `root_scout.py` uses `(z, th[2], R)` where `th_names[2] = 'p'`, i.e. the middle free
  coordinate is the **C/R-axis coordinate of the S2 site**, consistent with the new
  root's second coordinate. No conclusion depends on the old point.
* Kernel development failures (three of them) are recorded in `DEAD.md`; each was
  caught by the calibration script, not by inspection.

## 6. Remaining minimal obligation

The root certificate is a **local** statement. The next minimal obligation is not
global: it is to check whether this stationary zero is a *feasible covering*
configuration at `r` (i.e. the certified upper construction and this root are the same
object), and only then whether the metric stress/KKT diagnostic at this geometry
excludes a better local covering. The global n=14 question, the k10 finite-graph
completeness audit and the k11 exclusion are untouched here.
