# Midpoint rigidity: does the norm-uniform-convexity gain pay for the anchor radial-normalization repair?
*(analytic criterion · numeric indications · open gap)*

Scope: this directory only; no lead/registry file touched. One analytic route plus the finite
diagnostics already reported. This revision follows the lead's review: **§1 is the only analytic
claim kept**; everything else is re-labelled as numeric evidence, inherited mechanism, or gap.
No unconditional "no uniform gain" and no "amplitude harmless" statement remains.

## 0. Status of every statement in this file

| # | statement | status |
|---|---|---|
| §1 | exact interpolation identity, exact normalization term, (SUF) implies no radial repair | **analytic** (algebra); the growth/entry constants are **inherited** from `members/q10-effective-localization/REPORT.md` |
| §2 | `lambda_e = (1+r*^2-\|c_v*\|^2)/2`, values .250177621/.157532618/.110046143 | algebraic values, evaluated on the saved root strings (**numeric** to input precision, no interval certificate); `lambda_e = r*^2` at the X sites and the X pair-rotation identity are **exact** (proved below) |
| §3 | rank(J) = 61, 8-dimensional flex space, "for each of the 20 anchor edges a linearized feasible direction with gain 0" | **numeric** (float SVD + constructed vectors, residuals ~1e-15); exact only in the weak form `dim ker >= 7`, `dim(ker ∩ {d_e=0}) >= 5`. Refutes (SUF1) **on the linearized space**, conditional on the numeric rank; does **not** refute uniformity over actual covers (§4) |
| §5 | the 44-edge support, the six zero-weight faces, the stress mechanism | **inherited** from `lead/STRESS-SUPPORT-ANALYTIC.md` / `lead/STRESS-OBSTRUCTION.md`; my LP is a **numeric consistency check**, not a proof of rank or of forced zeros |
| §4,§6 | any bound on beta, any "harmless" / "at most factor 1.73" statement | **gap** (withdrawn; see §4) |

## 1. Analytic core (kept)

Setup. Candidate (C\*, w\*, A\*, r\*): 14 sites, 16 face witnesses, 10 boundary anchors, 68 incidences,
62 active (length exactly r\*) and 6 inactive (the two slack faces (4,5,13),(6,7,12), radius
rho = 0.320820854605). Endpoint (C,w,A,r): every incidence <= r <= U, so r - r\* <= eta = U - r\*.
Gauge: one **common rotation** is fixed first; afterwards A_j = exp(i(theta_j\* + a_j)),
beta := max_j |a_j|. Interpolate sites, witnesses and anchors linearly in Cartesian coordinates
("common Cartesian interpolation"); the interpolated anchor b_j(t) = (1-t)A_j\* + tA_j lies inside the
unit circle, so it is renormalized: q_j = |b_j|, ahat_j = b_j/q_j, e_j = 1-q_j.

**(A) Exact identity** (parallelogram law = uniform convexity of the Euclidean norm), per edge:
```
|x_e(t)|^2 = (1-t)|x_e*|^2 + t|x_e|^2 - t(1-t)|Dx_e|^2 ,   Dx_e := x_e(1)-x_e(0).
```
**(B) Exact effect of the normalization** (anchor edges only), mu_j := e_j/q_j:
```
|c_t(v) - ahat_j|^2 = |x_e(t)|^2 - 2 mu_j (x_e(t).b_j) + e_j^2 .
```
**(C) Sufficient condition (SUF)** for the linear radius r_t := (1-t)r\* + tr to need **no** radial
repair, i.e. `R_t = r_t`, hence `h_t = R_t^2 - r*^2 = 2 t r* (r-r*) + t^2 (r-r*)^2`: for every edge e
and every t in [0,1],
```
t(1-t) ( |Dx_e|^2 - (r-r*)^2 )  >=  Lambda_e(t),   Lambda_e(t) = -2 mu_j(t)(x_e(t).b_j) + e_j^2
```
(`Lambda_e = 0` for witness/site edges). Sufficiency is elementary: (A) and (B) bound the repaired
distance on every edge by `r_t^2 + t(1-t)(r-r*)^2 - t(1-t)|Dx_e|^2 + Lambda_e(t)`, and that expression
is `<= r_t^2` exactly when (SUF) holds.

**Inherited:** *if* (SUF) holds for all edges and all t, the first-exit argument of
`members/q10-effective-localization/REPORT.md` (local growth `P >= kappa t^2 D^2`, entry threshold
`(mu/2) eps^2` with eps = 4e-5, mu > .00857761) gives a localization bound `D` of order
`r*(r-r*)/(mu eps)`; with r-r\* ~ 1e-17 that is ~1e-10. Nothing in this file proves (SUF); it is the
target inequality. First-order form, on motions that preserve the 62 active lengths to first order:
```
(SUF1)   |d_e|^2 >= lambda_e phi_j^2   for every anchor edge e=(v,j),  d_e := v_v - J A_j phi_j.
```

## 2. The constants (algebraic; evaluated numerically)

`lambda_e = 1 - c_v*.A_j* = (1 + r*^2 - |c_v*|^2)/2` (using |c_v* - A_j*| = r\*):

| owner site | \|c_v*\|\^2 | lambda_e | crude bound r\* | ratio r\*/lambda_e |
|---|---|---|---|---|
| 0,1,2,3 | 0.6096909 | 0.250177621 | 0.331732034 | 1.33 |
| 4,5,6,7 | 0.7949805 | 0.157532618 | 0.331732034 | 2.11 |
| 8,9 (X sites) | 0.8899547 = s^2 | 0.110046143 = r\*^2 | 0.331732034 | 3.01 |

Values in `evidence/midpoint_rigidity.json`, recomputed in `logs/midpoint_rigidity.txt`; they are
evaluations of the formula above on `lead/root-scout.json` strings, not interval enclosures.
**Per-edge algebraic content:** the exact repair term in (B) is `2 mu_j (q_j^2 - c_t.b_j)`, whose
candidate value is `2 lambda_e e_j` — versus the crude `2 r_t e_j` obtained by dropping the sign of
`x.b`. So the sign-aware form replaces the crude *repair constant* by `2 lambda_e` instead of `2 r_t`
(per-edge factor `r*/lambda_e`). No bound on beta or on cell size is derived from this here (§4).

**Exact X-site identities.** In the construction the two X sites are `c* = (s,0)` with
`s^2 = 1 - r*^2`, and their anchors are `A*_± = (s, ± r*)`; hence `lambda_e = r*^2` exactly. Moreover,
along the *pair rotation* `A_±(a) = w A*_±`, `w := e^{ia}`, with the site at the midpoint
`c(a) = s w`, the following exact identity holds for every t (complex derivation, `u := (1-t) + t w`,
`q = |u|`, `e = 1-q`):
```
c_t = s u,      ahat_± = A*_± u/q,      c_t - ahat_+ = -u (s e + i r*)/q
=>  |c_t - ahat_±|^2 = (|u|^2/q^2)(s^2 e^2 + r*^2) = r*^2 + s^2 e^2 .
```
So *for that one-site rotation* the un-normalized distance is exactly `r* q` and the normalization
increment in squared length is exactly `s^2 e^2 = O(e^2) = O(beta^4)`: the first-order repair cancels
exactly there. This is a statement about that direction only (§4); it is not evidence that the
direction extends to feasible covers, and it gives no bound on beta. `logs/verify_claims.txt` records
only a numerical re-evaluation of this identity.

## 3. Numeric evidence: (SUF1) fails on the linearized space

`logs/midpoint_rigidity.txt` (`py/midpoint_rigidity.py`), `logs/verify_claims.txt`
(`py/verify_claims.py`). All numbers below are float computations.

* Jacobian of the 62 active length constraints (70 coordinates = 28 site + 32 witness + 10 anchor),
  with the gauge row: 63 x 70, numerically rank 62 (singular-value gap: ~1e-16 vs 0.0402), giving a
  numerically 8-dimensional flex space. **Exact dimensional context** (no rank computation): the
  kernel of a 63 x 70 real matrix has dimension >= 7; intersecting with the two conditions `d_e = 0`
  leaves dimension >= 5, and with `phi_j = 0` also >= 4.
* For each of the 20 anchor edges a vector was constructed on the numeric null space with `d_e = 0`
  (residual <= 1e-15), `phi_j = 1.0000` and `|J v| <= 6e-15`; all 20 lines are in
  `logs/verify_claims.txt`.

**Scope (as reviewed):** this refutes (SUF1) on the *linearized* feasible space, and only for the
numerically determined rank. It does **not** refute a uniform statement over actual covers: a tangent
direction need not integrate to a feasible endpoint family (§4). An exact version of the statement
would need exact (or rational) rank arithmetic for the 63 x 70 system plus the three extra linear
functionals, which is not available at these transcendental entries.

## 4. What is *not* established (gap; earlier claims withdrawn)

Withdrawn from the previous revision of this file:

* **"Amplitude confinement beta <= 3.1e-9."** That computation evaluated the second-order length
  coefficients of the **8 basis directions of the numeric null space along a straight-line path**
  (anchors on the circle, sites/witnesses interpolated linearly). It does not bound an arbitrary
  element of the flex space, the `O(s^3)` remainder is uncontrolled, and a general feasible curve
  carries its own second-order site/witness corrections — not the straight-line path used. Hence no
  bound on beta, and no statement that the failure is "harmless", follows.
* **"At most a factor 1.73 in the anchor cell."** Not proved: §2 is a per-edge algebraic statement
  about the repair constant, and converting it into a cell-size statement requires exactly the beta
  control that is missing.
* **"Zero-stress edges do not block uniform slack."** My LP only exhibits a numerically feasible point
  at solver tolerance; it cannot prove forced-zero structure or ranks, and the structural facts it
  reproduced are inherited (§5), not re-established here.
* **"X identity confirmed exact (residual 3.9e-62)."** Replaced by the symbolic derivation in §2.

Kept as *mechanism, not proof*: the two X sites are where the inherited zero-stress cascade operates
(`lead/STRESS-SUPPORT-ANALYTIC.md`: purely vertical anchor forces plus inward witness directions force
those face weights to zero) and where `lambda_e = r*^2` exactly (§2) — an observation tying the two
structures, not a theorem.

## 5. Numeric cross-check of the inherited stress structure (not a proof)

`logs/farkas_check.txt` (`py/farkas_check.py`). **Inherited analytically** from
`lead/STRESS-SUPPORT-ANALYTIC.md` and `lead/STRESS-OBSTRUCTION.md`: the stress support is 44 edges,
the 4 X-adjacent plus the 2 central faces carry zero weight, and the incidence system has one
dependency. My LP run is a *numeric consistency check* of that inherited picture: a nonnegative
combination with support 44 (all 20 anchor edges included) was found feasible by HiGHS, and
`min over |w|_inf<=1 of max_e grad_e.w` returned 0.0 at solver tolerance; it reproduces the six faces
(0,8,10),(1,9,11),(2,8,10),(3,9,11),(10,11,12),(10,11,13) as the numerically forced-zero set.
No exact rank, no exact Farkas statement and no exact forced-zero set is claimed from these runs;
exactness is inherited from the lead's analytic files, not established here.

## 6. Next minimal proof obligations (in order)

1. **(SUF) on the actual feasible set.** Decide §1(C) for every edge and every t (equivalently (SUF1)
   wherever `r'(0) = 0`) with the quantifier over *actual* covers at r <= U, not over tangent
   directions. This is the only route converting the analytic §1 into a localization gain.
2. **Exactness of the linearized obstruction.** Replace the float rank by exact rank arithmetic for the
   63 x 70 active system plus the three functionals `d_e = 0`, `phi_j = 1`, or give an explicit exact
   construction of the following direction; currently numeric (§3).
3. **Integration.** For each anchor edge, decide whether a tangent direction with `d_e = 0` and
   `phi_j != 0` integrates to a family of feasible endpoint configurations (this is what would make
   the failure bite); if it does, a *global* second-order bound along the whole flex space (with the
   `O(s^3)` remainder controlled and with the true feasible curves, not the straight-line path) is
   needed before any beta statement. If it does not integrate, the uniform question must be posed on
   the reduced network (44-edge support / its director form), not on the tangent space.
4. **Only then** the quantitative consequence: turn the per-edge repair constant `2 lambda_e` versus
   `2 r_t` (§2) into a cell-size statement.

No global claim, and no claim about the covering optimum or about the existing 2e-6 local access,
follows from this file.

## 7. Evidence, repro (all numeric unless stated)

```
py -3 -B .../midpoint-rigidity/py/midpoint_rigidity.py   # rank/flex (float SVD), lambda_e values
py -3 -B .../midpoint-rigidity/py/amplitude_confine.py   # second-order numbers, straight-line path only
py -3 -B .../midpoint-rigidity/py/verify_claims.py       # constructed following directions; X identity check
py -3 -B .../midpoint-rigidity/py/farkas_check.py        # HiGHS LP consistency check
```
Outputs: `logs/{midpoint_rigidity,amplitude_confine,verify_claims,farkas_check}.txt`,
`evidence/{midpoint_rigidity,amplitude_confine,farkas_check}.json`.
Geometry: `lead/root-scout.json` strings with the chain `a=(s+z)/2`, `b=r+sqrt(r^2-((s-z)/2)^2)`,
`d=1-sqrt(r^2-c^2)`, `t=r+sqrt(r^2-z^2)`; the construction reproduces 14 tight + 2 slack in-D
empty-circle vertices and 62 active incidences, as checked in `members/stress-cc2/logs/interface_run.txt`.
Index labelling is mine; the lead's q10/879 labels differ by the documented coordinate permutation, and
the statements about the X sites and the six zero-weight faces are geometric (label-invariant).

