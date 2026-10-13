# Independent audit of `lead/TC-BOUNDARY-CHART-RANK.md` (+ box branch signs, central `F_out`)

Scope: `research-2026/team-current/r20-rigidity/` only. Read-only inputs: `lead/TC-BOUNDARY-CHART-RANK.md`,
`lead/TC-TO-PHYSICAL-KKT-LIFT.md`, `lead/repaired_tc_krawczyk.json`. Instrument: `r20_tc_chart_rank.py`
-> `r20_tc_chart_rank.json` (+ `.log`), mpmath only, corrected box `iv(c)+iv([-rad,rad])`, decisions on
exact interval endpoints. No claim registered (lead owns registration). No generic rank search: the
rank statements are re-derived analytically and only their pivots (quantities) are box-checked.

Verdict: the lead's chart proof, the gap→boundary-radius proportionality and the interior-residual
conversion are all **correct**. Three refinements below (R1–R3) close two arguments that are stated
too briefly and fix one notation collision. All box readings are positive with the margins listed.

---

## 1. L1 — radial coordinate facts: correct, box-verified

Claim: with `a(rho,R) = acos((rho^2+1-R^2)/(2 rho))`, near the root `0<rho<sqrt(1-R^2)`, `0<a<pi/2`,
and `a_rho = (1-R^2-rho^2)/(2 rho^2 sin a) > 0`, `a_R = R/(rho sin a) > 0`.

* Structure: `rho^2 - 2 rho cos a + 1 - R^2 = 0` (the tie condition), so
  `1 - R^2 - rho^2 = 2 rho (cos a - rho)` **exactly** on the inward branch, and `rho < cos a` because
  `rho = cos a - sqrt(R^2 - sin^2 a)` with `R^2 > sin^2 a`. This is the clean way to state the
  inequality (`r20_tc_chart_rank.py [L1]` reproduces the identity as an interval enclosure of `0`,
  slack `3.7e-7`, pure dependency slack).
* Box readings (`[L1]`): `min (1-R^2-rho_k^2) >= 5.90e-2`; `min (pi/2 - a_k) >= 1.1826`;
  `min a_k >= 0.2808`; `min a_rho >= 9.786e-2`; `min a_R >= 1.1247`; `min (R^2 - sin^2 a_k) >= 1.093e-3`.
  So every radial inequality the chart needs is strict with margin >= `1.1e-3` on the whole box.

## 2. L2/L3 — `D_rho g = -(I+S) diag(a_rho)`, rank 5: correct, with a needed refinement (R1)

* `D_rho g = -(I+S) diag(a_rho)` is right: `g_i = delta_i - a_i - a_{i+1}` depends on `rho_i` and
  `rho_{i+1}`, so `(D_rho g)_{ij} = -(a_rho(rho_i) delta_ij + a_rho(rho_{i+1}) delta_{i+1,j})`.
* `9` odd ⇒ `I+S` invertible: kernel vectors satisfy `v_{i+1} = -v_i`, hence `v_0 = (-1)^9 v_0 = -v_0`,
  so `v = 0`; equivalently `det(I+S) = 2`. Correct.
* **R1 (refinement, not an error).** "It commutes with the reflection after the appropriate
  edge-index permutation, so it restricts to an isomorphism on the reflection-invariant 5D" is the
  step that carries the rank conclusion, and invertibility of `I+S` on `R^9` does **not** by itself
  imply invertibility of the induced 5x5 block (a general invertible operator can have a singular
  invariant restriction). The honest bookkeeping: the reflection acts on the radii by
  `sigma(k) = 8-k` and on the gaps by `tau(i) = 7-i = sigma(i+1)`; with those, `(I+S)diag(a_rho)` maps
  `sigma`-invariant radial variations into `tau`-invariant gap variations (this is exactly the
  equivariance `g_{tau(i)}(reflection x) = g_i(x)`, and it fails if one uses `k -> -k` instead of
  `k -> 8-k`). In the orbit bases — radial orbits `{0,8},{1,7},{2,6},{3,5},{4}` and gap orbits
  `{0,7},{1,6},{2,5},{3,4},{8}`, i.e. the five representatives `g_0,g_1,g_2,g_3,g_8` — the 5x5 matrix is
  ```
        [d0 d1  0  0  0]
        [0  d1 d2  0  0]
        [0  0  d2 d3  0]        d_k = a_rho(rho_k) > 0,  rho_8 = rho_0, ...
        [0  0  0  d3 d4]
        [2d0 0  0  0  0]
  ```
  (the last row is `g_8 = d_8 v_8 + d_9 v_9 = 2 d_0 v_0`), with determinant `2 d_0 d_1 d_2 d_3 d_4 > 0`.
  Box reading: this pivot is `>= 1.477e-2 > 0`. Hence rank 5 with an analytic pivot, and by the
  positivity of the row factors (L5) the five *boundary-radius* representatives have the same rank.
* Independent audit cross-check (different minor, deliberately): the four symmetric-rotation
  directions plus the `R`-direction give the pivot `2(beta_0+beta_1+beta_2+beta_3) + beta_4` with
  `beta_k = a_R(rho_k,R) > 0`, reading `>= 12.936 > 0`. Two structurally different minors, both
  nonvanishing, so the rank-5 conclusion does not rest on one computation.
* `D_Phi` rank 7 (immersion): against the coordinate functions `(rho_0..rho_3, x_H0, x_H1, R)` the
  Jacobian is block triangular with diagonal `d rho_k/d a_k = sin a_k rho_k / sqrt(R^2 - sin^2 a_k)`,
  reading `>= 13.249 > 0`; the `R`-column and the hub rows are identity/zero blocks. So `Phi` is an
  immersion of rank 7 into the 12D symmetric space.

## 3. L4 — the chart property: correct

On `{g = 0}`: `delta_i = a_i + a_{i+1}`, summing gives `sum_i a_i = pi`; reflection forces the
palindrome `(a0,a1,a2,a3,a4,a3,a2,a1,a0)` hence `a4 = pi - 2 sum_{i<=3} a_i`; with `theta_4 = 0` the
gaps recover all `theta_i` by recursion, and `rho_k` by the inward root. The claimed inverse
`(a_0..a_3, y_0, y_1, R) -> configuration` is smooth with all required nonvanishing derivatives
(`a_rho > 0`, `R^2 - sin^2 a > 0`, strict cyclic order, stable branch `C_4` on the positive axis).
Combined with `rank D_Phi = 7 = dim M`, this gives the local 7D chart, not merely a same-dimension
parametrisation. Audit note: the chart identity `B(Phi(z)) = 0` is *identically* true (the arcs tile
by construction), so no pullback Jacobian can prove the rank — the rank must come from the physical
variables, which is what both minors above do.

## 4. L5 — gap vs boundary-radius: the two routes agree, box branch sign positive

* Re-derived independently: the two functions have the same zero set near the root and both have
  nonvanishing `R`-derivative there (`dg_i/dR = -(a_{i,R}+a_{i+1,R}) < 0`, `d(t_i-R)/dR = -1`), so
  `g_i = mu_i (t_i - R)` and hence `dg_i|_{g=0} = mu_i d(t_i - R)` with `mu_i = a_{i,R}+a_{i+1,R} > 0`.
* Second, independent route: the boundary covering excess `v_i = t_i - R` can be differentiated
  explicitly at the touching configuration: the equidistance point splits the gap with
  `dw_i/dg = D'_{i+1}/(D'_i + D'_{i+1})`, `D'_k = rho_k sin a_k / R`, giving
  `dv_i/dg_i = rho_i sin a_i rho_{i+1} sin a_{i+1} / (R (rho_i sin a_i + rho_{i+1} sin a_{i+1}))`.
  Reciprocity check `(dv/dg) * mu = 1`: readings `|...-1| <= 3.2e-6` over the five representatives
  (interval slack) — the two derivations agree.
* Box signs: `dv/dg in [0.2900, 0.4332] > 0`, `mu_i in [2.309, 3.448] > 0` for all five orbits.
  Hence gap-constraint and physical boundary-radius multipliers have the same sign, as claimed.
* "No branch exchange": for every adjacent pair the two unit-circle points on the radical line were
  computed; the tie is within `3.9e-7` of `R` (box slack) and the **other** point is uncovered by the
  pair by `>= 1.314` — the far branch is far away, so no branch exchange.

## 5. L6 — interior residual conversion: identity and factor positivity confirmed

* The identity `4 y^2 (Rc^2 - R^2) = F_in F_out` is exact (re-derived from scratch). Differential
  consequence: at `F_in = 0`, `Rc = R`, `4y^2 · 2R dRc = F_out dF_in` and `dF_in = 2R df`
  (`F_in = |h-pin|^2 - R^2`, `f = |h-pin| - R`), hence `d(Rc - R) = [F_out/(4 y^2)] df` — the lead's
  constants are right, including the vanishing of the `d(4y^2)` and `F_in dF_out` terms.
* Numerical calibration of the exact identity over 120 random points of the box: central residual
  `7.2e-62`, fan residual `3.9e-61` (60-digit arithmetic) — no algebraic slip.
* **Central waist**: chord = the hub segment, third vertex `C_6`, `W_+ = (m,+sqrt(R^2-d^2))` with the
  lead's `d` = the *chord* length `|y1-y0|` (R2: let `h` be the height; `W_+ = (m,+h)`,
  `h = sqrt(R^2 - (chord/2)^2)`; the doc writes `d/2`, so no error, but the same symbol `d` is used
  for the chord length while the audit scripts use it for the half-chord).
  Readings: `F_out = |C_6 - W_-|^2 - R^2 >= 0.877423 > 0` (interval), and also
  `>= (c_y + h)^2 - R^2 >= 0.876329 > 0` (analytic lower bound, `|C_6 - W_-| >= c_y + h`),
  `c_y >= 0.694424 > 0`, `branch factor (s+h)/(2 c_y) in [0.454882, 0.454883] > 0`,
  reciprocity `2 c_y (s+h) - F_out` encloses `0` (exact algebra).
* **Fan**: `F_out = |H - B_k|^2 - R^2 > 0` both by interval (all four active orbits: `>= 0.4248`) and
  analytically by the triangle inequality: `|H| <= 0.272978` and `|B_k| = 1` exactly give
  `|H - B_k| >= 0.727022 > R = 0.379984` (margin `0.347`).
* Conclusion for the lift: with `F_out > 0` and `y != 0` (`y = c_y > 0` central, `y != 0` fan), the
  conversion factor is strictly positive and the multiplier signs are preserved, as the lead states.

## 6. What this audit does not establish

* Root existence/uniqueness: read-only Krawczyk certificate (12D symmetric system).
* Multiplier signs `mu_i, nu_j >= 0`: not audited here (lead/stress obligation).
* Anything first-order beyond the chart: no local minimality, no second-order statement, and no
  global `n = 11` bound. The chart is a local statement near the repaired symmetric candidate only.
* Interval kernel: `mpmath.iv` at 60 dps, same backend as the rest of this directory; no second
  backend was built (per the lead's instruction that none is needed).

## 7. Repro

```
py -3 -B -X utf8 r20_tc_chart_rank.py     # L1-L7 readings -> r20_tc_chart_rank.json/.log
```
