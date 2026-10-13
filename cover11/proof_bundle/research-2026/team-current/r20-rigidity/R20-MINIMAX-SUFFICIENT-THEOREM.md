# Generic minimax second-order sufficient theorem (weighted form, split proof)

Scope: `research-2026/team-current/r20-rigidity/` only. No claim registered (lead owns
registration). All numbers cited are readings from the already-saved artifacts
(`r20_second_order_certificate.json`, `r20_error_bound.json`, `r20_hess_cache.npz`,
`r20_calibration.json`); no new precision computation was run.

Supersedes the previous version of this note. The correction is substantive:

* the correct second-order hypothesis is **weighted** Hessian positivity
  `v^T M_lambda v >= c ||v||^2` for `v` in the critical cone `K`, with `lambda` a stationary
  multiplier (`sum lambda_i grad f_i(x*) = 0`), **not** `max_i v^T grad^2 f_i v > 0` on `K`;
* positivity of `M_lambda` on the *whole* rotation-orthogonal complement is **not** required (and
  is false at `X60`); the weighted `K`-restricted object is positive there (`lambda_min = 0.1649`);
* the rotation quotient is handled with a **local slice**, not by freezing the straight line
  `R r` (the orbit is a curve; only its tangent is a line);
* the quadratic-dominance radius is **linear** in the constant: `rho = nu/(2 C_3)`.

---

## 0. What exactly is false, and what is not

* **False (counterexample, `C_3 = 0`):** "`max_i v^T grad^2 f_i(x*) v > 0` for all `v in K \ {0}`
  `=>` local minimality". Take `f_1 = x + y^2`, `f_2 = -x - 2 y^2` at `x* = 0`: both active,
  `0 = (1/2) grad f_1 + (1/2) grad f_2 in ri conv`, `K = {v_x = 0}`,
  `max_i v^T grad^2 f_i v = 2 v_y^2 > 0` on `K \ {0}`; yet along `(x,y) = (-1.5 t^2, t)`,
  `f_1 = f_2 = -0.5 t^2 < 0 = gamma(0)`. The *max* of the Hessian forms ignores the curved path's
  transverse linear term at order `t^2`.
* **Not false (and this is the right hypothesis):** the *weighted* form. In the same example the
  multiplier set is `Lambda = {u = (1/2,1/2)}` and `M_u = diag(0,-1)`, so
  `v^T M_u v = -v_y^2 < 0` on `K`: the weighted hypothesis fails there too, consistently with the
  failure of local minimality. **The counterexample refutes only the `max_i` version.**
* **Not required:** positivity of `M_lambda` on `r^perp` (all directions). At `X60` the raw reading
  `lambda_min(P M_u P) = -3.28e-2 < 0` is therefore *not* an obstruction; see §3.

## 1. Rigorous first-order consequences of the interior condition

`gamma = max_{i<=m} f_i`, `f_i in C^3`, `gamma* = gamma(x*)`, all `f_i` active at `x*`.

* **(H1)** `exists u_i > 0, sum u_i = 1, sum_i u_i grad f_i(x*) = 0`.
* `K := {v : max_i grad f_i(x*).v = 0}`, `Q_2 := 1/2 max_i ||grad^2 f_i(x*)||`,
  `G := max_i ||grad f_i(x*)||`.

**Lemma 1.** Under (H1), `K = {v : grad f_i(x*).v = 0 for all i}`, and `max_i grad f_i.v >= 0` for
all `v`, with equality iff `v in K`. *Proof:* if the max is `<= 0` then all `grad f_i.v <= 0`, and
`0 = sum u_i (grad f_i.v)` with positive weights forces all terms `0`. ∎

**Lemma 2.** Under (H1), `mu := inf{max_i grad f_i(x*).v : v perpendicular K, ||v|| = 1} > 0`
(attained). *Proof:* otherwise a unit `v perpendicular K` with max `= 0`, hence `v in K`, hence
`v = 0`. ∎

**Remark.** (H1) is verified numerically at `X60` (`u_min = 0.0098947`,
`||sum u_i grad f_i||_inf = 3.5e-17`) — numeric, not exact; an `eps`-version of Lemmas 1-2 is
available if only `||sum u_i grad f_i|| <= eps` is known.

## 2. The corrected theorem (weighted hypothesis + split proof)

* **(H2) Symmetry orbit.** `x*` lies on a smooth curve `O` (for n11: the rotation orbit) with
  `gamma ≡ gamma*` on `O`, tangent `r != 0` at `x*` (`grad f_i(x*).r = 0` for all `i`).
* **(H3‡) Weighted Hessian positivity on the critical cone, modulo the orbit.** There exist
  `lambda in Lambda := {lambda in Delta : sum_i lambda_i grad f_i(x*) = 0}` and `c > 0` with
  ```
  v^T M_lambda v >= c ||v||^2      for all v in K with v perpendicular r ,
  M_lambda := sum_i lambda_i grad^2 f_i(x*) .
  ```
* **(H4) Remainder.** `|f_i(x*+d) - f_i(x*) - grad f_i(x*).d - 1/2 d^T grad^2 f_i(x*) d| <= C_3 ||d||^3`
  for `||d|| <= rho_0`.

**Lemma 3 (slice).** In a neighbourhood of `x*` every point `x` has a unique representation
`x = R_theta(x* + s)` with `s perpendicular r` and small `|theta|` (the orbit is transversal to the
slice `x* + r^perp`), and `dist(x, O) = ||s||`. Since `gamma` is invariant along `O`,
`gamma(x) = gamma(x* + s)`. (Equivalently, the invariance can be imposed as a constraint with a
Lagrange multiplier; the curvature of `O` enters only through the chart, not through the final
inequality, which is expressed in `dist(x,O)`.)

**Theorem.** Assume (H1), (H2), (H3‡), (H4). Put `M := Q_2 = 1/2 max_i ||grad^2 f_i(x*)||`,
`L := 2 ||M_lambda||` (so that both cross terms are dominated: `2|v^T M_lambda w| <= L|v||w|` and
`|w^T M_lambda w| <= (L/2)|w|^2`), and choose any `A > 2M/mu` (e.g. `A = 4M/mu`). Then for every `x` with `s` as in Lemma 3 and
`||s|| <= rho`,
```
gamma(x) - gamma*  >=  min( mu A / 2 , c / 8 ) * dist(x,O)^2 ,
where  rho = min( rho_0 , 1/(A sqrt2) , (mu A/2 - M)/C_3 , c/(16 (L A + C_3)) ) .
```
All constants are explicit; `mu, M, L` are computable from the data, `c` comes from (H3‡), and only
`C_3` remains an obligation (§4).

*Proof.* Write `d := s = v + w` with `v in K`, `w perpendicular K`. Two bounds.

*(a) First-order (uses (H1), (H4)).* Since `grad f_i(x*) perpendicular K` (Lemma 1),
`grad f_i.d = grad f_i.w`. Taking the index maximising `grad f_i.w` and bounding the quadratic term
by `M`,
```
gamma(x*+d) - gamma* >= mu |w| - M ||d||^2 - C_3 ||d||^3 .                              (a)
```
*(b) Weighted (uses (H3‡), (H4)).* For every `lambda in Delta`, `gamma(x) >= sum_i lambda_i f_i(x)`;
with `lambda in Lambda` the linear term cancels and (H4) gives
```
gamma(x*+d) - gamma* >= 1/2 d^T M_lambda d - C_3 ||d||^3
                     >= (c/2)||v||^2 - L||v|| ||w|| - L||w||^2 - C_3 ||d||^3 ,              (b)
```
using `d^T M_lambda d = v^T M_lambda v + 2 v^T M_lambda w + w^T M_lambda w`, the hypothesis on the
`v`-part, and the definition of `L`.

*Case 1: `|w| >= A ||d||^2`.* From (a),
`gamma - gamma* >= (mu A - M)||d||^2 - C_3||d||^3 >= (mu A/2)||d||^2` whenever
`||d|| <= (mu A/2 - M)/C_3`; the numerator is positive because `A > 2M/mu`.

*Case 2: `|w| <= A ||d||^2`.* Then `||v||^2 = ||d||^2 - ||w||^2 >= ||d||^2 (1 - A^2||d||^2) >=
||d||^2/2` for `||d|| <= 1/(A sqrt2)`, and `L||v||||w|| <= L A ||d||^3`,
`L||w||^2 <= L A^2 ||d||^4`. Inserting in (b):
`gamma - gamma* >= (c/4)||d||^2 - (L A + C_3)||d||^3 - L A^2 ||d||^4 >= (c/8)||d||^2` for
`||d|| <= c/(16 (L A + C_3))` and `L A^2 ||d||^2 <= c/16`.

In both cases `gamma - gamma* >= min(mu A/2, c/8)·||d||^2`, and `||d|| = dist(x,O)` by Lemma 3. ∎

**Corollary (simplest unsplit form).** If instead of (H3‡) one has the stronger
`P M_lambda P >= 2 nu P` on the whole rotation-orthogonal complement, then
`gamma(x*+d) - gamma* >= nu||d||^2 - C_3||d||^3 >= (nu/2)||d||^2` for `||d|| <= nu/(2C_3)`
(linear radius, as corrected).

**Relation to the earlier draft.** The hypothesis `max_i v^T grad^2 f_i v > 0` on `K` (§0) is
neither sufficient nor the right object; (H3‡) implies it with `c_2 = c` (max `>=` average), and
(H3‡) is what the proof uses.

## 3. Instantiation at `X60` (raw readings, labels corrected)

| item | raw reading | label |
|---|---|---|
| 18 active values | spread `7.78e-61` on a `1e-60` grid | **grid-scale stationarity only**, not an exact stationary root |
| `J18` smallest singular value | `1.7e-51` (FD floor), `sigma_17 = 0.0584199083` | numeric; **no rank claim** |
| (H1) | `u > 0`, `u_min = 0.0098947`, `\|\|sum u_i grad f_i\|\| = 3.5e-17` | numeric verification |
| multiplier face `Lambda` | 1-dimensional `ker J18^T`, so `Lambda = {u}` *under the numeric rank-17 reading* | numeric; needs exact/interval confirmation |
| **(H3‡)** `Q^T M_u Q` on `K ⊖ R r` (4-dim) | eigenvalues `0.1649026928, 0.2216701155, 0.2549598729, 0.2813311259` | **positive: `c = 0.1649026928`** (numeric, from the cached Hessians) |
| `M_u` on the whole `r^perp` | `lambda_min = -3.28e-2` | **not the object the theorem uses** (kept as a raw reading) |
| max-based value on `K ⊖ R r` | `0.25550766818243037826` | numeric; `>=` the weighted value, as it must be |
| `mu` (transverse rate) | `0.0014325394910901321` (complete vertex enumeration) | numeric |
| `M = Q_2`, `L = 2\|\|M_u\|\|` | `M = 2.2857905` (`max_i \|\|H_i\|\| = 4.571581`); `L = 1.792` (`\|\|M_u\|\| = 0.896`) | numeric |
| `G` | `0.728179` | numeric |
| local optimality conclusion | — | **conditional on `C_3` and exactness of (H1)/(H3‡)**: with `c = 0.1649`, `mu = 1.4325e-3`, `M = 2.2858`, `L = 1.792`, `A = 4M/mu = 6382` (so `LA = 1.14e4`), the theorem gives `gamma(x) - gamma* >= 0.0206 · dist(x,O)^2` for `dist(x,O) <= min(9.0e-7, (muA/2 - M)/C_3)` — the positive radius currently depends on the missing remainder bound |
| gaps | `R_stru - 3/8 = 4.98385e-3`; `R_stru - 0.3798939830 = 8.99e-5` (certification gap); proved `0.3709` gives `3/8 - 0.3709 = 4.1e-3` | the headline gap to the target **3/8** is `4.98385e-3` |

## 4. Obligations (in order)

1. **`C_3` on a ball** — one of three missing rigorous inputs, not the only one (the theorem is conditional on (H1) and (H3‡) being *exact*, and on the interval Hessians; see items 2-3): bound `(1/6) sup_B ||D^3 f_i||`
   for the 18 active functions on `B(X60, rho_0)`. The diagnostic estimate `~1.68` (200 random
   directions, `t = 1e-3`) is not a bound. With `C_3 <= L A` the radius at `X60` is `~9e-7`; otherwise the radius is `c/(16(LA + C_3))`.
2. **Exactness of (H1) and of `Lambda = {u}`**: interval/symbolic verification of
   `sum u_i grad f_i(x*) = 0` and of the rank-17 reading; otherwise the `eps`-version applies and the
   radius acquires `O(eps)` terms.
3. **Interval Hessians** to certify `c = 0.1649` (currently finite-difference, Richardson `<= 4e-31`
   on spot entries).
4. **Active-set stability radius** `rho_1 <= 1.1526819e-3/(G_act + G_inact)`; `G_inact` for the two
   critical points at the next level is not yet bounded.
5. **Exact object**: everything above concerns the saved `1e-60` rational `X60`, not an exact
   algebraic optimum.

## 5. Interface

This is the local half: *given* a certified `C_3` and exact (H1)/(H3‡), no configuration in a ball
of radius `~9e-7` around the orbit of `X60` has a smaller covering radius than `X60`, with
quadratic growth. The far region still needs moving witnesses
(`lead/R21-NO-FIXED-FINITE-SHARP-WITNESS.md`), and the gap to the target `3/8` is `4.98385e-3`.
