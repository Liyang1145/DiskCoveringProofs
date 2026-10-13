# Audit of the local minimax weighted-H theorem + how to certify locally from the isolating box

Scope: `research-2026/team-current/r20-rigidity/` only. Audits `R20-MINIMAX-SUFFICIENT-THEOREM.md`
against `r20_second_order_certificate.json`, `r20_error_bound.json`, `r20_target_objects.json`
(all previously saved; no new precision run). No claim registered.

## 1. The theorem is correct; three statements need repair

**1a. Slice/orbit (Lemma 3) — keep, but only `dist <= |s|` is needed.** The chart
`(theta,s) -> R_theta(x*+s)` has differential `[r, I]` at `(0,0)`, invertible because `r` is the
orbit tangent; by the inverse function theorem it is a local diffeomorphism, and `gamma(x) =
gamma(x*+s)` by orbit invariance. The text adds `dist(x,O) = ||s||`. That equality can fail in a
harmless way (if some other orbit point is closer, `dist < ||s||`). The proof needs only the
one-line inequality `dist(x,O) <= ||s||` (true because `x*+s ∈ O+s`), so the conclusion
`gamma(x)-gamma* >= c' ||s||^2 >= c' dist(x,O)^2` survives unchanged. Replacing the equality by the
inequality removes an unnecessary obligation (and any doubt about a global orbit-distance
argument).

**1b. Constant/radius formula — one condition is missing (substantive).** Case 2 of the proof uses
`L||w||^2 <= L A^2 ||d||^4`, so besides `||d|| <= min(rho_0, 1/(A sqrt2), (muA/2-M)/C_3,
c/(16(LA+C_3)))` one also needs the fourth-order condition
```
L A^2 ||d||^2 <= c/16      i.e.  ||d|| <= sqrt(c/(16 L A^2)) = (1/(4A)) sqrt(c/L) .
```
As stated, the radius formula can be too large in general. At `X60` the extra term is non-binding:
`sqrt(c/(16LA^2)) = 1.188e-5` vs the binding `c/(16(LA+C_3)) = 9.01e-7` (using `c = 0.1649026928`,
`L = 1.792`, `A = 4M/mu = 6382.49`, `C_3 ≈ 1.678`), so the published radius `9.0e-7` is right — but the
general theorem must carry the extra `min`.
**1c. Active set.** §1 assumes "all `f_i` active at `x*`". At `X60` only 18 of the 20 branches are
active (`u_min = 9.8947e-3` on those 18; the two others sit at `gamma* - 1.1527e-3`). The theorem
applies verbatim to the *active* index set: (H1) must be `u > 0` on the active set, `gamma* = f_i(x*)`
there, and `K = ∩_{i active} ker grad f_i`. Inactive branches never enter (a) or (b), so no
active-set stability radius is needed for the first-order part. Consequence: obligation 4 of
§4 (`rho_1`) is not required for the local statement; it would only be needed if the local minimum
were claimed for the true `R_D` on a neighbourhood with a *fixed* model. Note the correct version of
"stability" that *is* implicit: for `x` near `x*`, `R_D(x) >= gamma(x)` always holds (gamma is a max
over branch values, each a value of the distance function on `D`), so the model may only *understate*
`R_D` — the right direction.

**1d. Verified arithmetic.** `(H3‡)` reading `0.1649026928227386` matches
`Hbar_on_flat_eigs[0]`; `mu = 0.0014325394910901321`, `M = 2.2857905`, `L = 1.792`, `A = 6382.6`,
`min(muA/2, c/8) = 0.0206128`, radius term `c/(16(LA+C_3)) = 9.01e-7`. The counterexample in §0
(`f_1 = x+y^2`, `f_2 = -x-2y^2`) really does refute the `max_i`-form only: there `M_u = diag(0,-1)`
fails (H3‡) as well, so the weighted hypothesis is not merely weakened but correctly excluded.

## 2. `C_3` is not the only gap — full inventory

For the *local minimality of the true covering radius at `X60`* one needs all of:

| # | obligation | status |
|---|---|---|
| 1 | (H1) exact: `sum u_i grad f_i(X60) = 0` with `u > 0` | numeric (`3.5e-17`); needs exact/interval |
| 2 | (H3‡) exact: interval Hessians + `c > 0` on `K ⊖ Rr` | finite differences now (`<= 4e-31` spot Richardson) |
| 3 | `Lambda = {u}`: `rank J18^T = 17` reading | numeric singular values (`1.7e-51` FD floor) |
| 4 | `C_3` bound on a ball of radius `rho_0` | diagnostic only (`~1.68` from 200 directions) |
| 5 | `rho_0` itself (spatial, not just the constant) | not established |
| 6 | **model completeness at the base point**: `gamma(X60) = R_D(X60)` | **open** — this is the same "critical set is complete" obligation as `R20-TC-ROOT-AUDIT.md` (W10) but for the `X60` object: the 20 branch values must exhaust the local maxima of the distance function (all Voronoi vertices + boundary ties) |
| 7 | `X60` vs an exact object | the theorem is applied *at* the rational `X60`; that is legitimate, but then #6 must be established for that same point, and `gamma(X60)` is not an algebraic optimum |

Item 6 is the one that is easy to overlook and is not a remainder/interval issue: without
`gamma(X60) = R_D(X60)` the chain gives `R_D(x) >= gamma(x) >= gamma(X60) + c dist^2` but
`gamma(X60)` may be strictly below `R_D(X60)`. Structure of the conclusion: one only needs `R_D(x) >=
gamma(x)` (automatic) plus `R_D(x*) = gamma(x*)` **at the base point**; no neighbourhood stability of
the active set or of the Delaunay structure is required. So the local half of the program reduces to
(i) the three exactness items, (ii) one remainder/radius pair, and (iii) one base-point completeness
of the same type as W10.

## 3. Local certificate from the isolating box, without repeated 56D root solves

Under the accepted definition "**the exact root = the equation system + the rational isolating
box**" (lead `REPAIRED-TC-ROOT-INTERFACE.md`), a local certificate must be a *range* statement over
the box, not a point evaluation at a re-solved root. Concrete design (all instruments already exist
in this workspace):

1. **One** root enclosure: the repaired 12D symmetric Krawczyk box (`lead/repaired_tc_krawczyk.json`,
   radius `1e-9`, contraction `4.37e-3`). Never re-solve the system at perturbed points.
2. **Symmetry lift instead of a second solve**: the 18 physical ties are the 5 chart equations plus
   exact reflection (palindromic parameters, `theta_{8-k} = -theta_k`); the remaining 13 branch
   equations are images, not new constraints. This is what makes the 56D sharp-tied KKT system
   unnecessary for the certificate; the 56D system remains only an oracle.
3. **Multipliers from linear algebra, not from a solve**: with the chart rank 5 (W11) the boundary
   multipliers are `nu = -(DB DB^T)^{-1} DB w` (lead `TC-TO-PHYSICAL-KKT-LIFT.md` §"Exact multiplier
   lift"), and the interior multipliers are read off the 5 res5 representatives via the positive
   conversion factors (W12). Evaluate `nu`, `mu` and the conversion factors as intervals over the
   *same* box: that turns "re-solve and hope the signs are stable" into "interval enclosure with a
   certified sign".
4. **Second order over the box**: weighted Hessian `M_lambda = sum lambda_i grad^2 f_i` with the
   interval multiplier enclosure; certify `v^T M v >= c |v|^2` on the relevant subspace by an
   interval `LDL^T` (or a Cholesky attempt) on the restricted matrix, plus a certified lower bound on
   the complementary block (`sigma_min` of the interval Gram matrix) so that the subspace is
   certified to contain the kernel over the box. This replaces finite differences by interval AD —
   the same nested-AD construction as `repair_tc_krawczyk.py`, so no new backend.
5. **Remainder**: bound `(1/6) sup ||D^3 f_i||` on a ball of radius `rho_0` by interval AD over the
   box (again no root solving).
6. **Base-point completeness** (gap #6 above, or W10 for the TC root): a one-off geometric assembly
   at the base point, exactly the instrument of `r20_tc_box_audit.py`/`r20_tc_delaunay_completeness.py`
   (strict empty circles + triangulation certificate + no empty cocircular quadruple), applied to the
   `X60` configuration instead of the TC root.

Residual risk/cost: interval AD of the branch functions is the main new implementation (they are
smooth on the branch, no max/min needed); the interval eigenvalue test needs a strict pivot margin
(else only a weaker statement is certified); and the whole design inherits `mpmath.iv` as the single
backend.

## 4. Repro

```
py -3 -B -X utf8 r20_second_order_certificate.py   # readings cited in §1 (existing artifact)
py -3 -B -X utf8 r20_tc_chart_rank.py              # chart rank + conversion factors (W11/W12)
```
