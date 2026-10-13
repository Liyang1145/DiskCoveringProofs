# root-cc2 / area-safe-audit status

Scope `research-2026/next-cover-global/members/root-cc2/area-safe-audit/` (only). Lead
artifacts read-only. **No claim registered** (lead instruction).

## Verdict

The repaired cover-to-angle interface is **sound**: the retracted `f(alpha)` relation is
nowhere used, the area decomposition is exact, the angle domains are correct and the
supporting-plane step is an exact identity (my independent implementation with a genuine
incidence matrix `B`, legal `t`, random rational `t0,y`: 0 violations). Details and
evidence in `AUDIT.md`, `evidence/geom01_I1_I8.txt`, `evidence/geom03_I6legal_I7.txt`.

## Corrections to my own earlier statements (all withdrawn, per the lead's geometry check)

1. **No tangents.** There are no real tangents from an interior point `c_i` to `S^1`; my
   "two tangent lines" phrasing was false. Correct reason for `alpha_i < pi`: the arc
   endpoints `p,q` are on `S^1` and `c_i` is strictly on the origin's side of the endpoint
   chord, so `p - c_i` and `q - c_i` both have strictly positive projection along the
   outward chord normal — hence the angle between them is `< pi`.
2. **Facet triangle not isosceles.** `|c_i p|` need not equal `|c_i q|`, so
   `beta = pi - 2*(base angle)` is invalid and is not used. Correct reason for
   `beta_e < pi`: the facet lies on the supporting line of the (convex) cell at `pq`, and
   that line does not pass through `c_i`, so the two vectors to the endpoints have strictly
   positive projection along that line's inward normal.
3. **Cap monotonicity is needed.** I wrongly claimed it was unnecessary. The step
   "certificate at `U` covers `rho <= U`" uses `cap(rho) <= cap(U)` (together with
   `rho^2 <= U^2`). It holds because `h(L) = sin L/L` has
   `h'(L) = (L cos L - sin L)/L^2 < 0` — indeed `(sin L - L cos L)' = L sin L > 0` and
   `sin L - L cos L = 0` at `L = 0` — so `h` is strictly decreasing and
   `cap(rho) = pi(1 - h(2 asin rho))` is strictly increasing in `rho`.
4. **Convexity is not established by sampling.** `g(theta) = theta - sin theta` is convex
   because `g'' = sin theta >= 0`; my grid check was only numerical support. (My brief
   claim that `sin L/L` decreases only on `(0,L*)` was an artefact of a bad scan interval
   and is also withdrawn.)

Unchanged and still verified: `norm(c_i)^2 <= 1 - rho^2 <= cos^2(theta_i/2)` (site
strictly inside `S^1`); `area(W_i) = (rho_i rho_i' sin alpha_i)/2 + (theta_i - sin
theta_i)/2`; triangle bound using only `sin alpha_i >= 0`; the cap sum
`pi(1 - sin L/L)`; the site-angle equations; `pi <= cap + (rho^2/2)Sigma sin alpha +
rho^2 Sigma sin beta` as a necessary condition; the supporting-plane chain
(concavity of `sin` + `y^T(Bt - 2pi 1)` + box maximum over `[0,pi]`).

## Not audited

The 441 exact exclusions, the 12-graph probe and the optimiser outputs; the
finite-catalogue / limit-C1171 interface (the lead is writing the compact angle-limit
interface independently); degenerate cases beyond `beta = 0` fan handling.

## Repro

```
cd research-2026/next-cover-global/members/root-cc2/area-safe-audit
py -3 -B py/geom01_interface.py
py -3 -B py/geom03_i6legal.py
```
