# root-cc2 chord-envelope-audit: audit of lead/BOUNDARY-CHORD-ENVELOPE.md

Scope `members/root-cc2/chord-envelope-audit/` (only). Lead artifacts read-only.
**No claim registered** (lead instruction). Analytic interface only; the 12-graph probe
and the Fraction replay are the lead's and are not audited here.

## Verdict

**The envelope and its use are correct, and the proof needs none of the assumptions the
lead forbade.** Specifically it does not assume equal endpoint radii, does not assume the
facet/site triangle is isosceles, and does not use tangents from an interior point. The
one step that is genuinely delicate is the exact constant `f'(alpha0) < 31/250` — the
margin is about `7.3e-4`, and I verified it independently. The whole reduction is within
`~1.8` of being vacuous for the candidate graph, which is the main quantitative warning.
Evidence: `evidence/env01_constants.txt`.

## 1. The lifting lemma (the new repair)

`g(a,b) = a^2 + b^2 - 2ab cos(alpha)` has Hessian `[[2, -2cos],[−2cos, 2]]` with
eigenvalues `2(1 - cos alpha)` and `2(1 + cos alpha)`, both `>= 0` for `alpha in [0,pi]`.
So `g` is convex on the square `[0,r]^2`; a convex function on a polytope attains its
maximum at a vertex, and the four corner values are `0, r^2, r^2, 2r^2(1-cos alpha)`.
Hence

    max g = max(r^2, 2r^2(1-cos alpha)) = max(r^2, 4 r^2 sin^2(alpha/2)),

so `|x-y| <= max(r, 2r sin(alpha/2))` whenever `|u|,|v| <= r` with `u = x-c`, `v = y-c`
and included angle `alpha`. **This is where the extra `r` term comes from**: it is the
`(a,b) = (r,0)` corner, i.e. exactly the unequal-endpoint-radius configuration (one
endpoint at distance `r`, the other at distance `0`) that the withdrawn symmetric bound
could not see. The corner mechanism is verified numerically in the evidence file (corner
max >= grid max for all sampled `alpha`, with the `(r,r)` corner reproducing
`4r^2sin^2(alpha/2)` exactly).

## 2. The chord/arc transfer

On the unit circle the minor chord subtending an arc `theta in [0,pi]` has length
`2 sin(theta/2)`. Hence `sin(theta/2) <= max(r/2, r sin(alpha/2))`, and since `asin` is
increasing on `[0,1]` and both arguments are in `[0,1]` for `r <= 1`, `alpha in [0,pi]`,

    theta <= max(2 asin(r/2), 2 asin(r sin(alpha/2))).

Verified; note again that `alpha` here is the included angle *at the site* `c`, so the
argument does not need `|u| = |v|`. The endpoint distances are each `<= r` because every
site has norm `<= rho = U` after the normalization of the safe-area reduction, and each
arc endpoint is a site.

## 3. Concavity and the affine envelope

With `U = 0.33173203427623414` and `f(alpha) = 2 asin(U sin(alpha/2))`:

    f'(alpha) = U cos(alpha/2) / sqrt(1 - U^2 sin^2(alpha/2))
    f''(alpha) = -U(1-U^2) sin(alpha/2) / [2 (1 - U^2 sin^2(alpha/2))^{3/2}] <= 0,

so `f` is concave on `[0,pi]` (verified: `max f'' = 0` on a fine grid, attained at
`alpha = 0`; the expression is manifestly `<= 0` because `1 - U^2 > 0`). For a concave
`f`, the tangent at any `alpha0` lies above `f`, and the constant `A = 2 asin(U/2)` bounds
the `r`-branch. Therefore

    max(A, f(alpha)) <= [max(A, f(alpha0) - alpha0 f'(alpha0))] + f'(alpha0) * alpha

for every `alpha0`; taking `alpha0 = 121/50 = 2.42` and the exact constants gives the
rational affine envelope

    theta <= 167/500 + (31/250) alpha  =  0.334 + 0.124 alpha,      alpha in [0,pi].

**Independent verification of the exact constants** (mpmath at 60 digits, my own code):

| constant | value | required | holds |
|---|---|---|---|
| `A = 2 asin(U/2)` | 0.3332722560435834 | `< 167/500 = 0.334` | yes (margin 7.28e-4) |
| `f'(alpha0)` | 0.1231917171873321 | `> 0` and `< 31/250 = 0.124` | yes (margin 8.08e-4) |
| `f(alpha0) - alpha0 f'(alpha0)` | 0.3330484963622716 | `< 167/500` | yes (margin 9.52e-4) |
| `f''(alpha0)` | -0.160771519351 | `<= 0` | yes |

Endpoint checks of the envelope: at `alpha = 0` the slack is `0.000728` (the binding
point); at `alpha = pi` the slack is `0.04728`. Minimum slack over a 100001-point grid is
`0.000728 > 0`. So the envelope is valid, and its tightest point is at `alpha = 0`.
The lead's own script also asserts these three inequalities with interval arithmetic
(`area_chord_probe.py` lines 6-9); my independent computation confirms them.

## 4. Use of the envelope

For `q` boundary owners, `Sigma_i theta_i = 2pi` (the arcs tile the normalized circle)
and each `theta_i <= 167/500 + (31/250) alpha_i`, hence

    Sigma_i alpha_i >= K_q = (2pi - q * 167/500) / (31/250).

Verified: `K_10 = 23.73536538`, `K_11 = 21.04181699`, matching the document. The candidate
cover's numerical `Sigma alpha ~ 25.553` exceeds `K_10` by `~1.82`, so **the candidate
graph is not excluded by this inequality**, as the document says. The certificate-sign
step (`mu >= 0`, add `mu` to each boundary-angle slope and subtract `mu K`) is valid:
`Sigma alpha >= K` implies `obj <= obj + mu(Sigma alpha - K)` for `mu >= 0`, and the
supporting-plane machinery then applies to the augmented linear objective; the retained
`Bt = 2pi 1` and `alpha,beta in [0,pi]` are exactly the constraints the box maximum uses.

## 5. Quantitative warning (the one real caveat)

* **Slope.** The envelope's slope `31/250` is pinned by concavity: any valid affine upper
  bound of the form `g0 + k alpha` needs `k >= f'(alpha0)` for the tangent point to be
  covered, and `f'(alpha0) = 0.1231917...` is only `8e-4` below `0.124`. So the constant
  is not wastefully loose, but it cannot be improved by much either.
* **Weak region and the `K_q` gap.** The envelope is ~0.27 above the true `A` on the whole
  interval `alpha in [0, pi/3]`, and `K_q` is dominated by that constant: with `q = 10`
  the normalization leaves only `2pi - 10*0.334 = 2.943` to be distributed at slope
  `0.124`. For comparison, the sharp alternatives `Sigma theta <= q*A + k Sigma alpha`
  with `A = 0.333272256` (the true value) would give `K_10 = 23.73536538 + 10*(0.334 -
  0.3332723)/0.124 = 23.7354 + 0.0587 = 23.794`, i.e. only `0.06` better — so the loss
  from the rational rounding is small, but the loss from the `alpha in [0,pi/3]` plateau
  is intrinsic to this relaxation: any pair of graphs whose optimizer sits in that plateau
  will be reported `inconclusive`, not excluded.
* **Consequence for the probe.** The document's statement "safe-area optimizer proposals
  for ALL previously retained graph classes violate the new inequality" is a statement
  about the optimizer's *proposals*; violating the necessary inequality proves the
  proposal is not a cover, which is consistent but is not itself an exclusion. The
  exclusion only comes from a negative supporting-plane bound on the augmented relaxation.
  This matches the document's own framing; I record it so the wording is not read as an
  impossibility statement.

## 6. Assumptions audit (the lead's checklist)

| forbidden assumption | used? |
|---|---|
| endpoint radii equal (`|u| = |v|`) | **no** — `g` is maximized over the whole square; the binding corner is `(r,0)` |
| facet/site triangle isosceles (`beta = pi - 2*base angle`) | **no** — `beta` does not appear in this bound at all |
| tangents from an interior point | **no** — the transfer only uses the chord-length formula on the unit circle |
| optimizer feasibility / KKT | **no** — the affine envelope is proved, not assumed; `t0, y, mu` are arbitrary rationals |

## 7. What is not audited

The 12-graph probe and its 9 exclusions (`area_chord_probe.py` run output), the
independent Fraction replay, the catalogue/`q11` bookkeeping, and the interaction with the
safe-area certificate constants (`U`, `L`, `R`). I also did not re-derive the safe-area
reduction itself (audited separately in `../area-safe-audit/`).

## 8. Residual gap

None in the envelope. The relaxation's own strength is the limiting factor: the envelope
plus the existing angle equations leave the candidate graph unexcluded (`Sigma alpha`
margin 1.82 out of 23.7), and any graph whose optimizer proposals lie in the
`alpha <= pi/3` plateau will need a different coupling (e.g. a joint constraint on
`Sigma theta` and the number of owners). That is a modelling question, not an error in
this note.
