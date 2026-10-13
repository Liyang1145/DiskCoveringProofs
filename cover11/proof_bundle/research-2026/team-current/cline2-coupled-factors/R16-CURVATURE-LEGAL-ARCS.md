# R16 curvature diagnostic — legal face arcs, corrected second derivative

Own scope; current frozen coefficients (`lead/joint_nested_frozen.json` sha256 `5671967c…21fb`);
bounded calibration only, **no interval scale, no claim registered**.  Supersedes the
curvature-related content of `R16-SATURATED-FACE-DERIVATIVES.md` (withdrawn) and corrects
`r16S/r16T`.

## 0. The lead's chart: verified

`face1: v = r(sin2b1+sin2A), t = r(cos2A−cos2b1), theta = pi/2 − 2A` reproduces the correct
frame.  Checked numerically at three legal points:

* `dtheta/ddelta = 2` exactly (so `theta = pi/2 − 2A` is consistent with `A = b1−delta`);
* `|x_theta'| = r` exactly (0.375 / 0.378 / 0.3795 at the three test points), so the chart
  tangent is unit-modulus up to the factor `r`;
* `x_theta'' ⊥ x_theta'` with `|x_theta''| = |x_theta'|`, i.e. the chart is the circle of
  radius `r` in geodesic-curvature form.

So `G''_delta = 4[x_theta'^T Hess F x_theta' + grad F · x_theta'']` is the right curvature
identity, with both terms retained.  The frame also shows why `C863`'s norm bound does not
transfer here: the norm arcs have their own chart and the ridge bounds remain loose.

## 1. Bug found and fixed in my own second-derivative module

`r16S_g2_legal.py:81` assembled the off-face contribution as

```
off2 = (2 beta2 e2 + gamma2) e2'' + 2 beta2 (e2')^2 + 2 a2 phi2'     # WRONG
```

The third term of `d2V/ddelta2` is `a2 * phi2''` (no factor 2, and the second derivative of
phi2 rather than the first).  Verified three independent ways at `(r,b1,b2,delta) =
(0.375, 1.05, 1.05, 0)` (legal):

| route | value |
|---|---|
| module `G''` (buggy) | `0.36640683394183493` |
| hub² + on² + corrected off² | `0.4242546867396482` |
| high-precision second difference of `V` | `0.4242546866478459` |

The gap `0.0578478528` is exactly the missing `2 a2 phi2' + a2 phi2''` contribution.  All
face-1/face-2 scans below use the corrected assembly (`r16gg_corrected.py`), and `G'` was
revalidated against finite differences of `V`.

## 2. Legal-face-arc scan (≤200 legal points per face)

Legality = the three filters together: inside the face-1 cap, inside the face-2 cap, and
inside/on the norm circle, with `H > 0` and `delta ∈ [−b2, b1]`.  (My earlier `r16r` sign
census had **no** filters and is therefore not legal — withdrawn.)

| face | G' range | G' signs | G'' range | G'' signs | convex? |
|---|---|---|---|---|---|
| 1 | `[−0.018622, +0.373608]` | 4 neg / 196 pos | `[−1.632541, +0.512111]` | **138 neg** / 62 pos | **NO** |
| 2 | `[−0.397253, +0.011263]` | 199 neg / 1 pos | `[−1.636425, +0.518976]` | **127 neg** / 73 pos | **NO** |

**Answer to the posed question: neither face arc is convex on the legal set**, so the
conjectured route ("if the face arcs are convex then the maximum reduces to endpoints /
norm intersection / ridge") **does not apply as stated** — `G'' >= 0` fails at a majority of
legal points on both faces (138/200 and 127/200).

## 3. Interior stationary structure

`G'` does cross zero on both legal arcs, and the crossings are **interior minima**, matching
the lead's expectation:

* face 1: `G' = −0.011731` at `(r,b1,b2,delta) = (0.38, 1.00, 1.00, −0.200)`, `G'' = +0.228015`
  (also `−0.013124` at `r=0.379`); nearest positive crossing `G' = +0.014578` at
  `(0.38, 1.0362, 1.000, −0.18552)`, `G'' = +0.086764`.
* face 2: `G' = +0.011263` at `(0.379, 1.00, 1.00, +0.200)`, `G'' = +0.236909`;
  `G' = −0.011405` at `(0.375, 1.03728, 1.000, 0.222368)`, `G'' = +0.153382`.

At these points `G'' > 0`, so they are genuine interior **minima** and **endpoints still
suffice** for the maximum on the arc — exactly the lead's read of the corrected first
derivative.  The two faces mirror each other at `b1 = b2` (the same physical point), but the
coefficients are not equal (`a1 = 0.012841585` vs `a2 = 0.013306528`, `beta1 = +0.405431351`
vs `beta2 = +0.400827103`, `gamma1 = −0.870277865` vs `gamma2 = −0.86525597`), so no exact
reflection is claimed and none is used.

## 4. Strongest legal witnesses (as requested)

| quantity | witness | location |
|---|---|---|
| **strongest negative `G''` (face 1)** | `−1.632541002` | `r=0.376, b1=1.111192, b2=1.000000, delta=−0.366642`, `G'=+0.279677` |
| **strongest negative `G''` (face 2)** | `−1.636425185` | `r=0.379, b1=1.000000, b2=1.109249, delta=+0.367225`, `G'=−0.282421` |
| strongest positive `G''` (face 1) | `+0.512110501` | `r=0.379, b1=b2=1.000000, delta=0.000000`, `G'=+0.070913` |
| strongest positive `G''` (face 2) | `+0.518975505` | `r=0.378, b1=b2=1.000000, delta=0.000000`, `G'=−0.073015` |
| smallest `\|G'\|` (face 1) | `0.011731` | `r=0.38, b1=b2=1.000000, delta=−0.200000`, `G''=+0.228015` |
| smallest `\|G'\|` (face 2) | `0.011263` | `r=0.379, b1=b2=1.000000, delta=+0.200000`, `G''=+0.236909` |

## 5. Scope and next implication

* Established (bounded calibration, ≤200 legal points per face, corrected analytic second
  derivative validated against high-precision finite differences to `<1e-9`): neither legal
  face arc is convex; `G'` crosses zero and the crossings are interior minima; the strongest
  legal `G''` witnesses are `−1.6325` (face 1) and `−1.6364` (face 2).
* **Not** established: any interval certificate; any monotonicity; any reduction of the hub
  maximum to ridge/norm endpoints.  In particular the reduction the lead hoped to get from
  convexity is **not available**: `G'' >= 0` is false on the legal arcs, so "endpoints
  suffice" must be argued from the *structure* (interior stationary points are minima) rather
  than from convexity — and that structural statement is exactly what still needs a proof
  over the whole box, not just the ≤200-point sample.
* Ridge datum: the lead's `delta = b1 − b2`, `H = 2r sin(b1+b2)` remains the only feasible
  face-cap intersection (H₀ excluded); the ridge bounds are still loose, and nothing here
  tightens them.

Files: `r16bb_chart.py` (chart + curvature frame validation), `r16gg_corrected.py` (bug fix,
corrected assembly, legal-arc scan), `r16hh_witness.py` (`out/r16hh_witness.json`, witnesses).
Logs: `out/r16gg.log`.
