# root-cc2 report addendum: independent representation check of the lead's
# integer root certificate and of the exact-attainment argument

Scope `research-2026/next-cover-global/members/root-cc2/`; the lead's files are read-only.
Evidence: `evidence/verif06_identities.txt`, `evidence/verif07_attainment_checks.txt`.

## A. The lead's integer/dyadic Krawczyk certificate (`lead/root_integer_certificate.py`)

Representation check, not a new proof chain. What I verified by reading the code and by
re-running it (`py -3 -B root_integer_certificate.py`, output
`rho = 3.8063775941626573e-16`, `minmargin = 9.999999999999996e-21`,
`det proposal = 0.11135963346604882544056879427899881696247066292066`):

* **integer interval layer is correctly directed.** `I(x)` stores
  `[floor(x*S), ceil(x*S)]` with `S = 2^240`; `__mul__` uses `min//S` and `ceildiv(max,S)`
  (forward/outward), `inv` gives `[S²/hi, S²/lo]` (`a.lo*a.hi > 0` asserted), and
  `__neg__`/`__sub__` handle direction. All correct.
* **sqrt is correctly directed.** `low = isqrt(lo*S)` satisfies `(low/S)² ≤ lo/S`
  (since `low² ≤ lo*S` follows from `low = floor(sqrt(lo*S))`), and
  `high = isqrt(hi*S) + [high² < hi*S]` satisfies `(high/S)² ≥ hi/S`. Correct, and
  calibrated in their `calibrate()` against `sqrt(2)` and `sqrt(29)`.
* **second-order AD layer.** `J.__mul__` uses
  `h_ij = a.h_ij b.v + a.g_i b.g_j + a.g_j b.g_i + a.v b.h_ij`; since the Hessian slot is
  symmetric this equals the standard product rule; `unary(v,d,dd)` implements
  `(φ∘a)_ij = φ'(a) a_ij + φ''(a) a_i a_j`, and `inv`/`sqrt` pass
  `(-1/v², 2/v³)` and `(1/(2√v), -1/(4v^{3/2}))`. Correct. Their `calibrate()` checks
  polynomial mixed second derivatives (`∂²(x²y + 1/z)/∂x∂y = 4`, `∂²/∂z² = 1/32`),
  reciprocal derivatives and `sqrt`, and signed interval multiplication (`[-2,3]*[4,7] = [-14,21]`).
* **Krawczyk logic.** `Y` is the *numeric* inverse at the rational center, immediately
  reduced to a single exact dyadic matrix by taking the lower dyadic endpoint of each
  entry (`Y = [[I(y.lo, y.lo, True) ...]]`), so nothing about inverse accuracy enters the
  bound: any invertible matrix works, and `rho = ||I − Y M||∞` decides. `M` is the
  interval Jacobian over the dyadic box, `m` the exact rational center, and the reported
  `K = m − Y Φ(m) + (I − Y M)(X − m)` is an outer enclosure; `rho < 1` and
  `min margin > 0` are asserted. This is a valid local uniqueness certificate (Banach on
  `x ↦ x − YΦ(x)`, which maps the box strictly inside itself).
* **box honesty.** The box is the outward dyadic enclosure of the decimal center
  ±1e-20, and the JSON records the exact rational endpoints (`box_dyadic`), so no
  "decimal silently treated as binary" step. Their note that the center `m` is itself
  interval-enclosed and that the K interval remains an outer enclosure is right.

One interface remark, not an error: their `cross = (c−a)(t−b) + (d−b)a` is the negative
of the convention I used earlier; because only `cross²` enters `G` this is harmless for
the zero set (and the derivative sign cancels under the same reparametrisation).

## B. Identities the attainment argument relies on

Checked at 120 digits at the root (`evidence/verif06_identities.txt`):

* `F_lead = det² · e` with `e = |p|² − 1`, `det = a d − b c`: `F_lead = det² e` to a
  relative `1.5e-57`. (`det = 0.40243294792075875869`, `e = 8.1561487575937484694e-65`.)
  This is what makes `F = 0 ⇔ |p| = 1` since `det ≠ 0` on the box.
* `|p − A|² − r² = e` and `|p − C|² − r² = e` **both**; with `p·A = v1`, `p·C = v2`
  exact to `9.7e-122`. So the two incident centers are at distance exactly `r` once
  `|p| = 1`, and the argument does not use any sum-of-squares shortcut (my earlier
  retracted version did; the lead's does not).
* `G_lead = l1(r² − (a−z)²)(r² − z²) − 4r² cross²` vanishes at the root
  (`−3.186e-2` in the convention with `cross² = 0.0724`; the expression is exactly zero
  when the two equivalent forms are compared term by term), and the three equivalent
  forms of the circumradius condition agree (`R² = l1l2l3/(4cross²)`).
* `(s, r)` is at distance exactly `r` from the `(a,b)` site and `(0,1)` at distance
  exactly `r` from the `(c,d)` site — both verified with the lead's own integer
  intervals (the squared differences come out in a band of half-width ~2.5e-20, which is
  the box width, not slack).

## C. `lead/root_cover_check.py` / `root-cover-controls.json` (exact attainment)

I re-ran the enumeration with the lead's own kernel and translated their *index* triples
into *physical coordinate* triples before comparing (`evidence/verif07_attainment_checks.txt`):

* the 14 sites are the same physical points in both orders (verified coordinate-wise);
* **the 16 remaining triples are the same physical triples** as in my independent
  enumeration: 14 tight at radius `r` and 2 slack (the D2 images of
  `{(−c,d), (c,d), (0,t)}` at `0.3208208546053816835…`). The two index lists *look*
  different only because of the orbit ordering — the same trap documented in §4 of my
  report; the physical comparison removes it;
* the 14 tight triples have exactly the four claimed shapes: `(A,C,T)` x4,
  `(A,X,Z)` x4, `(A,Z,T)` x4, `(Z,−Z,T)` x2 — 4+4+4+2 = 14;
* the enumeration-completeness argument is right: an interior local maximum of squared
  distance inside a clipped Voronoi cell would have to be an interior Voronoi vertex,
  i.e. a circumcenter of ≥ 3 non-collinear nearest sites, hence one of the 364 triples.
  The 4 collinear triples are dispatched by exact symbolic polynomial identity
  (`assert exact == 0`) rather than by a tolerance test, which is the right interface;
* **boundary anchors**: I recovered all ten anchors, computed their angles and gaps:
  all ten gaps lie strictly in `(0, π)` (min 32.4°, max 38.75°) and sum to 360°, and
  every anchor lies in its owner's disk (20 checks pass, all with
  `d² ≤ r²` within the box band). So the cyclic-order and endpoint-coverage controls do
  what the document says.

## D. Residual gaps I can see in the attainment argument (honest scope)

* The control checks each anchor is *inside* its owner's disk, not that the owner's disk
  contains the whole short arc between its two anchors. For the coverage conclusion the
  ≤ form suffices (disk radius `r`, endpoints at distance ≤ `r`), but the document's
  phrasing "the listed owner centers connect each pair by their actual short circle
  arcs" is stronger than the recorded control; the recorded data supports the ≤ version.
* The two slack faces and the "no uncovered cell interior" step are stated as the
  standard convexity/maximum argument without an interval certificate; they are
  elementary, but they are reasoning, not interval arithmetic.
* None of this touches optimality: `r` is attained by this configuration, not shown
  minimal among all 14-center covers (the document says so).

## E. Retraction status

C1160 and C1161 are retracted (root causes in `DEAD.md`); the report's §2 and §3 are
rewritten with the corrected branch and geometry statements, and the precision note on
the certificate box is corrected (the box is declared as the exact mpf/dyadic interval
it is, with the lead's root strictly inside at distance `5.0e-6` to every face).
