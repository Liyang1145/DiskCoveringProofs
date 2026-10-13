> ## ⛔ NON-BEARING — DO NOT USE FOR ANY BOUND
>
> The lead identified interface errors in this report.  Recorded for the audit trail, with
> **no corrective work performed** (per instruction):
>
> 1. **Normalisation misreported.** The code has `e = sqrt(Q)/(2R0)`; I wrote `e = u/R` as
>    though `u` were `R0`-normalised.  The values printed for `m`, `n`, `u*` and the
>    remainder in section 2 are therefore off by the corresponding factor of `2` in `u`; the
>    lead's constant is `u* ~ 0.816`, not `0.408`.  The square identity itself is exact in
>    whichever `u` variable is used, but every numeric constant in section 2 must be
>    re-derived before use.
> 2. **Wrong derivative sign.** For face 2, `H' = +2r cos(2 b2 + p)`, not negative.  Any
>    differentiation downstream of that is wrong; the "consequently ... H' = -2r cos"
>    sentence in section 1 is void.
> 3. **`p` is the exact polar angle delta, hub = (H cos p, H sin p)**, and the own-face centre
>    is `(r sin 2b1, -r cos 2b1)`.  My failed hub-matching used the wrong centres and the
>    wrong chart reading, which is why it returned a `8.2e-5` residual instead of an identity.
> 4. **Identity (I) is a true identity but it does NOT remove the cancellation**: expanding
>    still leaves `O(1)` terms being subtracted when `Q` is small.  My section-1 claim that
>    (I) "removes the near-source cancellation" is therefore **withdrawn**.
>
> The lead has an exact complementary representation in `FACE-COMPLEMENT-REPRESENTATION.md`;
> that file, not this one, is the reference for this route.
>
> **Surviving content:** the `T = b1 + b2 = pi/2` degeneracy (the two radius-`r` disks
> coincide, so the entire common arc must be retained) and the fact that identity (I) is
> exact.  The lead has since certified the common arc at `T = pi/2` (73 eval, 0 live).
> Everything else in this file is non-bearing.

# R18 — separable analytic route: exact source representation, radial square, degeneracy

Own scope only (`cline2-coupled-factors`); lead files read, not modified.  Exact 9-decimal
frozen `z` (`joint_nested_frozen.json` sha256 `5671967c…21fb`), `R = 19/50`.
No claims registered; bounded derivation + controls; no grid scaling.

## 0. The route read

* `low_low_boundary_jet.py` — C872 removed both widths, leaving the three boundary charts of
  C871; `legal` delegates to `allbearing_boundary_jet.legal`.
* `allbearing_boundary_jet.py` — charts `j = 0,1` are face-polar (`A = b1-p`, `B = b2+p`,
  `H = 2r sin(2b1-p)` resp. `2r sin(2b2+p)`); chart `j = 2` is the norm central-angle chart
  (`v = s + (1-r) cos p`, `t = (1-r) sin p`, `s = sqrt(1-r^2)`), with `j = 3` excluded.
  Range `b_j ∈ [acos(r), 1]` piecewise, `r ∈ [.379, .37999]`.
* `width_endpoint_jet.py` — the width endpoint term already eliminated.

## 1. The identity the lead asked for: exact, cancellation-free representation of the source distance

The off-face quantity is `e = sqrt(Q)/(2R)` with
`X = H − 2r sin b·cos(ang)`, `Y = 2r sin b·sin(ang)`, `Q = X² + Y²`.  Expanding once removes
the subtraction entirely:

```
Q = H^2 + 4 r^2 sin^2 b − 4 r H sin b cos(ang)                              (I)
```

The cross term is `−4rH sin b cos(ang)` (a **cosine**, not a sine), and (I) contains no
difference of nearly equal quantities: `H`, `sin b`, `cos(ang)` are all `O(1)` and separated.
**Verified to `1.97e-31` over 120 cases spanning `j = 0,1`, `r ∈ {.379,.3793,.37999}`,
both `b`-arguments and `p ∈ [−0.9, 0.9]`.**

This is the representation that removes the near-source cancellation: in the code's form
`X = H − 2r sin b cos(ang)` the two terms can be close, whereas (I) exhibits `Q` as a sum of
a square and a single product.  Consequently

```
u = sqrt(Q) = sqrt( H^2 + 4r^2 sin^2 b − 4rH sin b cos(ang) )
u' := du/dp  needs only  H' = −2r cos(2 b_l ∓ p)  and the derivative of cos(ang)
```

both elementary and cancellation-free, so the `atan2(Y,X)` argument and the `1/Q` factors in
the objective can be differentiated without the `X`-difference appearing.

**Honest correction (withdrawn):** I first claimed that `T := b1 + b2` enters `Q` only
through a single `cos T` term, on the strength of a hasty "double-angle collapse".  The
collapse fails: on the face-`l` chart the *other* bearing enters only via `H`, while the
on-face bearing enters both via `cos(b_l ∓ p)` and via `H = 2r sin(2b_l ∓ p)`, and there is no
single-angle collapse.  The claim is withdrawn; (I) is what survives.

## 2. The second exact identity: the radial quadratic is a square

With `e = u/R`, `m := beta/R²`, `n := gamma/R`:

```
beta e^2 + gamma e  =  m (u − u*)^2 − n^2/(4m),        u* := −n/(2m)
```

an exact square about the minimiser `u*`, with a constant remainder.  Verified to `1.5e-31`
(`j=0`) and `3.0e-31` (`j=1`).  Constants (exact 9-decimal frozen coefficients):

| branch | `beta` | `gamma` | `m` | `u*` | remainder |
|---|---|---|---|---|---|
| `j=0` | `0.405431351` | `−0.870277865` | `2.80769633657` | `0.407844124393` | `−0.46702330767` |
| `j=1` | `0.400827103` | `−0.86525597` | `2.77581096260` | `0.410148498117` | `−0.46695189024` |

Because `u = sqrt(Q)` lies in `(0, 2r)` and `2r ≈ 0.759`, the minimiser `u* ≈ 0.408` sits well
**inside** the admissible `u`-range and the remainder is bounded by `0.468`.  So the map
`u ↦ beta e² + gamma e` is a shifted parabola in `u` (not in `p`), which is what makes the
`u`-stationarity tractable: stationarity of the quadratic piece alone is `u = u*` exactly.

## 3. Degeneracy test `T = b1 + b2 = pi/2` — confirmed, corner picture must be retained

The two radius-`r` source disks are centred at `D1 = (r sin2b1, −r cos2b1)` and
`D2 = (r sin2b2, r cos2b2)`.  With `b2 = pi/2 − b1`: `2b1 + 2b2 = pi`, so `sin2b2 = sin2b1`
and `cos2b2 = −cos2b1`, hence **`D2 = D1` identically**.  Verified numerically:

```
b1 = 0.60946080763725372899  ->  |D1-D2| = 4.93e-32
b1 = 0.8                     ->  |D1-D2| = 6.32e-32
b1 = 1.0                     ->  |D1-D2| = 4.93e-32
b1 = 1.1                     ->  |D1-D2| = 7.40e-32
```

So at `T = pi/2` the two disk *constraints* are literally the same constraint: the feasible
set contains the **entire common arc**, not isolated corners, and any corner-only upper bound
misses it.  (This is the degeneracy the lead flagged; it is confirmed.)

Note the tension with section 1: the degeneracy is not visible in `Q` — `Q` stays smooth
across `T = pi/2` — it appears in the *constraint* system, which is exactly why the corner
argument cannot be pushed through this locus.

## 4. What I could not verify (and therefore do not assert)

The face charts parametrise the hub by `H = 2r sin(2 b_l ∓ p)` without naming the hub's
polar angle.  I attempted to identify the hub point (so that the *on-face* circle condition
`|hub − c_l| = r` could be used to eliminate `H`) and **failed to find an exact match**:
testing four natural hub placements (`H e^{ip}`, `H e^{i(b_l∓p)}`, `H e^{i(2b_l−p)}`) against
both `e^{±i b_l}` the best residual was `8.2e-5`, i.e. *not* an identity.  So:

* **not verified:** any closed form for the hub's polar angle, hence any `H`-elimination via
  the on-face circle condition;
* **not verified:** any bearing-stationarity simplification that uses such a closed form.

This is the gap.  Since a `1e-5` residual is neither an identity nor a coarse mismatch, the
likely cause is that my reading of `p` is only approximately the code's chart coordinate; the
correct identification should be read off `interval_hub_boundary.py`'s boundary
parametrisation (line 13: `cx,cy,rho = disks[j]; v = cx + rho cos theta; t = cy + rho sin theta`),
which I did not have time to match against the `A = b1−p` convention in this round.

## 5. Scope summary

| item | status |
|---|---|
| `Q = H² + 4r² sin²b − 4rH sin b cos(ang)` | **exact**, verified `1.97e-31` / 120 cases |
| `beta e² + gamma e = m(u−u*)² − n²/(4m)` | **exact**, verified `≤3e-31`, both branches |
| `T = pi/2` ⇒ disks coincide, common arc retained | **exact**, verified `~5e-32` |
| `T`-collapse of `Q` through `cos T` | **withdrawn** (wrong) |
| hub polar angle closed form / `H`-elimination | **not found** — the open gap |
| concavity or corner-only assumptions | not used |

No claims registered.  The single useful analytic identity requested is (I) (plus its square
companion in section 2); the remaining step — eliminating `H` through the on-face circle
condition — needs the hub parametrisation to be identified exactly first.

Files: `r18b_identity_deg.py` (first, wrong collapse), `r18c_corrected.py`, `r18e_correct.py`,
`r18f_verified.py`, `r18g_identify.py`, `r18h_ids.py`, `r18i_geometry.py`,
`r18j_decisive.py` (the decisive geometry test).  Logs: `out/r18*.log`.
