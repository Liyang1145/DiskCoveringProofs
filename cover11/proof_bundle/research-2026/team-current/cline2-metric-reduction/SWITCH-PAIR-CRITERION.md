# Isolated switch-pair criterion: `cos b >= (r^2 + rho^2)/(2 rho)`

Own directory; no claims registered. Units: the unit disk `D`, `actual r` = the radius for which
the configuration is a cover; `R0` = a fixed abstract radius appearing in a later normalization
(not used in the derivation below except where stated).

## 0. Setting (isolated pair)

* `P` a **unit switch**: `|P| = 1`, `r < 1`.
* `c, d` the two inward centres incident to `P`, with `|c|, |d| <= sqrt(1 - r^2)`
  (the inward-root normal bound) and `|P - c| = |P - d| = rho <= r`, `rho > 0`.
* `b = (1/2) angle(c - P, d - P)`, so `b in [0, pi/2]` automatically
  (indeed `sin b <= sqrt(1-r^2)/(2 rho)`, and `b < pi/2` as soon as a pair exists and `r > 0`).

**Conjecture (lead).** The pair is feasible iff `cos b >= (r^2 + rho^2)/(2 rho)`.

**Verdict: true.** Necessity and sufficiency both hold, and the criterion is *equivalent to the
cone condition*, with no hidden inequality needed. Two clarifications: the cleanest form is the
cone statement (§1, equivalence (E)); the constant `(r^2+rho^2)/(2 rho)` is at most `1` exactly
when `rho >= sqrt(r^2 - (1-2r^2))`, so the inequality is a genuine restriction only above that
threshold (§3), and the **sharp bound over `rho`** at fixed `r` is `cos b >= r` (§4).

## 1. One point: exact feasibility cone (equivalence)

Fix `P`, `rho`, `r`. Put `n = -P/|P| = -P`. For a point `c` with `|P - c| = rho`, write
`alpha = angle(c - P, n)` (the angle between the vector `c - P` and the inward normal).
By the law of cosines,

```
    |c|^2 = 1 + rho^2 - 2 rho cos alpha .                                   (1)
```

The constraint is `|c| <= sqrt(1-r^2)`, i.e.

```
    (1) <= 1 - r^2   <=>   cos alpha >= (r^2 + rho^2)/(2 rho) =: cos H .    (2)
```

Because `rho <= r < 1` together with the nonemptiness bound `rho >= 1 - sqrt(1-r^2)` (§3)
implies `(r^2 + rho^2)/(2 rho) < 1`, the cap `min(1, .)` is never active on the admissible
domain; define `H = arccos((r^2 + rho^2)/(2 rho)) in (0, pi/2]`. Then

> **(E)** For a point `c` with `|P-c| = rho`: `|c| <= sqrt(1-r^2)` iff `alpha <= H`.
> The feasible set is the intersection of the circle `|P-c| = rho` with the closed disk
> `|c| <= sqrt(1-r^2)`, which is a nonempty arc symmetric about the direction `n = -P`.

*Proof.* `|c|^2 = 1 + rho^2 - 2rho cos alpha` is strictly increasing in `alpha in [0,pi]`,
so `|c| <= sqrt(1-r^2)` is equivalent to `alpha <= alpha_max` with
`1 + rho^2 - 2rho cos alpha_max = 1 - r^2`, i.e. `cos alpha_max = cos H`. Since
`H in (0, pi/2]` (and `alpha in [0,pi]`), `cos alpha >= cos alpha_max` holds iff
`alpha <= H`. The arc is nonempty iff
`alpha_max >= 0` iff `|P| - rho = 1 - rho <= sqrt(1-r^2)` iff `rho >= 1 - sqrt(1-r^2)`. ∎

So "each centre is within `H` of the inward normal" is exactly the individual feasibility
condition — not a relaxation.

## 2. Two points: necessity and sufficiency

**Necessity.** If the pair exists, (E) applied to `c` and to `d` gives
`alpha_c, alpha_d <= H`, hence the angle between the two rays is at most `2H` in absolute
value: `2b <= 2H`, i.e. `b <= H`, i.e.

```
    cos b >= cos H = (r^2 + rho^2)/(2 rho) .                                (3)
```

**Sufficiency.** Conversely assume (3). Then the two unit directions
`u = (c'-P)/rho`, `v = (d'-P)/rho` at mutual angle `2b <= 2H` fit inside the cone
`{w : angle(w, n) <= H}` (put `c'` at `alpha = -b`, `d'` at `alpha = +b`, both visible since
`b <= H`; equivalently the rotated configuration). By (E) both points satisfy
`|c'|, |d'| <= sqrt(1-r^2)` and both have distance exactly `rho` from `P`. Hence an admissible
pair exists. ∎

**Equality classification (`cos b = (r^2+rho^2)/(2rho)`, i.e. `b = H`).** Then `2b = 2H` and
the two directions are exactly the two boundary rays of the cone:

```
    |c| = |d| = sqrt(1-r^2)   (both centres on the inward-root boundary circle),
    alpha_c = -H, alpha_d = +H   (up to swapping c, d),
    the pair is mirror-symmetric about the line R n,
    |c - d| = 2 rho sin H ,    |c|^2 = |d|^2 = 1 - r^2 .
```

In particular at equality both `c, d` lie on the tangency circle `|x| = sqrt(1-r^2)`; if
`b < H` the pair is strictly inside the cone and no tangency is forced.

**The degenerate `H = 0` case (corrected).** `(r^2+rho^2)/(2rho) >= 1` holds exactly for
`rho in [1 - sqrt(1-r^2), 1 + sqrt(1-r^2)]`; the upper end is impossible since `rho <= r < 1`.
So `H = 0` occurs precisely at `rho = 1 - sqrt(1-r^2)`, and there it is **valid for every
`r < 1`**: the cone degenerates to the ray along the inward normal, `f(rho) = 1`, and the
criterion forces `b = H = 0`, i.e. the two directions coincide, so

```
    c = d = P + rho * (-P)      (one point on the line through P and the origin),
    |c| = 1 - rho = sqrt(1-r^2) ,   |P - c| = rho .
```

So the degenerate pair is a legitimate admissible configuration when coincident centres are
allowed. It is excluded in a covering configuration **only** because the centres there are
distinct; with that single extra hypothesis `H = 0` never occurs. (My earlier text wrongly ruled
out `H = 0` for all admissible pairs and is replaced by this.)

## 3. The criterion is never vacuous on the admissible domain

Write `f(rho) = (r^2 + rho^2)/(2 rho)`. Solving `f(rho) <= 1` gives `(rho - 1)^2 <= 1 - r^2`,
i.e. `rho in [1 - sqrt(1-r^2), 1 + sqrt(1-r^2)]`. So `f > 1` (criterion automatically true)
happens exactly for `rho < 1 - sqrt(1-r^2)` or `rho > 1 + sqrt(1-r^2)`. But the pair can exist
only if `rho >= 1 - sqrt(1-r^2)` (the nonemptiness bound of (E): the circle `|P-c| = rho` must
meet the disk `|c| <= sqrt(1-r^2)`), and `rho <= r < 1` excludes the other interval. Hence on
the **whole** admissible domain `1 - sqrt(1-r^2) <= rho <= r < 1` one has `f(rho) < 1`
(equality only at `rho = 1 - sqrt(1-r^2)` or in the limit `rho = r = 1`), so

> the criterion `cos b >= f(rho)` is a **genuine restriction everywhere** the pair can exist;
> there is no sub-regime where it is vacuous.

(The apparent "`<= 1`" simplification is a red herring, as the two thresholds coincide.)

## 4. Sharpening over `rho`: the bound is `cos b >= r`

At fixed `r`, one has the one-line identity

```
    (r^2 + rho^2)/(2 rho)  -  r  =  (r - rho)^2 / (2 rho)  >=  0      for 0 < rho <= r ,
```

with equality iff `rho = r`. (Equivalently the function is convex with vertex at `rho = r`.)
Hence

```
    (r^2 + rho^2)/(2 rho)  <=  r        for 0 < rho <= r ,
```

with equality iff `rho = r`. So the criterion implies the **rho-free** bound

```
    cos b >= r                                                              (4)
```

and (4) is sharp (attained in the limit `rho = r`, giving `b <= arccos r`, i.e. the extremal
pair separation `2 arccos r`).

## 5. Comparison with the existing weak bound (C840)

C840's switch bound is `sin b > 1/37999` and `cos b >= 3/16` for `R >= 3/8`. The present
criterion has threshold `f(rho) = (r^2+rho^2)/(2rho)` on `rho in [1 - sqrt(1-r^2), r]`, and by
§4 (the identity `f(rho) - r = (r-rho)^2/(2rho)`)

```
    f(rho) >= r >= 3/8 = 0.375 > 3/16 = 0.1875     for every admissible rho ,
```

so with `r >= 3/8`:

* the improvement factor is `f(rho)/(3/16) >= r/(3/16) = 16r/3 >= 2`, with equality **only** at
  `r = 3/8` and `rho = r` (where `f = 3/8`); for `r > 3/8` the factor is `> 2`. At
  `rho = r`, `f` is exactly `r`, which is the case of interest (`rho = R` in normalized units).
* the bound is uniform over `rho`: `f(rho) >= r >= 3/16` for every admissible `rho`, i.e. the
  criterion beats C840's cosine bound on the whole admissible domain, not merely near
  `rho = r`. (At the other end `f(1-sqrt(1-r^2)) = 1`, consistent with the tangency degeneracy
  of §3.)

So the criterion improves C840's cosine bound on the whole admissible domain (in particular at
the case of interest `rho = r`), and the two bounds are necessary conditions in different
normalizations: C840's sine/cosine pair is a coarse necessary-domain bound, (3) is the exact
isolated-pair criterion.

## 6. Scope and status

* Proved here: (E) and the pair criterion (3) with the equality classification of §2 — a
  self-contained statement about an **isolated** pair of centres at one switch, using only
  `|c|, |d| <= sqrt(1-r^2)`, `|P-c| = |P-d| = rho <= r`, `|P| = 1`.
* Not claimed: any global cover, any sharp optimality, any statement coupling different
  switches; and (4) is a consequence of the pair hypothesis, not a new global constraint
  unless the pair hypothesis is supplied globally.
* The one extra hypothesis needed to exclude the degenerate `rho = 1 - sqrt(1-r^2)` case is
  **distinct centres** (`c != d`); without it the criterion is non-strict there (§2).
* Units: everything is in the actual-cover radius `r`; no `R0`-normalized quantity enters, so
  (3) can be used directly at either normalization by substituting the corresponding `r`.
* Numeric checks (reported separately, not used as proof): the criterion `cos b >= (r^2+rho^2)/(2rho)`
  reproduces the exact cone half-angle `H` at machine precision in random instances.
