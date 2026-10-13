# Interface audit: ENDPOINT-SECTOR-EXCLUSION renormalization (explicit valid/invalid)

Object: `lead/ENDPOINT-SECTOR-EXCLUSION-INTERFACE.md`; checked against
`lead/CLOSURE-KERNEL-ANALYTIC-AUDIT.md`, `lead/CLOSURE-LOCAL-HALFPLANE-PROOF.md`,
`lead/certify_q0_closure.py`. No computations beyond the algebra quoted.
Verdict: **the renormalization interface is VALID**; one premise must be flagged
as *not needed* rather than assumed, and one numerical guard must be kept.

## 1. The degeneracy argument (valid; repaired — no equal-endpoint premise)

Let the sector have endpoints (switches) `P, Q in bd D`, chord line `PQ`, center
`c`, `alpha = angle QcP = pi`. Then `c` lies on the **line** `PQ`. Put
coordinates with that line at `n·x = k`, `n` the outward unit normal and
`k = cos(w/2)` the chord's distance from the origin (`w` = the sector's arc
width); write `c = k n + y tau` with `tau` the unit vector along the chord,
`y in R`. Then

```
   |c|^2 = k^2 + y^2 .
```

Genuine cover + inward replacement at the *actual* radius `r` gives
`|c| <= sqrt(1-r^2)`; the owned arc is covered at radius `r`, so `w <= 2 asin r`,
i.e. `k = cos(w/2) >= sqrt(1-r^2)`. Chaining,

```
   k^2 + y^2 = |c|^2 <= 1 - r^2 <= k^2    =>    y^2 <= 0    =>    y = 0 ,
   hence  k = sqrt(1-r^2) ,   w = 2 asin r ,   |cP| = |cQ| = r .          (D)
```

So `c` is the chord **midpoint**, the distance to each endpoint is exactly `r`,
and no equal-endpoint-distance assumption is used: `u' = v'` (and `c` = midpoint)
are *derived*. The bound `w <= 2 asin r` is the only place the radius enters, at
the actual `r`, not at `R0`. **Valid.**

## 2. Renormalization (valid; no premise at R0 is reloaded)

**What is rescaled: only the units in which metric lengths are expressed.** The
target disk `D` and the centers are *not* moved or scaled; no similarity
transformation of the configuration is applied. Correspondingly the kernel's
`u, v` are the endpoint distances measured in units of `R0` (i.e. `u = |S - c_i| / R0`
with `|S| = 1` kept as the unit target), so they are the same raw distances as in
the original problem divided by `R0`. From (D), the degenerate sector has

```
   u = v = t := r / R0  (the normalized *endpoint* distance) ,  t in [75/76, 1] ,
   w = 2 asin(R0 t) = 2 asin r  (the true width) ,
   alpha = pi .
```

Note `t` is not `|c'|`: the center's actual norm is `|c| = sqrt(1-r^2)` by (D),
and in units of `R0` its coordinate norm is `sqrt(1-r^2)/R0`; that quantity is
never used by the kernel. (Earlier wording `|c'| = t` mixed the center with the
normalized endpoint distance; corrected here.)

Why nothing at `R0` is needed:

* **C820 closure is scale-invariant.** `T + L_(i+1) + 2b + (w_i+w_(i+1))/2 = pi`
  is a statement about angles of a geometric configuration; multiplying all
  lengths by `1/R0` multiplies no angle. It holds for the rescaled
  configuration with the *same* `b, w` (angles). No norm bound at `R0` appears
  in its proof (containment uses `|c| <= sqrt(1-r^2)` at the actual `r`, then
  Cauchy-Schwarz; that conclusion is scale-free).
* **The width identity is exactly preserved.** The kernel's
  `w = 2 asin(R sqrt(q)/2)` is evaluated at `R = R0`, and for the rescaled
  configuration `sqrt(q) = |u - v e^{i alpha}| = 2t` (for `u = v, alpha = pi`),
  so `R0 sqrt(q)/2 = R0 t = r` and the kernel returns `2 asin r` — the true
  width. In general `R0 sqrt(q)/2 = (chord/(2R0))`-free form: the kernel's `q`
  is defined from the *normalized* distances, so it is itself scale-correct;
  no `sqrt(1-R0^2)` is used anywhere.
* **Area/sector terms scale as required.** In normalized units the kernel's
  `R0^2 u v sin(alpha)/2 + (w - sin w)/2` is exactly the area of the normalized
  wedge; at `alpha = pi` the first term is `0` and the sector contribution is
  `(w - sin w)/2`, matching the degenerate geometry (`L = T = 0`, triangular
  part `0`).
* **Kernel domain includes the point.** The ring factor's box is
  `alpha in [0,pi], u in [0,1], v in [0,1]` (code lines 8, 68, 108); the
  degenerate point `(pi, t, t)` is in this box. The certificate's `q`-filter
  (line 83) discards a box only when its whole `q`-interval lies below
  `qmin = 4 sin^2(pi - 8 asin R0)/R0^2`; at the degenerate point
  `q = (u-v)^2 + 4uv sin^2(alpha/2) = 4t^2 >= 4(75/76)^2 = 3.895...`, while
  `qmin = 0.01493566.../...` (= `4 sin^2(0.0232223)/0.1444 = 0.014936`), so the
  point is retained and never falsely discarded. **The qmin filter does not
  remove the degenerate corner.** (False-exclusion risk only arises if `qmin`
  were re-derived from `1 - R0^2`-type bounds; it is not.)
* **The derivative guard is scale-free.** `L = R/sqrt(1-R^2)` (line 88) is used
  only as a Lipschitz bound for `dw/d(u,v,alpha)`; the code's comment states
  `|w_a|, |w_u|, |w_v| <= R/sqrt(1-R^2)` for the kernel's normalized `w`, which
  is the exact derivative bound of `w = 2 asin(R sqrt(q)/2)` w.r.t. normalized
  distances, at any scale; it does not encode a center-norm restriction. The
  `den = sqrt(1 - R^2 q/4)` factor is likewise the derivative factor of the same
  `asin`, valid wherever `R sqrt(q)/2 <= 1`; for the degenerate point
  `R0 sqrt(q)/2 = t <= 1` (equality only at `r = R0`, the closed boundary).
* **Endpoint radius multipliers.** All copy multipliers of the endpoint
  radii (z[32:50], z[94:112]) are `<= 0.2436` in the stored certificate and the
  angle slacks are `0`; the factor is a valid upper bound for the relaxed
  primal set `u, v in [0,1]`, which contains the rescaled degenerate point.
  No multiplier is tied to `sqrt(1-R0^2)`.

## 3. What is NOT valid / what must be stated

1. **Do not claim the renormalization preserves a center-norm constraint at
   R0.** It does not: by (D) the center has actual norm `sqrt(1-r^2)`, so in
   units of `R0` its coordinate norm is `sqrt(1-r^2)/R0`, and for `r` close to
   `R0` this exceeds `sqrt(1-R0^2)` (indeed exceeds `1` when `r > R0` cannot
   happen, but `sqrt(1-r^2)/R0 > sqrt(1-R0^2)` whenever `r < R0`). This is
   harmless *only because the kernel never uses `|c| <= sqrt(1-R0^2)`*: the ring
   box is `u,v in [0,1]` (endpoint distances in units of `R0`), the width is
   `2 asin(R0 sqrt(q)/2)`, and the only radius inputs are `qmin` and the
   Lipschitz constant `L`. Any future edit that adds an "inward-root at R0" cut
   (e.g. asserting a bound `<= 1-R0^2` on the center coordinate norm as a domain
   restriction) would immediately exclude the degenerate corner and break the
   `r < R0` treatment. This is the one interface hazard.
2. **`u = v = 1` is the `r = R0` endpoint only.** The lead's note is right that
   the corner `u = v = 1` tests only `r = R0`; for `r < R0` the degenerate
   point sits at `t = r/R0 < 1`. The 1-D maximum must therefore be taken over
   the *segment* `t in [75/76, 1]`, and its sup need not be attained at an
   endpoint — a naive check of `t = 1` alone is not a proof (the note says
   this; confirmed here).
3. **The exclusion statement needs the case split.** To exclude `alpha = pi`
   for all `r in [3/8, 0.37999]` one needs `F_i(t) < pi` for every
   `t in [75/76, 1]`, *or* `total < pi` with the 1-D replacement in place for
   each possibly degenerate sector; a single value at `t = 1` gives no
   uniform statement.
4. **`q` is not `4t^2` for nearly degenerate but non-degenerate sectors.** The
   factor domain also contains small-`q` points with `alpha` near `pi` and
   `u != v`; those are excluded by `qmin` only if the *necessary* bound holds
   for them too, which it does (`w <= 2 asin r <= 2 asin R0`, so
   `q >= qmin` for every genuine configuration at every `r <= R0`). The
   filter's soundness is exactly this monotonicity argument, and it is
   scale-free.

## 4. Answer to the question posed

* Does any *factor validity* premise require the inward norm at `R0`?
  **No.** The kernel's premises are: `alpha in [0,pi]`; `u, v in [0,1]` as
  *endpoint* distances in units of `R0` (from `|endpoint distance| = r <= R0`);
  `q >= qmin` (from `w <= 2 asin r <= 2 asin R0`); and the Lipschitz bounds for
  `w` and `beta`. All are satisfied by the degenerate configuration. The
  inward-norm bound belongs to the *geometry proof* (C820 closure / containment)
  and is used there at the actual `r`; the closure identity itself is a
  statement about angles and lengths of the configuration and contains no `R0`
  norm constraint. Nothing is reloaded at `R0`.
* Does the renormalization break anything? **No**, provided (i) the degenerate
  point is treated on the segment `t in [75/76, 1]`, (ii) no new
  `1 - R0^2`-type center-norm cut is inserted, and (iii) `qmin`/`L` keep their
  current scale-free definitions.

## 5. Two exact statements for the record

```
   F_i(t) = (w - sin w)/2 - mu_i pi - (d_i+e_i) t^2 - (dl_i+el_i) t
            + lambda w + (hl_i + hr_i) w/2 ,      w = 2 asin(R0 t) ,  t in [75/76,1] .
   q(alpha=pi, u=v=t) = 4 t^2 >= 4 (75/76)^2 = 3.895... > qmin = 0.014936... .
```

Both follow from the geometry (D) and the kernel's definitions; they are the
exact interface the certificate needs.

Evidence: this note; `lead/certify_q0_closure.py` lines 8, 67-75, 79-108 (ring
factor domain, qmin filter, `L`, `den`); stored multipliers
`lead/q0_closure_dual_0_3.json` `z`.
