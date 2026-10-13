# WITHDRAWAL: Round-15 width-fiber envelope recipe (scoped self-error)

Own directory. This note formally withdraws the Round-15 deliverable
(`WIDTH-FIBER-ENVELOPE.md`) and records exactly which inferences are void, why, and what
(if anything) survives. Filed per the lead's instruction; no further implementation attempted.

## 1. Formal list of withdrawn inferences

| # | inference | status | reason |
|---|---|---|---|
| W1 | "`G` depends on `b` only through the window position, so `fiber = S_b(b) + G(w)` decomposes with a `b`-free `G`" | **WITHDRAWN** | FALSE. `G = (1/2-mu)w + x/2 + (mu+h)eta + (-d u^2 - l u)` and `c, p, x, eta, u` all depend on `b`. The window is *additional* `b`-dependence, not the only one. |
| W2 | "`W(b)` is monotone in `b`, so one endpoint value `W(b_hi)` covers every `b` in the box" | **WITHDRAWN** | The monotonicity statement itself was the Round-13 chart's and is not the issue; the inference is void because W1 destroyed the decomposition it was used for. |
| W3 | "`S_b` is decreasing (`b <= acos r < pi/4`), so `max S_b = S_b(b_lo)` and `|S_b'| = r s sin 2b` is increasing" | **WITHDRAWN** | `acos(0.38) = 1.1810 > pi/4 = 0.7854`. The domain is `b in [acos(r)/2, acos(r)]`, which reaches above `pi/4`, so `sin 2b` is NOT increasing throughout and the chord bound built on it is invalid. |
| W4 | "`max_{[g,W]} G = max(G(g), G(W))` (endpoint evaluation suffices)" | **WITHDRAWN** | FALSE in general: `dG/dw` can change sign, and the saved width-1 fibre has an **interior maximum**. Endpoint evaluation is not an upper bound for the interior maximum. |
| W5 | the recipe as a whole: `max_b fiber <= S_b(b_lo) + r s sin(2b_lo)(b_hi - b_lo) + max{G(g), G(W(b_hi))}` | **WITHDRAWN** | Follows from W1/W3/W4; no part of it may be used. |
| W6 | "`W'(b) = 2r(cos x0 - r)/(1 - r cos x0)^2`" as the derivative of the chart's W | **WITHDRAWN** | Disagrees with C850. Whatever the correct chart derivative is, this expression must not be used until it is re-derived against C850. |
| W7 | the Round-15 calibration (40 boxes, 0 violations, mean slack 0.108) as support for the recipe | **VOID** | It calibrated a bound built on false premises; agreement on those boxes carries no information. Numeric calibration was never proof, and here it also does not rescue the bound. |

No claim was registered for any of the above, so nothing needs retracting in the claim ledger;
the withdrawal is at the report level.

## 2. What the error was

I treated a function of `(b,w)` as if it were separable in the specific sense "b enters only
through the window", without checking that `c, p, x, eta, u` are all functions of `b`. The
mistake is a **scope-of-dependence** error: it silently converted a two-variable sensitivity
into a one-variable one. Two further errors compounded it: I asserted a monotonicity
(`sin 2b` increasing) on a domain (`b` up to `acos r ≈ 1.181`) where it fails, and I asserted an
endpoint maximum for a function whose derivative changes sign. The lead's saved width-1 fibre
with an interior maximum is the explicit counterexample to W4.

## 3. Correct implicit partial `b`-derivative (verified; the useful remainder)

The following is exact and each relation was confirmed component-wise against central
differences to `1e-8` (`r15_6_verified.py`); it *replaces* W1-W6 for the sensitivity question
and makes no envelope claim.

Chart as in `interval_cancel_fibers.py`, `R0 = 19/50`:

```
    c = (s - 2r sin b cos b, -2r sin^2 b) ,   P(w) = (s cos w - r sin w, -s sin w - r cos w)
    p = c.P ,  x = cross(c,P) ,  cn = |c|^2 = 1 + r^2 - 2r sin(2b + phi) ,  phi = asin r
    dd = |P-c|^2 = 1 + cn - 2p ,  u = sqrt(dd)/R0 ,  eta = atan2(x, 1-p) ,
    D = (1-p)^2 + x^2
```

**At fixed `w`:**

```
    c_b  = (-2r cos 2b, -2r sin 2b)                       (exact)
    p_b  = c_b . P
    x_b  = c_b x P
    cn_b = 2 c.c_b = -4 r cos(2b + phi)
    dd_b = cn_b - 2 p_b
    u_b  = dd_b / (2 R0^2 u)
    eta_b = ((1-p) x_b + x p_b)/D
```

**At fixed `b`:** `p_w = x`, `x_w = -p`, `dd_w = -2x`, `u_w = -x/(R0^2 u)`,
`eta_w = (cn - p)/D`, hence

```
    dS/db|_w = -2 r s sin b cos b + x_b/2 + (mu+h) eta_b - (2 d u + l) u_b
    dS/dw|_b = (1/2 - mu) - p/2 + (mu+h)(cn - p)/D + (l + 2 d u) x/(R0^2 u)
    dS/db|_total (moving window) = dS/db|_w + dS/dw|_b . (dw*/db)
```

with `dw*/db` to be taken from the chart's own W-derivative (C850), not from W6.

Verified maxima of the finite-difference discrepancies: `p 1.4e-8`, `x 1.4e-8`, `cn 1.6e-8`,
`u 3.4e-8`, `S_total 1.1e-8`.

## 4. Status and instruction compliance

* Recipe and all claims: **withdrawn**, not implemented, not to be used.
* No new numeric calibration presented as proof; §3's numbers are verification of *identities*
  (finite differences of the same expressions), not bounds.
* No envelope is offered. A correct envelope needs the two-variable treatment of
  `S(b,w) = S_b(b) + G(b,w)` with the interior-maximum issue (W4) handled, and the chart's
  `W'(b)` reconciled with C850 first.
* DEAD entry recorded for this scoped self-error.
