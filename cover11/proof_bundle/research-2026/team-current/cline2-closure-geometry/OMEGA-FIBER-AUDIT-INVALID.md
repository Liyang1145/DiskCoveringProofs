LEAD CORRECTION: For cosX>=B, B>1 is EMPTY and B<−1 is ALL. The member correction below still reverses this. Do not use it. Reference lead/SECTOR-SCALE-FIBER.md only.

# ω-FIBER AUDIT — **INVALID** (superseded by `lead/SECTOR-SCALE-FIBER.md`)

Status: the file `OMEGA-FIBER-AUDIT.md` in this directory is **marked INVALID**
for use as bearing evidence. It contains reversed inequalities and dropped terms
(listed in §2 below). The lead's `SECTOR-SCALE-FIBER.md` proof stands
independently of it. No further runs.

## 1. Corrected statements (verified in `verify_corrections.py`)

**B-direction (was reversed in my report).** With
`B(rho) = cos alpha + 2 K^2 rho^2` and the constraint `cos(2 omega - alpha) >= B`:

```
  B > 1   :  the constraint holds for ALL omega (cos <= 1 <= B) — no information;
  B < -1  :  EMPTY (cos >= -1 > B);
  B = 1   :  theta = 0, forces 2 omega = alpha;
  B in (-1,1) :  |2 omega - alpha| <= theta,  theta = acos(B) ,
                 i.e. omega in [(alpha-theta)/2 , (alpha+theta)/2] .
```

My report had `B>1` as a bound and `B<−1` as "no lower bound" — both reversed.

**Merged fiber (keep the upper end).** The upper endpoint `(alpha+theta)/2` must
be retained:

```
  omega in [ max{0, (alpha-theta)/2, omega_qmin} ,
             min{ (alpha+theta)/2 , pi/2 , asin(K e^{-|d|}) , omega_E } ]
```

with `omega_E = atan2(sin alpha, E + cos alpha)` dropped when `E + cos alpha <= 0`
(and the whole branch empty when `E + cos alpha < 0`). My report omitted
`(alpha+theta)/2` from the merged minimum.

**`alpha = pi`, `d = 0` branch (my direction was wrong).** With `K = R0`:

```
  (C844')  : sin(pi-omega) = sin omega >= sin omega  — vacuous at E = 1.
  (L)      : cos(2omega - pi) = -cos(2 omega) >= -1 + 2 R0^2 rho^2
             <=> sin^2 omega <= R0^2 rho^2   <=>  omega >= asin(R0 rho)   (lower bound!)
  covering : sin omega <= K = R0   <=>  omega <= asin(R0)
  =>  omega in [ asin(R0 rho) , asin(R0) ] ,
      numerically [0.3844, 0.3898] at rho = 75/76 and [0.3898, 0.3898] at rho = 1 .
```

My report asserted `s <= rho` and `omega -> pi/2`; the correct statement is
`s >= rho` with `s in [rho, 1]` (equivalently `omega in [asin(R0 rho), asin(R0)]`).
Verified: at `omega = 0.3`, `s = 0.7777 < rho` violates `(L)` while covering holds;
at `omega = 0.45`, `s = 1.1446 > 1` violates covering while `(L)` holds.

**Norm caliber (my error).** The correct, `rho`-independent bound is
`|c| <= sqrt(55)/8 = 0.927024810...` (ratio `sqrt(55)/8` from `|c| <= sqrt(1-r^2)`,
`r <= 19/50`); the sharper `sqrt(2139)/50 = 0.924986486...` follows only if one
uses `r <= 19/50` and **does not** transfer to `r >= 3/8`; the lead's point is
that `r >= .375` does not imply `rho >= .38`, so I must not build a bound on the
`r = 19/50` evaluation alone. Use `|c| <= sqrt(55)/8`.

**`|d|` bound (my error).** The bound `|d| <= 0.5536` came from the removed
`s_min <= s_max` nonemptiness argument and is **unsupported**. The elementary
bound from `u, v >= 0.19` is

```
  |d| = (1/2) |ln(u/v)| <= (1/2) ln(1/0.19) = 0.830365603... .
```

**Nonemptiness.** Empty fibers are necessary and allowed; there is no requirement
that `(Omega)` be nonempty for every `(alpha,d)`, and I do not claim it.

## 2. The invalidated items (for the record)

1. Reversed `B`-direction (was: `B>1` gives a bound, `B<−1` nothing).
2. Dropped `(alpha+theta)/2` from the merged upper end.
3. `alpha = pi, d = 0`: wrong sign (`s <= rho`, `omega -> pi/2`) — correct is
   `s >= rho`, `omega in [asin(R0 rho), asin(R0)]`.
4. `|c| <= sqrt(2139)/50` promoted to a general bound (valid only at the
   `r = 19/50` evaluation, and misused in the `r >= 3/8` regime) — use
   `sqrt(55)/8`.
5. `|d| <= 0.5536` unsupported — use `0.8303656...`.

## 3. What was correct (still usable as a check, not as bearing evidence)

* The three equivalences `(ω1), (ω2), (ω3)` and the identity
  `sin(omega) sin(alpha-omega) = (cos(2omega-alpha) - cos alpha)/2`.
* `sin(omega_E) = sin alpha / sqrt(sin^2 alpha + (E+cos alpha)^2)`.
* The endpoint lower bound `p, q >= 1 - sqrt(55)/8` and its exact comparison
  `sqrt(55) < 8(1 - (19/50)(19/100))` giving `u, v > 19/100`; the `|d|` bound
  `(1/2) ln(1/0.19) = 0.830366` follows from it.
* `omega_E` and `omega_cov` are independent upper bounds (verified
  independently of the reversed-direction error).

## 4. Files

`verify_corrections.py` (this turn's checks); `verify_U.py`, `verify_U2.py`,
`verify_bounds.py`, `verify_endpoint_bound.py`, `audit_omega.py` (earlier runs;
their residual content is superseded where it conflicts with §1).
