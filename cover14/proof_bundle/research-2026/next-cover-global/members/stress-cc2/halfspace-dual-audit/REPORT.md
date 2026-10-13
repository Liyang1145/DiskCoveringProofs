# Audit: halfspace-dual angle box (`q10-halfspace-angle-dual`) — C1371

Scope: `members/stress-cc2/halfspace-dual-audit/` only; read-only on `lead/`; no new agents.
Object: `lead/q10_halfspace_angle_dual.py/.json` (certificate) and
`lead/q10_halfspace_angle_dual_replay.py/.json` (lead's replay). Audited:

1. the analytic sign structure of the dual inequality,
2. the nonnegativity rows and the "x ≥ 0" requirement,
3. an independent replay of all 20 stored rational certificates,
4. the gauge identities (mean-zero) and the affine-angle/evaluation formula,
5. the exact L / π dependency, and
6. the inherited items (`identify inherited constants / halfspace necessity`).

**Verdict: sound.** All five analytic checks hold and my independent replay reproduces the certificate
exactly, including the headline value `0.004244852968770073 < 0.005`. The halfspace **necessity**, the
**θ0 reference**, and the **exact directed bounds on `L` and `π`** are inherited (named in §5–§6) and
were not re-verified here — for `L`/`π` this audit supplies only a 60 dps numeric-consistency check, not
a certified bracketing.

## 1. The dual inequality and its sign structure — valid

Object: the domain is the affine intersection `P = {x : N x >= b, sum x = 1}` with `N` the 128 stored
rational halfspaces (10 variables; the encoding `[10r, 0, -r] -> r` was checked) and, among them, the
ten rows `x_j >= 0` (see §2). For `y <= 0`, `lam` free of sign, `e := c - y N - lam*1`:

    c.x = y.(N x) + lam*(sum x) + e.x  <=  y.b + lam + max_i e_i .

Verified term by term:
* `y.(N x) <= y.b`: `y_k <= 0` and `(N x)_k - b_k >= 0` give `y_k ((N x)_k - b_k) <= 0`; the code
  enforces `y <= 0` by `y_k := min(0, marginal_k)` (float marginal truncated to 16 digits, so the
  *stored* `y` is rational and nonpositive).
* `lam * sum x = lam`: the stored equality `sum x = 1` (checked: `equality = ([1]*10, 1)`).
* `e.x <= max_i e_i`: needs `x >= 0` with `sum x = 1` (a weighted average); this is exactly why the ten
  nonnegativity rows must be present in `N` (§2). Using the nonnegativity *rows* in the `y.(Nx)` term and
  the *fact* `x >= 0` in the last step is not double counting: the chain is an identity first, then two
  one-sided estimates on different terms.
* **No optimality premise is used.** The identity/inequality is valid for *any* rational `y <= 0` and
  `lam`; the LP is only a heuristic for finding them, and the residual `max_i e_i` is what makes the
  bound self-correcting. The claim's "no numerical optimality premise" is therefore accurate, and the
  stored bound is verified as an identity below.

## 2. Nonnegativity rows — present, and used exactly once

`x_j >= 0` is among the stored halfspaces with rhs 0 for all `j = 0..9` (checked directly from
`q10-c1366-domain.json`): the ten rows `(e_j, 0)` occur in `N`, so any `x in P` satisfies `x >= 0`, and
the hypothesis "sum x = 1 and all 128 inequalities" therefore *implies* `x >= 0`. The producer passes
`bounds = (None, None)^10` to the float LP, which is consistent because nonnegativity is carried by the
halfspaces; no slack from an undeclared box bound enters.

## 3. Independent replay of all 20 rational certificates — exact

`logs/halfspace_dual_audit.txt`, `evidence/halfspace_dual_audit.json`
(`py/audit_halfspace_dual.py`; own code path, exact `Fraction` arithmetic, no scipy, no producer import
beyond the shared constants module).

For every `(anchor j, sign s)` pair (20 certificates) I rebuild
`c_i = s*((9-i)/10 - [i < j])`, take the *stored* rational multipliers `y <= 0` and `lam`, recompute
`residual_i = c_i - sum_k y_k N_ki - lam` and `bound = y.b + lam + max_i residual_i`:

* `bound` equals the stored `upper` **exactly** for all 20 certificates;
* the worst `|max residual|` over the 20 is `1.0e-16` (so the residual is negligible but not assumed to
  vanish — it is charged);
* `y <= 0` holds for all 20, row indices are distinct, and the number of active multipliers is 9 per
  certificate;
* as pure *test points* (no completeness premise), the inequality `c.x <= bound` holds on all 896
  decoded stored vertices, with `max (c.x - bound) = 0`.

## 4. Gauge identities and the affine/evaluation formula — valid

* `sum_i c_i = 45/10 - j = 4.5 - j` for every `j` (checked).
* `sum_j (the coefficient of x_i) = sum_j ((9-i)/10 - [i < j]) = (9-i) - (9-i) = 0` for every `i`
  (checked). This is the **mean gauge**: with `theta_j - mean(theta) = (j - 4.5) L + D * sum_i c_i x_i`
  (re-derived from the caliber's `theta_j = jL - D sum_{i<j} x_i`, `D = 10L - 2 pi`), it gives
  `sum_j (theta_j - mean theta) = 0` (the base part sums to `sum_j (j-4.5) = 0` and the `x`-part sums to
  `D sum_i x_i * 0 = 0`). So the box is stated in the mean-zero gauge required by C1370's caliber.
* The displacement `(j-4.5)L + D s - (ref_j - mean ref)` is affine in each of `s := c.x`, `L`, `pi`
  separately, hence **multi-affine**, so its extrema on the Cartesian box `(s, L, pi)` are attained at
  the `2 x 4 = 8` corners. Two *different* outer evaluations are in play and both are valid: the
  lead's replay (and my evaluation below) enumerates the 8 corners literally; the producer instead
  sums the interval products over `[slo,shi] x [L_lo,L_hi] x [pi_lo,pi_hi]` with `min`/`max` — a
  coarser but equally valid outer bound, not literally the corners. My evaluation over the 8 corners
  gives per-anchor corridors **identical** to `q10-halfspace-angle-dual-replay.json`, and

      max over the 20 x 8 corner evaluations of |displacement| = 0.004244852968770073  (< 0.005),

  attained at production anchor 4, lower end. Since `slo <= c.x <= shi` holds for **every** `x in P` by
  the dual bounds of §3, this corridor contains the displacement of every point of the halfspace
  intersection — the vertex list is not used as a completeness premise anywhere.

## 5. Exact L / pi dependency — directed, and used only as outer bounds

* `fr.L = [L_lo, L_hi]`, width `L_hi - L_lo = 1e-45`, held by the constants module to bracket
  `2*asin(0.33173203427623414)`;
* `fr.pi = [pi_lo, pi_hi]`, width `pi_hi - pi_lo = 1e-45`, held by the constants module to bracket `pi`;
* **Status of this check (tightened per review):** the comparisons were run at 60 dps against
  `mpmath.asin` / `mpmath.pi`, so they establish only *numeric consistency* of the stored 45-digit
  pairs with the true constants (the printed values agree to every shown digit, and the script's
  printed "brackets ... True" lines are that consistency printout). They are **not** a certified
  bracketing or a direction proof: the exact directed bounds `L_lo <= 2asin(U) <= L_hi` and
  `pi_lo <= pi <= pi_hi` are **inherited** from the series/interval proof in
  `q11_chord_flow_fraction_replay`, which this audit did not re-derive;
* `D = 10L - 2 pi` is used through `(10 L_lo - 2 pi_hi, 10 L_hi - 2 pi_lo)`, verified `> 0`
  (`D = 0.4795943756928976...`); in the affine part `(j - 4.5) L` the interval `[L_lo, L_hi]` is used
  (and `min/max` over the corners), and `pi` appears only through `D` and the `+2 pi` lift of the
  reference for `j >= 3`. No other use of `L` or `pi` occurs.
* Consequence to record: the *values* of `L` and `pi` are taken from the shared constants module
  `q11_chord_flow_fraction_replay` (disclosed by the lead's replay as "constants module shared"); with
  the caveat above, this audit neither proves nor needs their exactness — it depends on the module's
  already-proved directed bounds, and only records that the certificate consumes them in the
  conservative directions.

## 6. Inherited items (named, not re-verified here)

* **Halfspace necessity** for full 879 covers (that every remaining 879 cover's normalized deficit
  vector satisfies the 128 stored halfspaces, including the ten nonnegativity rows). This is inherited
  from the C1366 domain construction and is *not* cut by this certificate; C1371's statement says so
  explicitly. My audit therefore proves containment for the *halfspace intersection*, not that the
  intersection contains the remaining covers.
* **θ0** (the saved rational reference) and its lift/relabeling (`j -> (j+2) mod 10`, `+2 pi` for
  `j >= 3`) come from the adaptive-flow artifact.
* **Constants** `U`, `L = 2asin(U)`, `pi` and the deficit parametrization (`gap_i = L - x_i D`,
  `D = 10L - 2 pi`) as above — in particular the *exact directed bounds* on `L` and `pi` (series proof
  in the shared constants module); §5 records only a 60 dps numeric-consistency check of those values,
  not a certified bracketing.
* The **C1355 entry** and the C1370 chain are downstream and were audited separately (C1370 review).
* Also inherited, not re-derived here: the domain file's affine encoding (scalar triples `[10r,0,-r]`,
  the simplex equality, and the 128 halfspace rows themselves).

## 7. Evidence and repro

```
py -3 -B research-2026/next-cover-global/members/stress-cc2/halfspace-dual-audit/py/audit_halfspace_dual.py
```
Outputs: `logs/halfspace_dual_audit.txt`, `evidence/halfspace_dual_audit.json`.
Cross-checked against `lead/q10-halfspace-angle-dual.json`,
`lead/q10-halfspace-angle-dual-replay.json`, `lead/q10-c1366-domain.json`,
`lead/q10-adaptive-flow-interval.json`, `lead/q11_chord_flow_fraction_replay.py` (constants only).

No global claim, and no claim about the covering optimum, follows from this file.

