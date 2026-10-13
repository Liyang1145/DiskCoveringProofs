> **STATUS: INVALID — WITHDRAWN. DO NOT USE. NO DERIVED CLAIM IS OFFERED.**
> This file is retained only as a record of a withdrawn attempt.  The lead has rejected its
> report and will not use any claim from it.  **Every statement from section 1 onward is
> withdrawn in full**, including the chord bound (B1), the "global bound" (B2), the "sharp
> form" (B3), the requirement statement of section 2, the gap description of section 3 and
> the quantifier list of section 4.
>
> ## Concrete errors (lead-identified; recorded as the reason for withdrawal)
>
> 1. **Wrong algebra for the chord.**  I wrote `(M ell_i)^2 = gamma_prev^2 + gamma_i^2
>    - 2 gamma_prev gamma_i cos alpha_i`.  The correct relation is
>    `ell_i^2 = gamma_prev^2 + gamma_i^2 - 2 gamma_prev gamma_i cos alpha_i` — there is no
>    factor `M` on the left.  The monotonicity claim and the box maximum are consequently
>    wrong: the partial derivative `2u - 2v cos alpha` **can be negative** (e.g.
>    `u = .1, v = 1, alpha = .2`).  The correct box maximum of `ell_i` over
>    `gamma_prev, gamma_i in [0, M]` is `ell_i <= M * max(1, 2 sin(alpha_i/2))`, obtained by
>    separate convexity / corner enumeration — **not** `M ell_i <= 2 sin(alpha_i/2)`.
> 2. **Misreading of `M = 1`.**  `M = 1` means only `gamma_f <= 1` for all f with root
>    `gamma_0 = 1`.  It does **not** mean all `gamma_f = 1`, nor that all sine-law ratios
>    equal 1.  The `M = 1` reduction in section 3 collapses on this error.
> 3. **Wrong collapse of the circle system.**  From `sum_i w_i = 2 pi` and `q_i = R s_i` one
>    gets `sum_i 2 asin(R s_i / 2) = 2 pi`, **not** `R = sum_i s_i / (2 pi)`.  The scalar
>    reduction is invalid.
> 4. **Wrong target.**  The target `R >= .38` is **FALSE**, by the already certified cover
>    with `R < .37999`.  The human target is the sharp optimum `~.379983853`, not `.38`.
> 5. **Wrong status for the number.**  `.379983853119838733` is a rounded float, **not** a new
>    certified value, and may not be quoted as one.
>
> Consequence: this file established no proved identity and no proved bound.  Per instruction,
> no further exploration or numeric runs were performed, and no replacement claim is made.

---

# cline2-coupled-factors — [WITHDRAWN] analytic mechanism for the angle-only model (round 4b)

*(everything below is withdrawn; kept only for the record of the error)*

Scope: the C839 angle-only exact model (lead/ANGLE-ONLY-EXACT-MODEL.md): 20 branch radii
`gamma_f` eliminated by the sine-law recursion, objective `R_shape = M q_0/ell_0` with
`M = max_f gamma_f`; 42 angles, 13 linear equalities, 2 sine-product cycle equations (the
six circle equations are the identifications `q_i/ell_i = q_0/ell_0`, imposed by
construction). No claims registered here; this is one analytic mechanism plus the exact gap.

## 1. The mechanism [WITHDRAWN - error 1: wrong chord algebra, wrong box maximum]

Write `q_i = 2 sin(w_i/2)` for the switch chords and let `alpha_i` be the sector angle.
Put

    s_i := 2 sin(alpha_i/2).

**(B1) Chord bound.** `M ell_i <= s_i` for every i = 0..8.

*Proof.* `ell_i` is the distance between the two sector endpoints in the root gauge, i.e.
the third side of a triangle whose other two sides are `gamma_{i-1}/M` and `gamma_i/M`
(both `<= 1`) with included angle `alpha_i`.  By the law of cosines,

    (M ell_i)^2 = gamma_{i-1}^2 + gamma_i^2 - 2 gamma_{i-1} gamma_i cos alpha_i,

which is increasing in each of `gamma_{i-1}, gamma_i` on `[0, M]` (the derivative
`2 gamma - 2 gamma_other cos alpha_i >= 0` because `cos alpha_i < 1`).  Its maximum on
`[0,M]^2` is at `gamma_{i-1} = gamma_i = M`, i.e. `(2 sin(alpha_i/2))^2 = s_i^2`.  [] 
Equality holds iff both endpoint branches attain `M` simultaneously.

**(B2) Global lower bound.** `R_shape >= M^2 min_{i} (q_i/s_i) >= min_i (q_i/s_i)`,
the second inequality because `M >= 1` (a maximum of 20 branches one of which is the root).

*Proof.* `R_shape = M q_i/ell_i` for every i (the model's own identity, valid for all i
because the six circle equations force all `q_i/ell_i` equal).  By (B1),
`ell_i <= s_i/M`, so `q_i/ell_i >= M q_i/s_i`, hence `R_shape >= M^2 q_i/s_i` for every i,
and taking the minimum over i gives the claim.  []

This is the requested global mechanism: it is a single scalar inequality, it holds for
every legal shape, and it uses only the chord geometry and `M >= 1`.  It is a *product-type*
or per-sector bound depending on which of the two forms one takes; both are valid and
neither is claimed to be exhaustive.

**(B3) Invariance and sharp form.** Applying the bound sector by sector and multiplying
(the weights cancel because all `q_i/s_i = q_0/s_0` on the legal set) gives the equivalent
weighted form

    R_shape >= M^2 q_i/s_i   for every i,   and   R_shape >= M^2 (prod_i q_i/s_i)^{1/9}.

## 2. Requirement statement [WITHDRAWN - error 4: target .38 is false]

At the saved candidate the numbers are `M = 1`, `min_i (0.38 s_i/q_i) = 1.0000137527`,
`R = 0.3799838531198`.  So (B2) yields

    R >= min_i (q_i/s_i) = R_candidate / 1  = 0.37998385  --  short of 0.38 by 1.6e-5.

Since `M >= 1` is the only input, the bound saturates at the candidate's own value.  To
reach 0.38 the mechanism needs strictly more, and the exact missing statement is:

    (M)   for every legal shape,   M^2 min_i (q_i/s_i) >= 0.38,
          equivalently  M >= sqrt(0.38 / min_i(q_i/s_i)).

`M >= 1` alone cannot deliver (M): it would require `min_i(q_i/s_i) >= 0.38`, which is
false at the candidate (`0.37998385 < 0.38`).

## 3. Gap description [WITHDRAWN - errors 2 and 3]

The cycle equations do not supply the missing factor, and this is structural rather than a
limitation of effort:

* The two non-tree sine-product equations are `D_k = sum of signed log-sine ratios around
  the cycle = 0`.  The non-unit ratios occur in exactly cancelling +/- pairs: the observed
  values are four of `+3.038114e-3` and two of `-3.038114e-3` (plus one
  `+/-3.038111e-3` pair), so each cycle's `D_k` vanishes by pairwise cancellation.
* Equivalently: on the manifold `M = 1` one has `M ell_i = s_i` for all i (both chord
  endpoints attain the maximum), hence `q_i/ell_i = q_i/s_i` for all i, and the six circle
  equations reduce to the single scalar relation

        q_i = R s_i,  i.e.  2 sin(w_i/2) = R * 2 sin(alpha_i/2)  for all i,

  with `R = sum_i s_i / 2pi` after using `sum_i w_i = 2pi`.  In this regime the cycle
  residuals vanish identically (all ratios equal 1), so the two nonlinear cycle equations
  are automatically consistent with `M = 1`.

Consequently the angle-only model plus (B1) contains shapes with `M = 1` and
`R_shape < 0.38`; the mechanism of section 1 therefore cannot prove `R >= 0.38`, and no
re-weighting or re-averaging of `q_i/ell_i` can, since they all evaluate to the same
scalar at any legal shape.

**What would close it.** A statement outside (B1)-(B3), of one of these two shapes:
(i) a uniform bound `M >= 1 + delta(shape)` with `delta` positive and controlled by the
angles, coming from the sine-law recursion around the ring (the log-sine structure
`log gamma_g - log gamma_f = log sin a_fg - log sin a_gf`), not from the cycle products;
or (ii) a direct upper bound `sum_i 2 sin(alpha_i/2) < 0.38 * 2 pi / 1` on the `M = 1`
family, which needs an upper bound on `sum_i b_i` (equivalently `sum_i alpha_i`) that the
angle-only model alone does not contain.

## 4. Quantifiers [WITHDRAWN with the rest]

* (B1): `forall` legal shapes, `forall i = 0..8`.  Equality iff `gamma_{i-1} = gamma_i = M`.
* (B2): `forall` legal shapes.  No uniformity or compactness assumption; it is pointwise.
* Section 3's `M = 1` reduction: an identity on the submanifold, used to exhibit that the
  bound is not sufficient; it is not a claim about the global minimizer.
* No new exclusion, no radius improvement, no claim registered.  `0.38` appears only as the
  target the mechanism must reach; `R_cert` remains the certified numeric value.

## 5. Files [diagnostics only, not structural evidence]

Analytic derivation: this file.  Supporting numeric readings already obtained (NOT to be
reused as structural evidence per the lead): `out/g1_structure.json`, `out/g3_constants.json`,
`g7_cycle_products.py` output, `out/g8.log`.  No new numeric runs were made for this text.
