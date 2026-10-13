# RELATIVE-BASIS-AUDIT — source audit of the C920 basis-transport certificate

**Lane**: r20-gluing (cline2-r23-gluing), sole writer here. Read-only audit of
`lead/RELATIVE-STRESS-BASIS.md` (C920) and `lead/certify_relative_stress_ball.py`; lead files
untouched, **no numeric re-run**, no claim, no sub-agent. The reported constants are recorded, not
recomputed.

## 1. The transport lemma — verified analytically

`C919` uses exactly: (i) `BN = 0` (including normalization), (ii) `G = T₈N`, (iii) certified norms of
`N`, the anchor-flux map `A`, `G`, and the PSD margin of `H₀ + 2τ₀GGᵀ`. For **any fixed** `4×4` `R`:

* `B N' = B(NR) = (BN)R = 0` ✔ and `1ᵀN' = (1ᵀN)R = 0` ✔ (linearity in the second slot only);
* `G' = T₈N' = T₈NR = GR` ✔ (definitional);
* shapes: `N' : 45×4`, `G' : 8×4`, `(G')ᵀx ∈ ℝ⁴`, `A' : 18×4` — same as before, so `Q' = τN'(G')ᵀx`
  is a `45`-vector of weight increments with `1ᵀQ' = 0` ✔ (normalisation preserved);
* the adaptive gain identity is *instanced*, not modified: applying C919 to the family `N'` gives
  `2⟨M'x,v⟩ = τxᵀG'G'ᵀx = τ‖(G')ᵀx‖²` ✔.
**No premise is missing.** In particular `R` need not be SPD, invertible or whitening; nothing
spectral about it is used, only that it is a *fixed constant* of the certificate. The two quantities
that *must* be re-certified in the new basis are exactly the ones the note re-certifies: `B` and the
norm/PSD data; and `C_cross` is correctly **unchanged**, because `Cmat = J₈ᵀ(Λ0⊗I₂)Rad₈` is built from
chart objects (`J₈`, `Rad₈`, the base Schur form `Λ0`) and does not involve `N` at all ✔.

## 2. Source checks against the lead's four questions

**(a) float → interval, exact dyadic.** `R = iv.matrix(proposal['R'])` converts the JSON floats through
the shared kernel's interval constructor, and the note pins reproducibility by `basis_R_floathex`. Two
audit points (checks, not defects): `iv.mpf(float)` reproduces the float's exact binary value only if
the kernel's working precision is at least 53 bits — worth confirming once in the kernel — and the
certificate is then about *that* dyadic `R`, never about the idealised
`(Nᵀdiag(α⁻²)N)^{−1/2}` (the note says so explicitly, so the scope is honest) ✔.

**(b) `H` is base-unchanged.** Line 9 reads `H` from the base object (`k.H`), it is **not** rebuilt from
`NN`; only `G = k.G8*R` is transformed. This is the correct behaviour: `H₀` is the angular Hessian of
the *base* stress and the pinned chart, so it is basis-independent, and the new PSD condition
`H + 2τ₀G'G'ᵀ ⪰ μI` is exactly the C919 condition with the transported `G'` ✔.

**(c) the flux uses `NN` in every term.** Line 12 allocates `flux` as `18×4` and line 18 accumulates
`flux[2·node+c, j] += sgn·NN[e, j]·dd[c]`, i.e. `A' = AR` is built from `NN = N·R` throughout (no
mixture of `N` and `N'`); line 19's `B = max_e ‖NN_e‖/α_e` likewise uses `NN` and the **base** weights
`α` (correct: the β-bound divides by the base stress) ✔.

**(d) premises of the proposal.** The design `R ≈ (Nᵀdiag(α⁻²)N)^{−1/2}` is only a *proposal*; the
certificate consumes the pinned dyadic `R` and re-checks everything that C919 needs. The remaining
hypotheses are the two smallness conditions, both asserted at the end of the script:
`τ·B·‖G'‖·ρ < 1` (which gives `β < 1` on the ball, hence positive weights) and
`μ/2 − C_cross·ρ − Q₄ρ² > 1e-5` ✔. One interpretive point worth recording: the basis change does
**not** change the shape of the certified region — the ball is still `‖x‖ ≤ ρ` in the same raw-8 chart;
what improves is the *stress parameterisation* (the family is rescaled to match the `α`-metric), which
shrinks `B` and the quartic coefficient. So "relative metric" here means a relative *basis*, not a
relative *ball* ✔.

## 3. Interval certification of the PSD margin — and the Gershgorin honesty

The script forms `base = H + 2τ₀G'G'ᵀ − μI`, takes a numeric Cholesky of its midpoint, uses
`C = chol⁻ᵀ` as a fixed constant congruence, and interval-verifies `Cᵀ(base)C ⪰ 0` by a
Gershgorin-type test. This is sound: `C` is invertible by construction, so `Cᵀ(base)C ⪰ 0 ⇒ base ⪰ 0`
(for `x ≠ 0`, `xᵀ(base)x = yᵀ(Cᵀ(base)C)y` with `y = C⁻¹x ≠ 0`). The note's remark on the failed
`μ = .00199` attempt is the right reading: an interval test that cannot close is a **certification-width
limit**, not a witness that the Hessian has an eigenvalue below `.00199`; conversely the accepted
`μ = .0018` is not a claim that the true margin is at least `.0018 + width` — the *certified* statement
is exactly the interval conclusion. Both directions are stated correctly in the note.

## 4. Recorded constants (from the note; values not recomputed here)

`τ = 1468`, `τ₀ = 734`, `μ = .0018`, `B = .495`, `A = .00858`, `Gnorm = .015363`,
`Ccross = .0358` (unchanged from the previous certificate — expected, see §1),
`d = .08`, `ρ = .01458`, growth `> 1e-5`; scope: local raw-8 ball at the exact C891 root, not global.
Recorded consequence: with `ρ = .01458` the ball now contains `q ≈ .01` (the stated target), whereas the
previous `ρ` was `.00764`; the quartic coefficient drops from `≈12.25` to `d/3 + τ²(Bd+‖A‖)²/(4(τ−τ₀))
≈ .0267 + 1.705 ≈ 1.73`, so at this radius the cubic term (`C_crossρ ≈ 5.2e-4`) and the quartic term
(`≈ 3.7e-4`) are now comparable, and the margin (`≈ 1.0e-5`) is consistent with the two assertions in
the script. These are readings of exported numbers, not certified results of this audit.

## 5. Verdict

The C920 transport is correct and premise-complete for any fixed `R`; the source performs exactly the
three checks the lemma needs (base `H`, transported `G'` via `GR`, `NN`-based flux and `B`), pins `R` by
floathex, and states the certification-width caveat honestly. The only open items are the two
confirmation checks of §2(a) (kernel precision ⇒ exact float representation; certificate scope = the
pinned dyadic `R`), neither of which is a defect. **This audit certifies no constant and makes no global
statement.**
