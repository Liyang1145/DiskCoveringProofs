# ANISOTROPIC-LEAD-AUDIT — independent check of `lead/ANISOTROPIC-STRESS-REMAINDER.md`

**Lane**: r20-gluing (cline2-r23-gluing), sole writer here. Read-only audit of the lead's note
(`certify_anisotropic_stress_ball.py` is running; lead files untouched). **No claim, no sub-agent.** I
re-derived the algebra from scratch and did **not** reuse my earlier (retracted) assembly.

## 1. What I verified step by step

**Directional losses.** `β(x) := max_e |(Qx)_e|/α_e` with `Q = τNG₈ᵀ`: per row
`|(Qx)_e| = τ|⟨N_e, G₈ᵀx⟩| ≤ τ‖N_e‖·p`, so with `B = max_e‖N_e‖/α_e`, `β(x) ≤ τBp` ✔ (Cauchy–Schwarz,
direction correct). `Mx = A(G₈ᵀx)` gives `‖Mx‖ ≤ τ‖A‖p` ✔. Both bounds are **proportional to `p`**, hence
vanish on the critical kernel `G₈ᵀx = 0` — exactly what the uniform `bq`, `mq` could not do ✔.

**(A′)-type remainder, both signs.** `R_i := U_i(x) − U_i − v_i + ½x_i²U_i = w_i + ½x_i²U0_i`, and the
integral identity gives `|R_i| ≤ |x_i|³/6`, hence `‖R‖_F ≤ q³/6` — **valid for both signs of `x_i`**
(the bound uses `|x_i|`, the integrand `|U(t)−U0_i| ≤ |t|`) ✔.

**Full-tensor cubic, no diagonal guess.** `w = −½·Rad₈(x^{(2)}) + R`, so
`2⟨v,Λ0w⟩ = −xᵀCmat x^{(2)} + 2⟨v,Λ0R⟩` with `Cmat = J₈ᵀ(Λ0⊗I₂)Rad₈`; expanding indices gives
`xᵀCmatx^{(2)} = Σ_{ij}(Λ0)_{ij}x_jx_i²⟨t_j,U_i⟩` — the **double sum** (`Λ0` symmetric), whose
diagonal `i = j` vanishes (`⟨t_i,U_i⟩ = 0`) but whose off-diagonal does **not** ✔. Bound:
`|xᵀCmatx^{(2)}| ≤ C_cross·‖x‖·‖x^{(2)}‖ ≤ C_cross q³` with `C_cross = ‖Cmat‖_op` and
`‖x^{(2)}‖ = (Σx_i⁴)^{1/2} ≤ q²` ✔. Then `|2⟨v,Λ0R⟩| ≤ 2q·d·(q³/6) = (d/3)q⁴` ✔, so
`2⟨v,Λ0w⟩ ≥ −C_crossq³ − (d/3)q⁴` — **the direction is the lower one**, as required ✔.

**Variational comparison.** `δᵀΛ_αδ ≥ (1−β(x))δᵀΛ0δ` (unchanged mechanism), and with `Λ0 ⪯ dI`,
`‖δ‖ ≤ q`: `βδᵀΛ0δ ≤ βdq² ≤ τBdpq²` ✔ — note the β multiplies the **current** Dirichlet form
`δᵀΛ0δ`, not `⟨v,Λ0v⟩`; using the separate lower bound for the two pieces is still sound (both are
lower bounds) ✔. Adaptive remainder: `2⟨Mx,w⟩ ≥ −2‖Mx‖‖w‖ ≥ −2·τ‖A‖p·(q²/2) = −τ‖A‖pq²` ✔.

**Assembly.** With `−P_rad = 2Σa_i(cos x_i−1) ≥ −Σa_ix_i²` (exact radial lower, both signs) and
`⟨v,Λ0v⟩ = ½xᵀH0x + Σa_ix_i²`:
```
V² − R*² ≥ F − R*² ≥ ½xᵀH0x + τp² − C_crossq³ − (d/3)q⁴ − τ(Bd+‖A‖)pq²      (τBp < 1)
```
✓ — every term with the correct sign; `V² ≥ F` is weak duality with the *specific* field `α(x)` ✔;
`τp²` is the analytic identity `2⟨Mx,v⟩ = τxᵀGGᵀx = τp²` (factor 2 inside the identity) ✔.

**Complete-the-square (the structural gain).** Split `τp² = (τ−τ₀)p² + τ₀p²` and choose `τ₀ < τ` with
`H0 + 2τ₀GGᵀ ⪰ μ₀I`, so `½xᵀH0x + τ₀p² ≥ ½μ₀q²` ✔. With `Δ := τ−τ₀ > 0`, `c := τ(Bd+‖A‖)`,
`p = ‖G₈ᵀx‖ ≥ 0` and `min_{p≥0}[Δp² − cpq²] = −c²q⁴/(4Δ)` (attained at `p = cq²/(2Δ) ≥ 0`; if that
exceeds the attainable maximum `‖G₈ᵀ‖q`, the endpoint value is larger, so the bound remains valid) ✔.
Hence the final
```
V² − R*² ≥ [½μ₀ − C_crossq − {d/3 + τ²(Bd+‖A‖)²/(4(τ−τ₀))}q²] q²
```
✓ — matches the note, and the old **cubic `bd` loss is gone**: what remains cubic is only
`−C_crossq³` (the directional tensor constant), everything `b`-dependent is now **quartic** ✔ —
because `β` vanishes on `ker G₈ᵀ` (the "stress does not vary in the critical kernel" mechanism) ✔.

**Negative angles and factors.** All five numerical constants carry the right power of 2:
`τp²` (identity), `2⟨v,Λ0w⟩` with `w = −½Rad₈` (the ½ is inside `w`), `(d/3)q⁴` from
`2·q·d·q³/6`, `τ‖A‖pq²` from `2·τ‖A‖p·q²/2`, and the `4(τ−τ₀)` in the completion. Signs of `x_i` are
handled by `|x_i|`-bounds throughout; `p ≥ 0` is what makes the completion one-sided, and
`τBp < 1` is the only smallness condition besides `q ≤ ρ` ✔.

## 2. Interface notes (with my misreading corrected)

1. **`A`'s domain — MY ERROR, note is right.** I read `R⁴` as a typo; that was a wrong dimension
   count on my side. The correct shapes are: `N` is `45×4`, `G₈ = TN` is `8×4`, so
   `G₈ᵀx ∈ R⁴` (the raw chart is `x ∈ R⁸`, but the stress directions span only **four** dimensions),
   and `A` is `18×4` (`18 = 9 anchors × 2` flux components). The note's "`A` maps `t ∈ R⁴`" is therefore
   correct as written, and `‖A‖` is the operator norm `R⁴ → R^{18}`. Withdrawn as an interface item;
   the only retained part is that `B`'s `N_e` rows and `Q`'s `N` are the same `45×4` matrix ✔.
2. **Condition on `ρ` — accepted, lead is adding the line.** `p ≤ ‖G₈ᵀ‖·q ≤ ‖G₈ᵀ‖ρ` is implicit in the
   ball condition `τB‖G₈ᵀ‖ρ < 1`; making it explicit costs one line and fixes the hypothesis as
   `β < 1` on the ball ✔.
3. **Trade-off to record.** `μ₀` increases with `τ₀` while the quartic coefficient
   `τ²(Bd+‖A‖)²/(4(τ−τ₀))` increases with `τ` and blows up as `τ₀ → τ`; `(τ, τ₀)` is a genuine
   optimization, and the note's "further directional refinement possible (radial A, generalized metric)"
   is the right place to say so — no proof obligation attached.

## 3. Recorded readings from `lead/anisotropic_stress_ball_certificate.json` (output only, no code audit)

Notation as exported (pairs are exact fractions `(num, den)`), recorded verbatim, no recomputation:
`τ = 1/10`, `τ₀ = 1/20`, `μ = 1/500`, `B = (182,1)`, `A = (1074,1000)`, `Ccross = (358,10000)`,
`G = (1892,1000)`, `d = (80,1000)`, `ρ = 764/100000`, `growth = 1/100000`; diagnostics
`cross_upper = 0.03575788…`, `quartic_upper = 12.247764…`, `coefficient_lower = 0.0000115908…`;
`scope = "local raw8 ball; analytic … lemma; not global"`.

**What these readings say (arithmetic on the exported numbers only).** The cubic coefficient is now
`C_cross ≈ 0.0358` against the previously used uniform `d(1+b)+m ≈ 1.159` — a factor ≈ 32 smaller,
which is the structural gain the note predicted; the quartic coefficient
`d/3 + τ²(Bd+‖A‖)²/(4(τ−τ₀)) ≈ 0.0267 + 12.22 ≈ 12.25` matches `quartic_upper`; and the margin
`μ/2 − C_crossρ − Q₄ρ² ≈ 0.001 − 0.000273 − 0.000715 ≈ 1.16e-5` matches `coefficient_lower`. Hence
`ρ = 7.64e-3` versus the previous `4.31e-4` (≈ 17.7× larger), with certified positive growth on the
ball. Two recorded consequences for the route: (i) `x ≈ 0.01` is still ~30 % beyond `ρ`, and the
**quartic term now dominates the cubic one** at this radius, so the `(τ, τ₀)` trade-off (item 3 above)
is the natural next lever before falling back to the annulus; (ii) nothing here is a claim about the
constants' correctness — only the JSON's interval outputs are recorded, and the code that produced them
was not audited.

## 4. Verdict

The algebra in `ANISOTROPIC-STRESS-REMAINDER.md` **checks out**: directions (all losses are lower
bounds), the factor 2 (five places, all verified), the negative-angle handling (`|x_i|`-uniform, `p ≥ 0`),
the double-sum tensor bound (no diagonal guess), and the complete-the-square that converts the large
`bd` cubic into a quartic; the shapes are as in §2.1 (my earlier "typo" reading was wrong). The export
records a ball `ρ = 7.64e-3` with positive certified margin. **No constant is certified by this audit,
and no global claim is made** (the note itself says so).
