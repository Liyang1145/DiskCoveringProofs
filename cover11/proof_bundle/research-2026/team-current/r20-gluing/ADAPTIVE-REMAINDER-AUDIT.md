# ADAPTIVE-REMAINDER-AUDIT — independent derivation of the 5-constant finite remainder

**Lane**: r20-gluing (cline2-r23-gluing), sole writer here. **No claim registered.** No script, no
sub-agent. Object: `lead/ADAPTIVE-STRESS-FINITE-REMAINDER.md` (read directly; no other member's report
relied on). I re-derived every step below; the derivation is **essentially correct**, with four
interfaces that must be stated exactly (F1–F4) and one arithmetic correction (F3).

## 1. What I re-derived (and confirm)

**Expansion.** With `α(x) = α0 + Qx` supported on the carrying graph, all of whose 45 edges have length
`R*` (C909 §2), and with the free nodes unchanged at `U0` (see F2), the minimized energy is quadratic
in the anchor displacement `δ = U(x) − U0`:
`F(x) = E_{α(x)}(U(x)) = R*² + 2⟨l_{α}, δ⟩ + ⟨δ, Λ_{α}δ⟩`, `l_{α} = Λ_{α}U0 ≠ 2Λ_{α}U0` **only under the
half-quadratic convention for `Λ`** (the gradient at `δ=0` is `2l` — see F4). Linear in `α` at `U0`
because the free coordinates are frozen, so `l_α = l0 + Mx`.
**Direction.** `V(U)² = max_α E_α(U) ≥ E_{α(x)}(U(x)) = F(x)` ✔ (weak duality with the *specific* field
`α(x)`; no maximality over `α` is used).
**Variational comparison (no inverse derivatives).** `α(x)_e = α0_e(1 + (Qx)_e/α0_e)` with
`|(Qx)_e| ≤ b α0_e q` gives `(1−bq)α0 ⪯ α(x) ⪯ (1+bq)α0` edgewise; the anchored Dirichlet form is
`Λ_α = L_aa − L_af L_ff^{−1} L_fa`, and for edgewise-Loewner-ordered weights the *minimized* energies
are ordered, hence `(1−bq)Λ0 ⪯ Λ_α ⪯ (1+bq)Λ0` as quadratic forms ✔ (this is the variational/Loewner
step, correctly replacing any differentiated inverse; positivity of the free block is supplied by
`bq < 1` and `α0 > 0`, and `Λ0 ⪰ 0` is the Dirichlet energy principle).
**Radial term.** `l0_i = a_iU0_i` with `a_i ≥ 0` (C909: zero tangential, strictly positive radial) and
the circle's `⟨U0_i, δ_i⟩ = cos x_i − 1 ≥ −x_i²/2` give `2⟨l0,δ⟩ ≥ −Σ_i a_i x_i²` ✔ (the sign of `a_i`
is exactly what makes the inequality go the right way; a negative `a_i` would reverse it).
**Adaptive linear term.** `2⟨Mx,δ⟩ = 2⟨Mx,v⟩ + 2⟨Mx,w⟩` with `‖Mx‖ ≤ mq` and `‖w‖ ≤ q²/2 + o(q²)`
(see F3) gives `≥ τ xᵀGGᵀx − mq³` ✔ **provided the factor-2 identity** `2⟨Mx,v⟩ = τxᵀGGᵀx` holds as a
definitional relation between `M` and `G = TN`, `Q = τNGᵀ` (F4). The `−mq³` sign is correct (lower
bound; `|2⟨Mx,w⟩| ≤ 2mq·q²/2`).
**Quadratic term.** `⟨δ,Λ_αδ⟩ ≥ (1−bq)⟨δ,Λ0δ⟩` ✔; then
`⟨δ,Λ0δ⟩ = ⟨v,Λ0v⟩ + 2⟨v,Λ0w⟩ + ⟨w,Λ0w⟩ ≥ ⟨v,Λ0v⟩ − dq³` ✔ (drop the nonnegative `⟨w,Λ0w⟩`; the cross
term is `≥ −2‖v‖‖Λ0w‖ ≥ −2q·d·q²/2 = −dq³` with `Λ0 ⪯ dI`, `‖v‖ = q`, `‖w‖ ≤ q²/2`), and
`−bq⟨δ,Λ0δ⟩ ≥ −bq·d‖δ‖² ≥ −bdq³` ✔ (all three signs check, and each loss is in the *lower* direction).
**Combination.** Using `½xᵀH0x = ⟨v,Λ0v⟩ − Σ_i a_i x_i²` (this is the *definition* of `H0` in this
expansion — see F4) and hypothesis 4 `H0 + 2τGGᵀ ⪰ μI`:
```
F(x) ≥ R*² + ½xᵀ(H0+2τGGᵀ)x − [d(1+b)+m]q³ ≥ R*² + (μ/2 − [d(1+b)+m]q)q²  ✔
```
**Certificate consequence.** For rational `ρ` with `bρ < 1` and `[d(1+b)+m]ρ ≤ μ/4`:
`μ/2 − [d(1+b)+m]q ≥ μ/2 − μ/4 = μ/4` for all `q ≤ ρ`, i.e. growth `≥ μq²/4` on the whole ball ✔ —
correct, and it needs only the five constants, no third-derivative guess ✔.

## 2. Findings after the lead's reply — one of my four was wrong, two are being written in

**F1 — not a gap (withdrawn as a defect).** The file's opening line already restricts everything to the
"SAME C909/C912 carrying graph, 45 edges"; the six slacked edges are therefore outside `Q`'s range by
construction, and the identity `E_α(U0) = R*²` is fine. The lead will additionally record that the six
slack weights are identically zero. My paragraph is kept only as a remark on why that clause matters,
**not** as a claim of a gap.

**F2 — clarification, accepted upstream.** `B` is the geometric equilibrium operator (edge vectors at
`U0`) plus a normalization row, and `Σα = 1` is handled there; the lead is writing both in. No defect
claimed.

**F3 — WITHDRAWN (my error).** My Taylor objection was wrong: I dropped the negative `−x_i⁶/24`
contribution of `(cos x_i − 1)²` and then compared as if the result exceeded `x_i⁴/4`. The correct and
simpler argument is the **integral form**:
`w_i = U(x_i) − U0_i − JU0_i x_i = ∫_0^{x_i}(x_i − t)U''(t)\,dt` with `‖U''‖ = 1` on the unit circle,
hence `|w_i| ≤ ∫_0^{|x_i|}(|x_i| − t)\,dt = x_i²/2` **exactly**, and `Σ_i x_i⁴ ≤ q⁴` gives
`‖w‖_F ≤ q²/2`. The expansion in fact goes the other way (`|w_i|² = x_i⁴/4 − x_i⁶/72 + O(x_i⁸)`), so
the file's third term `−mq³` is correct as written and no constant needs adjusting.

**F4 — corrected: an analytic identity, not a numeric obligation.** Given the definition
`T = 2·sgn·d·JU` (twice the signed tangential displacement of each edge), the identity
`2⟨Mx,v⟩ = xᵀ(TN)τGᵀx` follows **purely analytically** — `M` is the flux map induced by
`Q = τNGᵀ`, and `T`'s definition turns the tangential pairing into exactly that quadratic form, factor
2 included. My demand that it "be verified numerically at C891 before being trusted" mis-stated its
status: that evaluation is a **check**, never the proof. Same for the two convention points (`Λ_α` the
half-quadratic form so that `l_α = Λ_αU0`; `H0 = 2(⟨t,Λ0t⟩ − diag_i a_i)` so that the margin reads
`μ/2`) — they are definitions to be fixed in the write-up, not gaps.

## 3. Verdict

Correct in outline and in every *sign*: the direction `V² ≥ F`, the Loewner/variational comparison
(no inverse derivatives), the radial term (`a_i ≥ 0` essential), the three lower-bound terms
(`−Σa_ix_i²`, `−mq³` — with `‖w‖ ≤ q²/2` **exact** by the integral form, see F3 — and
`−d(1+b)q³`), and the `μ/4`-growth certificate. After the lead's reply my list stands as: **F1 no
longer a gap** (the carrying-graph restriction is already in the file's opening, and the six slack
weights will be recorded as identically zero), **F2 a clarification being written in** (`B` = geometric
equilibrium operator + normalization row), **F3 withdrawn** (my error; the integral bound is exact),
**F4 an analytic identity plus two definitional conventions** (`T = 2·sgn·d·JU` ⇒
`2⟨Mx,v⟩ = xᵀ(TN)τGᵀx`, factor 2 included; `Λ_α` half-quadratic so `l_α = Λ_αU0`;
`H0 = 2(⟨t,Λ0t⟩ − diag_i a_i)` so the margin reads `μ/2`) — the numeric evaluation at C891 is a check,
not the proof. **No gap remains in the derivation as I re-derived it**; scope stays local (`q ≤ ρ`),
not a global reduction, as the file itself states.
