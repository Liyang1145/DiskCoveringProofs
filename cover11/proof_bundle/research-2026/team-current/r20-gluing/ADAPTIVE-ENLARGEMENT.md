# ADAPTIVE-ENLARGEMENT — anisotropic remainder, aligned loss, and an ellipsoidal ball

**Lane**: r20-gluing (cline2-r23-gluing), sole writer here. **No claim, no sub-agent.** Read directly:
`lead/ADAPTIVE-STRESS-FINITE-REMAINDER.md` (audited earlier in `ADAPTIVE-REMAINDER-AUDIT.md`) and
`lead/certify_adaptive_stress_ball.py` (constants read as given: `τ=.1, μ=.002, b=12, m=.119, d=.08,
C=1.159, ρ=.000431`). Context: the DBM far-field certificate has reached 20 leaves; ~75 cells remain
open near `x ≈ .01`. Goal: **enlarge the local ball** by removing the *uniform*-norm losses
(`−mq³`, `−d(1+b)q³`) that currently multiply the *smallest* eigenvalue `μ`; i.e. make loss and gain
live in the same directions. This note does not repeat the finite-Taylor derivation; it replaces three
of its constants by anisotropic ones and turns the ball into an ellipsoid. **Constants proposed here are
numeric candidates to be computed by the instrument; nothing numeric is promoted to a proof.**

## 1. Exact second-order structure kept from the audited file

`δ = v + w`, `v_i = x_i t_i`, `l_α = l0 + Mx`, `Λ_α = Λ0 + O(bq)`, `F(x) = R*² + 2⟨l0+Mx,δ⟩ +
⟨δ,Λ_{α(x)}δ⟩`. Two exact integral identities are used in place of Taylor truncation:
```
(A)  w_i = ∫_0^{x_i}(x_i−t)U''(t)dt ,  U'' = −U  ⇒  w_i + ½x_i²U0_i = −∫_0^{x_i}(x_i−t)(U(t)−U0_i)dt ,
     hence  ‖w + ½x²U0‖_F ≤ q³/6     (replacing the older ‖w‖ ≤ q²/2).
(B)  2⟨Mx,v⟩ = τ xᵀGGᵀx            (analytic identity, T = 2·sgn·d·JU; used as-is, factor 2 included).
```

## 2. Anisotropic constants (the structural gain)

**(R) Radial term, exact.** `2⟨l0,δ⟩ = Σ_i 2a_i(cos x_i − 1) =: −P_rad(x)`, kept *exactly* (it is a
negative term; the old `−Σa_ix_i²` threw away its positive `x⁴` part).

**(L) Adaptive remainder, anisotropic.** With (A), `2⟨Mx,w⟩ = −Σ_i x_i²·ℓ_i(x) + 2⟨Mx, w+½x²U0⟩` where
`ℓ_i(x) := ⟨(Mx)_i, U0_i⟩` is the **radial** component of the flux (linear in `x`). Hence
```
|2⟨Mx,w⟩| ≤ L_rad q³ + (m/3)q⁴ ,     L_rad := max_i ‖ℓ_i‖        (was: m q³).
```
**(Q) Quadratic mixed term — CORRECTED (my diagonal reduction was wrong).** The cubic order of
`2⟨v,Λ0w⟩` is a genuine **double sum**, not a diagonal one. With (A), `w_j = −½x_j²U0_j + R1_j`,
`‖R1_j‖ ≤ |x_j|³/6`, and `v_i = x_it_i`:
```
2⟨v,Λ0w⟩ = − Σ_{i,j} (Λ0)_{ij} x_i x_j² ⟨t_i, U0_j⟩  +  2Σ_{i,j}x_i(Λ0)_{ij}⟨t_i,R1_j⟩ ,
|2⟨v,Λ0w⟩| ≤ C_cross q³ + (‖Λ0‖_op/3) q⁴ ,
G_{ij} := (Λ0)_{ij} ⟨t_i, U0_j⟩ ,   C_cross := ‖G‖_op  (≤ ‖G‖_F) .
```
*Proof of the cubic bound.* `Σ_{ij}G_{ij}x_ix_j² = ⟨x, G x^{(2)}⟩` with `x^{(2)} = (x_j²)_j`, so
`|·| ≤ ‖G‖_op‖x‖‖x^{(2)}‖ ≤ ‖G‖_op q·(Σ_jx_j⁴)^{1/2} ≤ ‖G‖_op q³`; the remainder is
`≤ (1/3)Σ_{ij}|(Λ0)_{ij}||x_i||x_j|³ ≤ (‖Λ0‖_op/3)q⁴` by Cauchy–Schwarz. The **diagonal** part
`i = j` of the double sum vanishes because `⟨t_i, U0_i⟩ = 0`; the **off-diagonal** part does **not**,
and no diagonal guess may be substituted (this was my error). `C_cross` replaces both the invalid
"`C_rt`" and the uniform `d`; `Λ0 ⪯ dI` cannot see it.

**(B) The comparison loss, aligned.** `⟨δ,Λ_αδ⟩ ≥ (1−bq)⟨δ,Λ0δ⟩` (variational, unchanged), and
`−bq⟨δ,Λ0δ⟩ ≥ −bq⟨v,Λ0v⟩ − bq(C_cross q⁴ + c₅ q⁵)`. **The only quadratic-order loss is
`−bq⟨v,Λ0v⟩`, the same form as the gain** — the point of the exercise; everything else from `w` is
quartic or higher.

**(D) Replace `d` by the actual Schur data.** The certificate should use the true
`Λ0 = Laa − Laf Lff^{−1} Lfa` through `C_cross` and `‖Λ0‖_op` instead of the crude `Λ0 ⪯ Laa` bound `d`.
Whether they are numerically smaller is for the instrument to compute; no claim is made here.

## 3. The enlarged inequality (algebra re-done after the sign slips)

Collecting §2, keeping the radial penalty **exactly** (`−P_rad = 2Σ_ia_i(cos x_i − 1)`) and using
`⟨v,Λ0v⟩ = ½xᵀH0x + Σ_ia_ix_i²` (definition of `H0` in the half-quadratic convention,
`H0 = 2(⟨t,Λ0t⟩ − diag_i a_i)`):
```
F ≥ R*² + ½(1−bq) xᵀ(H0 + 2τGGᵀ)x
        + Σ_i a_i [ 2(cos x_i − 1) + x_i² ]  − bq Σ_i a_i x_i²
        − C_cross q³ − L_rad q³ − C₄ q⁴ − O(q⁵) ,
```
with `2(cos x − 1) + x² = x⁴/12 − … ≥ 0`, hence `−bqΣa_ix_i² ≥ −b·a_max·q³`, and the two positive
terms `τxᵀGGᵀx`, `(1−bq)⟨v,Λ0v⟩` absorbed into the first line. Therefore
```
F(x) ≥ R*² + ( μ/2 − [ C_aniso + b·a_max + C₄ q ] q ) q² ,
C_aniso := C_cross + L_rad .
```
(My earlier printed line had `−bqΣa_ix_i²` with the wrong sign relative to the exact `−P_rad` and
dropped the nonnegative `Σ_ia_i[2(cos x_i−1)+x_i²]`; the corrected form is above. **The two steps
(A) and (L) stand as derived; the (Q)-step and this assembly are corrected but their constants
(`C_cross`, `L_rad`, `a_max`, `C₄`) are not yet computed, so nothing here is promoted to a verified
chain.**)
and using `H0 + 2τGGᵀ ⪰ μI` and `Σa_ix_i² − τxᵀGGᵀx ≤ max_i a_i · q²`:
```
F(x) ≥ R*² + ( μ/2 − [C_aniso + b·a_max + C₄ q] q ) q² ,
C_aniso := C_cross + L_rad ,      C₄ := (m + ‖Λ0‖_op)/3 + b·(the quartic coefficients above) .
```
So the certificate condition becomes `[C_aniso + b·a_max + C₄ρ]·ρ ≤ μ/4`, i.e. the *same* shape as
before with `C = d(1+b) + m` replaced by `C' = C_aniso + b·a_max + O(ρ)`. The enlargement factor is
`C/C'` (the instrument computes it); `ρ = μ/(4C)` currently gives `0.000431`.

## 4. Ellipsoidal ball (the second structural gain, for `x ≈ .01`)

The loss and the gain are now both quadratic forms in `x`. Certify the **ellipsoid**
`ℰ_D := {x : xᵀDx ≤ ρ²}`, `D ⪰ 0` rational, instead of the Euclidean ball. In `D`-coordinates
`z = D^{1/2}x` the inequality of §3 reads
```
F ≥ R*² + μ_D/2·‖z‖² − [C_aniso + b·a_max + …]·‖x‖³ ,   μ_D := λ_min(D^{−1/2}(H0+2τGGᵀ)D^{−1/2}) ,
```
so choosing `D` proportional to `(H0+2τGGᵀ)` (or to its regularized inverse) makes the *gain* isotropic
while the cubic loss is paid at the *Euclidean* size of the ellipsoid. **Correction (lead)**: the
Euclidean radius containing `ℰ_D` is
```
max_{ℰ_D}‖x‖ = ρ · ‖D^{−1/2}‖_op = ρ / √(λ_min(D))        (NOT ρ·√(λ_max(D))) ,
```
because `x = D^{−1/2}z` with `‖z‖ ≤ ρ`. The certified region is then the Euclidean ball of radius
`ρ/√(λ_min(D))`. All three ingredients (`D` rational, `μ_D`, the cubic bound) are rational/interval
quantities; `D` itself is a *candidate* chosen by the instrument, and this section is a design
proposal, not a verified step.

## 5. Further levers, with honest status

1. **Optimize `Q = τNGᵀ` (design, numeric candidates).** `H0 + 2τTNNᵀTᵀ ⪰ μI` subject to `BN = 0`,
   `1ᵀN = 0`, `Q` supported on the 45 carrying edges. This is a generalized-eigenvalue design problem:
   the best `N` lifts exactly the low eigenspace of `H0` inside the allowed subspace. Proposal: a few
   τ values (e.g. `τ ∈ {0.1, 0.5, 1, 2}`) and `N` built from the low eigenvector(s) of `H0`; each
   resulting `μ`, `b`, `m` recomputed by the instrument. Status: **proposal, not proof.**
2. **Actual Schur bound.** Use `Λ0`'s operator norm and, better, the cross matrix `G`'s norm
   `C_cross = ‖G‖_op ≤ ‖G‖_F` (§2) rather than `Laa`; also bound `⟨v,Λ0v⟩` in the aligned way so no
   uniform `d` appears at quadratic order.
3. **Rotation gauge.** The certificate is invariant under a common rotation of all nine anchors, so the
   ball may be re-centred at **any** rotation of the root (free of charge), and the chart may be
   rotated to align the low eigenvector with a coordinate axis — this makes the pinned chart's
   gauge-induced anisotropy explicit instead of paying for it in `μ`. (The hard-pinned chart already
   quotients the rotation direction; the *near*-rotation directions are what the ellipsoid of §4
   handles.)
4. **Keep the exact radial penalty.** `−P_rad(x) = Σ 2a_i(cos x_i − 1)` can be carried exactly in the
   certificate (a per-anchor rational cos bound), instead of `−Σa_ix_i²`: at `x ≈ .01` this is a
   second-order effect, but it is free.
5. **Annulus plan (for the stated goal).** With §3–§4 the local ball may reach a few times `10^{-3}` at
   the same `μ`; covering `x ≈ .01` still needs either the annealed split "ball ∪ annulus" with the DBM
   far-field certificates on the annulus, or a larger `μ` via (1). The current tree state (20 leaves
   far field, 75 open near field, 61 certified) is unchanged by this note.

## 6. Scope (corrected)

**Verified here:** only the two integral steps **(A)** (`w + ½x²U0 = −∫(x−t)(U(t)−U0)dt`,
`‖·‖_F ≤ q³/6`) and **(L)** (`2⟨Mx,w⟩ = −Σ_ix_i²ℓ_i(x) + 2⟨Mx, w+½x²U0⟩`,
`|2⟨Mx,w⟩| ≤ L_radq³ + (m/3)q⁴`), plus the elementary quartic bounds.
**Corrected but not yet verified:** the (Q) double-sum step (the diagonal reduction I first wrote was
wrong — the off-diagonal entries `(Λ0)_{ij}⟨t_i,U0_j⟩`, `i ≠ j`, are exactly what a diagonal guess
loses), the re-done §3 assembly, and the ellipsoid §4 (whose Euclidean radius is
`ρ/√(λ_min(D))`). Their constants `C_cross, L_rad, a_max, ‖Λ0‖_op, C₄, D, μ_D` are to be computed by
the instrument, and the τ/N choices of §5.1 are numeric candidates — **nothing numeric is promoted to
a proof, and no part of this note is claimed as an established chain**. No claim is registered, no
global statement is made. No script is attached: the constant computation needs the instrument's own
data structures (audited graph, `Λ0`, `M`, `α0`), and a second reader would risk a silent interface
mismatch.
