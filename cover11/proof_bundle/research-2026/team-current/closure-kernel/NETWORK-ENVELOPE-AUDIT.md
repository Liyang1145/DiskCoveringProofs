# NETWORK ENVELOPE AUDIT — local kernel and quantitative lemma

Scope: `lead/interval_network_envelope.py`, `lead/NETWORK-ENVELOPE-QUANTITATIVE-LEMMA.md`,
`lead/FIXED-SWITCH-SHARPNESS-AND-LOCALITY.md` (context). Local kernel + quantitative lemma only.
**C911 far-region certificate is outside this audit.** Read-only; no lead file changed.
No new scripts were added after the lead's corrections.

## Executor provenance (observed only)

* Tool surface: `pwsh` (PowerShell/Windows), file read/write, claim ledger, team messaging.
  Python `py -3` with numpy / scipy / mpmath importable (`scipy.linalg.qr` present).
* **Provider and model are not observable from inside this session**; I do not guess them.

## Verdict

**原 kernel 未找到反例，但此审计初版无效，经 lead 指出后纠正。**

**The original kernel was not refuted — no counterexample was found. But the first version of this
audit is invalid and is withdrawn (§0).** The errors catalogued in §0 are all mine; they do not by
themselves overturn the kernel, and this report makes no claim in either direction beyond what is
stated after the corrections.

I am not issuing a PASS, and nothing in this file should be read as self-certification. The lead is
producing an independent analytic audit in a separate file.

## 0. Corrections (the first version of this report is withdrawn)

1. **`B α₀` is not `0`.** The 41×45 `B` includes the normalization row, so the radial identity is
   `B α₀ = e₄₀` (last component 1), while `B N = 0` holds for the tangent basis. My §2 and §8(a)
   wrote `B α₀ = 0`, which is dimensionally wrong by exactly the normalization row. Independent
   check on the script's own arrays: `B α` has sup-norm `7.8e-15` on rows 0:40 and row 40 equal
   to `1.0` — i.e. `e₄₀`, not zero.
2. **`dim ker B = 4` is pure rank–nullity, not C909.** Once `rank B = 41` is proved (the 41×41
   inverse), `dim ker B = 45 − 41 = 4` follows by the rank–nullity theorem with no appeal to
   C909. C909's role is only to supply **existence of a full radial solution** (consistency of
   `B α = e₄₀`). My §2 interchanged these roles.
3. **The kernel is `ker Gᵀ`, not `ker G`.** The script builds `K` (9×4) with `GᵀK = 0`: it solves
   `G_D K_D = −G_F` on a 4×4 invertible submatrix of `Gᵀ` restricted to the first 8 coordinates
   and sets `K_F = I₄`. Its own docstring says "Exact ker(G.T)". I wrote `G K = 0`, which is both
   the wrong identity and the wrong dimension count (`ker Gᵀ ⊂ ℝ⁹` has dimension `9 − 4 = 5`;
   the chart `θ₉ = 0` cuts it to 4, which is the `K` that is constructed).
4. **The spectral bound runs the other way from what I wrote.** For the symmetric inverse `A`:
   `λ_max(A) ≤ ‖A‖_∞`, hence `1/‖A‖_∞ ≤ 1/λ_max(A) = λ_min(Gram)`. The code's
   `sigma = lo(1/sqrt(norminf(GramInv)))` is therefore `≤ σ_min(G8)`, i.e. a **conservative lower
   bound** on `σ_min(G8)` — which is the safe direction for the certificate. I had the inequality
   reversed in two places while reaching the right practical conclusion.
5. **`mu` does not come from inverting `Q`.** Take `x = KQz`; from `QᵀHKQ ⪰ .95 I` we get
   `xᵀHx = zᵀQᵀKᵀHKQz ≥ .95‖z‖²`, and `‖x‖² = ‖KQz‖² ≤ ‖KQ‖_F²‖z‖²`. Hence the Rayleigh bound on
   `ker Gᵀ` is `mu ≥ .95/‖KQ‖_F²`. My §4 derivation via `‖Q⁻¹‖₂` was a different (and confused)
   route to the same constant.
6. **`H·1 = 0` proves nothing about graph structure.** `H` has off-diagonal entries
   `2 Λ_ij U_i·U_j`, which can be **positive** because `U_i·U_j` can be negative; a zero row sum
   does not make it a non-negative graph Laplacian, and its spectrum is **not** the set of those
   off-diagonal entries. The angle-induced `H` may be indefinite. My §6 asserted both the
   Laplacian reading and a spectral description; both are withdrawn. The script's Gershgorin test
   on `QᵀHKQ` is the thing that actually establishes positivity on the kernel, and it does not
   need `H` itself to be positive anywhere.
7. **The remainder constants are unaudited, full stop.** I did not re-derive the `‖H‖₂ ≤ 2` and
   third-order remainder estimates of the lemma. My "a defect would need to be ≳1e4 larger" was
   an unjustified inference from the size of one numerical slack and is **deleted**; the correct
   statement is only "not audited".
8. **`eps` needs the line-120 check.** The certificate uses the rational constant `eps = 1/1000`,
   which is **not** the same object as the diagnostic `eps = .001/nmax`. Applying `1/1000`
   requires `nmax·(1/1000) < .0029`, which is line 120's assertion, and that is also what makes
   the nonnegativity condition `ε·max|N| < min α₀` hold with the specific rational `ε`. My §5
   treated the chain as structural from `nmax ≥ 1` alone, which is insufficient.
9. **`growth = mu/4` is a proved quantity.** It is the lemma's conclusion constant derived from
   the written quantitative lemma with `mu = 1/600`, not something that becomes valid only when a
   downstream file reads the JSON. My §8 called it "a label rather than a proved quantity"; that
   framing is withdrawn. What remains true and was the only point worth making: no file I searched
   *consumes* it, and `1/8000` is not the tightest available `c1`. Both are bookkeeping remarks,
   not statements about validity.

---

## 1. `solve()` — Neumann multi-RHS interval enclosure: sound

`solve(M, b)` with `M` the exact 45×45 frozen subsystem and `b` the frozen RHS:

* `Cn = np.linalg.inv(arr(M))` is a **double-precision** matrix, but it is converted to an exact
  interval (`iv.matrix(Cn.tolist())`), so `Ci` is the exact binary rational matrix with those
  entries. The text "merely a preconditioner" is correct.
* `E = I − Ci·M` is computed in interval arithmetic; `q = norminf(E) + 1e-40`, asserted `< 0.01`.
  By the Banach/Neumann lemma, `‖A⁻¹‖_∞ ≤ ‖Ci‖/(1−q)` for **every** matrix `A ∈ M`
  (Hadamard: q < 1), so `M` is interval-nonsingular. This is the step that proves the
  invertibility — not the floating inverse, and not a residual check.
* `v = Ci*(b − M*y)` is the exact residual scaled by `Ci`, and the fixed point is
  `e = v + E·e`, i.e. `e = A⁻¹b`. The returned enclosure is `y + corr` with
  `corr_0 = ±(hi‖v‖/(1−q))`.
* **Truncation is a non-issue, and provably so.** The refinement `corr ← v + E·corr` has
  truncation error `≤ eps·q^K/(1−q)`. At the worst contraction actually present
  (`q = 1.2632e-3`, 20-node Schur block) the 12 executed iterations give
  `eps·q^12/(1−q) ≈ 1.65e-38`. More strongly: the initial box already contains the fixed point
  and the iteration is a contraction, so *any* `K ≥ 0` leaves the enclosure valid; the 12 steps
  only buy tightness. There is no K at which this could silently lose the solution.
* `norminf` is a valid ∞-norm upper bound; `hi(iv.mpf(norminf(v))/(1−iv.mpf(q)))` is a
  conservative upper bound, and `1 − q > 1/2 > 0`, so no division through zero.

Independently observed contractions in the emitted JSON: `q(M)=1.98e-4`, `qB=3.88e-5`,
`qG=1.43e-4`, `qL=1.26e-3`, `qGram=8.37e-4` — all far below 1, so every linear identity the
script asserts (`B N = 0`, `GᵀK = 0`, `L_ff Y = L_fa`, `G8ᵀG8 · GramInv = I`) is *proved* by
contraction at the interval level rather than by a small residual.

## 2. Rank structure of `B`

Independently reproduced from the C891 root (`auditC_ranks.py`, rebuilt `B`, `T`):

| quantity | measured |
|---|---|
| `rank(B)` | 41 / 41 rows (min singular value 3.74e-2) |
| `rank(B[:40])` | 40 / 40 — the 40 free-coordinate rows already have full row rank |
| `rank([B;T])` | 45 of 50 rows |
| `rank(T)` | 9 / 9 |
| `dim null(B)` | 4 — equals the JSON `normalized_stress_dimension` |

**Roles, stated correctly:** `B` = 40 free-coordinate balance rows **+ 1 normalization row**. The
radial stress satisfies `B α₀ = e₄₀` (not `0`); the tangent basis satisfies `B N = 0`. By the
**rank–nullity theorem**, `dim ker B = 45 − rank B = 4` once `rank B = 41` is proved; this does
**not** depend on C909. C909 supplies only the **existence** of a full radial solution, i.e. the
consistency of `B α = e₄₀`. (My earlier version said `B α₀ = 0` and attributed the nullity to
C909; both wrong, see §0.1–§0.2.)

Since `ker B` is a linear space, `B(α₀ ± εN) = e₄₀` for every `ε`: the radial identity is needed
once, for `α₀`, and the perturbation needs no separate radial re-derivation.

## 3. The `theta8` chart and the kernel `K`

`G8` is `G` restricted to the first eight anchors (ninth angular component held at 0). The script
selects 4 of those 8 coordinates (`adep = [4,2,5,0]`, `afree = [3,1,6,7]`), solves
`G_D K_D = −G_F` on the corresponding 4×4 submatrix of `Gᵀ`, and sets `K_F = I₄`. The resulting
`K` is 9×4 with **`GᵀK = 0`** (the script's own docstring: "Exact ker(G.T)"), proved by the
contraction `qG = 1.4e-4`. Dimensions: `ker Gᵀ ⊂ ℝ⁹` has dimension `9 − rank G = 5`, containing
the rotation direction; in the chart `θ₉ = 0` the rotation is not representable, leaving the
4-dimensional kernel that `K` spans. (I had written `G K = 0`; wrong identity and wrong count.)

`rank G = 4` matches the JSON `angular_gradient_rank` / `critical_angle_dimension_mod_rotation`,
and is consistent with `rank B = 41`, `rank([B;T]) = 45`.

## 4. `sigma` and `mu`

* `GramInv` is a contraction-proved enclosure of the exact `(G8ᵀG8)⁻¹`, which is **real
  symmetric**. For a symmetric `A`: `λ_max(A) ≤ ‖A‖_∞`, hence
  `1/‖A‖_∞ ≤ 1/λ_max(A) = λ_min(A)`. Applied to `A = (G8ᵀG8)⁻¹` this gives
  `(G8ᵀG8)⁻¹ ⪰ (1/‖(G8ᵀG8)⁻¹‖_∞) I`, so `λ_min(G8ᵀG8) ≥ 1/‖(G8ᵀG8)⁻¹‖_∞` and therefore
  `σ_min(G8) ≥ lo(1/√‖(G8ᵀG8)⁻¹‖_∞) = sigma`. So `sigma` is a **conservative lower bound** on
  `σ_min(G8)`, which is the safe direction.
  Measured with the actual midpoint: `σ_min(G8) = 0.29678564` (singular values
  1.3713 / 0.9775 / 0.8080 / 0.2968), `‖(G8ᵀG8)⁻¹‖_∞ = 15.89099`,
  `1/√λ_max((G8ᵀG8)⁻¹) = 0.25085601`; the JSON `sigma_lower = 0.2508071` is the interval version.
  (My two earlier statements of this inequality were reversed; see §0.4.)
* `mu` follows by substituting `x = KQz`: from `QᵀHKQ ⪰ .95 I`,
  `xᵀHx = zᵀ(QᵀKᵀHKQ)z ≥ .95‖z‖²`, while `‖x‖² ≤ ‖KQ‖_F²‖z‖²`. Hence every nonzero `x ∈ im KQ`
  (= `ker Gᵀ` in the chart) satisfies `xᵀHx/‖x‖² ≥ .95/‖KQ‖_F² = mu`. The preconditioner `Q` is
  the numerical inverse Cholesky of the midpoint (an exact dyadic interval object), and the
  congruence is a similarity, so the kernel-restricted Rayleigh bound is exactly this. The JSON
  `mu_lower = 0.0018900 > 1/600 = 0.0016667̅`. (My earlier derivation through `‖Q⁻¹‖₂` was a
  different route to the same constant; see §0.5.)

## 5. Explicit constants and the certified `eps`

* The stopping rule at line 114 and the doc's line 24 sufficient-radius inequality are the **same**
  inequality. With `mu = 1/600`, `M = 16000`: `ρ = 1e-7` gives `3.2026e-3 > mu/4 = 4.1667e-4`
  (fails); `ρ = 1e-8` gives `3.2003e-4 ≤ 4.1667e-4` (passes). Largest power of ten `= 1e-8`,
  matching `rho_power10`. `M = 2/c1 = 16000` is consistent with the enclosed `M_upper = 15948.51`
  (which is `≤ 16000`).
* Line 122's assertion at `(M, mu, ρ) = (16000, 1/600, 1e-8)`: LHS `3.20031e-4 ≤ 4.16667e-4`,
  slack `9.66e-5`.
* **`eps`:** the certificate uses the rational constant `eps = 1/1000`, which is *not* the same
  object as the diagnostic `eps = .001/nmax`. Applying `1/1000` requires line 120's check
  `nmax/1000 < .0029`, which is what makes the nonnegativity condition
  `ε·max|N| < min α₀` hold with that specific rational `ε`; `alpha_min_lower = 0.0029334 > 0.0029`
  is the interval-measured companion. My earlier claim that the chain is structural from
  `nmax ≥ 1` alone was insufficient (§0.8).

## 6. Schur matrix `H` and its kernel restriction `HK`

* `L` is assembled from the 45 interval weights `alpha`; `Lam = L_aa − L_faᵀ Y` with
  `Y = Lff⁻¹ L_fa` is legitimate because `qL = 1.3e-3` proves `Lff` invertible over the frozen box.
* `H` has off-diagonal `2 Λ_ij U_i·U_j` and diagonal minus the off-diagonal sum. **`H·1 = 0` and
  that is all one can say from this construction:** since `U_i·U_j` can be negative, the
  off-diagonal entries can be **positive**, so `H` is not a non-negative graph Laplacian and its
  spectrum is not determined by the off-diagonal entries. The angle-induced `H` may be
  indefinite. What the certificate needs — and what the script actually proves — is positivity of
  `H` restricted to `ker Gᵀ`, via the congruence `QᵀHKQ` and its Gershgorin bound.
  (My earlier Laplacian/spectrum statements were false; §0.6.)
* `HK = Kᵀ H K` with the same `K` for every column of `N`: this is the object the split lemma is
  applied to, and the harmonicity of the same candidate free coordinates is what permits using a
  single `K` across the `ε`-family.

## 7. Uniform remainder control — NOT AUDITED

I did not re-derive the lemma's `‖H‖₂ ≤ 2` and third-order remainder estimates. That is the whole
statement: **not audited.** (My earlier "the slack would need to be ≳1e4 larger" was an
unjustified inference and is deleted; §0.7.)

## 8. Observations (bookkeeping only)

* `certified_rational_constants['growth'] = 1/2400` is the **proved** conclusion constant
  `mu/4` for `mu = 1/600` — it follows directly from the written quantitative lemma and does not
  need a downstream reader to become valid. Bookkeeping remarks only: no file I searched consumes
  it, and `1/8000` is not the tightest available `c1` (the enclosed value is `≈1.254e-4`).
  (My earlier "label rather than proved quantity" framing is withdrawn; §0.9.)
* `sigma` is a conservative lower bound on `σ_min(G8)`, not an identity (§4).

## 9. What I independently reproduced, and what I did not

* **Reproduced independently (own reconstruction):** the C891 root box (radius `1.0e-9` binary,
  all coordinates positive with margin, `R = 0.379983853120`, `R + rad < 1`); the nine half-angle
  widths with `Σa = π`, so `Σ(a_k + a_{k+1}) = 2π` and the arcs close; positivity of the nine
  `rho`; unit normals; the 45-edge incidence (ring degree 2, hubs degree 3, face centroids
  degree 3, 9 faces); the rank table of §2; both rational inequalities of §5; the Neumann
  truncation bound; and `σ_min(G8)` vs `sigma`.
* **Verified only at the level of the script's own assertions (JSON read):** `sigma > 1/4`,
  `mu > 1/600`, `alpha_min > 0.0029`, `lower(HK) > 0.95`, and the contraction factors.
* **Not audited:** the uniform remainder constants of §7; the C909 sharpness proof (used as the
  stated upstream input); and the Schur-elimination algebra beyond the block definitions and the
  `Lff` invertibility contraction.
* **Out of scope by instruction:** C911.

## 10. Repro (scripts written before the correction request; no new scripts added)

```
cd research-2026/team-current/closure-kernel
py -3 auditA_constants.py     # M=2/c1, both rational inequalities, C891 root box
py -3 auditB_geometry.py      # arcs close, rho/normal positivity, 45-edge incidence
py -3 auditC_ranks.py         # rank(B)=41, rank(B[:40])=40, rank([B;T])=45, rank T=9
py -3 auditD_consumers.py     # stopping rule vs doc, the eps chain
py -3 auditE_neumann.py       # Neumann truncation bound
py -3 auditF_sigma.py         # sigma vs sigma_min(G8) with the actual midpoint
```
