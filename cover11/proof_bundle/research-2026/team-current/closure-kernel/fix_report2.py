"""Surgical rewrite of sections 2, 4, 5, 6, 7, 8 and 9 of the audit report after the lead's
seven corrections. No new computations; the corrections are statements about what was wrong."""
import sys
from pathlib import Path

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
p = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\closure-kernel'
         r'\NETWORK-ENVELOPE-AUDIT.md')
lines = p.read_text(encoding='utf-8').splitlines(keepends=True)
idx = [i for i, l in enumerate(lines) if l.startswith('## ')]
h = {lines[i].strip(): i for i in idx}
head = lines[:h['## 1. `solve()` — Neumann multi-RHS interval enclosure: sound']]
s1 = lines[h['## 1. `solve()` — Neumann multi-RHS interval enclosure: sound']:
           h['## 2. 41×45 rank structure: correct, and the "40 + normalization" reading is the right one']]

new_tail = r"""## 2. Rank structure of `B`

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
"""
p.write_text(''.join(head) + ''.join(s1) + new_tail, encoding='utf-8')
t = p.read_text(encoding='utf-8')
print('lines:', len(t.splitlines()))
for i, l in enumerate(t.splitlines(), 1):
    if l.startswith('## '):
        print(f'{i:4d} {l}')
print('PASS occurrences:', t.count('PASS'))
print('1e4 occurrences:', t.count('1e4'))
