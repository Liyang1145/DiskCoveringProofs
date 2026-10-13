"""Rewrite the NETWORK-ENVELOPE-AUDIT.md header/verdict and apply the lead's seven corrections.

The body sections that carry the corrected statements are rewritten wholesale; the script-based
facts are kept only where they were independently reproduced and are now stated correctly.
"""
import re, sys
from pathlib import Path

sys.stdout.reconfigure(encoding='utf-8', errors='replace')
p = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\closure-kernel'
         r'\NETWORK-ENVELOPE-AUDIT.md')
t = p.read_text(encoding='utf-8')

new_head = r"""# NETWORK ENVELOPE AUDIT — local kernel and quantitative lemma

Scope: `lead/interval_network_envelope.py`, `lead/NETWORK-ENVELOPE-QUANTITATIVE-LEMMA.md`,
`lead/FIXED-SWITCH-SHARPNESS-AND-LOCALITY.md` (context). Local kernel + quantitative lemma only.
**C911 far-region certificate is outside this audit.** Read-only; no lead file changed.
No new scripts were added after the lead's corrections.

## Executor provenance (observed only)

* Tool surface: `pwsh` (PowerShell/Windows), file read/write, claim ledger, team messaging.
  Python `py -3` with numpy / scipy / mpmath importable (`scipy.linalg.qr` present).
* **Provider and model are not observable from inside this session**; I do not guess them.

## Verdict

**The original kernel was not refuted — I found no counterexample. But this audit's first version
is invalid and is withdrawn (§0).** The seven errors below are all mine; they do not by themselves
overturn the kernel, and I make no claim in either direction about the kernel's correctness beyond
what is stated after the corrections.

I am not issuing a PASS. The lead is producing an independent analytic audit in a separate file.

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
"""

# keep everything from "## 1." onward, but strip the parts that are now corrected in §0
body_start = t.index('## 1. `solve()`')
body = t[body_start:]

# surgery on the body: remove the withdrawn claims and the fake spectrum/pass language
body = body.replace(
    'i.e. `B N = 0`, satisfying `B N = 0`.',
    'i.e. `B N = 0`.')
body = body.replace(
    '`rank(B) = 41` (min singular value 3.74e-2, well clear of the 1e-8 tol)',
    '`rank(B) = 41` (min singular value 3.74e-2)')
p.write_text(new_head + '\n' + body, encoding='utf-8')
print('rewritten. length', len((new_head + body).splitlines()), 'lines')
print('check: "PASS" occurrences =', (new_head + body).count('PASS'))
print('check: "1e4" occurrences =', (new_head + body).count('1e4'))
