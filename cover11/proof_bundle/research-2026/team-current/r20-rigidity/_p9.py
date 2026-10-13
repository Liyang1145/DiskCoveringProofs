from pathlib import Path

p = Path('FINITE-REMAINDER-FINAL-AUDIT.md')
s = p.read_text(encoding='utf-8')

# (1) V^2 is a lower bound after minimization, equality only at the exact root
s = s.replace(
    "Let `E_α(U) = UᵀΛ_αU` be the carrying-graph Dirichlet energy (weighted Laplacian `Λ_α`), `U0` the root\nembedding, `V² = min_free E_{α(x)}` the oracle's squared radius, `α(x) = α0 + τN(G^T x)`,",
    "Let `E_α(U) = UᵀΛ_αU` be the carrying-graph Dirichlet energy (weighted Laplacian `Λ_α`), `U0` the root\nembedding, and `V² = V²(U(x))` the oracle's squared radius. The minimised energy is a **lower bound**:\n`V² ≥ E_{α(x)}` after the free-node minimisation, with **equality only at the exact root** (and at the\nanchors' tangential data used there); it is *not* an identity away from the root. `α(x) = α0 + τN(G^T x)`,")

# (2) positivity: the max-relative condition is SUFFICIENT, not equivalent
s = s.replace(
    "Positivity holds iff\n   `β(x) := max_e |(Qx)_e|/α0_e < 1`, and",
    "Positivity is the direct condition `α_e = α0_e + (Qx)_e > 0` for every edge `e`; the max-relative\n   bound `β(x) := max_e |(Qx)_e|/α0_e < 1` is a **sufficient** criterion for it (not an equivalence). Also")

# (3) 45 vs 51: carrying subgraph, not an edge-count inconsistency
s = s.replace(
    "* **Graph size wording.** ADAPTIVE-STRESS-FINITE-REMAINDER describes the object as \"(45 edges, 9\n  anchors, 20 free nodes)\" while the later documents and the certificates say \"fixed51edge\". The two\n  documents therefore name the same oracle by two different edge counts; the derivation does not depend\n  on the count, but the scope lines should be made uniform.",
    "* **Graph 45 vs 51 (not an inconsistency).** The 45-edge graph is the *carrying subgraph* of the\n  51-edge graph (the stress audit maps 45 ⊂ 51 with six zero weights), so both descriptions refer to the\n  same oracle; the documents are consistent once that nesting is stated.")

# (4) BN includes the normalization row -> kernel gives free balance AND sum N = 0
s = s.replace(
    "2. **Adaptive normalised positive stress.** `1ᵀN = 0` (from `BN = 0`), so `1ᵀ N G^T = 0`, i.e. every\n   column of `Q = τNG^T` has zero entry-sum: `α(x)` is normalised for all `x`.",
    "2. **Adaptive normalised positive stress.** Here `BN` *includes the normalisation row*, so membership of\n   the kernel gives **both** the free-node balance and `Σ_e N_e = 0` (`1ᵀN = 0`) simultaneously; the\n   latter implies `1ᵀ N G^T = 0`, i.e. every column of `Q = τNG^T` has zero entry-sum, so `α(x)` is\n   normalised for all `x`. (Phrasing as \"a generic circulation implies normalisation\" would be too\n   weak: the normalisation is part of `BN` itself.)")
p.write_text(s, encoding='utf-8')

for tag in ['lower bound', 'sufficient', 'carrying subgraph', 'includes the normalisation row']:
    print(tag, '->', tag in s)
