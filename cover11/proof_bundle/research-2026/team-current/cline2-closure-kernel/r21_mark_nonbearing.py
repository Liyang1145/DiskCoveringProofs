"""Mark R19 nonbearing: prepend a withdrawal header and strike the two wrong equations.
No new algebra is introduced; the corrected identities live in the lead's own
check_hub_radial_kernel.py / hub_radial_kernel_control.json."""
from pathlib import Path

p = Path(r'C:\Users\袁力阳\Desktop\ai4math2\research-2026\team-current\cline2-closure-kernel'
         r'\R19-AXIS-RADIAL-AUDIT.md')
t = p.read_text(encoding='utf-8')

header = """# R19 — NONBEARING / WITHDRAWN

**Status: this report carries no result. Do not cite it for the hub radial lemma or the
3D reduction.** Both versions of R19 were wrong on the angle Hessian, and the equations below
are withdrawn:

* `d²θ2/dρ² = 0` (first version) — **withdrawn**;
* `d²θ2/dρ² = 2α2/L2²`, `Hess θ` 2-homogeneous, operator norm `2/L2²` (second version) —
  **withdrawn**.

The lead's exact control is the authority for the correct identities:
`lead/check_hub_radial_kernel.py` (symbolic `H_θ² = I/L⁴`; radial quadratic form vanishes) and
`lead/hub_radial_kernel_control.json` (Cartesian-vs-axis gradient and Hessian interface
controls, `A = (d/2)n`). I am not restating those formulas here.

Also withdrawn: my statement `|y ± d/2| = L1, L2`. The identities are
`L_j² = x² + (y ∓ d/2)²` and the **constraints** are `|y ∓ d/2| ≤ L_j ≤ 0.76`, hence
`|y| + d/2 ≤ 0.76` and `|y| ≤ 0.535` for `d ≥ 0.45`.

## What in this file is still usable (bookkeeping only, not new mathematics)

* the list of locations where my R19 text was wrong (kept as a trace);
* the observation that the proof-vs-code distinction must be kept explicit, and that
  `probe_axis_radial.py` (1495 evals / 0 live) and `axis_no_contraction_control.json`
  (1851 evals / 0 live) are budget diagnostics of a root-*retention* contractor, not existence
  or uniqueness proofs, and not evidence that surviving maxima were classified.

## Ledger

No claim of mine asserted the withdrawn equations: C833/C834 are the q0(5,8) closure-kernel
claims, C866 was already retracted as a duplicate review of C863. Nothing needs retracting in
the ledger; this note is the record.

---

"""

# withdraw the two specific equations wherever they appear in the body
t = t.replace('`d²θ2/dρ² = 0` along the ray from Q1',
              '`d²θ2/dρ² = 0` along the ray from Q1 **[WITHDRAWN — see header]**')
t = t.replace('`d²/[d]ρ² θ2 = 0`', '`d²θ2/dρ² = 0` **[WITHDRAWN]**')
t = t.replace('`d²/dρ² θ2 = 2α2/L2²`',
              '`d²/dρ² θ2` **[my value WITHDRAWN — see header]**')
t = t.replace('Hess θ2 has operator norm 2/L2²  (α2 is 2-homogeneous in X−Q2)',
              'Hess θ2 operator norm: **[my 2/L2² statement WITHDRAWN — see header]**')

p.write_text(header + t, encoding='utf-8')
print('header prepended; file lines:', len((header + t).splitlines()))
for i, l in enumerate((header + t).splitlines()[:20], 1):
    print(f'{i:3d}| {l}')
