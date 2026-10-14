<!-- SPDX-License-Identifier: MIT -->
# Eleven disks: scope of the portable arithmetic checker

Run from a fresh clone, with Python 3.10 or newer:

```sh
python tools/mathcheck_n11.py
python tools/mathcheck_n11.py --json
python tools/mathcheck_n11.py --report build/n11-math-report.json
```

This command uses **only Python's standard library**. It requires neither the
historical 100 GB workspace, restored proof bundles, a numerical optimizer,
Windows/WSL path mapping, nor third-party Python packages. It recomputes
mathematical quantities; it does not use recorded `PASS` flags or saved
residual/interval bounds as evidence. A failed inequality, absent input, corrupt
field or incomplete list of fields gives a nonzero exit code, including under
`python -O`.

Successful execution prints **`SCOPED_PASS`**. This expressly does **not** mean
that the complete unrestricted eleven-disk optimality proof was replayed.
The global proof and its analytic reductions remain in the immutable historical
bundle; the limitations below apply to this new executable entry point.

## What is recomputed

| Mathematical object | Recomputed checks | Historical identifier |
|---|---|---|
| Isolated candidate | Full 12-equation KKT system, interval Jacobian from second-order automatic differentiation, strict Krawczyk inclusion and contraction | C891 |
| Same-root radius | Inclusion-preserving refinement; published 30-decimal enclosure; comparison with `19/50` and the exact global-tree energy threshold | C922 |
| Attaining configuration | Branch legality, boundary nearest-site margins, 11-face incidence, 210 edge pairs, 88 site/face pairs, 189 site/edge pairs, empty circles, and two strictly smaller circumradii | Arithmetic premises of C892 |
| Reduced scalar energies | All 371 positive normalized 51-edge stresses; exact elimination of 22 free nodes; 13,356 pair weights, symmetry and zero row sums | Field identities used by C921 |

The checker also rejects a deliberately shifted multiplier box and a
deliberately corrupted rational pair weight as negative controls. These controls
supplement the recomputation; they are not substitutes for it.

No value obtained by a numerical solver is trusted. A midpoint inverse is only
a proposal for an exact finite-decimal preconditioner. Its validity is checked
by the interval contraction inequality. Schur elimination uses integer Bareiss
arithmetic and exact divisibility, followed by a check of the solution against
the original integer matrix. Saved Schur weights are compared with freshly
derived rational weights.

## Explicit candidate and equality identities

Write `z=(a0,a1,a2,a3,y0,y1,R)` and
`a4=pi-2(a0+a1+a2+a3)`. The cyclic halfwidth vector is
`a=(a0,a1,a2,a3,a4,a3,a2,a1,a0)`, hence its sum is exactly pi.
Choose `theta4=0` and `theta[k+1]-theta[k]=a[k]+a[k+1]`.
Set

```text
rho[k] = cos(a[k]) - sqrt(R^2 - sin(a[k])^2)
C[k]   = rho[k] * (cos(theta[k]), sin(theta[k]))
H0     = (y0, 0),   H1 = (y1, 0)
B[k]   = (cos(theta[k]+a[k]), sin(theta[k]+a[k]))
U[k]   = C[k] + C[k+1] - B[k]
m      = (y0+y1)/2, d = (y1-y0)/2
W      = (m, sqrt(R^2-d^2))
```

All square roots use their positive branch, verified throughout the root box.
The five constraints `f(z)=0` are
`|U1-H1|-R`, `|U2-H0|-R`, `|U3-H0|-R`, `|U8-H1|-R`, and `|W-C6|-R`.
The other seven equations are `e_R-Df(z)^T lambda=0`.
The exact dyadic input box defines **this root**, not a rounded configuration.
Krawczyk strict inclusion is compared with the original rational box itself;
the outward Decimal representation does not redefine or enlarge that box.
Refinement preserves the root originally isolated there. Every mean-value
Jacobian enclosure uses the convex hull of its fixed centre and current box.

The arithmetic checker does not infer an exact equality from an interval
containing zero. The nine active face equalities follow from the five exact
constraints and the following elementary identities:

1. `rho^2 - 2*rho*cos(a) + 1 = R^2`. Therefore adjacent sites are exactly
   distance `R` from their common boundary switch `B[k]`.
2. Reflection in the midpoint of two equal-radius centres takes one circle
   intersection `B[k]` to the other, `U[k]=C[k]+C[k+1]-B[k]`.
   Thus `U[k]` is exactly distance `R` from both ring sites.
3. Reflection in the x-axis sends `C[k]` to `C[8-k]` and `U[k]` to
   `U[(7-k) mod 9]`, and fixes both hubs. The four fan constraints therefore
   give the seven active fan faces with edges `1,2,3,4,5,6,8`.
4. The points `(m,+sqrt(R^2-d^2))` and its reflection are exactly distance
   `R` from both hubs. The fifth constraint and reflection give central faces
   `(6,H0,H1)` and `(2,H0,H1)`.

The remaining faces `(C0,C1,H1)` and `(C7,C8,H1)` are checked by an explicit
interval determinant formula for their circumcentres, with radius strictly
smaller than `R`.

The positive hull, embedding, incidence and site-exclusion tests show that the
listed triangles form a triangulation of the convex hull. Their strict empty
circumcircles then identify all Delaunay triangles and Voronoi vertices;
no unproved general-position assumption is made. Boundary arcs tile by
`sum(a)=pi`, and the boundary is covered by their corresponding disks.
The usual nearest-site/Voronoi critical-point argument transfers these exact
identities and arithmetic margins to coverage of the entire closed unit disk.
These analytic identities and the critical-point argument are mathematical
explanations of the checked quantities, **not proof-assistant-checked lemmas**.

## Arithmetic backend and input provenance

The backend has 64 significant decimal digits. Addition, multiplication and
division round endpoints down/up explicitly. Decimal square root is correctly
rounded to nearest; one adjacent representable value on either side encloses
the true root. Sine and cosine use degree-113/112 Taylor polynomials with an
explicit Lagrange remainder on `|x|<=8`. Pi is enclosed afresh by Machin's
identity and alternating rational arctangent sums. Neither Python binary64
trigonometry nor a stored decimal pi is used as a bound. Binary hexadecimal
input strings are recovered as exact dyadic rationals with `Fraction`.

The small public inputs are:

- [`root_input.json`](../math_data/n11/root_input.json): only `center_hex` and
  `radius_hex` from the original `repaired_tc_krawczyk.json`.
- [`schur_fields.json`](../math_data/n11/schur_fields.json): only each field's
  name, 51 rational input stresses and 36 candidate output weights, extracted
  from `cosine_dbm_local920.json` (371 fields).

Each input embeds its repository-relative historical source path, exact source
SHA256 and extraction description. The original data and proof executors were
not rewritten. Source hashes document provenance; they do not establish any of
the inequalities checked by this command.

## What this command does not replay

The following are **not covered by `SCOPED_PASS`**:

- All 36 C450 two-circle capacity intervals and their complete subdivision
  checks (historical counts around 198,000 kernel boxes per replay).
- All seven actual metric graph-class exclusions and their full-domain
  face/switch/sector certificates.
- All 2,386 global angular energy leaves, 120 local containment leaves and
  2,505 splits of the final eight-dimensional simplex/DBM certificate.
- The local stress-ball inequalities used by those 120 leaves.
- The unrestricted analytic geometry/topology reduction from an arbitrary
  eleven-centre cover to the surviving canonical oracle.

The global n11 tree has **2,506 terminal leaves**; the **7,041** count used for
n12 must not be attached to this command. Re-deriving all Schur fields supplies
their scalar energy identities, but it does not establish the terminal angular
inequalities. Accordingly, `full_global_proof_replayed` is always `false` in
this report. A future full-chain entry point must run the missing numerical
checks and carry their analytic interfaces explicitly; old status summaries
cannot discharge them.

中文：这个入口已真正重算候选精确根、达到构型的区间几何条件及全部371个
能量场的有理消元。它返回“有限范围核验通过”，不把 n11 的全局下界称为已
独立重跑；C450、七个图类排除及2506个终端角域叶仍属于未重跑范围。
