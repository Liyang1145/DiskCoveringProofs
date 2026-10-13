# Audit: lead/repair_tc_krawczyk.py — peripheral normalization and 12D Krawczyk root certificate

Reviewer: r20-geometry. Read-only wrt `lead/`: the module is **imported** (its `__main__` block,
which rewrites `lead/repaired_tc_krawczyk.json`, does not run). Evidence:
`audit_repair_tc_krawczyk.py/.out.txt/.json` (this directory).

**Verdict: the normalization is legitimate and the certificate structure is sound; the AD
enclosure audit stays formally pending, but an independent finite-difference/re-scaling audit of
the derivative blocks passes, and two quantitative limits are added.** No counterexample found.

## 1. What the normalization block is (decoded independently)

The system is 12 equations in 12 unknowns $u=(z_0,\dots,z_6,\lambda_0,\dots,\lambda_4)$:
$F_{0..4}=$ the five residual functions $f_k(z)$; $F_{5+i}=\delta_{i6}-\sum_{k<5}\lambda_k\,j_k{}_i(z)$
for $i=0..6$, where $j_k{}_i=\partial f_k/\partial z_i$. The second block is **exactly**
$\sum_k\lambda_k\nabla f_k=e_6=\nabla z_6$, i.e. **KKT stationarity for minimising $z_6=R$ on
$\{f_0=\dots=f_4=0\}$**, with $\lambda$ the multipliers. It is not an arbitrary gauge: with only
the five constraints the solution set is $7-5=2$-dimensional (exactly the obstruction recorded for
the old square forms), and the seven stationarity equations cut that manifold to isolated points.
Verified at the reported root: residual max $1.4\cdot10^{-58}$, stationarity max
$1.3\cdot10^{-57}$, the combination reproduces $e_6$ to $10^{-57}$.

## 2. Independent derivative audit (different inference: central differences in 60-digit mpmath)

* the 5 residuals' AD gradient block $j_k{}_i$ and second-derivative block $h_k{}_{ij}$ agree with
  central differences to $5.4\cdot10^{-5}$ resp. $3.5\cdot10^{-1}$ at step $2^{-18}$ — but the
  agreement is **truncation-limited, not defective**: re-scaling the step gives clean $O(h^2)$
  convergence (gradient error $11.9,\,8.0,\,0.23,\,0.0138,\,8.6\cdot10^{-4},\,5.4\cdot10^{-5},
  \,3.4\cdot10^{-6}$ for $h=2^{-8},\dots,2^{-20}$). Equivalently, the residual's higher
  derivatives are enormous near this root ($f'''\sim10^{7}$, $Q/\mathrm{rad}\approx4.4\cdot10^{6}$).
* my re-derivation of the manual chain-rule block of $J$ (rows 5..11) from the AD blocks agrees
  with the assembled $J$ **exactly** (max difference 0.0), and the assembly is correct by
  differentiation of $F_{5+i}$.

## 3. Rank / isolation / uniqueness margins (independently recomputed)

* five constraint gradients: rank **5**, singular values $34.0,\,11.4,\,3.95,\,1.97,\,0.666$
  (two null directions in $\mathbb R^7$) ⟹ $\lambda$ is **unique**, margin $0.666$.
* full $12\times12$ Jacobian at the root: rank **12**, smallest singular value $0.2324$ ⟹ the root
  is isolated; Krawczyk gives uniqueness inside the certified box.

## 4. Krawczyk test vs box radius (same centre, same float64 $Y$)

| rad | $2^{-20}$ | $2^{-23}$ | $2^{-26}$ | $2^{-30}$ (script) | $2^{-33}$ |
|---|---|---|---|---|---|
| inclusion | **fail** | pass | pass | pass | pass |
| $Q=\|I-YJ(X)\|_\infty$ | 4.171 | 0.521 | 0.0651 | 0.00407 | $5.09\cdot10^{-4}$ |

So $Q\approx4.4\cdot10^{6}\,\mathrm{rad}$: the usable box radius is $\lesssim2.3\cdot10^{-7}$, and
the script's $2^{-30}\approx9.3\cdot10^{-10}$ sits comfortably inside ($Q=0.0041$, shift ratio
$0.0041$). The old C408 radius $10^{-7}$ is right at the edge ($Q\approx0.5$) — consistent, no
conflict. $Q$ is dominated by the second-derivative term, not by the float64 inverse $Y$ (the
$Y$-induced part is $O(10^{-9})$), so using a float64 $Y$ as exact dyadic entries is harmless here.

## 5. Interface and scope notes

* Certified $R$-coordinate enclosure $[0.3799838531198365386519,0.3799838531198408407926]$
  contains the registered covering radius $R^\*=0.3799838531198387$ — a cross-check of the root,
  **not** an implication about covers.
* Scope as declared by the script: an isolated root of the explicitly specified symmetric TC KKT
  system only; no full-geometry / local-minimum / global statement. Nothing in this audit upgrades
  that.
* Implementation notes (not mathematical): (i) the module resolves
  `Path('research-2026/session2/n11tc/py')` against the **current working directory**, so it must
  be run/imported from the repository root (from any other CWD the import fails); (ii) running it
  rewrites `lead/repaired_tc_krawczyk.json` (I imported instead); (iii) its negative control is
  weak — it shifts one $\lambda$ coordinate and the inclusion fails trivially because the centre
  is no longer a root; a stronger control would perturb along the two tangent directions of the
  constraint manifold and show that the *interval* test still refuses.
* Pending (as the script itself states): an independent *enclosure* audit of the interval AD over
  the box (my check is derivative-consistency at a point plus scaling, which is calibration and
  cannot replace an interval-enclosure proof).

Repro (from the repository root):
```
py -3 -B research-2026/team-current/r20-geometry/audit_repair_tc_krawczyk.py
```
