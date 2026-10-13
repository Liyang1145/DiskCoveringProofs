# TC-FAMILY-ELIMINATION — symmetric active family, finite branch (corrected representation)
### (r20-gluing, sole writer this round · **no claim registered** · C899 stays pending)

**Caliber (quote with every number below).** Everything here concerns the **symmetric active
family**: mirror-symmetric configuration, the **5 active tight rows**, boundary saturation
assumptions, **finite branch** only. It is **not** a statement about the whole ring domain, not
about "moving rings" (that wording is withdrawn), and not about the unconditional n=11 optimum.
All root readings are **point readings** at the certified centre, whose own accuracy is ≈ 4.3e-12
(Krawczyk image half-width), so O(1e-16) deviations are expected and are not small numbers.
Rank-drop readings are **numeric diagnostics only**.

Evidence / repro:
```
py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_r_dependency.py   # corrected R-dependency
py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_germ_arith.py    # germ-file arithmetic audit
py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_elim2.py         # historical E0/E0b checks
```

---

## §0 Correction notice (what was withdrawn and why)

The 20:35–20:38 version of this file claimed:

1. *"(U_1) with `y1` is LINEAR in `R`, hence `R = −[(ReU_8−ReU_1)²+(ImU_1)²]/(2(ReU_8−ReU_1))` is an
   explicit function of the angles"*, and
2. *"the residues are exactly TWO angle-only equations `g1, g2`"*.

**Both are withdrawn.** `ReU_8, ReU_1, ImU_1` are built from `ρ_k = cos a_k − T_k` with
`T_k = √(R² − sin²a_k)`, so they **depend on `R`**; substituting `y1 = ReU_8 + R` cancels only the
*explicit* `R²` term and leaves `R` inside every `U`. The rearrangement is a **fixed-point map**
`φ`, not a solution formula. Numerical demonstration (`r20_tc_r_dependency.json`):

```
φ(R*) − R*             = +6.4e-17      (the fixed-point identity; R* = 0.3799838531198387)
φ(R*+1e-3) − (R*+1e-3) = −4.46e-3
φ(R*−1e-3) − (R*−1e-3) = +4.50e-3
∂ρ_k/∂R = −R/T_k = −3.4311, −2.1031, −1.4617, −5.5285, −11.4930   (k=0..4; finite diff agrees to 8e-27)
∂ReU_1/∂R = +0.7844                                                (finite diff = analytic chain)
```

Consequently the correct residue count is **THREE equations in FIVE unknowns** `(a0..a3, R)`
(§3), and the leverage statement of §4 is restated accordingly. The **exact** elimination content
that survives is: the two hubs `y0, y1` (closed form), and `h` derived from `h² = R² − d²`.

---

## §1 E0a — chain identity (valid, symbolic + numeric)

With `e_k = e^{i(θ_k+a_k)}`, `C_k = ρ_k e^{iθ_k}`, `U_k = C_k + C_{k+1} − e_k`,
`ρ_k = cos a_k − √(R²−sin²a_k)`:

```
ring identity : ρ² − 2ρ cos a + 1 − R² = 0                              [SymPy simplify → 0]
chain identity: U_k − C_k = C_{k+1} − e_k = e^{iθ_{k+1}}(ρ_{k+1} − e^{−ia_{k+1}})
                ⇒ |U_k − C_k| = |U_k − C_{k+1}| = R                    [all k, via the ring identity]
axis facts    : θ_8 + a_8 = π (e_8 = (−1,0)), ρ_8 = ρ_0 ⇒ Im U_8 = 0;  C_4 = (ρ_4, 0)
```

Numeric at the certified centre (`mp.dps = 60`): `max_k |U_k−C_k|−R = 1.9e-61`,
`max_k |U_k−C_{k+1}|−R = 7.8e-62`, `Im U_8 = −1.1e-61`, `Im C_4 = 0`.
The symbolic statements of both identities were verified with generic symbols (→ 0).

## §2 E0b — hub elimination (valid part, exact)

```
(U_3) + chain identity |U_3 − C_4| = R + C_4 on the axis
      ⇒ y0 = 2·Re U_3 − ρ_4                       (branch A; the other axis root is y0 = ρ_4 = C_4.x)
(U_8) + Im U_8 = 0 (axis)
      ⇒ y1 = Re U_8 + R                           (branch B; the other root is y1 = Re U_8 − R)
h   : h² = R² − d²  (derived; d = (y1−y0)/2), and the waist row can be REWRITTEN as
      h = [((y0+y1)/2 − ReC_6)² + (ImC_6)² − d²] / (2 ImC_6)      (needs ImC_6 = 0.694424 ≠ 0)
```

These are exact eliminations of `y0, y1` (and a rewrite of the waist row for `h`), valid on the
stated branches, **not** an elimination of `R`. Root readings: `y0` diff `4.58e-16`,
`y1` diff `6.86e-18`, closed-form `h` diff `−5.3e-17`.

**Branch table (complementary roots, feasibility).**

| branch | value at the centre | geometric meaning | feasibility |
|---|---|---|---|
| `y0 = 2ReU_3 − ρ_4` | +0.2729774663 | certified `H0` | **feasible** (certified) |
| `y0 = ρ_4` | +0.8925217299 | `H0 = C_4` (hub coincides with ring centre 4) | excluded **if** hubs must be inner-disk centres: `|H0| = 0.8925 > 1−R = 0.6200` |
| `y1 = ReU_8 + R` | −0.1494284989 | certified `H1` (negative x-axis) | **feasible** (certified) |
| `y1 = ReU_8 − R` | −0.9093962052 | other axis intersection of `∂B(U_8,R)` | excluded under the same hypothesis: `|H1| = 0.9094 > 1−R` |

The exclusion is **conditional** on the inner-disk-centre requirement `|H| ≤ 1−R`, which belongs to
the definition of the class and is not proved here.

## §3 The corrected closed representation: 3 equations / 5 unknowns

Unknowns `(a0, a1, a2, a3, R)`; everything else is derived:

```
ρ_k = cos a_k − √(R² − sin²a_k)      (k = 0..4; mirror ρ_{8−k} = ρ_k)
θ_k = explicit recursion (θ_4 = 0),   C_k = ρ_k (cos θ_k, sin θ_k),   e_k = e^{i(θ_k+a_k)}
U_k = C_k + C_{k+1} − e_k
y0  = 2 Re U_3 − ρ_4 ,   y1 = Re U_8 + R ,   m = (y0+y1)/2 ,   d = (y1−y0)/2 ,   h = √(R² − d²)

E1 : (y1 − ReU_1)² + (ImU_1)² − R² = 0                       (U_1 tight row)
E2 : (y0 − ReU_2)² + (ImU_2)² − R² = 0                       (U_2 tight row)
E3 : (m − ReC_6)² + (h − ImC_6)² − R² = 0                    (waist tight row)
```

At the certified centre: `E1 = 5.26e-17`, `E2 = 2.01e-18`, `E3 = 1.35e-16`
(`r20_tc_r_dependency.json`). The family is 2-dimensional, as it must be (5 unknowns − 3 equations
= 2, matching the germ dimension of C899).

**Dependency graph (the point of §0).**

```
a_k  → sin a_k, cos a_k, θ_k, e_k,  and T_k jointly with R
R    → T_k = √(R² − sin²a_k)  →  ρ_k  →  C_k  →  U_k  →  Re U_k, Im U_k
R    → y1 = Re U_8 + R,  d = (y1−y0)/2,  h = √(R²−d²)
R    → explicit  −R²  and  +R  terms in E1, E2, E3
```

`R` is therefore **not eliminable** from the closed representation: it occurs inside every `T_k`,
inside `y1`, inside `d, h`, and explicitly. The rearranged forms
`2R(ReU_8−ReU_1) + (ReU_8−ReU_1)² + (ImU_1)² = 0` (E1) and
`2h·ImC_6 = (m−ReC_6)² + (ImC_6)² − d²` (E3) are useful *as equations* (no explicit `R²` term), but
they determine `R` only **implicitly**; `dE1/dR = −3.7013 ≠ 0` at the centre, so `R` is *locally*
an implicit function of the angles from E1 alone — no closed form exists.

**Concyclic / crescent interface (cited, corrected).** Each tight row is the condition "the triple
formed by the two adjacent ring centres and the hub point has circumradius `R`", i.e. `F_c = 0` with
`F_c(a,b,c) = 4R² det(b−a, c−a)² − |a−b|²|c−a|²|c−b|²` (normal form of
`r20-alternative/CENTRAL-CRESCENT-STRESS.md`). **Warning: C894 was retracted** (its part (ii)
reversed a half-plane containment); the product-identity/concyclic part may be cited, the retracted
universal implication must not. **C896 is `numeric`** and cannot serve as an exact filter. Own
numeric check at the centre: `F_c(C_2,C_3,H0) = −6.4e-18`, `F_c(H0,H1,C_6) = −5.7e-18`.
Division of labour: C879/C890 eliminate hubs by **relaxation** (necessary-condition filters); §2
eliminates them **exactly** on the tight branch. The two calibers must not be mixed.

## §4 Leverage (corrected) and what is *not* achieved

1. **Presentation gain (exact).** 7 unknowns / 5 tight rows → **5 unknowns / 3 rows**, with
   `y0, y1` in closed form and `h` derived; all coefficients analytic, no resultants, no Gröbner.
2. **Branch rigidity (conditional).** The two complementary root choices are excluded by
   `|H| ≤ 1−R` (§2 table) — this is what makes the branch a *single* configuration family rather
   than four; it is conditional on the inner-disk-centre hypothesis.
3. **Threshold = finite Lagrange problem.** On `{E1=E2=E3=0} ⊂ ℝ⁵`, the `R`-critical points solve
   `e_R − Σ_{i≤3} λ_i ∇E_i = 0` (5 equations) together with the 3 rows: **8 equations in 8 unknowns
   `(a0..a3, R, λ1..λ3)`** — finite and analytic, replacing the 12×12 rank-numerics route. The
   `3×5`/`4×5` singular-value readings (`σ = [12.00, 5.74, 1.51]` from the reduced-coordinate
   differentiation used here; `[1.8998, 1.0971, 0.2644]` from the worker's concyclic-variable
   computation — the two differ by variable scaling and both are diagnostics; augmented 4th value
   `6.9e-16` / `5.0e-16`) remain **numeric diagnostics only**: a small numerical singular value does
   not prove an exact rank deficiency, and a rank-condition ⇔ KKT equivalence would need the 3×5
   full-row-rank as a separate hypothesis.
4. **Not achieved: a univariate `q(R)`.** The reduced form is not polynomial in `(a, R)`
   (`R` sits inside `T_k = √(R²−sin²a_k)` and `h`); rationalising first is required. The
   *polynomial* encoding of the same content (rotations and `ρ` carried as variables) is measured at
   **19 variables / 17 equations / total degrees `[2,6,8,10,14,18]` / largest expression 23 210
   ops** — the recorded explosion point. Per instruction, no 8D resultant was expanded.
5. **Decidability scheme (proposed, NOT executed).** "∃ tight configuration with `R < r*` in this
   branch" is a 5-variable feasibility question on `{E1=E2=E3=0}` with `R` implicit. A rigorous
   route would be: (i) an explicit-inverse (Neumann) rank certificate for the 3×5 Jacobian in the
   style of C899, giving smoothness of the family; (ii) certified enclosure propagation along the
   family with the C891-style interval machinery, splitting cells only where the enclosure is
   inconclusive — every conclusion an enclosure statement, never a sampled grid. No such run is
   claimed here.
6. **Falsifier.** Any `(a, R)` in the branch domain with `E1 = E2 = E3 = 0` and `R ≠ r*` refutes the
   branch-level uniqueness phrasing; this is the reading that would change the decision.

## §5 Status

**Verdict (b)** for the `q(R)` target inside this round's budget, with the reduction above, the
explosion-point specification, and the named representation change (`R` kept as a variable; attack
the 8-equation Lagrange object rather than the 19-variable content system). No claim registered;
**C899 remains pending**; no new precision, no new box, no branch-and-bound was used.
