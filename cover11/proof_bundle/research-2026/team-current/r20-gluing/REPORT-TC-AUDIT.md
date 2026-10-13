# R20-TC-AUDIT — independent representation certification of the symmetric TC `res5` system

Author: cline2 / DS v4.1f (r20-gluing, own file set; **no lead file and no historical file
modified**). Two rounds of work are recorded here; the second supersedes the first's framing.

---

## 0. Object and sources (read-only)

| file | role |
|---|---|
| `session2/n11tc/py/tc_s32_kraw.py` 121–154 | `res5`: the 5 independent representatives (C366) |
| `session2/n11tc/py/tc_s33_kkt.py` 130–160 | nested-dual second-order AD (`f5_nested`, `J12_iv`) |
| `team-current/lead/repair_tc_krawczyk.py` | Krawczyk wrapper, 12×12 = 5 tight + 7 pins |
| `team-current/lead/repaired_tc_krawczyk.json` | fixed Y, center hex, radius hex, F/K enclosures |

## 1. Framing correction (lead audit, accepted)

The first round compared my SymPy derivatives against the repo's nested dual **at the threshold
point**: gradient `0.00e+00` difference, Hessian `4.3e-50`. That is **pointwise numerical
agreement at 50–60 digits**, not an identity proof. "0 diff" is not a symbolic equality, and the
earlier phrasing "exact-symbolic equality" is withdrawn. What survives: the two derivative
*representations* agree to evaluation precision at that point, and the nested-dual algebra is
consistent with an independently written symbolic model.

No interval rank test was performed (12D invertibility is already guaranteed by the contraction).

## 2. Interval evaluation over the lead's repaired box (`r20_tc_iv1.py`)

My SymPy model (independent construction from the explicit geometry) is compiled with
`sympy.lambdify(..., modules=<own mpmath.iv sin/cos/sqrt/pi backend>)` and evaluated over
`center ± 1e-9` with `iv.dps = 40`; center/radius hex are reused from the lead JSON.

| block | comparison with the lead's own interval `J12` (`tc_s33_kkt.J12_iv`) |
|---|---|
| first-order block 5×7 (35 entries) | **35/35 entries overlap** |
| second-order block −Σλ_m H_m (7×7 = 49 entries) | **0 non-overlaps** |
| mixed-partial enclosures | endpoint spread 0 (same expression evaluated twice — a self-check, not a cross-check) |
| max \|Hessian\| entry over the box | 12014.04 |

Overlap is a **control**, as specified; interval equality is neither expected nor claimed. All
interval entries are finite and non-degenerate where the model is non-constant (the
`∂f5/∂a3 ≡ 0` directions stay exactly `[0,0]`).

## 3. Independent one-box Krawczyk inclusion (`r20_tc_iv2.py`)

Residuals/gradient/Hessian from **my** SymPy + `iv` backend; box and fixed `Y` reused from the lead
certificate; the 12×12 assembled independently as
`J[0:5,0:7] = grad f`, `J[5+i,0:7] = −Σ_m λ_m H_m[i,:]`, `J[5+i,7+m] = −grad f[m][i]`.

| quantity | independent value | lead certificate | agreement |
|---|---|---|---|
| `F(center)` (12 components) | computed as point intervals | identical | **max abs diff = 5.7e-40** |
| `K(c,U) − c` | computed | stored | **max abs diff = 1.0e-13** (box radius 1e-9 ⇒ 1e-4 relative) |
| contraction ∞-norm `Q = max_i Σ_j \|(I − Y J(U))_ij\|` | **[0.0043324, 0.0043324]** | 0.00437197 | same order, mine 1.6 % tighter |
| `K(U) ⊂ int(U)` strict, all 12 coordinates | **True** | True | pass |
| negative control (λ shifted by 0.01) | — | fails (does not certify) | discriminating |

Containment margins: the largest coordinate shift is index 4 (`K − c` spans ≈±4.33e-12) inside the
box `(−1.0e-9, 1.0e-9)`; the `R` coordinate spans ≈±2.0e-15. So the inclusion is not marginal.

### 3b. Corrections applied to this section (second lead audit, both load-bearing)

The first version of `r20_tc_iv2.py` had two defects and its "proved-interval" reading is
**withdrawn**:

1. the box was built from `float(z ± rad)`, whose outward-rounded endpoints do not enclose the true
   box. Now: `U_i = [exact_mpf(c_hex_i) − rad, exact_mpf(c_hex_i) + rad]` for **all 12**
   coordinates, with `exact_mpf` converting the dyadic hex through `Fraction` (exact);
2. the Hessian block was multiplied by the **point** values `numeric_root[7:]` rather than by the
   box variables, so the matrix was not a full-12D enclosure. Now the multipliers are `U[7+m]`.

Also applied: `F(center)` from the exact dyadic center hex (not a re-parsed numeric string);
containment compared on `K − c` against `(−rad, rad)` (no float endpoint arithmetic); full hex and
six source SHA-256 hashes recorded in `r20_tc_iv2.json`.

Hypothesis recorded as requested: **no verification of `Y` is attempted or needed.** Any fixed
dyadic `Y` is legal; `‖I − Y J(U)‖_∞ < 1` already yields `Y J` invertible and hence `Y` invertible,
so an extra inverse-enclosure step would be useless.

## 4. Verdict and scope

* **Independent representation certified (interval)** for the 12×12 symmetric TC KKT root: a
  from-scratch symbolic model, compiled onto a hand-written interval backend, reproduces (i) every
  interval Jacobian entry of the lead code up to overlap, and (ii) a full-12D Krawczyk enclosure
  with strict inclusion and contraction `Q = 0.0043324 < 1` on the same one box.
* Root data reproduced: `R = 0.3799838531198387` (dyadic center hex
  `0x1.851bb1fd39d40p-2`-class, see the JSON) — the C249-consistent value.
* Language discipline: the earlier derivative comparisons are **numeric** (pointwise agreement at
  50–60 digits). The phrase "pointwise-exact" is withdrawn; nothing here is an identity statement.
* **Scope guards.** This certifies an isolated 12×12 root of the explicitly specified symmetric TC
  KKT system on **one box** using the lead's fixed `Y`. It does **not** establish: any
  covering-radius or global-optimality statement; the full interval branch-and-bound; family-wide
  (multi-box) rank or independence; and it does not touch C408's old withdrawal. 12D invertibility
  is taken from the contraction as instructed, not re-tested.
* No claim registered; no lead/historical file modified.

## 5. Repro

```
py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_iv1.py     # interval eval + overlap control
py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_iv2.py     # independent Krawczyk inclusion
py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_audit.py   # SymPy model (point comparison)
py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_audit2.py  # nested dual vs SymPy (point)
py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_audit3.py  # all 5 residuals + rank (point)
py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_audit4.py  # joint F12 + mutation control
py -3 -B -X utf8 research-2026/team-current/r20-gluing/r20_tc_audit5.py  # dual coefficients
```
Evidence: `r20_tc_iv1.json`, `r20_tc_iv2.json`, `r20_tc_symbolic.json`, `r20_tc_audit2..5.json`.

---

## Appendix: earlier (superseded) point-comparison detail

The first-round scripts remain valid as point comparisons and as the source of the SymPy model:
full 5×7×7 Hessian agreement with the nested dual (max diff 4.3e-50), Jacobian rank 5 at the point
(singular values 34.03, 11.41, 3.955, 1.965, 0.666), mutation control (sqrt derivative
`1/(2√x) → 1/(3√x)` shifts the gradient by 9.15e+00, so the gate is discriminating), and the dual
coefficients `e_R = Σ c_i ∇f_i` with `c` matching the repo's λ to 8.3e-17. These are pointwise
statements and are labelled as such.
