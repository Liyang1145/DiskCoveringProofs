# n=14 three-equation system: independent derivation and the new root

Scope `research-2026/next-cover-global/members/candidate/`. Inputs read-only.
Reproduce: `py -3 -B members/candidate/three_eq_check.py` → `evidence/three_eq_check.txt|json`.
**All numeric; no exact coverage, no optimality claim.**

## 1. Sign audit — my earlier sign was WRONG, confirmed

Branch audit over all 8 sign choices of the three square roots, evaluated exactly on the
`th` literals (error = max deviation from the data's B, D, t):

| σ_B | σ_D | σ_t | error |
|---|---|---|---|
| **+** | **−** | **+** | **4.0e-51  ← the data** |
| − | − | − | 0.1138 |
| − | − | + | 0.2450 |
| + | + | ± | 0.3151 |
| − | + | ± | 0.3151 |

So `Bs = r + sqrt(r²−(A−z)²)`, `D = 1 − sqrt(r²−C²)`, `t = r + sqrt(r²−z²)`. My earlier
`Bs = r − sqrt(...)` was wrong, as you said.

**One fewer free sign than expected:** with the five relations, `A − z = (U−z)/2` where
`U = sqrt(1−r²)`, and the algebraic identity

```
r² − (A−z)² − (r²−z²) = −(U+3z)(U−z)/4
```

is **not** identically zero, so `σ_B` is *not* forced by `σ_t` through an identity — it is
selected by the data (σ_B = +). Both the σ_D = − and σ_B = + choices are genuine branch
conditions that must be carried.

## 2. The three equations (as implemented)

Free coordinates `(z, C, r)`; `U=√(1−r²)`, `A=(z+U)/2`, `s=U`, `V=√(r²−z²)`, `t = r+V`,
`B = r + √(r²−(A−z)²)`, `Wd=√(r²−C²)`, `D = 1−Wd`.

- **(EQ1) A–C switch:** exist `p` with `|p| = 1` and `|p−(A,B)| = r = |p−(C,D)|`.
  Implemented as: intersect `S¹` with the circle `|p−(C,D)| = r`, take the branch whose
  `|p−(A,B)| − r` is smallest in modulus. *(No squaring ambiguity: both circle equations
  are used directly.)*
- **(EQ2) circ3:** the three centres `(A,B)`, `(C,D)`, `(0,t)` have circumradius exactly `r`,
  via `R = abc/(4·Area²)` in squared form (so no square root / branch ambiguity).
- **(EQ3) stationarity:** `det ∂(EQ1,EQ2)/∂(z,C) = 0`.

## 3. The old `hprec` point is NOT stationary — confirmed

| quantity | value |
|---|---|
| EQ1 residual at old point | 1.17e-61 |
| EQ2 residual at old point | 3.89e-62 |
| switch point `p` found | `(0.61875918826019150618, 0.78558071955947906)`, `|p| = 1.0` |
| **`det ∂(EQ1,EQ2)/∂(z,C)` at old point** | **−3.0836e-8** (mine) |
| lead's report | −4.6184e-10 |

**Discrepancy reported honestly:** my Jacobian determinant differs from yours by a factor
≈ 66.8. Both are nonzero, so the conclusion (*the old point is not stationary*) is the same,
but the two `Jdet` normalisations are not identical and one of us has a different scaling or
convention. This must be reconciled before either number is used as a certificate.

## 4. The new root — independently reproduced

Solving `(EQ1, EQ2, EQ3) = 0` from the old point:

```
z_new = 0.3268180689499140633184051253300649312206
C_new = 0.2919411189649396619446920604622870296816
r_new = 0.3317320342762341225578155488024095382709     (residuals ≤ 1.4e-61, Jdet ~1.4e-37)
```

| | r |
|---|---|
| old `hprec` | 0.3317320342762341235155066403893542 |
| **new root (mine)** | **0.3317320342762341225578155488024095** |
| lead's value | 0.3317320342762341225578155488 |
| **difference from lead** | **2.4e-30** |
| improvement over old | **−9.5769e-19** |
| equals your test threshold `0.3317320342762341226` | `r_new ≤ threshold` ✓ (by 4.2e-20) |

Magnitudes at the new root (all changed by ≈1e-9 relative, as you said):

```
A = 0.6350958631640119662587036718917151
B = 0.4542511926129566135529851059221879
C = 0.2919411189649396619446920604622870
D = 0.8424673823535344208160175653985371
s = 0.9433736573781098691990022184533652
z = 0.3268180689499140633184051253300649
t = 0.3886186967982857037751131529620841
r = 0.3317320342762341225578155488024095
```

## 5. The new root still realises the covering radius

Rebuilding the 14 centres at the new root and enumerating nearest-site Voronoi vertices
inside `D` (authoritative indexing, as per `JOIN-CONFIRMED-n14.md`):

- **deepest hole `f = 0.331732034276234122557815548802`**, `f − r_new = 5.9e-41`;
- 2 of 16 vertices are slack (`f − r = −0.0109112`);
- **the active triples are now `[0,4,12] [1,5,13] [2,6,12] [3,7,13]` (×4 rotation) and
  `[10,11,12] [10,11,13]`** — note these are *not* the old root's active triples
  (`[0,6,13]`-type), so the contact structure changed; the old solution was not merely
  non-stationary, its activity pattern was different.

So `R_D(new configuration) = r_new` to 5.9e-41: the new root does cover `D` at a strictly
smaller radius than the old `hprec` object. This is a **numeric** statement; your finite
exact upper test (`improved-upper-test.json`, 493 candidates / 0 uncovered at
`0.3317320342762341226`) is the certified side and is not replaced by this.

## 6. What is still missing

- `Jdet` normalisation reconciled (mine −3.08e-8 vs yours −4.62e-10).
- The root isolated **exactly** (interval/Krawczyk on a rational box), not merely to 30 digits.
- Exactification with the branch conditions of §1 carried explicitly — the squared
  eliminations must retain `σ_B = +`, `σ_D = −`, `σ_t = +`.
- Independent replay of the finite exact upper test on the new rational coordinates using
  an independent kernel (your note asks for exactly this).
- Nothing here speaks to global optimality, and no symmetry statement about n13/n15 is made
  (withdrawn earlier; unresolved).
