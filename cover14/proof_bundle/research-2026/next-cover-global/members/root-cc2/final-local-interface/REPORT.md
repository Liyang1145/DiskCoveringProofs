# root-cc2 final-local-interface: audit of the q10 localization chain (corrected)
# C1355 exact 2e-6 anchor cell -> C1262 gauged site box -> no r < r*

Scope `members/root-cc2/final-local-interface/` (only). Lead/member artifacts read-only.
**No claim registered**; no lead file modified. Independent arithmetic only.
Evidence: `evidence/interface02.txt` (exact-token trace), `evidence/interface01.txt`.

## 0. Correction of my previous version

The previous draft claimed the saved `0.8458` and my `0.199` were "different constant
sets, both < 1". **That was wrong; the lead's diagnosis is right: it is an arithmetic slip
on my side.** `diagnostic.py` lines 64-65 use exactly
`exit_rhs = (665/1000)*(eta + a*beta^2)`, `exit_lhs = kappa*eps^2`, with
`beta = anchor_eps + alpha` (line 62) — the **post-gauge** anchor bound, not `anchor_eps`.
I substituted `beta = anchor_eps = 2e-6`. With the saved `beta`, exact-Fraction
recomputation reproduces the saved rationals **exactly**:

| token | value |
|---|---|
| `RHS = (665/1000)(eta + a*beta^2)` | saved `exit_rhs` (match `True`) |
| `LHS = kappa*eps^2` | saved `exit_lhs` (match `True`) |
| `RHS/LHS` | **0.84578364474801238** = saved `display_ratio` |
| `beta^2` ratio (post-gauge / anchor-only) | 4.249059 |

So `0.846` **is** the true value of that formula; my `0.199` came from the wrong `beta`
token. Sections below are corrected accordingly.

## 1. The chain under audit

    (global necessity)  C1330/C1366 + Q10-QUADRATIC-GLOBAL-BRIDGE
        -> remaining full-graph-879 anchors within <1e-6 of the bridge reference, true
           candidate within 2e-14                                        [anchored cell]
    (localization)      C1355 penalty box (LOCAL-DIRECTIONAL-BOX.md) -> gauged site box,
                        r >= r*
    (attainment)        C1167 exact root

## 2. Independently reproduced constants (exact Fractions)

| quantity | value | check |
|---|---|---|
| `b` | 0.3743708410423505 | `< 1` |
| `B` | 72.9374352744 | `\|\|W\|\|_2^2` upper bound |
| `mu = (1-b)/B` | 0.00857761390435 | residual `0` |
| `kappa = mu/(2(1+27/1000))` | 0.00417605350747 | residual `0` |
| `U - r*_lo <=` | 1.745218445119759e-17 | from the root box |
| `H = (U+2e-6)^2 - r*_lo^2` | 1.3269321371165155e-06 | recomputed |
| lens `alpha = H/[2r*(s-sqrt H)]` | 2.1226490125528137e-06 | **identical** to saved `gauge_angle_upper` |
| `beta = anchor_eps + alpha` | 4.1226490125528137e-06 | **identical** to saved `post_gauge_anchor_bound`; `<1e-3` |
| `(ENTRY) RHS/LHS` | **0.84578364474801238** | exact-Fraction match; `<1` |
| `sqrt((U^2-r*_lo^2)/kappa)` | **5.265633e-08** | equals saved `site_error_display` 5.265632842102119e-08 |

## 3. The norm entry (corrected wording)

* The anchor cell is a **sup-norm** statement on the ten principal angles; every site
  statement is **Euclidean** (`||C-C*||_2^2 <= (U^2-r*^2)/kappa`); the only implication
  used is the elementary `|v|_inf <= |v|_2`. This is the correct norm entry, **not** the
  C1352 growth ratio.
* **Direction of containment (previous draft reversed this).** At the same `eps`,
  `|v|_inf <= |v|_2` gives `{ |v|_2 <= eps } subset { |v|_inf <= eps }`: the Euclidean
  ball is the *smaller* set, so the **sup box is the weaker (larger) hypothesis**. A
  statement valid on the sup box is therefore valid on the Euclidean ball; the sup box is
  what is assumed, and it is the weaker of the two hypotheses.
* `K = 29/9` is **not** the anchor-lens factor. It appears only in the optional
  joint-gauge (Procrustes) variant of the member report §4, where the final X+ alignment
  inflates the per-site error by at most `K`. The anchor-lens factor is
  `alpha = H/[2 r* (s-sqrt H)]`.

## 4. Interface verdicts

**Proved (locally, in the chain):** penalty sign and strict convexity (`P(C*)=0`,
`grad P(C*)=0`, `W^T Hess(P) W >= (1-b) I`, `Hess(P) >= mu I`; covers have `P <= 0` while
`P > 0` off `C*`; the negative/positive `delta_k` split with the weaker saved sign is
sound); gauge `C_19 = 0` with the gauge Hessian inside the matrix bound; Cartesian
interpolation and first exit (`rhat_t - r* <= t eta + a t(1-t) beta^2`, order preserved for
`beta <= .001`, `t = eps/D`, giving `(ENTRY)`); anchor-only gauge control via the X+ pair
with the lens `H/[2r*(s-sqrt H)]` (reproduced exactly) and the O(sqrt(eps_A))/O(eps_A)
scaling; cover necessity from `F <= 0` (balance + Cauchy-Schwarz only, no optimality
premise) with C1281 supplying sufficiency; the norm minorant lemma
(`|z0+w| <= n+a+b^2/(2l)`, `l > .00562379`) and the cap cancellation
(`q = .033749977`, `|delta|^2 <= 1.265464e-14`, `caploss = 0`).

**Inherited premises (retained explicitly; they carry the chain and I did not re-certify
them):** C1167 exact root existence and exact contact data; the exact stationarity/KKT
identities of `LOCAL-SOSC-PROOF.md`/C1182 and the exact KKT source under `lead/root-local/`;
the underlying **AD chain rules** of the interval kernel; the saved C1262 geometric
enclosures with the exact rational `W`, `v` and the bound `b` (I verified `b < 1` and the
derived constants, not the enclosure provenance); C1330/C1366 global reductions and the
`10/4[879]` catalogue correspondence; C1281 PL-degree sufficiency for cover.

## 5. Corrected points, gaps, and what must not be over-claimed

1. *(corrected)* The `(ENTRY)` ratio is **0.8458** from the stated formula; there is no
   second constant set. My earlier `0.199` is withdrawn as my own substitution error.
2. *(corrected)* The sup box is the **weaker** hypothesis (it contains the Euclidean ball);
   the previous "stronger than needed" phrasing is withdrawn.
3. *(corrected)* `K = 29/9` belongs to the joint-gauge inflation, not the anchor lens.
4. **Removed over-claim about witnesses.** A zero multiplier means the constraint is not
   active in the multiplier system, **not** that the variable is free. The correct and
   sufficient statement is: **C1355 asserts no witness uniqueness and none is required**
   by the chain (the penalty depends only on the 28 site coordinates and the 18 positive
   contacts).
5. **`4e-5` is not the localization precision.** The final Euclidean site box is `5.27e-8`
   in both routes (set by `sqrt((U^2-r*^2)/kappa)`, independent of cell size); the dual's
   `2.763e-5 < 4e-5` is a membership check for the 2e-6 cell.
6. **The load-bearing external interface** is the global necessity: if the C1330/C1366
   reduction plus the `10/4[879]` catalogue correspondence covers every remaining system,
   the 2e-6 cell is global over the necessary domain; the localization arithmetic does not
   supply that step.
7. **No exterior claim.** Nothing here excludes covers outside the cell; the unrestricted
   optimum remains open, as all source documents state.

## 6. Bottom line

The chain **2e-6 anchor cell -> gauged `5.27e-8` Euclidean site box -> no `r < r*`** is
arithmetically consistent: with the correct `beta` token the saved `(ENTRY)` ratio is
reproduced exactly (`0.84578364474801238 < 1`) and the final site error matches the saved
`5.265632842102119e-08`. The norm entry is `|.|_inf <= |.|_2` (sup box weaker), not the
C1352 growth ratio. Remaining risk sits entirely in the inherited premises listed in §4.
