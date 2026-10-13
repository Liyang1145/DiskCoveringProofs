# Audit: analytic interfaces of the adaptive-flow bridge (`q10_adaptive_flow_*`)

**PART A** = the 3e-5 interval-Hessian certificate (`q10-adaptive-flow-*`).
**PART B** (below, appended) = the large-box *quadratic minorant* extension
(`q10-quadratic-minorant-*`, `q10-current-angle-width`, `q10-quadratic-global-bridge`), audited on
the three named analytic lemmas: norm minorant, anchor remainder, cap-quadratic cancellation.

Read-only on `lead/`; no new scaling/proposal work; no new agents; no numeric rank/KKT claims.
Only the five requested interfaces are audited. Arithmetic is *not* replayed here (the lead reports
an independent replay); interval-arithmetic validity and the resulting numbers are therefore taken as
given, and are marked "inherited" below.

**Verdict: limited acceptance.** I found **no algebraic or identification error** in the five
interfaces; I supply the missing derivations for two of them (the `F<=0` orientation, the cap
arc-width lemma) and one exact-span fact that the Hessian test needs. One **scope requirement** stands
(§6.1: the bare 40-edge system needs the two cap conditions explicitly; the baseline JSON is being
narrowed accordingly), plus one quantified fragility (§6.2: the loss is a difference of two `~1e-17`
quantities whose cap term is a property of the saved reference).

*Corrections applied after review:* (i) §6.1's earlier claimed counterexample ("move anchors 4,5";
it would change only deleted edges) is **withdrawn as wrong** — each of those anchors keeps one
retained owner edge (`owners[4] = {8,1}`, `owners[5] = {0,8}`), so such a move does change retained
incidences; (ii) §6.3 (a growth-ratio "exclusion margin") is **deleted**: it inferred a lower bound
from an *upper* bound `rad2`, and no C1352 growth ratio is used anywhere in the bridge — the entry is a
*hypothesis check* on the anchors (§5, and PART B B.5); (iii) §8's corresponding obligation is replaced
by the norm-domination statement.

Files read: `lead/Q10-ADAPTIVE-FLOW-BRIDGE.md`, `lead/q10_adaptive_flow_interval.py`,
`lead/q10_adaptive_flow_fraction_audit.py`, `lead/q10_adaptive_local_bridge.py`, and
`q10-adaptive-flow-{interval,fraction-audit,local-bridge,jet}.json`,
`q10-relaxed-anchor-probe.json` (incidence source), `q11_chord_flow_fraction_replay` (`fr.pi`, `fr.L`).

## 1. `F <= 0` orientation — **accepted**

Object: retained rows `D` (40 edges x 20 retained free points: 14 sites minus the two X sites, plus the
8 retained faces' witnesses), offsets `b_e = -A_j(theta_j)` on anchor rows and `b_e = 0` on face rows,
flow `z(delta) = z0 + T delta` with `D^T z0 = 0`, `D^T T = 0` componentwise.

Derivation of the direction used (this is the step that must be right, and it is):
`sum_e z_e (D[e].x) = (D^T z).x = 0` for every free-point vector `x`, and the identity
`sum_e z_e b_e = sum_e z_e (D[e].x) - sum_e z_e (edge vector)` holds because the anchor row carries
`+1` on its site column and no entry for the anchor (`b_e = -A_j`). Hence
`|sum_e z_e b_e| <= sum_e |z_e| * ||edge vector|| <= r sum_e |z_e| <= U sum_e |z_e|`, i.e.
`F := sum_e b_e.z_e - U sum_e |z_e| <= 0` for **every** realization whose 40 retained edge norms are
`<= r <= U`. So `F <= 0` is the *necessary* direction, and the later use `0 >= F(theta(delta))` is the
correct side. No optimality, stationarity, KKT or differentiability of the optimum is used. The row
conventions I checked in the source matrix are exactly the ones the derivation needs: face rows are
`+1` at the site, `-1` at the witness column (`14+f`); anchor rows are a single `+1` at the site.

## 2. Full mixed Hessian / cross-product formula — **accepted**

Norm term: with `f = -U|z(delta)|`, `z` affine,
`d^2 f = -(U/|z|^3) (Jz.z_i)(Jz.z_j)`, using the 2D identity
`|z|^2 (z_i.z_j) - (z.z_i)(z.z_j) = (Jz.z_i)(Jz.z_j)`, i.e. `Hess_z |z| = (Jz)(Jz)^T/|z|^3`.
Both scripts implement `cross_i = z0*T_i^y - z1*T_i^x` (= `(Jz).z_i`) and subtract
`U cross_i cross_j / |z|^3`. Correct, including the sign of `-U sum |z|`.

Anchor term: for `T_e = -A_{a(e)}(theta_a).z_e` with `theta = theta0 + delta`, the *total* second
derivative in `delta` has three parts, and all three are present:
`h_a^2 (A_a.z) - 2 h_a A'_a.(z_theta h)`, i.e. code lines
`V[a][i]V[a][j]*d2 + V[a][i]*mix[j] + V[a][j]*mix[i]` with `d2 = A_a.z` (using `A'' = -A`) and
`mix[i] = (A_y,-A_x).z_i = (-A'_a).z_i`. I re-derived this from
`d^2 T_e = -A''_a z_e d_{ia}d_{ja} - A'_a T_{e,j} d_{ia} - A'_a T_{e,i} d_{ja}` and checked the
frequently-mis-set factor 2 (the cross term is doubled only after summing *ordered* pairs; the code's
form is the correct one). No cross term between the norm term and the angles exists (the norm term has
no explicit `theta` dependence), and `z` is affine so `z'' = 0`. The formula is complete.

Enclosure: `z` is enclosed componentwise by `z0 +- eps*sum|T|`, angles by `+-eps` (elementary
Lipschitz), `TT`/`TV` exact, `1/|z|^3` by interval division with a positive lower bound
(`min_norm_lower_display = 0.008013813`, so `F` is differentiable on the box). **Inherited**: the
directed-arithmetic validity of these enclosures (replayed independently by the lead).

## 3. Mean-zero basis / integral Taylor — **accepted**

`V` is 10x9 with `V[9] = -(V[0]+...+V[8])`, so every column sums to *exactly* zero (rational
arithmetic, checked: `all(...) == True`) and `span(V) ⊆ {sum h = 0}`. I re-ran an exact rational
elimination on the *saved* `V` and obtained rank 9, hence `span(V) = {sum h = 0}` exactly. That is the
fact the test needs: `V^T(Hess F - kappa I)V = I + E`, `||E||_inf < 0.878 < 1` with `E` symmetric gives,
for `h = Vw`, `h^T Hess F h >= kappa |h|^2` in the **original** coordinates (not up to a basis change),
for all mean-zero `h`. The Taylor integral along `0 -> delta` stays in the box (`{|delta|_inf <= eps,
sum delta = 0}` is convex) and the bound is applied *inside* the integral, which is what makes
`F(0) + gradF(0).delta + (kappa/2)|delta|^2 <= F(delta)` valid. The gradient-correction term
`- eps * |gradF(0) - gcap|_1` is the correct Hölder bound with `|delta|_inf <= eps`.

## 4. Cap gradient signs / principal lifts — **accepted**

Sign pattern: `gcap = q(-1,0,0,0,1,-1,0,0,0,1)` is reproduced by direct derivation. With
`delta_j = theta_j - theta0_j` and the cyclic gaps `gap4 = theta5 - theta4 + 2pi`,
`gap9 = theta0 - theta9` (the principal lifts used are the ones the data actually has: probe anchors
0..4 positive, 5..9 negative; the other gaps are plain differences),
```
capbase + 2pi = (theta0_5-theta0_4) + (theta0_0-theta0_9) + 2pi = gap0_4 + gap0_9,
gcap.delta   = q[(gap0_4 - gap4) + (gap0_9 - gap9)] = q[(gap0_4+gap0_9) - (gap4+gap9)].
```
so the used inequality `gcap.delta >= q[(gap0_4+gap0_9)-2L]` is exactly "replace `gap4+gap9` by `2L`",
i.e. it needs only `gap4 <= L` and `gap9 <= L`, one gap at a time.

Cap lemma (supplied; the document states it without proof): for a disk of radius `r` centred at
distance `rho` from the origin, the angular half-width of its trace on the unit circle is
`psi = acos((1+rho^2-r^2)/(2 rho))`, and `psi <= asin(r)` because
`(1+rho^2-r^2)/(2rho) >= sqrt(1-r^2)` is equivalent to `(rho - sqrt(1-r^2))^2 >= 0`. Hence each owned
arc has width `<= 2 asin(r) <= 2 asin(U) = L`. (Each gap's arc is a single-owner arc because the
anchors are the boundary switch points, so its points are all within `r` of that one owner.)

Identification checked against the data (`q10-relaxed-anchor-probe.json`, `owners`):
`owners[4] ∩ owners[5] = {8}` (gap 4 is site 8's arc) and `owners[9] ∩ owners[0] = {9}` (gap 9 is
site 9's arc): the two cap-active gaps are exactly the arcs of the two sites that the flow *deletes*.
Gap widths from the saved `theta0`: `0.6762779682872486769` (gap 4) and `0.67627796828724869398`
(gap 9) versus `L = 2 asin(U) = 0.6762779682872484`, i.e. the reference's cap gaps exceed `L` by
`+2.65e-16` and `+2.8e-16`.

Bound directions: with `fr.pi = 3.141592653589793238462643...` (`< pi` by `3.8e-46`) and
`fr.L = 0.676277968287248411741301...` (`> 2asin(U)` by `9.0e-46`), both entries of `caplower` are
conservative, and I reproduce exactly `caplower = 5.334426847218212e-16` and
`q*caplower = 1.8003559370293915e-17`, matching `capgradient_lower`. So the two "directed interval"
claims of the document are, in the saved data, genuinely directed (45-digit rationals), not
double-precision points.

## 5. True-candidate entry (C1355) and literal-graph incidence source — **accepted, with one scope requirement**

Incidence source: the 44x22 matrix is the *literal* graph's reduced system: 24 face rows
(`+1` site, `-1` witness column `14..21`) and 20 anchor rows (single `+1` on a site). The 22 columns
are 14 sites + 8 retained witnesses; the witness columns correspond to the 8 retained faces. The
selected 40 rows are the 44 minus rows `25, 32, 35, 42` = precisely the four incident edges of sites
8 and 9 (anchor 0's site-9 edge, anchor 4's site-8 edge, anchor 5's site-8 edge, anchor 9's site-9
edge) — matching "remove sites 8,9 and their 4 anchor edges", and no retained face row touches sites
8,9. The anchor offsets `b_e = -A_j` are consistent with the single-`+1` row convention used in §1.

Anchors/reference: `theta0` equals `atan2` of the probe's `anchors` (checked digitwise for the saved
rationals) and the probe's anchor order equals the bridge's `A` list order (both cyclic from `+s,+r`),
so the termwise comparison in the bridge is the right pairing. The bridge's
`reference_anchor_error_squared = 2.3542937e-31` gives chord `4.85e-16`, so the reference is within
`~1e-15` (angle) of the C1167 root-box candidate — better than the `1e-14`/`2e-14` asserted, and far
inside the `2e-6` cell.

## 6. Scope requirement and fragilities

### 6.1 Scope requirement: the bare 40-edge system needs the two cap conditions explicitly
The cap step (§4) is **not** a consequence of the flow hypothesis. The flow is built on the 40 retained
incidences, which contain *no* incidence of the two deleted X sites and therefore no inequality on the
two cap-active arcs `gap4 = theta5 - theta4 + 2pi`, `gap9 = theta0 - theta9`. Consequently the stored
conclusion

> `scope`: "Any r<=U witnessconfiguration with mean-gauged theta-th0 sumzero and supnorm<=eps has Euclidean angleerror<1e-6"

should be read as carrying the two cap conditions, i.e. for `r <= U` data **whose anchors are the
boundary switch points of a cover and whose gaps satisfy `gap4, gap9 <= L`** (equivalently, data
arising from a cover of the literal 879 type; the lead's note is that the unchanged full graph supplies
the caps even though the X sites are removed from the flow). The lead is narrowing the baseline JSON
accordingly; the markdown's §"Gradient + cap inequalities" already derives the caps for covers, so this
is a scope-string repair, not an added hypothesis on the mathematics.

*Withdrawn from the earlier revision:* the claim that one can exhibit violating configurations by
"moving the anchors 4,5 (resp. 9,0) apart, which changes only deleted edges". That is **wrong**: anchor
4 also owns site 1 and anchor 5 also owns site 0 (`owners[4] = {8,1}`, `owners[5] = {0,8}`), so those
moves do change retained incidences. No explicit counterexample of this kind is established here; what
stands is only the logical point that the cap conditions are not among the 40 incidences.

### 6.2 Fragility: the localization constant is a difference of two `~1e-17` quantities, and the cap term is reference-specific
`loss = -F(0) - q*caplower + eps*err = 3.7941762e-17 - 1.8003559e-17 + 2.3e-19 = 2.01699e-17`, hence
`rad2 = 2*loss/kappa = 4.03398e-14`, `|delta|_E <= 2.0085e-07`. The cap term is a property of the
*saved* reference point: its cap gaps exceed `L` only by `~2.7e-16` each, whereas the exact candidate's
cap gaps are `L* = 2asin(r*)`, i.e. `2L* - 2L = -7.4e-17 < 0`. What the artifacts actually prove about
the reference is only `|theta_cand - theta0| <= ~1e-15` per anchor, whence `caplower >= -4.1e-15` (the
saved value is `+5.334426847218212e-16`), and therefore `loss in [2.017e-17, 1.76e-16]`,
`rad2 in [4.034e-14, 3.5e-13]`, `|delta|_E in [2.008e-07, ~5.9e-07]`. So the document's
`0 < rad2 < 1e-12` is robust (it needs `caplower >= -1.5e-11`) and the *entry* into the 2e-6 cell is
robust (it needs `caplower >= -5.8e-14`, a factor ~14 margin), but the *reported* numbers
(`capgradient_lower = 1.80e-17`, `rad2 = 4.03e-14`, `|delta| = 2.009e-07`) are stable only for this
reference; a differently rounded (equally admissible) reference can weaken them by up to ~10x. Report
them as "for the saved rational reference" rather than as structural constants.

### 6.3 Note (not a defect)
The probe row that fixes the reference is a calibration point, not a cover:
`min_constraint = -1.6653345e-16 < 0` and `radius - U = +7.11e-17 > 0` (status
`numeric_only_fixedanchor_convex_calibration`). That is harmless — the reference only centers the
cell — and it is in fact why the cap term can be positive (the reference lies slightly *outside* the
cap-feasible region). It does mean the reference's cap data must not be read as "a feasible
configuration's gaps".

## 7. Accepted vs inherited (what this audit does and does not establish)

* Accepted on algebra/identification: `F <= 0` orientation; the full mixed Hessian (norm + anchor, all
  cross terms, correct doubling of the bilinear `mix` coefficient); the exact span of `V` and the
  Taylor chain; the cap gradient's sign pattern, the cyclic-gap identities and the cap arc-width lemma;
  the literal-graph incidence source, the 40-row selection, the anchor offsets, and the
  reference/candidate pairing.
* Inherited (not re-verified here): the directed-arithmetic validity of the interval enclosures and
  all arithmetic values (`row_bound = 0.8783346`, `min_norm = 0.0080138`, `f0`,
  `gradient_l1 = 7.7234e-15`, `caplower`); the C1167 root box; the 879 literal graph type and the
  cover -> witness-system passage; C1352/C1355 themselves.
* Not claimed: any KKT/rank statement, any optimality statement, or any statement about the remaining
  `879` complement (the document says so itself: `C1366` domain is still larger, goal not complete).

## 8. Next minimal obligations

1. Narrow the stored scope of `q10-adaptive-local-bridge.json` (and the "C1355 applies" sentence of
   `Q10-ADAPTIVE-FLOW-BRIDGE.md`) to include the two cap conditions — the only place where the
   argument consumes information not present in the flow's 40-edge hypothesis. (The lead is applying
   this narrowing to the baseline JSON.)
2. State the localization as "for the saved rational reference" and, if a structural constant is
   wanted, re-run the bridge with `caplower` replaced by its rigorous reference-independent lower
   bound (`2L* - 2L - 4*(the reference angle error)`), which yields `|delta| <= ~5.5e-07` and still
   enters the 2e-6 cell.
3. (Replaces the deleted growth-ratio item.) Record the *norm domination* that is actually used:
   `rad2 = 4.03398e-14` bounds from above, so `|delta|_inf <= |delta|_E <= 2.0085e-07 < 1e-6`, and with
   the reference error `< 2e-14` the anchors sit inside the C1355 `2e-6` entry cell. No lower bound on
   `|delta|`, no growth constant and no exclusion ratio enters anywhere.

## 9. Evidence (read-only checks run for this audit)

All checks were run inline (`py -3 -B -c ...`) against the saved artifacts; nothing under `lead/` was
written. Key printed values: `iota` row conventions of the 44x22 source matrix (24 face rows with
`(+1 site, -1 witness)`, 20 anchor rows with a single `+1`); `jet['edges']` = the 44 rows minus
`{25,32,35,42}`; `V` last row `= -(sum of first 9)` and exact rational rank 9; `theta0` = `atan2` of the
probe anchors digitwise; gap widths (rad) `0.6762779682872486769` and `0.67627796828724869398` for gaps
4 and 9 with shared owners `{8}` and `{9}`;
`caplower = 5.334426847218212e-16`, `q*caplower = 1.8003559370293915e-17`,
`f0 = -3.7941762e-17`, `loss = 2.0169905e-17`, `rad2 = 4.033981e-14`, `sqrt(rad2) = 2.008477e-7`;
probe row `min_constraint = -1.6653345e-16`, `radius - U = +7.11e-17`.

---

# PART B — audit of the large-box quadratic minorant extension

Objects: `lead/q10_quadratic_minorant_certificate.py/.json` (box `|delta|inf <= 1/200`, `sum delta = 0`,
damped flow `T = jet/4`), `lead/q10_quadratic_minorant_fraction_audit.py/.json` (replay),
`lead/q10_quadratic_global_bridge.py/.json` (cap penalties + C1366 bridge),
`lead/q10_current_angle_width.py/.json` (domain -> box). Focus as instructed: the **new norm minorant
lemma**, the **anchor remainder**, the **cap-quadratic cancellation**. The 3e-5 baseline is not
re-audited here.

## B.1 Norm minorant lemma — **valid** (proof supplied)

Statement as used: for each of the 40 retained edges, with `z(delta) = z0 + T delta`, `n = |z0|`,
`u = z0/n`, `a_i = u.T_i`, `b_i = (Ju).T_i` (`T_i` the i-th column of `T`), and
`l := n - eps * sum_i max|u.T_i|` (a bound on `min` over the box of `n + a.delta`),

    |z(delta)|  =  sqrt( (n + a.delta)^2 + b.delta^2 )  <=  n + a.delta + (b.delta)^2 / (2 l)
    provided l > 0.

Proof. (i) In 2D the orthogonal decomposition `T delta = (u.T delta) u + (Ju.T delta) Ju` is exact, so
`|z|^2 = (n + a.delta)^2 + (b.delta)^2` exactly. (ii) For `X > 0`, `sqrt(X^2 + c^2) <= X + c^2/(2X)`
(square both sides). (iii) `X = n + a.delta >= l > 0` and `c^2/(2X) <= c^2/(2l)`. QED.

Checks on the saved data: `min over the 40 edges of l = 0.005623790888 > 0`
(`radial_lowers`, min `5623790887631942171707185322579326140651213777689161959/1e54`); the code
`assert lower.lo > 0` is therefore justified. The bound is applied pointwise over the whole box
because `l` is a global lower bound over the box (the box is used only through `|delta|_inf <= eps`),
which is exactly what the minorant needs.

Implementation notes:
* the code subtracts `U * cross_i * cross_j / l` with `cross_i = -u1 T_0i + u0 T_1i = (Ju).T_i`. Under
  the report's matrix convention `(1/2) δ^T H δ` this is **exactly** the lemma's term: it contributes
  `(1/2) * (U/l) * (sum_i cross_i delta_i)^2 = U (b.delta)^2 / (2 l)`, i.e. the coefficient `U/(2l)`.
  **Correction to an earlier statement in this report: the coefficient is NOT doubled and there is no
  conservatism here.** (This is why `kappa` enters the scope as `0.005 = kappa/2`.)
* `u` is kept as an interval enclosure of the exact unit vector (`|z0|` enclosed by directed `sqrt`),
  so the `cross` products are enclosed too.
* `f0 -= U*n` and `g[i] -= U*along[i]` are the constant and linear parts of `-U(n + a.delta)`, i.e.
  the gradient of the *lemma's* linear term — consistent with the lemma, not with the un-damped flow.

## B.2 Anchor remainder — **valid** (proof supplied); two *separate* expansions

For an anchor row (`edges[e] >= 24`), the term is `-A_b(theta0_b + d) . (z0 + w)` with `d = delta_b` and
`w := T delta`. The two factors are expanded **separately**, exactly as in
`lead/Q10-QUADRATIC-GLOBAL-BRIDGE.md`:

* `z0` part, second order: `A(θ+d) = A + A'd + A''d²/2 + R`, `|R| <= |d|³/6`, `A'' = -A`, giving
  `-A(θ+d).z0 >= -A.z0 - (A'.z0) d + (A.z0) d²/2 - n |d|³/6`, with remainder `n |d|³/6`.
* `w` part, first order: `-A(θ+d).w >= -A.w - (A'.w) d - |w| d²/2`, with remainder `|w| d²/2`
  (from `|A'(ξ) - A'(θ)| <= |d|` and `|A''| <= 1`).

Under `(1/2)δ^T H δ` these give exactly the code's entries: `H_bb ⊇ A.z0 - n*eps/3 - wbound`
(second-order term `(A.z0)d²/2`, remainder `-n|d|³/6 >= -n*eps*d²/6`), `H_bk = H_kb ⊇ mix_k = (-A').T_k`
(first-order terms `-A.w` in the gradient and `-(A'.w)d` in the bilinear entry), and the `|w| d²/2`
remainder gives `-wbound` because `wbound := eps * sqrt(sum_k (sum_i |T_ki|)^2) >= max over the box |Tδ|`
(via `|sum_i delta_i T_i| <= eps * |sum_i |T_i||`).
The code assigns `mix[b]` twice (`H[b][i] += mix[i]; H[i][b] += mix[i]`), which is correct: the bilinear
term `-(A'.Tδ) d` has `d²` coefficient `-2(A'.T_b)` in this convention. `z` is affine (`z'' = 0`), each
anchor offset depends on its own angle only, so there are no anchor-anchor cross terms and the only
coupling is through `w = T delta`. *Correction:* an earlier revision merged the two remainders into one
bound `(d³/6)(|z0|+|Tδ|)` and then compared `-wbound` with `-eps*wbound/3`; that comparison is
irrelevant to the code, which uses the two separate remainders above. The saved gradient equals
`gcap = q(-1,0,0,0,1,-1,0,0,0,1)` only *within the residual* bounded by the bridge's
`gradient_l1_error = 5.0662858e-15` (it is not exactly `gcap`); that residual is what the `eps*ge` term
in the bridge charges.

## B.3 Cap-quadratic cancellation — **valid** (proof supplied); needs the cap conditions

The penalty `3 C^T C` (`C` = the two cap functionals `c1 = delta5 - delta4`, `c2 = delta0 - delta9`) is
a device: the certified matrix is `H_total = H_valid + 3 C^T C` and the minorant compensates exactly,
because `(1/2) δ^T (3 C^T C) δ = (3/2)(s1^2 + s2^2)` with `s_j := c_j.delta`. Writing
`g = -q (c1 + c2) + e_g` with `|e_g|_1 <= ge = 5.0662858e-15` (the bounded residual of B.2, charged as
`eps*ge` in the bridge), the two cap-sensitive parts of the minorant are bounded by

    g.delta - (pen/2)(s1^2 + s2^2) >= sum_j h(s_j) - eps*ge,   h(s) = -q s - 1.5 s^2.

`h` is concave, so its minimum on an interval is attained at an endpoint, and

    h(s) >= 0   <=>   -q/1.5 <= s <= 0     (i.e. -0.022499 <= s <= 0),

not merely `s >= -q/1.5`. The bridge supplies exactly the two needed bounds:
* `s_j >= -2 eps = -0.01` from `|delta|_inf <= eps = 1/200` (`|s_j| <= |delta5| + |delta4| <= 2eps`).
  The bridge's `assert q > pen*eps  <=> q/1.5 > 2eps` is precisely the condition `-2eps > -q/1.5`
  (margin: `0.022499` vs `0.01`, a factor 2.25).
* `s_j <= 0`: the bridge computes `b_j = L_hi - gap0_j` and uses `upper = max(0, b1, b2)`. With the saved
  reference `b1 = -2.6518398574419006711542881127e-16`, `b2 = -2.68258698977631053467034487292e-16`
  (both `< 0`), so `upper = 0` and `caploss = 2(q*upper + pen*upper^2/2) = 0`. The direction of each
  constant is conservative (`L` used as an upper bound via `L_hi`, and `gap0_4 = th5-th4+2*pi_lo` with
  `pi_lo <= pi`, which *shrinks* `gap0_4` and hence *enlarges* the bound `b1`).

Hence `sum_j h(s_j) >= 0` and the bridge's `caploss = 0` is **correct as a conservative lower bound**.
Wording correction (lead): `s_j = 0` is *not attained*, because the saved bounds `b_j` are strictly
negative; the true minimum of `h` over the admissible range `s_j in [-2eps, b_j]` is at an endpoint and is
*strictly positive* (`h(b_j) = q|b_j| - 1.5 b_j^2 > 0`, `h(-2eps) = 1.875e-4 > 0`). The bridge charges
nothing (`caploss = 0`) instead of that small positive gain — conservative, and not "tight" in the sense
of being attained. Dependency to state explicitly: `s_j <= 0` is *not* a consequence
of the flow hypothesis — it needs the two **cap conditions** `gap4 <= L, gap9 <= L`, i.e. the anchors
must be the boundary switch points of a cover. Without them `s_j` could reach `+2eps = +0.01` and
`caploss` would be `2(q*0.01 + 1.5*1e-4) = 9.75e-4`, which swamps the whole conclusion. (The lead's note
"full graph provides caps even for removed Xs" is the same statement; in the registered claim C1370 the
caps are part of the caliber, and the baseline/global JSON scopes have been updated and rerun.)

## B.4 The bridge's combination — **valid**

`loss = -f0.lo + eps*ge + caploss = 3.7941762e-17 + 0.005*5.0662858e-15 + 0 = 6.327e-17`, hence
`rad2 = 2*loss/kappa = 1.26546e-14 < 1e-12` and `|delta| <= 1.1253e-7`. Directions are all conservative
(`-f0.lo` for `-F(0)`, Holder `|delta|_inf <= eps` for the gradient error, `caploss >= 0`). The
reported `angle_error_squared = 126546381496284465742212436320896082079893/1e55` reproduces the numbers.

Containment of the domain in the box: `q10-current-angle-width.json` gives, per production anchor, the
interval range of the **mean-centred** displacement `(theta_j - mean theta) - (a_j - mean a)` over the
C1366 vertex set. I checked the structure and the numbers by hand:
* the displacement is linear in the deficits `x` (`base = (2j-9)/2 * L`, `coeff_i = (9-i)/10 - [i<j]`,
  `z = s*D` with `D = 10L - 2 pi`), the domain is a polytope in the simplex `sum x = 1`
  (`decode` asserts `equality = ([1]*10, 1)`), so its range over the polytope equals its range over the
  saved 896 vertices — exact, not sampling;
* the production -> literal map `j -> (j+2) mod 10` and the lift (`+2 pi` for `j >= 3`) match the lead's
  `anchor_map`, and both sides are mean-centred in the same lift;
* the extreme values are `+4.245e-3` (production anchors 1) and `-4.245e-3` (production anchors 4, 9),
  i.e. `max |delta|_inf = 4.245e-3 < 5e-3 = eps` with a 15% margin. The bridge's assertion
  `all(-eps < delta_lower <= delta_upper < eps)` is therefore sound.

## B.5 Verdict for PART B and the conditions it rests on

**The three named lemmas are valid** (B.1, B.2, B.3 — proofs supplied, with the conservative choices in
the code identified and shown to be safe), the arithmetic replay is now present
(`q10-quadratic-minorant-fraction-audit.json`, row bound 3.873523408986842e-14 — with the observation
that this replay shares the *formulas* and its scope string says so itself: "Explicit balanced
flow/rank/incidence checked; independently rounded quadratic matrix and trig. **Analytic minorant lemma
separate**" — that separate lemma is exactly B.1-B.3), the domain-to-box containment is exact and
holds with a 15% margin, and the bridge's combination is correct. I found **no algebraic or
identification error** in the extension.

So the extension is accepted as an analytic chain **conditional on**:
1. the **cap conditions** `gap4, gap9 <= L` (needed for `s_j <= 0` in B.3; essential: without them the
   cap loss is `9.75e-4`). For the global bridge these are *already part of the C1366 hypothesis*
   (its deficits satisfy `d_j >= 0`, i.e. `gap_j <= L`); what is needed is only that the *bare 40-edge*
   baseline statement carries them explicitly — the lead is narrowing the baseline JSON for that.
2. the **inherited global reductions**: that C1366 is the current necessary angle domain for the
   remaining 879 family, and the cover -> witness-system interface.
3. **the norm-domination entry (replaces the deleted growth-ratio item).** The certificate's `rad2` is an
   *upper* bound, so `|delta|_inf <= |delta|_E <= sqrt(1.26546e-14) = 1.1253e-7 < 1e-6`; with the
   reference error `< 2e-14` the anchors therefore lie inside the C1355 `2e-6` entry cell, so C1355
   applies (its statement is read as an entry/hypothesis statement). **No lower bound on `|delta|`, no
   C1352 growth constant and no exclusion ratio is used anywhere**; an earlier revision's ratio
   (3.03 vs 0.30) was an invalid inference from an upper bound and is deleted.
4. no new arithmetic error in the interval enclosures (independently replayed as above).

Minor observations, not errors: the two row bounds (producer `3.873523408986842e-14` and replay
`3.873523408986842e-14`) agree to all printed digits, which is expected only if the dominant enclosure
entries are point-like; and `q10-current-angle-width.json` calls `4.245e-3` a "width" although it is the
sup-norm *radius* about the mean-centred reference (the conservative direction anyway).

No global claim, and no claim about the covering optimum, follows from this file. The remaining
obligations are the conditions above, not new analytic lemmas.


