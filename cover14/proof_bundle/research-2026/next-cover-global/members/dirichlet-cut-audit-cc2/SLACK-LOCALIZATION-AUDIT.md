# SLACK-LOCALIZATION-AUDIT — audit of `lead/DUAL-SLACK-LOCALIZATION.md`
+ `dual_slack_localization_certificate.py/json` (member `dirichlet-cut-audit-cc2`; no claims)

Object audited: the inequality chain that carries an anchor angle cell (±1e−6 around the literal
anchors) to a site bound < 4e−5 for C1262, at fixed incidence graph of the C1281 witness SOCP, for
every feasible system with r ≤ U = 0.33173203427623414.  Verdict: **the analytic chain is correct as
stated; the certified endpoint reproduces independently (1.3817344e−5 vs 1.3817346e−5); no
load-bearing flaw found.**  Three interface/scope notes and one pipeline recommendation below.
Repro: `members/dirichlet-cut-audit-cc2/slack_audit_checks.py`, `slack_recompute.py` (own code, no
lead imports; exact Fractions + 60-digit mpmath — a different representation from the directed
interval kernel).

## 1. Analytic chain, step by step (each step's exact requirement)

**(1) `Σ λ_e‖p_e − r u_e‖² ≤ 2r (rN − L_z(A))`, λ_e = ‖z_e‖.** Expansion is exact:
`‖p_e − r u_e‖² = ‖p_e‖² − 2r p_e·u_e + r²`, and `λ_e u_e = z_e` gives
`LHS = Σλ_e‖p_e‖² − 2r L_z(A) + r²N`. Required premises, all satisfied:
* `‖p_e‖ ≤ r` **for every edge with λ_e > 0**. In this graph this holds because *every* incidence
  edge is a constrained pair: the data census gives 68 = 48 site–witness + 20 anchor edges, with
  **zero** site–site or witness–witness edges (checked in `slack_audit_checks.py`). This is the single
  most load-bearing implicit premise: an unconstrained pair in the support would break (1).  Keep the
  census check in the pipeline.
* `z` exactly balanced, so `L_z(A) = Σ z_e·p_e` depends only on the anchors. Independently verified
  in exact arithmetic: `Σ_e D[e][j] z_e = 0` at **all 30 nodes and both coordinates** (0 nonzero).
* `rN − L_z(A) ≥ 0`: immediate from `Σ z_e·p_e ≤ Σλ_e‖p_e‖ ≤ rN`.
Zero-weight edges contribute nothing (λ_e = 0), as stated.

**(2) Reference/alignment version.** With `ρ = r/r*`, `y = x − ρx*`, `b = A − ρA*`, one has
`p_e = x_tail − x_head = (y_tail − y_head) + ρ p*_e` for free *and* anchor heads (the anchor case uses
`A = b + ρA*`), so exact alignment `p*_e = r* u_e` turns (1) into `E(y,b) = Σλ_e‖y_tail − y_head‖² ≤
2r(rN − L_z(A))`.  Correct as written.

**(3) Path bound.** Telescoping `y_v − b_a = Σ_{e∈P_v} ±(y_tail − y_head)` plus weighted
Cauchy–Schwarz `(Σ‖Δ_e‖)² ≤ (Σλ_e‖Δ_e‖²)(Σ 1/λ_e)` gives `‖y_v − b_a‖ ≤ sqrt(R_v E)`,
`R_v = Σ_{e∈P_v} 1/λ_e` — the *unsquared* weights, as the doc defines them (I checked this
convention explicitly: using squared weights inflates R by ‖z‖, a real trap).  Then
`‖x_v − x*_v‖ ≤ ‖A_a − A*_a‖ + |ρ−1|‖x*_v − A*_a‖ + sqrt(2rR_v(rN − L_z(A)))` follows from
`x_v − x*_v = (y_v − b_a) − (ρ−1)(x*_v − A*_a) + (A_a − A*_a)`.  Correct.

**Approximate alignment.** `p_e − r u_e = (p_e − ρp*_e) + ρ(p*_e − r*u_e)`, Minkowski on the
λ-weighted L², and (1) give `sqrt(E) ≤ sqrt(2r(rN − L_z(A))) + (r/r*) sqrt(Σλ_e‖p*_e − r*u_e‖²)`.
Correct, and the doc's insistence that approximate alignment is not silently exact is the right call
(here the residual is ≈ 4.4e−28, so it is moot, but the term is what makes the certificate robust).

**Slack monotonicity.** `r ≤ U` and `L_z(A) ≥ Lmin` give `rN − L_z(A) ≤ UN − Lmin`; a positive lower
radius bound `r ≥ Lmin/N` is what makes `|ρ−1|` controllable. Both are exactly what the script does
(`slack = U*N − Lmin`, `rlo = lower(Lmin/N)`, `assert rlo > 0`).

**Anchor-cell lower bound `Lmin = F0 − Tε − Gε²/2`.** With `L_z(A) = Σ g_j·A_j` and unit-circle
anchors, first order `|g_j·A_j'(θ)| = |g_j × A_j|` (T) and second order `|g_j·A_j''| = |g_j·A_j| ≤
‖g_j‖` (G), so the bound is valid for the *directed* angular cell `|δ_j| ≤ ε`.  Verified: all 10
anchor radii are exactly 1 in my reconstruction, as the angle-cell conversion requires.
Structural fact worth recording: at the reference the anchor forces are **exactly radial**
(`T = 3.7e−14 ≈ 0` because `g_j ∥ A_j`), so `Lmin` is *second-order only*: `slack ≈ 1.9e−13`.  The
whole bridge therefore rides on a genuinely tiny slack and a large resistance (R ≈ 103.3).

**Rotation gauge.** `siteerror < s/4` puts us in the small-angle regime where
`rotation = 2·siteerror/s` is a valid bound, and `gaugederror = siteerror + rotation·maxsite`.
The divisor must be the *distance from the rotation centre to the pinned site*: the pin is X+ = site 9
(`LOCAL-SOSC-PROOF.md:13`), i.e. the site `(s,0)`, whose distance from the origin is
`s = sqrt(1−r²) = 0.943373657378` — I verified `|site 9| = 0.943373657378` and `y(site 9) = 0` exactly
in the reference.  So `lower(s)` is the right divisor, and the extra factor 2 is conservative.  This is
a cross-file interface: it is correct *only* under the label map "X+ = site 9".

## 2. Interface conditions verified in the data

* `nv = 30 = 14 sites + 16 witnesses`; the first 14 nodes are the sites (so `pts = C + W`, `dist[:14]`
  and `R = max(dist[:14])` mean what the doc says).
* Anchor rows: indices 48..67 (after `3·16`), two rows per anchor, anchor `j` owning `48+2j, 48+2j+1`.
  The pairing is not merely assumed: a wrong pairing would make the alignment residual of order r²,
  so the certified residual ≈ 4.4e−28 *validates* it.  I reproduced the same value independently
  (4.4446e−28, inside the certified interval 4.4444e−28 … 4.4448e−28).
* Positive support: 44 of 68 edges, and sites 4, 5, 8, 9 are now touched (3, 3, 2, 2 edges) and the
  Dijkstra distance to the anchor sink exists for all 14 sites.  The doc's "First support diagnostic"
  paragraph describes the *superseded* 32-edge proposal; as of the symmetric flow the localization
  premise holds.  **Doc note:** that paragraph should be marked historical, otherwise a reader takes a
  stale premise as current.
* Anchors: all 10 contact points have radius exactly 1 in my reconstruction.

## 3. Independent recomputation of the endpoint (different representation)

Exact Fractions for the flow combinations, mpmath for geometry and square roots (see the precision
caveat below), own Dijkstra, own circumcentre reconstruction of the witness points; root box taken at
its midpoints.

| quantity | independent value | certificate |
|---|---|---|
| N = Σ‖z_e‖ | 1.143102380327200462417… (rigorous `isqrt` enclosure; inside the certified interval to 24 digits) | 1.1431023803272004624 (two-sided, width 6.4e−70) |
| F0 = L_z(A_ref) | 0.3792036780119476535… | 0.37920367801194765356 (two-sided, width 1.26e−19) |
| T (tangential L1) | 3.732e−14 | 3.73e−14 |
| G | 0.37920367801 | — |
| Lmin | 0.379203678012 > 0 | — |
| slack = UN − Lmin | 1.89622e−13 | 1.89622e−13 |
| alignment | 4.4446e−28 | 4.4444e−28 … 4.4448e−28 |
| √R (max over 14 sites) | 10.1659128191, R = 103.345783446 | R = 103.34578344644869, matches the flow file's own `site_path_resistances` max |
| site_error | 4.605781241e−6 | 4.605781842e−6 |
| **gauged error** | **1.381734372e−5** | **1.381734553e−5** |

**Correction (lead-raised, accepted).** The certificate's `N` and `F0` are **two-sided interval
enclosures**, not directed upper point values: measured widths 6.40689e−70 (N) and 1.26359e−19 (F0),
and no collapse happens in the code before `slack_upper`.  My earlier note said otherwise because my
20-digit display print could not resolve the width — the widths were visible in my own output and I
misread them.  Consequence: every interval field of the JSON is usable as a two-sided enclosure, and
no re-emission is needed.  Related disclosure: my mpmath value for N (1.1431023803272004094) was in
turn an artifact of converting the huge rational λ_e into 60-digit mpf (≈1e−16 relative error);
replacing it with a rigorous scaled-integer square-root enclosure (`isqrt` at 80 digits) reproduces
the certified interval to 24 digits.  The same ~1e−16 caveat applies to the other mpmath entries in
this table, so their agreement with the certificate should be read as agreement to the 7–8 digits
shown plus the rigorous N check.

The final constant is essentially `3 × site_error` because `maxsite/s = 1` — the rotation gauge
contributes two thirds of the budget, leaving only a factor ≈2.9 margin under 4e−5.

False alarms I checked and cleared (recorded so nobody re-opens them): the `path_resistance_upper`
field *does* equal 103.34578344644869 (an earlier digit-count misread on my side), and the anchor-edge
pairing is validated by the alignment residual.  My two intermediate discrepancies were bugs in my
own recomputation (witness circumcentre sign; squared instead of unsquared λ in the resistance),
fixed before drawing conclusions.

## 4. Scope and what this does not establish

* Everything is conditional on the anchor angle cell ±1e−6 and on r ≤ U; **no conclusion outside the
  cell**, no exclusion of other anchor cells for q10/879, no treatment of the 200 q11 systems.  The
  lemma alone removes no catalogue family, as the doc says.
* The conclusion is stated "after X+ rotation".  In the derivation (3) the frame is actually fixed by
  the anchors being data, so no rotation price is needed if C1262's box is read in that fixed frame;
  the rotation price is *necessary* under the reading that the box lives in the X+ gauge.  The script
  covers the stronger (gauged) requirement, so its conclusion is valid under either reading — but the
  scope line and the box definition must be kept consistent.  One caveat in the gauged reading: the
  rotation moves the candidate's anchors too, so the cell premise must be understood as a premise on
  the site configuration *before* gauging (the anchors are contact points of the site disks, hence
  functions of the sites), which is exactly what the doc's phrase "every feasible r ≤ U site
  configuration" says.
* The positive weighted paths must be verified explicitly (unweighted connectedness is not enough) —
  correct in the doc and enforced in the script by the hard assertion that all 14 distances exist.

## 5. Answers to the four requested audit questions

* **Analytic**: (1)→(2)→(3), the approximate-alignment variant, slack monotonicity and the
  path/Cauchy–Schwarz step are all correct, with the requirements listed in §1.
* **Gauge**: the rotation gauge is `y(X+)=0` with X+ = site 9 = `(s,0)`, and the divisor `s` is the
  right one; the extra factor 2 and the `maxsite` price are conservative; the label-map dependency is a
  cross-file interface, correctly flagged in the doc.
* **Radius scaling**: `ρ = r/r*` with `r ∈ [rlo, U]`; `rhoerr` bounds `|ρ−1|` in both directions
  (`rlo/upper(r*) − 1` and `U/lower(r*) − 1`) and `rlo = lower(Lmin/N) > 0` is certified.
* **Norm bounds / coordinate incidence**: every quantity entering the final constant is used in the
  conservative direction (upper bounds for slack, alignment, √R, √E, ε, diam; lower bound for the
  gauge divisor); the incidence conventions (sites 0..13, witnesses 14..29, anchor head = missing −1)
  and the two anchor rows per anchor were verified in the data.
