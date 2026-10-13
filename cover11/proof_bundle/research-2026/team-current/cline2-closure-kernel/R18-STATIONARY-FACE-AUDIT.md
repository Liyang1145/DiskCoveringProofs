# R18 analytic audit — stationary face bound + endpoint closure (conditional certificate)

Read-only, source-analytic. No grids, no random loops. Sources:
`probe_stationary_face_bound.py` (05:16, count 3480, live 0, terminal 28.10694882274086),
`face_second_jet.py` (05:04), `face_derivative_outer_jet.py`, `check_face_derivative_outer.py`,
`face_derivative_outer_control.json`, `stationary_face_bound_probe.json`.

## Verdict

**(1) WITHDRAWN — the Taylor block is algebraically CORRECT; my objection was an arithmetic
error of mine** (I used `|f''|` with a sign flip and got 9.999375 instead of 10). **(4) WITHDRAWN
and corrected** — the `A=0` point is `Q1 = (r sin2b1, 2r sin²b1)`, not the face centre `Di`, and
the outer `(r,b1,b2)` box edge `b = acos r` is not an endpoint of the δ-arc; C861 already excludes
the wedge boundary. **(2) and (3) stand.**

The prior version of §1 (a "sign error" with a "witness rule" salvage) and of §4 (the
`b_j = acos r` endpoint class) were wrong. Both are replaced below. No source patch was made or
requested.

---

## (1) Stationary Taylor block, lines 25-31 — CORRECT (objection withdrawn)

Write `d*` for the stationary point in coordinate 3 (δ) and `m` for the box midpoint with
coordinate 3 centred. About the **stationary** point the expansion has no first-order term:

```
f(m) = f(d*) + ½ f''(ξ)(m − d*)² ,      ξ between m and d*
```

hence, solving for the quantity of interest,

```
f(d*) = f(m) − ½ f''(ξ)(m − d*)² .        (*)
```

Line 29 computes exactly `centered = am.v − a.h·(x₃−mid₃)²/2` with `am.v ≅ f(m)` and
`a.h` the interval enclosure of `f''` on the box, then replaces `a.v` by the intersection with
`centered`. Direction check with the lead's parabola `f(T) = −½(T−2.175)² + 10`, `m = 2.20`,
`d* = 2.175`, `(m−d*)² = 0.000625`, `f'' ≡ −1`:

```
f(m)              =  9.9996875
(*)  f(d*)        =  9.9996875 − ½(−1)(0.000625) = 10.0000000
code centered     =  9.9996875 − (−1)(0.000625)/2 = 10.0000000        MATCHES f(d*)
```

My earlier `9.9993750` came from evaluating `−½·|f''|·(m−d*)²`, i.e. from flipping the sign of
`f''` before substituting — arithmetically wrong. **Withdrawn.**

Correct facts about the block, for the record:

* `f''(ξ) ∈ a.h` (interval enclosure), so using `a.h` in `(*)` is a valid enclosure; the code
  additionally intersects with `a.v` (the direct saturation enclosure), and an intersection of two
  enclosures is still a valid enclosure.
* The `a.h.a > 0` gate rejects boxes where `f''` is provably positive on the whole box. Those are
  local-minimum candidates for the δ-slice and cannot carry a strict maximum, so nothing is lost.
  **Correction to my earlier phrasing:** `closed['positivecurvature'] == 0` does *not* imply
  "all remaining boxes have `f'' ≤ 0`". It only records that the `a.h.a > 0` branch never fired;
  other reasons (non-stationarity `a.d`, illegality, or the value rule) can carry a box out first.
  I withdraw that inference.
* Nothing here needs changing in the kernel.

---

## (2) `face_derivative_outer_jet.derivative` — formulas verified term by term

* `v, t` (line 10) and `vd, td` (line 11): with `c = A = b1−δ` (j=0),
  `dv/dδ = r cos2A·(−2)`, `dt/dδ = −r sin2A·(−2) = +2r sin2A` — matches. With j=1 the `t`
  definition already carries the `−` so `td = +2r sin2B` is correct as coded. ✔
* active face (line 15): `e = r sin(ang)/R`, `ed = ∓r cos(ang)/R`, `pd = ∓1`. `d(φ)/dδ = ±1`
  matches the brief's "active φ′ = ±1". ✔ (φ is the active face's own bearing angle, so its
  derivative is exactly ±1 — not zero.)
* passive face (line 16-18): `Q = X²+Y²`, `root = 2Re`, so
  `ed = (X vd + Y·sg·td)/(2R·root)` is exactly `d(√Q/(2R))/dδ`; and
  `pd = (X·sg·td − Y·vd)/Q` is exactly the generic `d atan2(Y,X)/dδ = (X Y′ − Y X′)/Q`.
  The brief's "off e′ denom 2R√Q" is the same factor since `√Q = 2Re`. ✔
* `enclosure` (line 22-24) = min(raw interval value, MVT linearisation about the midpoint),
  both upper bounds, no clipping in the derivative path. ✔ Calibration
  (`check_face_derivative_outer.py`) asserts `a.d−b.v ∋ 0` and `a.h−b.d[3] ∋ 0`, i.e. it checks
  the **first- and second-order** consistency of the hand/AD derivatives against each other, plus
  30 finite-difference gradient checks. That is the right control.

---

## (3) `face_second_jet.saturated` — equals the Cartesian objective on the legal wedge

* `coords` (j=0) gives `v = r(sin2b1 + sin2A)`, `t = r(cos2A − cos2b1)`; the point lies on the
  face circle identically, and `H = 2r sin(2b1 − δ) = 2r sin(b1 + A)` reproduces the face cap
  2r sin(b1+A) used in `interval_hub_saturated` line 14. Same for j=1 with `B = b2+δ`. ✔
* the linear coupling `(z3−z1)·δ` (line 66) matches the Cartesian objective's `J(a)·φ` for the
  active face, whose `dφ/dδ = −1` (j=0). ✔
* single formula on the box, with the active/passive selection by `i==j` being a branch of the
  objective, not of the interval: no branch switching inside a box. ✔
* `angle` (line 32) raises unless `y` is strictly one-signed or `x>0`; in `saturated` the passive
  call has `Y = 2r sin b sin(ang) > 0` strictly (`b ≥ 1`, `ang ∈ (0,π)`), so the atan2 branch is
  always the safe one. `sqrt` raises on radicands touching 0. ✔

---

## (4) Endpoint closure — corrected statement

**Geometry correction (lead).** On the δ-arc with `A = b1−δ`, the point `A = 0` is

```
Q1 = (r sin 2b1, 2r sin²b1)      (verified numerically, r ∈ {0.379, 0.3795, 0.37999})
```

with `|Q1| ≈ 0.638-0.703`, **not** the face centre `Di = (r sin2b1, −r cos2b1)` with `|Di| = r`.
My §4 scan plotted `t = −r cos 2b1`, i.e. the centre — the wrong point. **Withdrawn.**

**Also withdrawn:** the claim that `b_j = acos r` is an endpoint class of the δ-arc. The hub is
optimised with `(r,b1,b2)` **fixed**; `b = acos r` is an edge of the *outer* box, not an endpoint
of the δ-arc within a fixed-outer fibre. My §4 scan varied `A` over `[0,π]` at fixed `b1`, which
is not what "endpoint of the δ-arc" means.

**Correct closure argument.** Within a fixed outer triple, `δ` ranges over a closed interval and
the legal fibre is cut out by the closed constraints

```
g_wedge  : A = b1−δ >= 0 and B = b2+δ >= 0
g_faceop : |c − c_opp|² <= r²
g_norm   : |c|² <= (1−r)²
```

An endpoint of the legal δ-interval is therefore a δ where at least one of these is active
(equality). C861 settles the wedge case: its compactness argument shows the closed wedge boundary
is **infeasible** for the hub fibre (at `A = 0` the hub site equals `Q1` and
`|Q1|² − (1−r)² = 2r[1 − cos(2b1 − acos r)] > 0`, contradicting the hub-norm constraint), which is
precisely why the maximum of the hub objective can only lie on the union of the three disk-boundary
arcs. So the wedge endpoints contribute **no candidate maximum**, and the surviving endpoint class
for the δ-arc is `g_norm` active, i.e. `|c| = 1−r` — handled by C863; `g_faceop` active is C861.
That is the correct closure, and it matches the lead's "fixed r,b1,b2 before hub optimization".

**Net:** the endpoint enumeration in the brief is right; my §4 additions were based on a
mis-plotted point and a mis-scoped box edge. Both struck.

---

## (5) Language

`live=0` with `budgetdiagnostic` scope means the search terminated with every remaining box below
the probe target; the stored `terminal` 28.10694882274086 is a valid **upper bound** on the
stationary-candidate values over the covered boxes, not an attained maximum. Consistent with the
C863/C867 convention.

## (6) Repro

```
cd research-2026/team-current/cline2-closure-kernel
py -3 r18_correction.py      # exact code expression vs f(d*) for the lead's parabola;
                             # and A=0 -> Q1 = (r sin2b1, 2r sin^2 b1) geometry
```

Superseded / do not cite: `r18_taylor_sign_demo.py` and `r18_endpoints.py` were built on my two
errors (the `|f''|` sign flip and the mis-plotted `A=0` point); they are kept only as a trace of
the withdrawal.
