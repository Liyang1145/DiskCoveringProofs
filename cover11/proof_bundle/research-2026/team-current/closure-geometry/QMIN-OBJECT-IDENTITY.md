# QMIN-OBJECT-IDENTITY — the `qmin` filter is the own-arc chord of the same switches

Assigned report. Question: in the closure kernels the filter reads
`q = (u−v)² + 4uv sin²(a/2)` and is compared against
`qmin = 4 sin²(π − 8 asin r)/r²`. Are the two sides statements about the **same
geometric objects**, or only about quantities of the same sign? Answer: **the same
object**, and the derivation is three lines of the law of cosines. Sources read:
`lead/VORONOI-BOUNDARY-REDUCTION.md`, `lead/INWARD-ARC-SWITCH-UNIQUENESS.md`,
`lead/ODD-BOUNDARY-SCALE-ELIMINATION.md`, `lead/BOUNDARY-CYCLE-COUPLING.md`,
`lead/RING-HOMOGENEOUS-REPRESENTATION.md`, `lead/ARC-WIDTH-EXACT-INVERSION.md`,
`lead/WIDTH-STATIONARY-POLYNOMIAL.md`, and the kernels
`lead/certify_q0_closure.py`, `lead/certify_q0_lower375.py`,
`lead/certify_q0_moments.py`, `lead/certify_shared_moments_dense.py`.
No numerical run is used as evidence (the one diagnostic is quarantined; see §6).

---

## 1. The geometric objects

Fix a genuine radius-`r` cover of the unit closed disk `D` in the canonical
9-ring + 2-hub reduced class, inward-root representative.

* `c_0, …, c_8` — the nine ring centers, `|c_i| ≤ sqrt(1−r²)`;
* `I_i` — the actual covered arc of disk `i` on `bd D` (one connected closed arc,
  positive length, by `VORONOI-BOUNDARY-REDUCTION.md` §1);
* `P_i` — the **unique** common nearest-center boundary switch of the pair
  `(I_i, I_{i+1})`. Uniqueness is `INWARD-ARC-SWITCH-UNIQUENESS.md`: the equality
  points of `c_i, c_{i+1}` on `bd D` lie on the radical line `m + t n`; if both were
  covered by both disks then `|m|² + k² ≥ 1` while
  `|m|² + k² = c_i·c_{i+1} + r² < 1`, a contradiction;
* **owned arc of ring `i`** — the closed arc from `P_{i−1}` to `P_i`, contained in
  `I_i`, of angular width `Δ_i > 0`. The nine owned arcs tile `bd D`, so

```
   Σ_i Δ_i = 2π .                                                            (T1)
```

(Also derived independently in `BOUNDARY-CYCLIC-CLOSURE.md` §1 for the closure
identity, and in `ODD-BOUNDARY-SCALE-ELIMINATION.md` as `Σw_i = 2π`.)

Per-arc width bound (`FIXED-SWITCH-SOC-REDUCTION.md` §4; the "short arc" lemma): a
radius-`r` disk with `r<1` meets `bd D` in at most one arc, and its angular width is
at most `2 asin r`. Applied to `I_i ⊇` the owned arc,

```
   0 < Δ_i ≤ 2 asin r          (r ≤ 19/50  ⇒  2 asin r < π/2).               (T2)
```

Combining `(T2)` for `j ≠ i` with `(T1)` gives the uniform lower bound

```
   Δ_i = 2π − Σ_{j≠i} Δ_j ≥ 2π − 8·(2 asin r) =: m ,     m > 0.              (T3)
```

So `m ≤ Δ_i ≤ 2 asin r` for every `i`, and `m > 0` because `r < sin(π/8)`.

---

## 2. The kernel's `q` is the chord of the owned arc — exactly

Let `P := P_{i−1}`, `Q := P_i` (the two switches bounding ring `i`'s owned arc),
`C := c_i`, and

```
   u := |P − C|/r  (= |P − c_{i−1}|/r by the switch tie),   v := |Q − C|/r ,  u, v ≤ 1 ,
   a := angle(P C Q)   (the interior angle of the triangle (P, C, Q) at C).
```

`u, v ≤ 1` is the switch tie plus covering (at a switch the common nearest-center
distance is `≤ r`). `u, v > 0` uses the **inward-root bound**, not the disk geometry:
the ring centers satisfy `|c_i| ≤ sqrt(1−r²) < 1` (`VORONOI-BOUNDARY-REDUCTION.md`
§3, inward-root replacement C464), so for `P ∈ bd D`

```
   u = |P − c_i|/r  >=  (1 − |c_i|)/r  >  0 .
```

(The naive reason — "a disk centred at a boundary point cannot cover its own arc" —
is **false** in general: a disk centred at a circumference point does cover
neighbouring arcs. The inward bound is what excludes `u = 0` here.)

**The kernel's form is the squared chord.** In the triangle `(P, C, Q)`, the law of
cosines gives `|PQ|² = |CP|² + |CQ|² − 2|CP||CQ| cos a`, i.e., after dividing by
`r²` and adding and subtracting `2uv`:

```
   Q_src := |PQ|²/r² = (u − v)² + 2uv(1 − cos a) = (u − v)² + 4uv sin²(a/2) .
                                                                    (Q-src)
```

This is literally the kernel's line
`q=(u-v)^2+4*u*v*iv.sin(a/2)^2` (`certify_q0_closure.py` line 82 and the same
expression in the other three kernels).

**The arc form is the same squared chord.** Let `Δ := Δ_i` be the angular width of
the owned arc. Because `P, Q ∈ bd D` and the *minor* arc between them is the owned
arc of angle `Δ ∈ (0, π)` (indeed `Δ ≤ 2 asin r < π/2` by `(T2)`), the chord
satisfies `|PQ| = 2 sin(Δ/2)`. Unwrapping the normalization (the chord is normalized
by the same `r` that appears in `u, v`):

```
   Q_arc := 4 sin²(Δ/2)/r² = |PQ|²/r² .
                                                                    (Q-arc)
```

Hence

```
   q in the kernels  =  Q_src  =  |PQ|²/r²  =  Q_arc  =  4 sin²(Δ_i/2)/r² ,   (IDENTITY)
```

as numbers, not merely same-signed. Equivalently, `Δ_i = 2 asin(r√q/2)`, which is
the kernel's own `w = 2*asin(R*iv.sqrt(q)/2)` and also the arc-width inversion of
`ARC-WIDTH-EXACT-INVERSION.md`. **The kernel's `w` is the owned arc width and its
`q` is that arc's chord (squared, normalized) — the same object as the boundary
decomposition's `Δ_i`.**

*Diagnostic* (not evidence, quarantined): a constructed `(C, P, Q)` with
`u = 0.95, v = 0.80, a = 0.91524204248` and `Δ = 0.29934007472` gives
`Q_src = Q_arc = 0.615909939884579316` (difference `−3.9e−26`).

Note the two occurrences of `Δ` in the literature coincide: the same width is (i)
the owned-arc angular width of the boundary decomposition and (ii) the `w` of the
ring sector that appears in the closure equation
`T_i + L_{i+1} + 2b_i + (w_i + w_{i+1})/2 = π` (`BOUNDARY-CYCLIC-CLOSURE.md`,
`BOUNDARY-CYCLE-COUPLING.md` §1 where `(u,v) = (y_{i−1}, y_i)` and
`y_i = |P_i − c_i|/r`).

---

## 3. The filter constant `qmin` is `4 sin²(Δ_min/2)/r²`

By `(T3)`, `Δ_i ≥ m = 2π − 16 asin r`; and by `(IDENTITY)`,

```
   q_i = 4 sin²(Δ_i/2)/r²  ≥  4 sin²(m/2)/r²  =  4 sin²(π − 8 asin r)/r² =: qmin .
```

The last step uses `m/2 = π − 8 asin r`, which is exactly the expression in the
kernels (`certify_q0_closure.py` line 82:
`qmin = 4*iv.sin(pi-8*asin(R))**2/R2`). Two sign checks make the identification
safe rather than formal:

* `m/2 = π − 8 asin r ∈ (0, π/9]` on the range `sin(π/9) ≤ r ≤ 0.38`: at the top
  end `r = 0.38` one has `asin(0.38) = 0.389796…`, so
  `π − 8·0.389796 = 0.0232… > 0`, while at the bottom end `r = sin(π/9)` gives
  `π − 8·(π/9) = π/9`; equivalently the range statement is
  **`0.38 < sin(π/8)`** and **`r ≥ sin(π/9)`**, i.e. `0 < m/2 ≤ π/9`. (My earlier
  figures `asin(0.38) = 0.3886`, `8 asin(0.38) = 3.109` were wrong; no decimals are
  needed beyond these two elementary facts.)
* `sin` is increasing on `[0, π/2]`, so `Δ_i ≥ m ⇔ Δ_i/2 ≥ m/2 ⇔ sin(Δ_i/2) ≥
  sin(m/2)`, i.e. the `Δ`-inequality and the `q`-inequality are equivalent — again
  the same object, no sign-only transfer.

**Exactness of the calibration** (diagnostic, quarantined): `4 sin²(m/2)/r²` and the
kernel's `4 sin²(π − 8 asin r)/r²` agree to `0.0e+00` at `r = 0.375, 0.378, 0.38`
(values `0.125295743346214294`, `0.045920836530145635`, `0.014935663152905879`).

---

## 4. Consequence used by the radius transfer (domain nesting)

Since `qmin` is a **necessary** lower bound for `q_i` on genuine configurations, the
`qmin` guard is a legal domain cut. Its `r`-dependence matters for the transfer in
`lead/RADIUS-TRANSFER-MOMENT-DUAL.md` because the cut moves. Put

```
   t := π − 8 asin r ,      qmin = 4 sin² t / r² .
```

Differentiating (chain rule; `dt/dr = −8/sqrt(1−r²)`,
`d(sin² t)/dr = 2 sin t cos t · dt/dr`):

```
   Λ'(r) = 4 [ 2 sin t cos t · (−8/sqrt(1−r²)) · r² − sin² t · 2r ] / r⁴
         = − 64 sin t cos t / ( r² sqrt(1−r²) )  −  8 sin² t / r³ .
```

**Both terms are `≤ 0`, and the first is `< 0` whenever `cos t > 0`**, i.e. for
`t < π/2`. On the stated range `sin(π/9) ≤ r ≤ 0.38` we have
`t ∈ (0, π/9] ⊂ (0, π/2)`, so `sin t > 0`, `cos t > 0` and

```
   Λ'(r) < 0      for   sin(π/9) ≤ r ≤ 0.38 .
```

Hence **`Λ` is strictly decreasing on that interval**, which is the monotonicity the
transfer note uses; equivalently, a smaller radius `r` imposes a **larger** `qmin`,
so the `r`-domains are nested in the direction the transfer requires, and the guard
applied at the largest radius is the weakest one. (My previous version of this
derivative was wrong twice over: it wrote `sinθ` where `cos t` belongs in the first
term and dropped the `−8 sin²t/r³` term entirely; the monotonicity conclusion is now
established by the two-term formula above, where both terms have the same sign.)

*Diagnostic* (quarantined; not evidence): `qmin` decreases in `r` for
`r = 0.3750 … 0.3825` and turns near `r ≈ 0.3827`; this is consistent with
`Λ'(r) < 0` on `[sin(π/9), 0.38]` and does not extend the interval.

---

## 5. What this note does and does not do

* **Does**: identify the two sides of the `qmin` filter as the *same* geometric
  object (the squared, normalized chord of the owned arc linking two consecutive
  switches), so that the width bound `Δ_i ≥ 2π − 16 asin r`, the constant `qmin`,
  and the kernel variable `q` are three descriptions of one quantity. This closes
  the "same object, not merely same sign" question.
* **Does not**: re-derive any part of `lead/RADIUS-TRANSFER-MOMENT-DUAL.md`, nor
  re-audit the analytic kernel of `CLOSURE-KERNEL-ANALYTIC-AUDIT.md`.
* **Assumes** (declared, not re-audited): the canonical 9-ring+2-hub inward-root
  class and the arc-ownership lemma (`VORONOI-BOUNDARY-REDUCTION.md` §1), switch
  uniqueness (`INWARD-ARC-SWITCH-UNIQUENESS.md`), and `(T2)`
  (`FIXED-SWITCH-SOC-REDUCTION.md` §4).

## 6. Files

Sources read: `lead/VORONOI-BOUNDARY-REDUCTION.md`,
`lead/INWARD-ARC-SWITCH-UNIQUENESS.md`, `lead/ODD-BOUNDARY-SCALE-ELIMINATION.md`,
`lead/BOUNDARY-CYCLE-COUPLING.md`, `lead/BOUNDARY-CYCLIC-CLOSURE.md`,
`lead/RING-HOMOGENEOUS-REPRESENTATION.md`, `lead/ARC-WIDTH-EXACT-INVERSION.md`,
`lead/WIDTH-STATIONARY-POLYNOMIAL.md`, `lead/certify_q0_closure.py` (lines 76–108),
`lead/certify_q0_lower375.py` (lines 76–98), `lead/certify_q0_moments.py` (lines
76–97), `lead/certify_shared_moments_dense.py` (lines 75–96).

Diagnostic (not evidence, quarantined): `closure-geometry/scratch-scaletest/
check_qmin_object.py`.

Written: this file only. No claim registered, no lead file modified, no subagent.
