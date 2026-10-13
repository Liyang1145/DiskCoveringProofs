# Audit of `lead/FLAT-PATCH-ARC-CHART.md` (compact; rev 2 — three corrections applied)

Checks re-run independently (`r12_3_chart_check.py`, `r12_4_W_check.py`, `r12_5_W_why.py`);
no claims registered. **Three errors of my previous version are corrected below and marked
`[was wrong]`.**

## 1. Closed forms and the sign threshold

With `phi = asin r`, `s = sqrt(1-r^2)`, `c1 = (s - 2r sin b cos b, -2r sin^2 b)`, `P1 = (s,-r)`:

```
    cross(c1,P1) = -r cos(2b + phi)          [max |numeric - closed| = 2.8e-16]
    D = c1.P1    = s^2 - 2 s r sin b cos b + 2 r^2 sin^2 b   [2.2e-16]
```

`[was wrong]` **The implication runs the other way.** `cross > 0` holds iff
`cos(2b + phi) < 0` iff `2b + phi > pi/2` (equivalently `b > acos(r)/2`). My previous version
wrote `2b + phi < pi/2`; the correct chain is

```
    X = cross(c1,P1) > 0   <=>   2b + phi > pi/2   <=>   b > acos(r)/2 .
```

Verified with 0 mismatches over a full `(r,b)` scan. The lead's derivation and its conclusion
(`b > acos(r)/2`) are unaffected — only my transcription of the inequality was wrong.

## 2. `W = 2 atan2(X,D)` and the orientation (unchanged, correct)

With `delta = angle(c1,P1)`: `X = |c1| sin delta`, `D = |c1| cos delta`, and `|P1-c1| = r`
gives `D = (1+|c1|^2-r^2)/2 = |c1| cos delta`, hence `1 + |c1|^2 - 2|c1| cos delta = r^2` —
the arc half-width equation. So `Delta_max = delta` and `W = 2 delta = 2 atan2(X,D)`
(checked to `1.6e-14`), and `X > 0` means `P1` is the **counter-clockwise** end with the
neighbour clockwise from it. This part stands.

## 3. `W >= g` is NOT automatic — the lower end must be cut off explicitly

`[was wrong]` **My "`W >= g` holds for every admissible `b`" is false.** `W -> 0` as
`b -> acos(r)/2`, so near the lower end `W < g`. Numerically at `r = 0.38`
(`g = 2pi - 16 asin(0.38) = 2.661077 deg`):

```
    b = 34.000 deg :  X = +0.002213,  W = 0.40902 deg   < g   -> DISCARD
    b = 35.000 deg :  X = +0.015473,  W = 2.85781 deg   >= g
```

So the fibre must be intersected with the floor: the admissible fibre is
`{ w1 : g <= w1 <= W(r,b) }`, non-empty only for `b >= b_min(r)` with `W(r, b_min) = g`;
`b_min(r) < acos(r)` at the radii of interest (`r = 0.38`: `b_min ≈ 34.6 deg < 67.67 deg`).
The floor `g` is a genuine cut of the `b`-interval, not a consequence of the arc geometry.

## 4. `alpha1` can equal `pi` — the window end is not uniformly `< pi`

`[was wrong]` **I asserted `alpha1 in (0,pi)` with "always `< pi`".** At the inwardness end
`b = acos(r)` with `w1 = W` the adjacent sector is **flat**: `alpha1 = pi` exactly
(reproduced to `1e-9` at `r = 0.38`, `b = acos r = 67.666 deg`, `W = 44.6674 deg`, `u1 = 1`).
The correct statement is `alpha1 in (0, pi]` with `alpha1 = pi` attained at that corner — which
the lead's chart already permits. For `b < acos(r)` the value of `alpha1` at `w1 = W`
increases with `b` toward `pi`; it is not uniformly below.

## 5. Interface: the floor is not implied by width positivity alone

Correction of my previous interface answer. `b > acos(r)/2` is equivalent to `W > 0`, and
*that* part is implied by "positive neighbouring width". But the seven-factor domain carries
the stronger floor `w1 >= g > 0`, and a `b` with `0 < W < g` satisfies `W > 0` while producing
no admissible `w1`. So:

* `b > acos(r)/2` is implied by the chart's (and the seven-factor chart's) positivity
  requirement — no new condition there;
* the **strengthened** condition `b >= b_min(r)` (i.e. `W >= g`) is *not* implied by positivity
  alone; it is where the `(b1,w1)` chart and the seven-factor floor interact, and `w1 >= g`
  must be imposed explicitly;
* on that restricted `b`-range the fibre `{ w1 : g <= w1 <= W }` is the interval the chart
  states.

## 6. Verdict

Orientation, `W`, and the threshold `b > acos(r)/2` are correct as the lead derived. My three
extra claims — the `<` vs `>` direction, automatic `W >= g`, and uniform `alpha1 < pi` — were
wrong and are withdrawn; no unproved numerical generalization is retained. No correction is
requested in the lead's chart.
