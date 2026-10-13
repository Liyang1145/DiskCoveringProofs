# root-cc2 innernorm-envelope: audit of lead/INNERNORM-ENVELOPE.md (corrected)

Scope `members/root-cc2/innernorm-envelope/` (only). Lead artifacts read-only.
**No claim registered.** This file replaces my earlier draft entirely; every "correction"
I raised there was wrong, and it is withdrawn.

## Verdict on the points raised by the lead

The lead's corrections are all **verified correct**; my objections were arithmetic slips of
my own. Each is checked below with a direct computation.

1. **`r^2/d^2[1/w − 1/(2v)]` is identical to `r^2(2v/w − 1)/(2vd^2)`** (with
   `w = sqrt(r^2−d^2)`): multiply the first by `2v/(2v)`. Numerically, at
   `(r,v,d) = (0.33173203427623, 0.1, 0.2)`: both `−3.36081025736`; at
   `(0.3, 0.05, 0.15)`: both `−24.6039928216`. My "factor of 2" was a mis-multiplication.
2. **The norm branch increases in `d`.** `d/dd [H/v − r^2/(2vd)] = +r^2/(2v)·d^{−2} > 0`
   (I had the sign of `d(1/d)` backwards). Numeric at `(H,v,d) = (cos 0.2, 0.1, 0.3)`:
   `6.113674587`, matching `+r²/(2vd²)`.
3. **`B(d) = min(...)`** is what the note has; I wrote "max" by misreading.
4. **The left endpoint `d = H − s`, `b = 0` gives `alpha = 2 atan(v/(H−s))`, not `pi`.**
   Verified at `h = 0.1`: `alpha = 2.18701989573` and `2 atan(v/(H−s)) = 2.18701989573`.
   With `b = 0` the three points are isosceles about the horizontal axis, so
   `cot alpha = (d²−v²)/(2dv)` and `tan(alpha/2) = v/d` exactly. `pi` is the chord
   midpoint `d = H`, a different point — I conflated them.
5. **`tan(alpha_sym/2) = v/D`, not `v/r`.** With `d = D`, `b = 0`:
   `cot alpha = (D²−v²)/(2Dv)`, so `tan(alpha/2) = v/D`; and `r² = D²+v²` gives
   `alpha_sym = 2 asin(v/r)`. Verified: `v/D = 0.315575674856`,
   `tan(asin(v/r)) = 0.315575674856`, `D²+v² = 0.110046142565 = r²`.
6. **For small `alpha`, `a > b`** (not `a < b` as I claimed). Verified: `alpha = 0.05`
   gives `a = 0.04646 > b = 0.01659`; crossover at `alpha* = 0.920345827345`. My reversal
   followed from the same sign slips.
7. **Majorant logic on the convex half.** `a` is concave on `[0,pi/2]`, so its tangent `T`
   at `alpha_a` majorizes `a` there; on the convex half `[pi/2,pi]` the maximum of `a − T`
   is at an endpoint, so one needs `T(pi/2) >= a(pi/2)` *and* `T(pi) >= a(pi)`.
   Comparing `T(pi)` with `a(pi/2)` alone is insufficient — the endpoint `pi/2` is
   controlled by the concave tangent on the first half. Verified margins:
   `T(pi/2) − a(pi/2) = 0.137773340562`, `T(pi) − a(pi) = 0.141029103078`.

The positive content I checked earlier stands: both branch inversions, `a_r' > 0` (via
`sqrt(1−s²cos²α)^2 − (s sinα)^2 = r^2`), the concavity facts, and the exact line
certificate (`135/1000 + 218/1000 alpha` dominating `max(a_r,b_r)` with positive margins).

## Withdrawn

* All three "corrections" in my previous draft (the `d`-derivative factor, the norm-branch
  direction, the `a'` sign suspicion).
* My statements that the left endpoint gives `alpha = pi`, that `tan(alpha_sym/2) = v/r`,
  that `B = max`, and that `a < b` for small `alpha`.
* My claim that the certified line needed a different endpoint check than the note uses;
  the note's logic is the correct one (point 7).

## What I could not settle (recorded as a check target, not an objection)

I tried to locate the extremizer/envelope shape by brute-force scanning. That work is
**not reliable and I draw no conclusion from it**: my scans used an `alpha` expression I got
wrong twice (`atan2` argument order, then the cot/arccot branch), and after fixing it I
still obtained mutually inconsistent `theta_max(alpha)` values on different grids. I record
only this fully-verified datum, as a question for the analytic proof:

* At `h = 0.15` (`theta = 0.3`), the legal configuration `c = (H−D, 0)` with
  `D = sqrt(r²−v²)` (both endpoint distances equal `r`, `|c| = 0.6926 < s = 0.9434`) has
  `alpha = 0.93460234415`, `A(alpha) = 0.296927731316`, `B(alpha) = 0.300000000`.
  So `theta = 0.3 > A(alpha)` while `theta = B(alpha)` exactly. This is the `b = 0`
  symmetric point, which satisfies `|c−x_±| = r` but not `|c| = s`; whether the
  `A`-branch formula is meant to apply there is exactly the interface the lead's exact
  proof of the two candidates settles, and my arithmetic in this area has not been
  trustworthy. Offered as a check target only.

## Scope

Single-arc theorem only. I did not audit the combined probe, the catalogue counts, or the
`q10`/`q11` bookkeeping.
