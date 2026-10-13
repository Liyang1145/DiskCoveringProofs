# FAR-BRANCH-EXCLUSION -- **INVALID / DO NOT CITE** (see POLAR-PLUS-BRANCH-EXCLUSION.md)

> Errors: (1) it proves the CARTESIAN far half v>=s, not the polar H+ root (the polar + root is only characterised by v>=2r(1-r)/s); (2) the Taylor truncation S_5(2)=141782/155925=0.909296 is a LOWER bound for sin2, not an upper bound; (3) it conflates s=sqrt(1-r^2) with 1-r in the radical 2r(1-r)/s. Superseded.

# Far polar root of the hub-norm circle is infeasible in the high-bearing region

Ownscope report. Task: prove that the **far (+) branch** of the hub-norm circle
is never feasible for `r in [3/8, 19/50]`, `b1,b2 in [1, acos r]`, and supply an
exact/outward rational certificate. No sampling is used as evidence; the proof is
elementary and the numerics below only re-check the rational inequalities.

## 0. Result

```
   THEOREM. Let r in [3/8, 19/50], b1,b2 in [1, acos r].  The hub domain
   (Cartesian, per interval_hub_boundary.py)
        D1: (v - r sin2b1)^2 + (t + r cos2b1)^2 <= r^2
        D2: (v - r sin2b2)^2 + (t - r cos2b2)^2 <= r^2
        DN: (v - s)^2 + t^2 <= (1-r)^2 ,        s := sqrt(1-r^2)
        W : |t| <= v tan(min(b1,b2))   (wedge, any orientation)
   has NO point with v >= s.  Hence the far branch of DN (the "+" root
   v = s + sqrt((1-r)^2 - t^2)) is infeasible.
```

The wedge is not needed for the claim (it only shrinks the domain), so the
statement is indifferent to the wedge orientation.

## 1. Proof

**Step 1 (far branch means `v >= s`).** On `DN`, `(v-s)^2 = (1-r)^2 - t^2`, so
the two branches are `v = s ± sqrt((1-r)^2 - t^2)`. The far ("+") branch
therefore has `v >= s`, and on it `v <= s + (1-r)`; the near ("−") branch has
`v <= s` and `v >= s - (1-r) = 2r(1-r)/(1-r) > 0`. (The file's equivalent
characterization `v >= 2r(1-r)/s` is the *interior* first-coordinate bound of
DN; the far-branch inclusion `v >= s` is the strongest form and is what is used.)

**Step 2 (the face disks cap `v`).** For any point of `D_j`,
`(v - r sin 2b_j)^2 <= (v - r sin 2b_j)^2 + (t ∓ r cos 2b_j)^2 <= r^2`, hence

```
   v <= r (1 + sin 2b_j) ,    j = 1,2  =>  v <= r (1 + min(sin 2b1, sin 2b2)) .   (Cap)
```

**Step 3 (monotone majorant).** `b -> sin 2b` is decreasing on `[1, pi/2]`
(derivative `2 cos 2b <= 0` because `2b in [2, pi]`), so for every admissible
`b_j >= 1`,

```
   sin 2b_j <= sin 2 < 91/100 .
```

The last bound is exact: `2 in (0, pi)` and the alternating series for `sin`
gives `0 < sin 2 < S_5(2) = 141782/155925 = 0.9092961359... < 91/100`
(gap `7.039e-4`).

**Step 4 (assembly).** For `r <= 19/50` and every admissible `b`,

```
   r (1 + sin 2b) <= (19/50)(1 + 91/100) = 3629/5000 = 0.7258
                  < sqrt(2139)/50 = sqrt(1 - (19/50)^2) <= sqrt(1 - r^2) = s .
```

The middle comparison is exact: `3629/5000 < sqrt(2139)/50`
`<=> 36.29 < sqrt(2139) <=> 36.29^2 = 13169641/10000 < 2139` (gap `822.036`).
The last comparison uses `r <= 19/50`. So

```
   v <= r (1 + min(sin2b1, sin2b2)) <= 3629/5000 < s <= v    — contradiction.
```

**Conclusion.** No feasible hub point has `v >= s`; the far branch is excluded.
The strict gap is `s - 3629/5000 >= sqrt(2139)/50 - 3629/5000 > 0.1991`, so all
tangency cases (equalitites in the disk inequalities, `r = 19/50`, `b_j = 1`,
`v = r(1+sin2b_j)`) are covered with room to spare.

## 2. Exact rational certificate (all comparisons integer)

```
  (i)   sin 2 < 141782/155925 < 91/100            [alternating series remainder]
  (ii)  (924/1000)^2 * 50^2 = 53361/25 < 2139     => sqrt(2139)/50 > 924/1000
  (iii) 2139 < (925/1000)^2 * 50^2 = 34225/16     => sqrt(2139)/50 < 925/1000
  (iv)  (19/50)(191/100) = 3629/5000 < sqrt(2139)/50
        <=> 13169641/10000 = (3629/100)^2 < 2139
  (v)   sqrt(1-r^2) >= sqrt(2139)/50 for r <= 19/50
  (vi)  sin 2b <= sin 2 for b >= 1                 [monotonicity]
```

So the chain `v <= r(1+sin2b) <= 3629/5000 < sqrt(2139)/50 <= s` is entirely
rational after (i). Script `rational_certificate.py` re-checks (i)–(vi) with
`fractions.Fraction`.

## 3. Assumptions (carefully stated)

1. **Hub domain = the three-disk intersection read from the frozen kernel**
   (`interval_hub_boundary.py` line 11): the two face disks have centres
   `(r sin2b_j, ∓ r cos2b_j)` and radius `r`, and the norm disk is
   `(v-s)^2 + t^2 <= (1-r)^2` with `s = sqrt(1-r^2)`. If a different chart is
   used, only Steps 2 and 3 change; the argument needs (a) a disk constraint
   whose centre's first coordinate is `r sin 2b_j` and radius `r`, and (b) the
   norm disk as above.
2. **Bearing range `b_j in [1, acos r]`.** Step 3 uses only `b_j >= 1`; the
   upper end is not needed. (If the domain were `b_j >= b_min < 1`, the cap
   would become `r(1 + sin 2b_min)` and the conclusion would hold as long as
   `r(1 + sin 2b_min) < sqrt(1-r^2)`.)
3. **`r in [3/8, 19/50]`.** Only `r <= 19/50` is used (for `s`); the lower end
   `3/8` is irrelevant to this claim.
4. **Inward hub norm `|h| <= sqrt(1-r^2)`** — this is the DN above; it is the
   `s = sqrt(1-r^2)` convention of the frozen kernel (not `1-r`).
5. **No wedge needed.** The claim holds on the larger domain (DN ∩ D1 ∩ D2);
   the wedge constraints can only remove points.
6. **Tangency covered**: all inequalities in Step 4 are weak where the domain
   constraints are weak; the final gap `> 0.199` is strict, so equality
   configurations (`r = 19/50`, `b_j = 1`, point on `∂D_j`, point on `∂DN` with
   `v = s`) are all excluded.

## 4. What this does and does not remove

* **Removes 1 of the 4 polar boundary branches**: the "+"/far branch of the
  hub-norm circle. Remaining: 2 face-disk branches + the near ("−") branch.
* Does **not** remove the norm circle entirely, does **not** bound the near
  branch (it is genuinely present: e.g. `b1=b2=1`, the near arc reaches
  `v` up to `s - 0 = 0.925` in principle; the feasible part is limited by the
  disks, numerically `max v ~ 0.6916` at `t = 0` — not claimed here).
* Does **not** cover `min(b1,b2) < 1`, and gives no objective bound.

## 5. Independent numeric re-check (not evidence)

`far_branch_exclusion.py`: a 27-configuration scan (`r in {0.375, 0.376, 0.38}`,
`b_j in {1, mid, acos r}`) over the far half of DN with the wedge included found
**0** feasible points. `rational_certificate.py`: all rational comparisons pass;
numeric gap `s - r(1+sin2) = 0.19945...` at the worst corner `(r,b) = (19/50, 1)`.

## 6. Files

* `far_branch_exclusion.py` — domain scan (diagnostic).
* `rational_certificate.py` — the exact rational chain (i)–(vi).
* this report.
