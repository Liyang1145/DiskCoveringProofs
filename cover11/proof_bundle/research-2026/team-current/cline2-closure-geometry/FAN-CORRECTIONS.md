# Fan-deficit coordinates — corrected note (two explicit algebra errors fixed)

Caliber: hub `H`, consecutive neighbours `U,V`, `|HU| = 2r cos s`,
`|HV| = 2r cos t`, `s,t in [0,pi/2]`, `theta in (0,pi)` = angle at `H`,
`a = |UV|`, `K = area(HUV)`, `R_circ` = circumradius of `HUV`. Diagnostics only;
no audit-completeness claim. Lead uses its own sine-law derivation.

## Error 1 (mine): circumradius closed form

`R_circ = |HU||HV|a/(4K)` with `K = (1/2)|HU||HV| sin theta` gives

```
   R_circ = a / (2 sin theta)                                                        (1)
          = r sqrt( cos^2 s + cos^2 t - 2 cos s cos t cos theta ) / sin theta       (2)
          (2) valid as written only when a = 2 r sin theta, which holds on the
          saturated family; in general use (1) with a from the cosine law.)
```

The expression `R_circ = 2 r cos s cos t / sin theta` that I used earlier is
**wrong**: it is (1) only in the isosceles case `s = t`. Numerically
`(s,t,theta) = (0.5, 0.7, 1.0)`: (1) = `0.943124434`, the wrong form
`1.595330506`. Equilateral check `s = t = pi/6`, `theta = pi/3`:
`|HU| = |HV| = |UV| = sqrt(3) r` (equilateral), so by `R = side/sqrt(3)` the
circumradius is `r`; (1) and (2) give `r`, the retracted form gives `sqrt(3) r`.
**Retracted.**

Consequences (from (1)):
* `R_circ <= r`  <=>  `cos^2 s + cos^2 t - 2 cos s cos t cos theta <= sin^2 theta`
  <=>  `(cos theta - cos s cos t)^2 <= sin^2 s sin^2 t`
  <=>  `|s - t| <= theta <= s + t`  (monotone `cos` on `[0,pi]`).
* The side bound `a <= 2r` alone gives only `R_circ = a/(2 sin theta) <= r/sin theta`.

## Error 2 (mine): the saturated boundary `theta = s + t`

Two correct facts at `theta = s + t` (both immediate from `cos(s+t)`):
`cos theta = cos s cos t - sin s sin t` (so the angle at `H` is **not** right in
general — it is right iff `theta = pi/2`), and, by the cosine law,

```
   a^2 = (2r cos s)^2 + (2r cos t)^2 - 2(2r cos s)(2r cos t) cos(s+t) = (2 r sin theta)^2 ,
   i.e.  a = 2 r sin theta  and  R_circ = r  by (1).
```

Regular 7-star (`s = t = pi/7`, `theta = 2pi/7`): `|HU| = |HV| = 1.801937736 r`,
`|UV| = 1.563662965 r = 2r sin(2pi/7)`, `R_circ = r`. My earlier claims
"right angle at `H`" and "`a = 2r`" are both **retracted**; the correct pair is
"`a = 2r sin theta` and `R_circ = r`".

## Exact loss identity and the regular-star check (unchanged, verified)

`K_i = 2r^2 cos s_i cos s_(i+1) sin theta_i`; by
`2cos s cos t = cos(s+t)+cos(s-t) <= 1 + cos theta` (using `s+t >= theta`),

```
   K_i <= r^2 sin theta_i (1 + cos theta_i)      (attained iff s_i = s_(i+1) = theta_i/2)
   r^2 sin theta (1+cos theta) - K
      = r^2 sin theta [ (1 - cos(s-t)) + (cos theta - cos(s+t)) ]                    (L)
      = 2 r^2 sin theta [ sin^2((s-t)/2) + sin((s+t+theta)/2) sin((s+t-theta)/2) ] ,
```

both brackets `>= 0`. Regular star `s_i = t_i = pi/d`, `theta_i = 2pi/d`: both
brackets vanish, so **loss = 0 exactly for `d = 6` and `d = 7`**
(`d = 6`: `K/r^2 = env/r^2 = 1.2990381057`; `d = 7`: `1.2692954386`). No strict
shared-edge penalty at balanced stars; my earlier `0.0357 r^2` claim is
withdrawn.

Correct coefficient (replaces the reversed `1 - cos x >= x^2/2`):
`1 - cos x >= 2x^2/pi^2` on `[0,pi]`, hence for a `d`-star
(`sum theta_i = 2pi`, `sum s_i >= pi`)

```
   loss_i >= r^2 sin theta_i [ 2(s_i-s_(i+1))^2/pi^2 + 2(s_i+s_(i+1)-theta_i)^2/pi^2 ] ,
```

regular-case coefficient `(2/pi^2) d sin(2pi/d)` = `1.0529606` (`d = 6`),
`1.1090253` (`d = 7`).
