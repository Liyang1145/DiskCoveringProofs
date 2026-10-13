# R17 — width coupling on the low-bearing domain: W_ww structure, counterexample, majorant

Own scope only; lead files read, not modified.  Exact 9-decimal frozen `z`
(`joint_nested_frozen.json` sha256 `5671967c…21fb`), `R = 19/50`.
Bounded derivation + controls; no large grids.

## 0. The object

From `lead/joint_boundary_jet.py:6-14`:

```
x0 = 2b - pi/2 + asin r
p  = cos w - r cos(x0+w)        x = -sin w + r sin(x0+w)
cx,cy = (s - r sin2b, -2r sin^2 b),  s = sqrt(1-r^2)
px,py = (s cos w - r sin w, -s sin w - r cos w),   q = |(px,py)-(cx,cy)|^2
cn = 1 + r^2 - 2r cos x0,   gap = 1 - sqrt(cn),   den = 1 - p
u  = sqrt(q)/R,   a = atan2(x, den)
W  = -r s sin^2 b + (1/2 - mu) w + x/2 + (mu+h) a - d u^2 - l u
```

with `(mu,h,d,l) = (z1,z112,z34,z96)` for `j=0` and `(z3,z115,z39,z101)` for `j=1`.
Domains: `r ∈ [.379,.37999]`, `b ∈ [acos(r)/2, 1.19]`, `w ∈ [g, Wmax(r,b)]`,
endpoint gate `q >= (R·0.19)^2 = 0.005213`.

**Verified collapse:** `q = 1 + cn − 2p` exactly (checked at 30 dps, diff `~1e-32`).

## 1. Exact derivatives in `w` (the keys to everything below)

Two identities make `W` completely explicit:

```
p'  = x                    x'  = -cos w + r cos(x0+w) =: xp      x'' = -x
Y := 1 - p,  Y' = -x,      Y'' = -x' = -xp
q'  = -2p' = -2x           q'' = -2p'' = -2x'
u'  = -x/(R sqrt q)        u'' = -x'/(R sqrt q) - x^2/(R q^{3/2})
g := x'Y - xY' = xp Y + x^2,   g' = x''Y - xY'' = -xY + x·xp
a'' = g'/q - g q'/q^2
W'' = x''/2 + (mu+h) a'' - 2d (u'^2 + u u'') - l u''
```

**Validation (three independent routes at `(r,b,w) = (0.379, 1.10, 0.1914)`):**

| route | value |
|---|---|
| closed form above | `2.426729047202865` |
| term-by-term FD (each piece differenced alone) | `2.426746802058497` |
| direct FD of `W` at `h=1e-3` | `2.426746802058497` |

and over six further points spread across both branches and the `b`-range the closed form
agrees with the direct FD to relative deviation `≤ 7.7e-5`, i.e. FD truncation only.

## 2. Answer to the posed question: `W_ww < 0` is FALSE

Sampling 810 points of the stated domain (three `r`-values, nine `b`-values, fifteen
`w`-values, both branches):

```
W'' > 0 at 283 of 810 (34.9%)
LARGEST  W'' = +27.064164  at r=0.37999 b=1.190 j=1 w=0.35  (q = 0.006118, a'' = -130.20)
smallest W'' = -23.200962  at r=0.37999 b=1.190 j=1 w=0.45  (q = 0.008033, a'' = +114.57)
```

**`W` is neither concave nor strongly concave on the low-bearing domain.**  The sign of
`W''` changes inside the domain, so no tangent/Schur width elimination and no
`W_ww < 0` certificate is available.  This answers the lead's question in the negative and
identifies the counterexample as required.

**Mechanism (why).**  Only `a''` can be positive-large: it carries `1/q` and `1/q^2`
factors, while every other term in `W''` is bounded (`x''/2 ≤ 0.5`, the `u`-terms are
`O(1)` for `q` bounded away from 0).  The coefficient is `mu + h = -0.202197298` (`j=0`) /
`-0.202939569` (`j=1`), so near the last-listed gate `q ~ (R·0.19)^2` the `a''` contribution
dominates: at the largest sample `(mu+h)a'' = 26.42` while the `q`-terms total `≈ +0.65`.
This is structural, not accidental: **the width objective's `w`-curvature is large exactly
where the listing gate `q ≥ (R·0.19)^2` is tight.**

## 3. The replacement: a valid quadratic majorant (and `kappa`)

Since `W_ww < 0` fails, use the second-order (not first-order) majorant.  For any `w0` and
any interval `J ∋ w`,

```
W(w)  <=  W(w0) + W'(w0)(w - w0) + (kappa_J/2)(w - w0)^2 ,     kappa_J >= sup_J W'' .
```

This is an identity-free, assumption-free majorant: it needs only a finite bound on `W''`,
which the exact formula of section 1 supplies by interval arithmetic.  Substituting a
quadratic majorant for `W` in the coupled objective keeps the bearing coupling intact
(`w0` and `W'(w0)` still depend on `r,b`), which is what the obligation asked to retain.

Rigorous interval enclosures (`mpmath.iv`, 30 dps) per `(b, w)` slab with `r ∈ [0.379,
0.37999]`, both branches — full table in `out/r17S.log`; representative rows (j = 0):

| b slab | w slab | `q_min` | sup `W''` | inf `W''` |
|---|---|---|---|---|
| [0.80,0.85] | [0.05,0.10] | 0.10111 | **+1.92** | −1.05 |
| [0.90,0.95] | [0.15,0.20] | 0.06232 | **+4.29** | −1.30 |
| [1.00,1.05] | [0.25,0.30] | 0.02748 | **+12.83** | −1.70 |
| [1.10,1.15] | [0.30,0.35] | 0.00750 | **+90.21** | −4.09 |
| [1.15,1.20] | [0.20,0.25] | 0.01771 | **+29.90** | −5.30 |

Reading: `kappa` is small (order 1–5) away from the tight-gate corner and blows up like
`1/q_min` there, exactly as the `a'' = O(1/q)` structure predicts.  The interval enclosures
are conservative (the pointwise maximum seen is `+27.06` while the slab enclosure reaches
`+90.21`), because a `1/q` term evaluated over a `q`-slab inflates; refining the slabs near
the gate tightens this one-for-one.

## 4. Scope, proof level, and the gap

**Established (exact identities + validated numerics):**
* the closed form for `W''` of section 1, validated against three independent routes;
* `W_ww < 0` is **false** on the stated domain, with an explicit counterexample
  (`＋27.06` at `r = 0.37999, b = 1.19, j = 1, w = 0.35`) and a mechanism (`a'' = O(1/q)`
  times a fixed `≈ −0.202` coefficient);
* `q = 1 + cn − 2p` exactly;
* the quadratic majorant is *valid* for any finite `kappa ≥ sup W''`, and slab-wise
  rigorous `kappa` enclosures are tabulated.

**Not established / the gap:**
* **no width elimination by concavity** — the route is closed by the counterexample;
* the slab `kappa` values in section 3 are **interval enclosures, not tight** — they are
  valid upper bounds on `sup W''` but conservative by up to a factor `~3.3` at the tightest
  slab.  If the final objective bound is sensitive to `kappa`, the slab subdivision must be
  refined near the gate (a bounded, mechanical refinement), or a sharper enclosure of `a''`
  obtained by factoring the `1/q` structure out explicitly;
* the majorant **does not by itself bound the width maximum**: it converts "maximize `W` over
  `w`" into "maximize a quadratic over a bounded interval", which is a closed-form
  computation, but the resulting affine-in-`b` expression still has to be fed to the
  bearing-coupling bound the lead is building.  I make no claim that `kappa` is small enough
  for that final step to close.

## 5. Files

`r17_width_ww.py` (first probe, coarse), `r17b_ww_structure.py` … `r17R_final4.py`
(the successive corrections of my `u''`/`Y''` signs — the final verified version is
`r17R_final4.py`), `r17S_kappa.py` (`out/r17_kappa.json`, the `kappa` table).
Logs: `out/r17*.log`.  Artifacts: `out/r17_ww_final.json`, `out/r17_kappa.json`.
