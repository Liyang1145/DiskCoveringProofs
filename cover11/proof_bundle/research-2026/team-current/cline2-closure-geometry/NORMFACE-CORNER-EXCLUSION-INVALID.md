# NORM-FACE CORNER EXCLUSION — **NON-BEARING / WITHDRAWN**

Status: `NORMFACE-CORNER-EXCLUSION.md` in this directory is **WITHDRAWN as
evidence**. Its core claim ("exactly one of the two norm-face corners is
excluded") is **false**, and its formula for the other-face residual was wrong.
No further formula correction attempted, per instruction. The lead's chart
`lead/NORM-FACE-CORNER-CHART.md` plus the direct disk filter retains both signs
correctly and is unaffected.

## 1. The counterexample (verified)

Face centers `C_1 = (r sin 2b1, -r cos 2b1)`, `C_2 = (r sin 2b2, +r cos 2b2)`
coincide **iff `b1 + b2 = pi/2`**, since then `sin 2b2 = sin 2b1` and
`cos 2b2 = -cos 2b1`. This lies in the both-low region (`b1 = b2 = pi/4`).
Verified: `|C_1 - C_2| < 1e-31` at `(b1,b2) = (pi/4,pi/4)`, `(0.7, pi/2-0.7)`,
`(0.9, pi/2-0.9)`, and `|C_1 - C_2| = 0.0221` at `(0.8,0.8)` where
`b1+b2 = 1.6 != pi/2`.

When the centers coincide, both corners satisfy the other-face test with
**residual exactly 0** (the other face circle is the same circle; both corners
lie on it), so both signs are live:

```
   (b1,b2) = (pi/4, pi/4), r = .379:  g = -4.8e-32, +4.8e-32, +4.8e-32, -4.8e-32
```

(±1e-32 is round-off for 0 at 30 digits.) Away from the degeneracy the signs are
strictly opposite, e.g. `(b1,b2) = (0.75,0.80)`: face 1 gives `-1.169e-2` and
`+1.185e-2`. So the "one excluded" statement holds only off the codimension-1
surface `b1 + b2 = pi/2` and is not a general reduction.

## 2. Errors in my report (all confirmed)

1. **Core claim false**: at `b1+b2 = pi/2` both corners are admissible
   (residual 0), so the 4-to-2 corner reduction fails there.
2. **Formula wrong**: I wrote
   `g = |V|^2 + r^2 - 2a*chi*B - 2*chi*Cdot`. The correct expansion of
   `|X_chi - C_o|^2 - r^2` from `X_chi = C + a e + chi h Je` is

```
   g = |V|^2 - 2 ( a e + chi h Je ) . V ,        V = C_o - C ,           (correct)
```

   i.e. the `r^2` term does not appear and **the `a`-term is not multiplied by
   `chi`** — exactly as the lead stated. Verified: the lead's formula agrees with
   the direct computation to `1e-32` at every test point, while mine disagreed by
   up to `4e-1` (my diagnostic scripts also had an unnormalized `e`, compounding
   the error).
3. **`|V|` depends on both bearings**, not on `(r, b_j)` alone: it is
   `|C_1 - C_2|`, e.g. `0.1722` at `(1, 0.8)`, `0.3154` at `(1,1)`, `0.0221` at
   `(0.8,0.8)`. So the "corner is a function of `(r,b_j)` only" simplification
   does not hold for the admissibility test.
4. **Derivative/sign alone cannot decide `g <= 0`**: the sign of `dg/dchi` gives
   the direction of change only; the offset `|V|^2 - 2a(e.V)` decides whether
   either root is admissible. My rule (R) implicitly assumed the offset was
   positive in the right amount.

## 3. What remains valid from my work (non-bearing, diagnostics only)

* The intersection formula and the checks that `|X - C_j| = r` and
  `|X - N| = 1-r` at both roots (the lead's chart already provides this).
* The observation that the wedge in its geometric form
  (`angle(X - p_j, -p_j) <= b_j`) does not by itself remove corners.
* Nothing here is needed as bearing evidence; the lead's chart plus the direct
  disk filter is the correct treatment.

## 4. Files

* `corner_leadcounterexample.py`, `corner_degeneracy.py`, `lead_formula_check.py`
  — verification of the counterexample, the degeneracy surface, and the lead's
  formula against the direct computation.
* `corner_probe.py`, `corner_pattern.py`, `corner_admitted.py`,
  `corner_rule*.py`, `corner_final.py`, `corner_complete.py`,
  `corner_survivors.py`, `corner_jacobian.py` — earlier buggy diagnostics; **do
  not cite**.
