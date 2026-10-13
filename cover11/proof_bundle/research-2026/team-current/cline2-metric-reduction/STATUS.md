# cline2-metric-reduction — STATUS (final for this round)

## Live deliverable: correct unsaturated 9-ring reconstruction

Implements the lead's parametrisation literally and verifies it on the exact candidate.

```
per ring site, switches P_prev, P on |x| = 1, width w = angle(P_prev, P):
    k = cos(w/2), d = 2 sin(w/2),
    P_prev = k n - (d/2) e,  P = k n + (d/2) e,
    a = rho_prev, b = rho_i,
    x = (a^2 - b^2)/(2d),
    h = sqrt( b^2 - (x - d/2)^2 )  =  sqrt( a^2 - (x + d/2)^2 ),
    c = (k - h) n + x e
identities:  |c - P| = b,  |c - P_prev| = a,  |c|^2 = (k-h)^2 + x^2
feasibility: b^2 - (x - d/2)^2 >= 0,  k - h > 0,  |c| < 1
```

**Verified** (`c41_recon.py`): nine candidate sites rebuilt with max error `7.9e-16`; the two
radical forms agree exactly; `|c-P| = b`, `|c-P_prev| = a` to `3.3e-16`.
**Higher-precision check** (`c42_hp_check.py`, mpmath 50 digits on the exact integers): max
reconstruction error `6.7e-51`, identity error `3.3e-51`, and the nine switch minimal
distances reproduce `0.3799838531198386…` to 17 digits — so the reconstruction is exact and
the float64 residual is round-off, not a radical-domain artefact.

**Parameter count:** 9 widths (sum `2 pi`) + 9 radii + 4 hub coordinates = 21 after removing
the rotation; the bound `r` is an extra variable. Covering gives `rho <= r` only.

**Candidate facts (not theorems):** all nine radii equal `R = 0.37998385311983884`; radical
slacks `+1.09e-3` (site 1, tightest) to `+6.76e-2`; `x = 0` at this configuration
(`a = b`), which is why the saturated special case looked general.

## Corrections to my earlier work (all accepted from the lead's audits)

1. Boundary-saturation lemma (rev 2): **retracted** — `min_j |P-c_j| <= R` does not imply
   equality at a maximiser or at all nine switches; lead's `C821` is an exact counterexample.
2. Antipodal criterion (rev 2): **retracted**; correct form
   `2 x*·(c_j - c_i) <= |c_j|^2 - |c_i|^2`.
3. Radius count: **9** radii, not 18 (`a_i = rho_(i-1)`, `b_i = rho_i`).
4. Radical: my `sqrt(k^2 - 1 - x^2 + b^2)` omitted the `d x` term; the lead's
   `sqrt(b^2 - (x-d/2)^2)` is correct.
5. Closure rows: my rev-1 "fails by 0.107 rad" was my index error; the identity holds at
   `3.1e-15` with the owned width. Registered `C823` withdrawn (wrong L/T endpoints in the
   equation; "8 independent" had no analytic rank proof — a floating residual is not a proof).
6. The rational form `h = (d^2+b^2-a^2)/(2d)` quoted in my previous message was my own
   invention, mis-attributed to the lead; the lead's delivered formula was the radical.
7. Local finite-difference optimality: **stopped** per instruction (lead holds the KKT work).

I will not register further claims from numeric tolerances.

## Files

| file | content |
|---|---|
| `c41_recon.py` | correct unsaturated reconstruction, verified `7.9e-16` |
| `c37_unsaturated.py` | candidate `(w,a,b)` table; radical domain |
| `c31_closure.py` | closure rows with the owned width (identity check) |
| `c25_model.py`, `c27_verify.py` | saturated special case (conditional, `a = b`) |
| `c13_blocks.py` | 21 matching rows; log-radius Jacobian rank 19 |
| `c36_unsaturated.py`, `c38_recon.py` | earlier attempts with the wrong radical — superseded |
| `c39_unsaturated_test.py`, `c40_gradient.py` | diagnostics only (not part of the model) |
| `CLINE2-RING-REDUCTION.md` | the corrected write-up (rev 4) |

## Next obligation

The nine radii are **not** eliminated (lead: only a necessary norm filter exists, no elimination
proved), so the 21-dimensional model of §1 stands as-is. Obligation, stated without anticipating
an elimination: on the domain of §1 (nine positive widths summing to `2 pi`, nine radii `rho <= r`,
two hub sites, feasibility `h^2 >= 0`, `k - h > 0`, `|c| < 1`), show that
`max over switches and Voronoi vertices >= r*`, or exhibit a configuration of that domain with a
smaller covering radius. No new claim before this interface is checked.

## Reference correction

The universal-saturation counterexample is registered as `C830` (correct threshold object `C529`,
original `1e-17` threshold with `+1e-5`, actual displacement `1e-6`); the earlier
`C821 -> C249` citation pointed at a different object (`1e-60`). Geometry intervals and the
conclusion are unchanged.
