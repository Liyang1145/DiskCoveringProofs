# Independent audit of the uniform-simplex certificate (r20-rigidity) — revised

Artifact audited: `lead/certify_uniform_simplex.py`, `lead/SIMPLEX-CONCAVITY-BOUND.md`,
`lead/uniform_simplex_certificate.json`, reusing the stored C911 forces read-only.
Independent instrument: `audit_uniform_simplex.py` (this directory; no lead helper code, no solver).
Reproduction: `py -3 -B -X utf8 audit_uniform_simplex.py` (writes `audit_uniform_simplex.json/.log`).

## Arithmetic scope actually audited

1. **Graph + loads.** 51-edge canonical graph rebuilt from the written description (identical to the
   stored edge list); anchor loads `l_i` recomputed by exact `Fraction` incidence summation of the
   stored rational forces; all 22 free-node divergences exactly zero.
2. **Radial frame.** `l_i·U(theta_i) = a_i cos t + d_i sin t` with the **offset** `t = theta_i - 2 pi i/9`.
   The work `l_i·U(theta_i)` is theta-dependent; this is what the `kappa_i` track. (My first run used
   the absolute frame and produced spurious negatives; corrected before reporting.)
3. **Whole simplex `{y_i >= 31/450, sum y = 1}`.** `S_i = sum_{j<i} y_j` has **i** terms, so its exact
   attainable range is `[i·31/450, 1-(9-i)·31/450]`; `theta_i = iL - D S_i`; the minimum of the work
   over the offset interval is evaluated by a certified endpoint rule (`g(t) = R cos(t-phi)`: if
   `a_i > 0` and the interval lies in `(-pi/2, pi/2)` the interior minimum is excluded, otherwise `-R`
   is included conservatively). Result: **all nine radial works are `>= 0` on the whole simplex**
   (`i = 1,2,6` exactly 0), hence `kappa = 0` and no Taylor penalty.
4. **Width cap.** `D = 9L - 2pi > 0` (interval), `Delta_max = L - D·(31/450) = 0.729086839815031763`;
   `Delta_i <= Delta_max <-> y_i >= 31/450` is an identity since `Delta_i = L - D y_i` with `D > 0`.
   Endpoints: `Delta(1) = 2pi - 8L = 0.0464445635914174594`, `Delta(0) = L = 0.779592592948521127`.
   `L` is **defined** by `L = 2 atan2(19/50, sqrt(1-(19/50)^2))`; the `sin(L/2)` interval enclosure is
   only a consistency diagnostic, not a proof of the identity.
5. **Nine vertices at `t = 19/50`.** `y^j = (1-t)/9·1 + t e_j` (rational), each vertex angle vector
   satisfies `sum Delta = 2pi` (asserted). At this cell: `kappa_i = 0` for every anchor (asserted) and
   the dedicated `cellvmin = 0.38012312708559108164 > 19/50` (asserted). The separate 100-point sweep
   over rational `t` is a **numeric selector** only (38 of 100 pass, largest `t = 19/50`); it carries
   no exact identity.

## Limits

Not audited: the dual/support-function derivation itself, the cell-covering tree logic, C912's
containment test, the passage to a global bound, and any phase-constancy claim (none is made or used).
No new claim; this is an instrument audit of the arithmetic scope above.
