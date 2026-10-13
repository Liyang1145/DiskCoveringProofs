# C911 independent instrument audit (r20-rigidity)

Scope of this audit: the certificate kernel of `lead/certify_uniform_sector.py` /
`UNIFORM-SECTOR-CERTIFICATE.md` / `uniform_sector_certificate.json`. The original solver was **not**
used; the script `audit_c911.py` (this directory) rebuilds everything it can from the written
description and the stored artifact. Reproduction: `py -3 -B -X utf8 audit_c911.py`
(reads `lead/uniform_sector_certificate.json`; writes `audit_c911.json/.log` only).

## What was recomputed independently, and what it read

1. **Graph from the description, raw/canonical mapping.** 9 anchors `0..8`, 11 sites `9..19`,
   11 auxiliary face nodes `20..30`; site-anchor edges `(9+s, s)` and `(9+s, (s-1) mod 9)`; the 11 faces
   `[9,k,k+1] (k<4)`, `[10,k,(k+1) mod 9] (4<=k<9)`, `[9,10,0]`, `[9,10,4]` each contributing 3 edges
   from the auxiliary node to its sites gives **51 edges**. My rebuilt edge list (order included) and
   face list are **identical** to the stored ones. Degrees: anchors all 2, sites all a mix of the
   face incidences, auxiliaries 3 each — consistent with the described canonical graph.
2. **Incidence/divergence of the stored forces, exact rationals.** Reading `forces_rational` as
   `Fraction` and summing the 51 edge contributions over the 31 nodes: the divergence at all **22 free
   nodes is exactly zero** (`max |.| = 0` in exact arithmetic, no tolerance). This is an identity on
   the stored artifact, established independently of the lead's forest traversal.
3. **Norm / dual feasibility.** Interval evaluation gives `sum_e ||p_e|| = 0.99999999999881553691 < 1`
   (the coordinate `l1 = 1.27129590146068…` is a diagnostic, unused).
4. **Support minimums by a different expression.** Instead of the lead's endpoint linearisations I used
   the exact minimum of `g(t) = a cos t + d sin t` on `[-h,h]`:
   `min(g(-h), g(h), -R * [phi + pi in [-h,h]])` with `R = sqrt(a^2+d^2)`, `phi = atan2(d,a)`.
   For this data no interior critical point is active (`|phi| < pi - h` for all 9 anchors), so the
   terms reduce to `a cos h - |d| sin h`; anchor values:
   `0.0702241981742471743, 0, 0, 0.0675764640002018973, 0.0743823616055860269, 0.0501287736995833481,
   0, 0.0509497787127183975, 0.0773116264176777618`.
   Total lower bound `= 0.390573202610014606 > 39/100`, **identical to the lead's diagnostic to all
   printed digits**.

## Load-bearing check: the angle-0 fixation

The certificate fixes `theta0 = 0` exactly (term `= a_0`), and the scope statement says so. Audit of
the necessity: if `|theta0| <= h` were allowed instead, the `i=0` term drops from `0.0702241981742472`
to at most `0.0690746272102568`, and the total becomes `0.3894236316460242 < 0.39`. **The fixation is
load bearing**; the certificate's stated scope (theta0 fixed, other eight angles free) is therefore the
correct one and no over-claim is present in that direction.

## Verdict and limits of this audit

* Independent confirmation: graph identity, exact free-node divergence zero, `sum_e ||p_e|| < 1`, and
  the arc-support bound `> 39/100` (by an independently written minimum expression) all reproduce.
* Not audited here (outside the instrument): the dual/support-function derivation itself, the
  fixed-switch SOC reduction, the provenance of the SLSQP proposal, and the passage from the angular
  box to `V(U) > 39/100` for the oracle radius. The audit is of the certificate kernel, not of the
  modelling chain.
* No PASS flag of this script is claimed as a proof; the evidence is the printed exact identities and
  interval endpoints above, reproducible by the one command.
* Optional extension requested by the lead (maximal conservative rational `h` instead of the exact
  optimum): not attempted here; the binding constraint is anchor 1/2/6 with zero divergence and
  anchor 4/8 near the boundary of the `0.39` budget, so an `h`-increase would have to be traded against
  `3/100` margin; left for a separate run.

## Audit revision (lead source audit of this audit, 2026-09-25)

The first version of `audit_c911.py` selected the interior-minimum branch with a single-sided
comparison (`phi.lower >= threshold` with `mp.pi`), so an interval straddling the threshold could
silently drop the term `-R`. Fixed as follows:

* the branch is decided only by a **certified exclusion**: with `g(t) = a cos t + d sin t` the interior
  minimum is at `t = phi + pi` (value `-R`) and is excluded when `a_lo > 0` (then `|phi| < pi/2`) and
  `h_hi < iv.pi/2`; the threshold is taken from `iv.pi`, never `mp.pi` or `h.lower`;
* if the exclusion is **not** provable the term `-R` is included conservatively (three-state, no
  straddling), with a log line naming the anchor;
* zero-`l` anchors are handled exactly in `Fraction` arithmetic (`l = (0,0)`: term exactly `0`);
* hard `assert`s now cover the graph identity, the exact free-node divergence, `sum_e ||p_e|| < 1`,
  and the total `> 39/100` (logged booleans are not enough to stop a silent failure);
* for this artifact the exclusion is provable at every nonzero anchor: `a_lo > 0` for `i = 0,3,4,5,7,8`,
  and `i = 1,2,6` have `l = 0` exactly. Re-run readings unchanged: total
  `0.390573202610014606 > 39/100`, norm `0.99999999999881553691 < 1`, free divergence `0`.

Revised file hashes: `audit_c911.py`, `audit_c911.json`, `audit_c911.log` (see the log header of the
re-run; the printed identities are the evidence).
