# root-cc2 status

Scope `research-2026/next-cover-global/members/root-cc2/` (only). Old n11/n12 assets
read-only. Owner: cc2 (commandcode2 / deepseek/deepseek-v4.1-flash).

## Latest (after the lead's independent certificate and attainment argument)

* Lead's `lead/root_integer_certificate.py` (240-bit integer-directed dyadic intervals +
  2nd-order AD, no shared kernel) certifies a unique zero in the exact dyadic box
  (center = the decimal root strings, halfwidth 1e-20), `rho < 3.807e-16`,
  `margin > 9.999e-21`, `det = 0.11135963346604882544...`. My independent
  representation check of that implementation: interval layer, sqrt directed rounding,
  2nd-order AD rules and the Krawczyk/Y-selection logic all verified; identities
  `F_lead = det^2 e`, `|p-A|^2-r^2 = |p-C|^2-r^2 = e`, `p·A = v1`, `p·C = v2`
  confirmed at 120 digits. Evidence `evidence/verif06_identities.txt`.
* `lead/root_cover_check.py` + `root-cover-controls.json`: re-enumerated with the lead's
  own kernel. The 16 remaining triples are the **same physical triples** as my audit04
  (14 tight + 2 slack), the tight shapes are 4+4+4+2 as claimed, the 4 collinear triples
  are dispatched by exact symbolic identity, and the 10 boundary anchors have cyclic
  gaps strictly in (0, pi) summing to 360 deg with every anchor inside its owner disk.
  Evidence `evidence/verif07_attainment_checks.txt`; residual caveats in
  `REPORT-addendum-lead-check.md` section D.
* My own certificate (C1164) remains available as a second, independent local root
  certificate on a wider box (halfwidth 5e-6); the lead now has the tighter box.

## Current claim level

* **proved-interval (local) root certificate** for the n14 D2-family 3-equation system
  `Phi = (F, G, F_z G_C - F_C G_z)`: exactly one zero in the declared dyadic box
  `X = [0.326813068949914,0.326823068949914] x [0.291936118964939,0.291946118964939] x [0.331727034276234,0.331737034276234]`
  (half width 5e-6; the lead's reported root lies strictly inside, distance 5.0e-6 to
  each face). Existence: Krawczyk `K(X) subset int(X)`, smallest face margin `4.35e-6`.
  Uniqueness: `rho = ||I - Y M||_inf = 0.1292 < 1`. Interval `det M = [4.0739,4.4207]`
  excludes 0. Interface to the coded `F`: `F_coded = e(e+1)` with `e = |p1|^2-1`, and my
  kernel's `F_tilde` is the same expression (equal at 200 digits to 7.3e-203); in-box
  facts `|p|^2 in [0.9995226,1.0004776] > 0` and `det in [0.4024037,0.4024622] != 0`.
  Evidence `evidence/cert01_krawczyk.{txt,json}`, `evidence/verif03_interface_highprec.txt`,
  `evidence/verif02_interface.txt`; kernel calibration `evidence/calib01_kernel.txt`.
  **NOT proved:** optimality, coverage of D by the 14-centre configuration, global n=14.
  Independent re-verification of this object is being done by the Lead with a separate
  fixed-dyadic/integer-interval + 2nd-order-AD implementation (not shared with my kernel).
* **RETRACTED (were mine, false):** C1160 (sigma_B forcing) and C1161 (F geometry /
  plus-minus). Root causes and corrected numbers: `DEAD.md`, `REPORT.md` §2–§3,
  `evidence/diag_disputed.txt`. The candidate's original branch statement was right.
* **audited (numeric + algebraic, unaffected by the retractions):** all four `+` radical
  branches reproduce `root-scout.json`; `A - z = (s-z)/2 = 0.3082777942140979` while
  `r - sqrt(r^2-z^2) = 0.2748453717541834`, so `sigma_B` and `sigma_D` are genuine
  independent branches; `G = l1 l2 l3 - 4 r^2 cross^2 <=> R_circum = r`, verified at the
  root; the lead's solve returns the unit-circle intersection `(0.6187591879148537,
  0.7855807198314828)`, `|p| = 1.0`, `|p-S1| = r`.
* **audited (numeric):** the physical contact structure is *identical* at the old and
  new root (14 tight vertices at `r` plus the same slack pair at `0.3208208546053816835`),
  so the candidate's "contact structure changed" is an indexing artefact.
  `evidence/audit04_contacts_corrected.txt`.

## Superseded / invalid (kept for traceability)

* `evidence/audit02_contacts.txt`, `evidence/audit03_coverage.txt`: contact portrait of
  the *incomplete* 10-centre free family (my error: the boundary reference points are
  covered by the fixed x-axis pairs), and the OLD-hprec side built from
  `json['centers']` (float64) instead of the exact `th` literals. **Do not use**; the
  lead's instruction to discard that portrait is followed. Replaced by `audit04`.
* Naming trap: `mpmath iv.mpf([1,2])` is the *thin* interval at 1 — endpoints must be
  `iv.mpf([mp.mpf(1), mp.mpf(2)])`. Cost me one wasted coverage run.

## Repro

```
cd research-2026/next-cover-global/members/root-cc2
py -3 -B py/audit01_root.py
py -3 -B py/audit04_contacts_corrected.py
py -3 -B py/calib01_kernel.py          # ~30 s (sympy)
py -3 -B py/cert01_krawczyk.py         # ~0.6 s  -> the certificate
py -3 -B py/verif01_krawczyk_independent.py
```

## Next executable step (minimal obligation)

Check whether this stationary zero is the *same object* as the certified exact-rational
upper construction (`lead/improved-upper-test.json`): i.e. rebuild the 14 exact-
rational centres from the certified upper test and test whether the certified
construction's contact configuration is the one whose free parameters satisfy
`Phi = 0` (and whether its exact covering radius equals its `r`). If yes, the root
certificate transfers; if no, state the two objects separately. Same check decides
whether the stress/KKT diagnostic may be rerun at this geometry.
