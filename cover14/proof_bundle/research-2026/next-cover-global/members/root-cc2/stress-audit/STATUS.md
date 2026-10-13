# root-cc2 / stress-audit status  (CORRECTED)

Scope `research-2026/next-cover-global/members/root-cc2/stress-audit/` (only). Lead
artifacts read-only. One source re-run performed (the lead's certificate script).

## Verdict on the assigned obligation

**The fixed-sharp-stress obstruction holds at the audited interface.** The certificate's
test path is feasible and its certified second variation is correct:
`d^2 E/d eps^2 = -0.14455823...` along the path, confirmed both by the certificate's
formula with the certificate's own weights/velocities and by explicit symmetric second
differences of the weighted energy at eps = 2e-5, 5e-5, 1e-4, 1e-3. So the candidate is not
a local minimum of the weighted energy and `E_w < r*^2` nearby: no fixed nonnegative sharp
stress with this support pattern exists.

My first audit of this reached the opposite conclusion and was wrong (my reconstruction
froze the witnesses, and I mis-stated the feasibility condition). Corrections and root
causes are in `AUDIT.md` section 5; no claim was ever registered from the false finding.

## Mechanics confirmed

* feasibility: `sum_k g_k = 2 pi` is conserved identically for any velocity field, since
  `g_k' = v_{k+1} - v_k` telescopes; the cap-active indices 4 and 9 satisfy
  `v_5 - v_4 = 0` and `v_0 - v_9 = 0`, so they stay at the cap; the nearest non-cap gap is
  9.116e-3 rad below `L* = 2 asin r = 38.74787336 deg`, giving a legal window
  `|eps| < 0.0219`;
* the second-variation formula was verified numerically on a rotating example; the
  certificate's formula and the explicit energy both give `-0.1445582359`;
* everything else from the previous pass stands: anchors on `S^1` in cyclic order with
  gaps in `(0,pi)`; the two published D2 permutations are bijections and 20/20 physically
  covariant with the `Sx`/`Sy` reflections, generating exactly the six recorded orbits;
  the symmetry-averaging and weight-uniqueness steps are sound; the zero-central branch is
  path-independent.

## Interface note for the lead (not a defect)

The certificate moves the face witnesses (`24+f`) too; the prose of
`STRESS-OBSTRUCTION.md` section 3 says only "move free central nodes", which reads as if
the witnesses stay at their equilibrium positions. Freezing them changes the second
derivative from `-0.1446` to `+7.968`. Worth naming the witness velocities in the prose.

## Evidence / repro

```
cd research-2026/next-cover-global/members/root-cc2/stress-audit
py -3 -B py/fix01_corrections.py                  # telescoping, cap condition, moved nodes
py -3 -B py/fix02_curvature_with_witnesses.py     # explicit energy + certificate formula
py -3 -B py/geo02_perms_velocity.py               # D2 permutations physically covariant
```
Superseded drafts kept for traceability: `py/geo01_facts.py` (its orbit count was later
corrected), `py/path02_invariant.py`, `py/path03_empirical.py` (frozen witnesses).
Write-up: `AUDIT.md`. The lead's own repro is
`py -3 -B research-2026/next-cover-global/lead/stress_obstruction_certificate.py`.

## Next executable step

None for this obligation. The remaining open items (global covering bound; piecewise or
Voronoi-based routes) are outside this audit's scope and are unchanged.
