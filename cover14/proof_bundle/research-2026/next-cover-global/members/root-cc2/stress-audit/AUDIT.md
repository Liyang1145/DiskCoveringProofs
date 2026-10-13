# root-cc2 stress-audit: audit of lead/STRESS-OBSTRUCTION.md + stress_obstruction_certificate.py
# (CORRECTED version, superseding the first draft of this file)

Scope `members/root-cc2/stress-audit/`. Lead artifacts read-only. One source re-run
performed; the lead's script reproduces its posted output
`[-0.1445582359335557, -0.1445582359335545]`, `orbits`, `rows [28,0,1,8,9,25]`.

## Verdict

**The mechanism checks out.** The obstruction's test path is feasible and the certified
second variation is correct: the explicit weighted energy along that path has second
derivative `-0.14455823...` (verified by symmetric second differences at eps = 2e-5, 5e-5,
1e-4, 1e-3), matching the certificate's interval. The earlier negative finding in this
directory was **my error** (see section 5) and is retracted. Evidence for the corrected
verdict: `evidence/fix01_corrections.txt`, `evidence/fix02_curvature_with_witnesses.txt`.

## 1. What the certificate establishes, and its interfaces

* **Feasibility of the path.** The anchors are points of `S^1` at angles
  `theta_k(eps) = theta_k + eps*v_k` (this is the correct kinematics: a rigid rotation
  `v = (1,...,1)` leaves all gaps constant). The gaps are `g_k = theta_{k+1} - theta_k`
  with the index taken mod 10, so `g_k' = v_{k+1} - v_k` for every k, and

      sum_k g_k' = sum_k (v_{k+1} - v_k) = 0   **identically in v**.

  Hence `sum_k g_k = 2 pi` is conserved for every path, and `sum_k v_k = 0` is **not**
  required. What feasibility needs is that the cap-active gaps stay at the cap, i.e. that
  their GAP derivative vanishes: `v_{k+1} - v_k = 0` at those k. For the certificate's
  field `v = (0,-1/4,-2/3,-13/12,-4/3,-4/3,-13/12,-2/3,-1/4,0)`:
  `g_4' = v_5 - v_4 = 0` and `g_9' = v_0 - v_9 = 0`, so the two cap-active gaps
  (indices 4 and 9, the two maximal gaps of 38.747873 deg = `L* = 2 asin r`) are
  stationary to first order. The remaining gaps are strictly interior, the nearest one
  9.116e-3 rad below the cap with derivative 0.41667, giving a legal window
  `|eps| < 0.0219`.
* **The second variation.** `d^2/deps^2 |x_u - x_v|^2 = 2[|dv|^2 + (x_u-x_v).(a_u-a_v)]`,
  verified numerically on a rotating-anchor example (`0.527272732` from both the explicit
  second derivative and the formula). With the certificate's weights, velocities and
  formula I get `-0.1445582359`; the explicit energy along the same path gives the same
  value. So the candidate is not a local minimum of the weighted energy and
  `E_w < r*^2` for nearby feasible configurations.
* **Scope.** A local statement at the candidate: this fixed-weight graph's energy is not
  minimised there, hence no fixed sharp stress with this support pattern exists. Not a
  statement about the covering optimum, piecewise energy bounds, graph strengthenings or
  restricted anchor domains (the document says so).

## 2. Verified independently and kept

* the cap `L* = 2 asin r = 38.74787336 deg` against the actual gap list; the two maximal
  gaps are exactly the cap-active indices, with zero gap derivative;
* the ten anchors lie on `S^1` (`max | |p|^2 - 1 | = 1.5e-37`), are cyclically ordered
  with gaps in `(0, pi)` summing to `2 pi`;
* the two published D2 permutations (length 34) are bijections and are **20/20 physically
  covariant** with the `Sx` / `Sy` reflections on the kept edge variables; the orbit
  decomposition is `[0,3,6,9]`, `[2,5,8,11]`, `[14,23,24,33]`, `[16,21,26,31]`,
  `[17,20,27,30]`, `[18,19,28,29]` -- six orbits, as recorded;
* the symmetry-averaging step (document section 1) is sound: for a `D2`-closed domain,
  `E_w(x) = sum_g E_{g w}(g x)/4`, so averaging preserves sharpness, and any slack face
  with positive weight forces the weighted energy below `r*^2` at that face;
* the weight-uniqueness step (document section 2) is sound: the site-equilibrium
  conditions are linear in the weights, the 6x6 system is interval-non-singular by guarded
  elimination, so the normalised positive solution is unique up to scale, and the
  homogeneous argument excludes the zero-central branch;
* the zero-central branch (document section 4) is analytic and path-independent.

## 3. Interface notes (not defects)

* The certificate moves **all** free central nodes, including the face witnesses
  (nodes `24+f`), with velocities stored in `stress-obstruction-certificate.json`. The
  document's section 3 sentence "move free central nodes linearly with the fixed rational
  velocities stored in the certificate" should say "including the witnesses": a reader
  following only the prose ("witnesses are equilibrium points") can reasonably freeze
  them, and with the witnesses frozen the energy's second derivative is `+7.968` instead
  of `-0.1445582`. The curvature is a property of the path as constructed, so the
  witnesses' velocities are load-bearing and deserve to be named in the prose.
* Those witness velocities are consistent with the certificate's first-order least-action
  condition: the nodes held fixed under the minimisation are the anchors, so the witnesses
  are free and receive the Schur/Lagrange velocities.

## 4. Scope of my audit

Read the script and the document; recomputed the gap/cap structure, the symmetry action,
the orbit decomposition, the first-order gap motion, the derivative formula on a rotating
example, the explicit energy along the certified path (witnesses moving), and the second
variation from the certificate's formula. Did not re-derive the site-equilibrium cascade
(`STRESS-SUPPORT-ANALYTIC.md`) beyond using its consequence, and did not attempt the
zero-central branch's calculus.

## 5. My errors, corrected and retracted (in order of severity)

1. **Frozen witnesses.** I evaluated the path with the witnesses held fixed, which is not
   the certificate's path, and reported `+7.968` as a curvature mismatch. With the
   witnesses moving the explicit energy reproduces `-0.14455823...`, i.e. the certificate.
   Method error: I compared my own reconstruction against their number without first
   making my reconstruction match their interface.
2. **False "feasibility invariant".** I claimed `sum_k v_k = 0` was necessary. It is not:
   the telescoping `sum_k (v_{k+1} - v_k) = 0` holds identically because the last gap wraps
   to `g_9' = v_0 - v_9`. Nothing was registered from this claim; this directory's earlier
   text is superseded by this file.
3. **Mis-read cap-active condition.** I wrote "cap-active gaps have `v_4 = v_9 = 0`". The
   controlling quantities are the gap derivatives `g_4' = v_5 - v_4 = 0` and
   `g_9' = v_0 - v_9 = 0`; `v_4 = -4/3` is not zero and need not be.
4. **Mis-attributed stale constant.** I wrote that the document cites `L* = 38.7355 deg`.
   It does not; `STRESS-OBSTRUCTION.md` writes only `L* = 2 asin r*`, and the box value is
   38.74787336 deg. Withdrawn.
5. Earlier in this directory (`geo01`): I first reconstructed the orbits with the
   whole-vector permutations applied to a different variable indexing and reported
   "2 orbits"; corrected to 6 by testing physical covariance.

## 6. Remaining obligations

None for the audited claim at the local level. The open items in the document's own scope
remain open and are not touched by this audit: the fixed-stress obstruction does not imply
the global covering bound, and the piecewise/Voronoi routes are separate.
