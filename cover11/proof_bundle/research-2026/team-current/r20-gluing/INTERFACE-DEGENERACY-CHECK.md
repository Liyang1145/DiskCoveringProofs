# INTERFACE-DEGENERACY-CHECK — does the central-face / adjacent-arc interface cover the degeneracies in the q0(6,7) global topology chain?

**Auditor**: r20-gluing lane (cline2-r23-gluing). Read-only; **no claim registered**. Sources read:
`lead/INWARD-ARC-SWITCH-UNIQUENESS.md`, `lead/R20-CHAIN-HUB-CONVEXIFICATION.md` (C879), registered
claims **C809, C818, C819, C824** (proved-exact / proved-interval, all unreviewed except C809), plus
my own `CENTRAL-SCREEN-INDEPENDENT-AUDIT.md` and `C900-INDEPENDENT-CHECK.md`. No local-germ work.

## 1. Dependency map of the surviving global topology

```
C809 (union-measure star lemma + two-triple capacity)      q <= 1, K in {12,13}
  -> C818 (29-factor shared-moment dual, q1 (6,6) classes)  ALL q1 excluded
      -> C819 (moment dual, q0 degree (4,9))                (4,9) excluded
          -> C824 (shared moment + C820 cyclic closure)     (5,8) excluded
              => only q0(6,7) survives at r <= 19/50
```
All four are **relaxation-type** statements: area upper bounds over *closed* angle/radius domains
with zero limits included (C819 caliber; C824 "Domain contains every genuine configuration, including
unequal switch radii and degeneracies"; C809 explicitly closed disks with tangency). An upper bound
on a superset bounds the genuine set, so **degenerate configurations cannot leak out of these four
proofs** — the relaxation direction is the right one for each.

## 2. The two interfaces and their degenerate strata

**(a) Central-face interface (C879 corollary → C900 fiber theorem).** The strata:
* *collinear `(a, b, c_i)`*: no circumradius exists. C900's proof excludes them from the disk
  intersection — on the chord line the two factors coincide, so near-disk membership contradicts the
  **strict** positivity of the far factor (my check: factors equal at 4/4 sampled chord points). They
  are outside the non-collinear necessary domain of the cover graph, **not** treated as vacuously
  true (lead correction, now in both my audit doc and the member's JSON).
* *`|AC| = 2r` (`k = 0`)*: `q_near = q_far = m`; the identity degenerates to
  `4y²(ρ²−r²) = (|b−m|²−r²)²`, and such tuples are excluded by the **strict** distal bound `G`,
  not by `ρ ≥ r` and not by domain-vacuity (lead correction; verified in my audit).
* *arc tangency / double radial root*: the new inward-arc lemma covers them explicitly
  ("This includes double radial roots and arc tangency") and uses the inward radial bound
  `|a|,|b| ≤ √(1−r²)` — the control states that arbitrary (non-inward) centres are NOT covered.
* *strict hub norm* `|h| < 1−r`: required by C879 Lemma 2 (a full cover has hubs strictly inside);
  my box audit certifies the localisation balls stay strictly inside on the audited box.
⇒ **Within its conditional scope the central-face interface does cover these degeneracies.** What is
*not* global is the hypothesis (E) (uniform strict distal separation): C900 says so itself, and my
independent certification of (E) exists only on the single audited ring box (the candidate's
neighbourhood). The four topology claims above do **not** invoke the central-face interface, so they
are unaffected; the q0(6,7) *sharp* route remains conditional on global (E).

**(b) Adjacent-arc interface (inward lemma → C879 ledger).** The lemma now proves existence and
uniqueness of the covered boundary switch for every **intersecting pair of noncontained arcs** in the
canonical inward representative, so C879's hypothesis "exactly ONE equal-distance point in the common
covered arc" no longer has to be assumed *for those pairs*; degenerate cases (duplicate centres,
tangent singleton arcs) are disposed of in the lemma. The lemma's own caveat names the remaining,
**separate** interface: *"proving the selected fan graph corresponds to these adjacent arcs remains a
separate graph interface"*. The classification used by C809/C818/C819/C824 enumerates graph classes,
so it inherits that graph-interface obligation — it is not a degeneracy leak, but it should be listed
as the open interface feeding all four claims.

## 3. Answer to the lead's question (short)

* Does "canonical inward + 9 essential arcs" still need to **assume** boundary-switch uniqueness?
  **No** — for adjacent intersecting noncontained arcs it is now proved (inward lemma), provided the
  inward radial representative (C464/C451) is the one in force; the assumption is replaced by that
  representative's bound plus the still-separate fan-graph ↔ adjacent-arc correspondence.
* Do the central-face non-collinear and adjacent-arc interfaces **cover the degeneracies**?
  **Yes at interface level**: collinear strata are excluded by strict far-factor positivity, `k = 0`
  by strict `G`, tangency by the lemma, strict-interior by the class definition — all now stated in
  the same place. **No at global-certificate level** for the central-face premise (E): it is certified
  only on the audited box (C900-conditional), while the four topology claims are relaxation proofs
  that do not depend on it.
* Residual interface list (named, not expanded): (i) global (E) for the central faces; (ii) fan-graph
  ↔ adjacent-arc correspondence; (iii) the inward-representative bound's own derivation
  (C451/C464 — outside this lane).

**Repro / evidence**: this note reads only; supporting computations are
`r20-gluing/r23_central_screen_audit.py`, `c900_independent_check.py`, `CENTRAL-SCREEN-INDEPENDENT-AUDIT.md`,
`C900-INDEPENDENT-CHECK.md`. No claims registered, no other directory modified.
