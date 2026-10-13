# C900-INDEPENDENT-CHECK — bearing-interface pass on the conditional central-fiber elimination

**Auditor**: r20-gluing lane (cline2-r23-gluing). **No claim registered.** Read-only; the audited
objects are `lead/CENTRAL-FIBER-HELLY-REDUCTION.md` and registered claim **C900** (proved, unreviewed),
with dependencies C879 and the central-screen premise certified in
`r20-gluing/CENTRAL-SCREEN-INDEPENDENT-AUDIT.md`.

Per the lead this is **one bearing-interface pass**: no repeated symbolic algebra, no claim counts
beyond what the interface needs. My own verification scripts: `c900_independent_check.py` / `.json`
(enumeration, MEC criterion, strict-min lemma, collinear stratum) and `audit_product_identity.py`
(the product identity, already used in the central-screen audit).

## The interface chain and its wiring

1. **C879 → chain domains.** `K_X = B_open(0, 1−r) ∩ ∩_{p ∈ P_X} B_closed(p, r)` (strict hub norm,
   closed equal-radius pin disks). I re-derived the underlying identity
   `4y²(ρ²−r²) = (|b−q|²−r²)(|b−q'|²−r²)` (SymPy, my own transcription → 0) and the corrected
   half-plane direction `g_q − g_{q'} = −4yk`, i.e. `B(q',r) ∩ H_q ⊆ B(q,r)`. The chain reduction
   `ρ ≤ r ⟺ b ∈ B(p_in, r)` (strict interior `|h| < 1−r`) is correctly wired.
2. **C900 hypothesis (E).** `∀a ∈ A, ∀b ∈ K_B, i ∈ {0,4}: |b − q'_i(a)| > r`. C900 is explicitly
   **conditional** on (E); its own text says it is "not a certificate of its distal-exclusion premise".
   *Where (E) is discharged on the lead target box*: my central-screen audit's `G > 0` with the
   far/near branch fixed by `sref` (strictly signed on the whole box), and `K_B ⊆ B(b_B, ε_B)` by the
   variance identity — so the box's certification gives (E) on the C900 domain
   `A = K_A ∩ {0 < |a − c_i| < 2r}` for that box. This is the one bearing addition of this pass.
3. **Fiber equivalence.** Under (E), for each `a`:
   `{b ∈ K_B : both central non-degenerate circumradius ≤ r} = K_B ∩ B(q_0(a),r) ∩ B(q_4(a),r)`.
   The two interfaces that could silently leak are both closed:
   * *non-collinear*: the near-disk criterion contains no collinear point — on the chord line the two
     factors coincide, so near-disk membership contradicts the strict positivity of the far factor
     (my check: factors equal at 4/4 sampled chord points); collinear triples have no circumradius and
     are outside C900's non-collinear necessary domain (not treated as vacuous);
   * *`|AC| = 2r` (`k = 0`)*: the product identity degenerates to `4y²(ρ²−r²) = (|b−m|²−r²)²`, so
     `ρ ≤ r` forces `|b−m| = r`, while the strict (E) forces `|b−m| > r` — excluded by the strict
     bound, **not** by the invalid `ρ ≥ r` argument, and **not** by a domain-vacuity shortcut
     (this is the correction the lead issued; it is now in my audit doc and in the member's JSON
     `radicand_branch_semantics`).
4. **Helly elimination (b).** For fixed `a` the fiber is an intersection of 7 convex planar sets:
   1 open norm ball + 4 chain-pin disks + 2 central disks. Nonempty ⟺ all 35 triples meet; with
   `K_B ≠ ∅` the 10 triples without a central disk are automatic; the remaining **25** split as
   `12 + 4 + 8 + 1` (1 central + 2 pins; 2 central + 1 pin; ball + 1 central + 1 pin; ball + 2 central)
   — my own enumeration reproduces exactly this (`c900_independent_check.json`, (A)).
   * Three equal-radius closed disks meet ⟺ **MEC**(centres) ≤ r, **not** circumradius-alone
     (obtuse/collinear cases included); my sampled test agreed 12/12, and the standard case split
     (half the longest side for right/obtuse, else circumradius) is what C900 records.
   * Open ball + two closed disks: the triple meets iff `min_{b∈B(u,r)∩B(v,r)} |b| < 1−r` **strictly**,
     computed by 0/single-circle nearest point/circle-intersection points; my sampled test agreed 4/4.
5. **What C900 leaves open (and does not claim).** The a-domain `A` is 2-dimensional and not convex;
   the elimination is exact only on certified-(E) regions; no global coverage, no optimality.

## Findings for the lead

1. **Wiring is sound** and no unmentioned stratum leaks through the central-face interface: the
   non-collinear domain and the `k = 0` boundary are both handled explicitly, and (E) is a strict
   inequality throughout.
2. **The conditional ↔ conditional gap is closable on the audited box**: my `G > 0` supplies (E),
   so C900's fiber elimination is instantiated there (with the branch uniform over the box). Outside
   that box (E) remains an obligation — C900 stays conditional.
3. **Evidence bookkeeping**: C900's evidence text still says the member file is "currently under
   repair" and that its earlier δ bounds are "NOT accepted as interval certificates". That is now
   stale — the file has been repaired and independently audited at the frozen sha
   `dcffaf17…/22a78b34…` (see `CENTRAL-SCREEN-INDEPENDENT-AUDIT.md`); the C900 evidence pointer
   should be updated, while the conditional scope stays as registered.
4. **Residual (not bearing today)**: my checks of the MEC and strict-min test routines are sampled
   (12/12, 4/4); exact certification of those two small routines would be a separate obligation if a
   downstream result ever depends on their interval implementation rather than on the cited formulas.

**Repro**: `py -3 -B -X utf8 research-2026/team-current/r20-gluing/c900_independent_check.py`.
