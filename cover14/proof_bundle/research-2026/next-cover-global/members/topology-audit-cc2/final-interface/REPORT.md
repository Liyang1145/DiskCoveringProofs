# Final-interface REPORT (v2) — provenance of the C1366 necessary domain

Scope: members/topology-audit-cc2/final-interface/. Read-only inputs. No claims registered.
Second pass per lead's instructions: cut-set provenance from fully closed exteriors, hashes and
transport, analytic clip inspection. No synthetic brute force, no dual re-audit, no 703-file walk.

## 0. Job status (asked explicitly)

`dual_and_clip_check.py` was started in the background and **finished on its own** (no hang, no
kill needed); the process no longer exists. It is **withdrawn as validation** (its off-side
comparison enumerated the on-side polytope and then filtered; its certificate check ignored the
residual). The follow-up `final_chain_check.py` also completed normally. Nothing from either is
used as evidence below except the exact facts in §1 and §3.

## 1. C1366 halfspace angle-dual (C1371) — verified from the stored JSON only

`lead/q10-halfspace-angle-dual.json`: 20 certificates,
`status = exact_halfspace_dual_angle_box_no_vertices`, `domain_sha256` matches
`q10-c1366-domain.json`, and
* **all 20 certificates have every multiplier ≤ 0** (0 positive), as the algebra requires
  (`y ≤ 0`, `N x ≥ b` ⇒ `y·Nx ≤ y·b`);
* **22 of the 128 rows are used**: {2, 7, 104, 105, 107, 109–111, 113, 115–127} — no vertex list
  and no optimizer read enters the bound;
* **max |δ| = 0.00424485296877007 < 1/200 = 0.005**, exact rational
  54334118000256937627170388946814721898872443262184033361831219 / 12800000000000000000000000000000000000000000000000000000000000000.
So the final-width step **no longer rests on the 896-vertex list being complete**; it is an exact
halfspace/LP-dual representation. I did not re-derive the dual algebra beyond these structural
checks (per instruction).

## 2. Coefficient identity (wording correction accepted)

coeff_{j,i} = (9−i)/10 − 1_{i<j}. Verified exactly:
* row sum Σ_i coeff_{j,i} = **4.5 − j** for j = 0..9 (rows do NOT sum to 0);
* column sum Σ_j coeff_{j,i} = **0 for all ten columns**; total Σ = 0.
The sum-zero property used downstream is Σ_j δ_j = 0, which follows from the column identity
(and Σ_j(j−4.5)=0), not from a zero row sum. My earlier "zero-sum coeff" phrasing was ambiguous.

## 3. Cut-set provenance and transport

* C1366 declares **8 cuts**; C1365 had **4** ([0,1,2,3,4] ≥ 63/128, {2} ≤ 1/512,
  [5,6,7,8,9] ≥ 63/128, {7} ≤ 1/512). The 8 are exactly the 8 declared by the round-8 audit
  (`cuts_equal = true`); that audit file's bytes hash to C1366's `audit_sha256`.
* Base of round 8 is `q10-c1365-domain.json`: its file hash equals the config's `domain`,
  C1366's `source_sha256`, and the audit's `domain_sha256` (all three).
* Round-8 stored cases: 4. **Case 0 ([0],11/512,+1)** and **case 2 ([0,1],65/256,+1)** have
  `pending == []` (closed, 1 and 3 excluded leaves, 0 open). **Case 1 ([0],9/512,−1)** has
  pending [1,3] and 2 open cells; **case 3 ([0,1],63/256,−1)** has pending [5,6] and 2 open.
* **Transport**: `q10-fan-transport.json` is `finite_graphautomorphism_transport_checked`, 4 runs,
  `site_permutation` and `deficit_permutation` are bijections on 14 and 10 symbols (checked). Its
  `source_sha256` is **not** the C1365 hash, so it binds an earlier domain and is reused across
  rounds (it declares `strict_upper_half_cut_indices`).

### Correction: my earlier "six unverified cuts" claim was WRONG

I previously claimed the round-8 artifact could justify only two planes because
`q10_metric_mean_round_audit.py` emits a cut only when `pending` is empty. I misread the loop:
lines 28–30 run **per case**, and for each closed case they run over ALL transport automorphisms
and add the **transported** index sets:
    `if not pending: for g in autos: dg=...; cuts.add((sorted(dg[i] for i in ids), sense, t))`
So the two closed cases (case 0 with the 11/512 plane, case 2 with the 65/256 plane) emit
**four cuts each = 8**, which is exactly what the audit declares and C1366 integrates. The script
emits 8, not 2; no rotated case files are needed. I verified the closure arithmetic directly on
the transport data: the orbit of {0} under the four deficit permutations is {0},{4},{5},{9} and
the orbit of {0,1} is {0,1},{3,4},{5,6},{8,9} — taken together exactly the eight C1366 cuts,
with the two families both fully covered.

I also accept the transport inference as stated: every feasible full-graph system maps under the
automorphism to a feasible full-graph system, which lies in the prior (globally necessary)
domain; therefore the transported inequality is necessary on the current domain, and the current
domain need NOT be invariant under the automorphism for this to hold. My additional "the
transport binds an earlier domain" observation is not a defect for the same reason (the
`source_sha256` of the transport artifact is the original leaf/domain of the family it was built
from, which is what the inference uses).

I did not verify the 16-face/20-anchor automorphism preservation myself; the lead's
`q10_cut_transport_provenance.py/.json` does that for rounds 2..8 (exact four automorphisms of
the 16 faces and 10 owner pairs, owner-deficit map, source hashes, split-into-2-children, pending
and open agreement, leaf indices with lower > U, and exact transport-closure cut sets; closed-case
counts 5,3,3,2,3,2,2 with transported cut counts 16,10,10,6,12,4,8). I report that as the lead's
audit, not as my own replay.

For the record, both of the consequences I listed in my earlier draft are RETRACTED: (1) the
artifact does justify all eight planes, and (2) it IS the output of the stored script (the
per-case loop over automorphisms emits 8). The withdrawn draft text is not reproduced here.

## 4. Unchanged from the first pass (verified)

* Hash integrity: bridge ↔ minorant certificate ↔ C1366 domain all bind (bridge's declared
  `domain_sha256` equals the file's hash).
* All 896 stored vertices satisfy Σx=1, the stored equality and all 128 inequalities (exact
  Fractions, 0 violations), active rank 10 — internal consistency only (and now not needed for
  the width step).
* The local object is the literal 14-site / 16-face-witness / 10-anchor system; the
  production→literal map is the correspondence identifying catalogue index **879**
  (`candidate-catalogue-match.json`, exact isomorphisms only at 879, empty at 848/878).
* The 1.1e-7 quantity is an **angular** input to the C1355 cell; it is not a site-box coordinate
  and must not be compared with the 4e-5 / 2e-5 site boxes (correction accepted).

## 5. Analytic clip inspection (accepted, not re-derived)

The edge criterion (two vertices whose common active constraints have rank 9 span a
1-dimensional minimal face = an edge) is correct, including degeneracies; the inductive child
construction (old on-side vertices plus edge crossings) is complete for a bounded
full-dimensional parent; exact Gaussian elimination preserves earlier pivots. I inspected the
routine and the analytic statement; I did not line-audit the implementation, and my attempted
synthetic comparison was wrong (on-side-only enumeration) and is discarded.

## 6. Bottom line

The final-width step is independent of vertex-list completeness (C1371, §1: exact halfspace
LP-dual, 20 certificates, all multipliers ≤ 0, 22 rows, max |δ| = 0.00424485 < 1/200). The
cut-set provenance is closed: the round-8 loop emits the transported closure per closed case
(8 cuts from 2 closed cases × 4 automorphisms), the transport automorphisms are exact four
16-face/10-owner-pair automorphisms of the 879 graph, and transported necessary inequalities are
necessary on the current domain without requiring domain invariance. My earlier "six unverified
cuts" claim is retracted in full (§3). What I verified myself in this pass: the LP-dual
structural facts, the coefficient identity, the hash links round8-audit ↔ c1366 and
config/base ↔ c1365, the orbit arithmetic of the two cut families under the four deficit
permutations, and the polytope self-consistency. The lead's independent
`q10_cut_transport_provenance.py/.json` (rounds 2..8) is the automorphism/leaf evidence and is
cited as the lead's audit, not as my replay.

## 7. Evidence files (this directory)

`hashchain.json`, `provenance-check.json`, `final-chain-check.json`, `terminal-provenance.json`,
`polytope-check.json`, `transport-automorphism-check.json`; scripts `hashchain.py`,
`provenance_check.py`, `final_chain_check.py`, `terminal_provenance.py`, `polytope_check.py`,
`transport_automorphism_check.py`.

