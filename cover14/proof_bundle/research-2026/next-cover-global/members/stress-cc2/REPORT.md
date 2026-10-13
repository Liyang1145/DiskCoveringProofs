# stress-cc2 — round 2: error retraction + the corrected, shared representation

Supersedes round 1 (`REPORT-round1-superseded.md`). Scope `members/stress-cc2/` only.
All incorrect claims are retracted (C1153, C1154, C1155, C1157). The corrected six-face support fact is
now carried by C1166, whose mechanism is analytic and belongs to the Lead
(`lead/STRESS-SUPPORT-ANALYTIC.md`); my part is independent numeric confirmation plus the two controls
the Lead asked for. No new LP was run beyond the single sign control.

## 0. Retractions and root causes

| claim | verdict | root cause | evidence |
|---|---|---|---|
| C1157 "input is only double precision" | **retracted** | my own print line `interface.py:28` did `%.60g % float(z)`, converting the full-precision mpf to a binary double for display. The parsed strings have 72 digits (z tail `...445044701312`, r tail `...283469118412`), and `mpf(z)` at 80 dps = 0.326818068949914063318405125330064931220648062761624763290945. | `logs/audit_fix2.txt` §1 |
| C1155 "the Lead's audit is not a relabelling" | **retracted** | (a) compared my 14 tight triples against the Lead's 16 (category error); (b) compared by index while the Lead's triples are keyed to `n14-actual-vertices-numeric.json`, which holds the **old `hprec_sol_refined` coordinates** (diff 3.2e-10…1.4e-9) in a different order. | `logs/join.txt`, `logs/witness_pos.txt` |
| C1154 "18 witness-site edges forced to zero (from witness balance)" | **retracted** | wrong reason: sign slip reading an SVD null vector (defined only up to sign) plus an unnormalised determinant in my own barycentric helper. Right fact, wrong mechanism. | `logs/audit_fix2.txt` §2, `logs/witness_pos.txt` |
| C1153 "KKT feasible with g_k ≥ 0" | **retracted** | opposite inequality direction; the cap condition is `g_k ≤ c`. | `logs/kkt_sign.txt` |
| (round 1) covering radius 0.3699 / 2 tight vertices | superseded | expansion used `b = r+sqrt(r²−z²)`; correct is `b = r+sqrt(r²−((s−z)/2)²)`. | `logs/step7_fg.txt` |

## 1. Fixed geometry interface (unchanged, verified)

`py/interface.py` on `mpf` of the raw strings: r\* = 0.3317320342762341225578155488024095382709,
a = 0.6350958631640119662587036718917150620598, b = 0.4542511926129566135529851059221879255690,
c = 0.2919411189649396619446920604622870296816, d = 0.8424673823535344208160175653985370577514,
s = 0.9433736573781098691990022184533651928989, t = 0.3886186967982857037751131529620840584040,
L\* = 0.676277968287248374762985346957. Covering radius of D = **0.33173203427623412256** = r\*
(292 in-disk circumcentres + 200k boundary sweep). Ordered-centre sha256(50 digits) =
`cf416bd6fb998b389a82d5253e20948549567a1ca043ddcd7b0efae79984b9b6`. 16 in-disk vertices =
**14 tight + 2 slack** ((4,5,13), (6,7,12), radius 0.32082085); **10 anchors each degree 2 → 20 tight
anchor-site edges**; gaps sum 2π, cap-active **{4,9}**; **all 14 tight faces acute**.

## 2. Coordinate join (Lead was right)

Permutation my centres → `lead/n14-actual-vertices-numeric.json`, matched by coordinates:

    [0, 2, 1, 3, 6, 4, 7, 5, 9, 8, 10, 11, 12, 13]      (pair distances 3.2e-10 … 1.4e-9)

Re-keying the Lead's 14 `tight` triples through it gives **exactly** my 14 tight triples:
(0,4,13) (0,8,10) (0,10,13) (1,5,13) (1,9,11) (1,11,13) (2,6,12) (2,8,10) (2,10,12) (3,7,12)
(3,9,11) (3,11,12) (10,11,12) (10,11,13). The two complexes agree under the coordinate join.

## 3. Control 1 — witness balance is strictly positive (no local obstruction)

Sign-free test (angular gaps of the three unit directions all < π; min slack 19.75°), equivalent to
the Lead's barycentric form (all β strictly positive, min 0.14638). Exact cross-product null vectors,
residual ≤ 4e-62:

    witness  0 (0,4,13)   : (0.38703883, 0.21398505, 0.39897612)
    witness  1 (0,8,10)   : (0.26971676, 0.36514162, 0.36514162)
    witness  2 (0,10,13)  : (0.40414530, 0.21463642, 0.38121828)
    witness 12 (10,11,12) : (0.42680915, 0.42680915, 0.14638169)

So the witness balance forces nothing; the six zero faces are a **global** site+KKT effect
(Lead's `STRESS-SUPPORT-ANALYTIC.md`: at X=(s,0) the anchor has no horizontal force while its two
face witnesses sit at x = a < s, forcing those sites to zero anchor weight; at Z=(z,0) the outer
witness at (z,r) has no horizontal force and the central witness at x = 0 then forces the central two
faces to zero). Independent numeric confirmation of the resulting support:
`logs/kkt_sign.txt` (correct sign) → 4 forced-zero witness edges 24,33,42,51 among the singles tested
there; the full 6-face/18-edge count is the Lead's `stress_barycentric`/`stress-schur-probe` result.

## 4. Control 2 — KKT sign and r factor

Functional `E(θ) = Σ_e w_e |e(θ)|²`, `w_e = r α_e`, α normalised, so `E(θ*) = r²`.

* `d|e|²/dθ_i = 2|e| (d_e · t_i)` with `d_e` the unit vector from the anchor outward and
  `t_i = (−sin θ_i, cos θ_i)`, hence the anchor coefficient is `2 w_e |e| (d_e·t_i) = 2 r² α_e (d_e·t_i)`
  at `|e| = r`: **r² with normalised α** (equivalently 2r with weight-per-length stress).
  Finite-difference control, uniform `w_e = r/ne`: anchor 4 0.0111209836785 vs formula 0.0111209836785;
  anchor 9 0.0175601827743 vs 0.0175601827743.
* `g_k = Σ_{i>k} tau_i = ∂E/∂Δ_k`. Lagrangian with `Δ_k ≤ L*` gives `g_k = λ + μ_k`, `μ_k ≥ 0`, i.e.
  **`g_k ≤ c = λ`** at cap-active gaps — the Lead's theorem.
* Sign control (one LP pair, `logs/kkt_sign.txt`): with `g_k ≤ c` the system is feasible and the
  multipliers `c − g_k` are **≥ 0** (witness point: c = 0, g_4 = −0.9434, g_9 = 0 → μ = 0.9434, 0);
  with my round-1 sign `g_k ≥ c` the only difference is the sign of the multipliers
  (`c − g_k = −8.71e-03 < 0`), i.e. **not a KKT point**. Both multipliers can be non-zero on other
  solutions (Lead: symmetric solution gives μ ≈ (0.0206855, 0.0206855)).

## 5. Status

`THIS` stress is numerically non-convex; that is not a disproof for all stresses, nor for the covering
optimum (Lead's `stress-schur-probe.json`, `stress-curvature-control.json`). What is established here:
the fixed geometry interface, the coordinate join, the strictly-positive witness balances, and the
correct KKT sign + r factor. Open for this route: whether the reduced (44-edge, six zero faces)
network can carry a sharp certificate at the true optimum.

## 6. Files

Authoritative: `py/geom.py`, `py/interface.py` (`logs/interface_run.txt`), `py/join.py` (`logs/join.txt`),
`py/witness_pos.py` (`logs/witness_pos.txt`), `py/audit_fix2.py` (`logs/audit_fix2.txt`),
`py/kkt_sign.py` (`logs/kkt_sign.txt`), `py/calib.py` (`logs/calib.txt`).
Superseded/wrong (kept for the trail): `py/n14v2.py` (KKT line signed wrongly), `py/n14final.py`,
`py/witness_balance.py`, `py/final_check.py` (SVD sign reading), `py/step3/4/5/6*.py` (wrong b),
`py/n14kkt*.py`, `py/n14cone.py`, `py/n14hess*.py`, `py/n14curv.py`.
