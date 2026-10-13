# stress-cc2 — n14 sharp-candidate stress/KKT at the stationary root (final, corrected)

Scope `members/stress-cc2/` only. Old `members/stress/`, n11/n12 read-only. One candidate + one
calibration. No 1535 sweep, no 106-subnet sweep.

## 0. Result in one paragraph

The **fixed geometry interface is now correct** and self-consistent: expanding the Lead's
`root-scout.json` `z_c_r` strings with the Lead's own chain (`b = r+sqrt(r²−((s−z)/2)²)`, **not**
`r+sqrt(r²−z²)`) gives a 14-centre configuration that **covers the unit disk at exactly the declared
r\*=0.33173203427623412** with **14 tight + 2 slack** in-disk Voronoi vertices, **10 anchors** each of
degree 2, **20 tight anchor-site edges**, gap vector with **cap-active gaps {4,9}**, and **all 14 tight
faces acute**. On that geometry the capped-simplex KKT stress system is **feasible** (equilibrium at
the 14 sites, `g_k = c` on the 8 inactive gaps, `g_4,g_9 ≥ 0`, `α ≥ 0`, `Σα = 1`). The old
C1145 emptiness verdict used the **nonstationary coordinates and the wrong `b`**; it does not
transfer. Two honest limitations: (i) the provided `z_c_r` strings are **double precision** (72
characters, 17 significant digits), so KKT equalities at the 1e-17 level are not certified; (ii)
when the **witness force balance** is imposed (the 14 witnesses are fixed points with exactly 3
incident edges each — the old kernel never imposed it), **18 of the 42 witness-site edges are forced
to zero** in every feasible stress, leaving 44 positive-capable edges.

## 1. Fixed geometry interface

`py/interface.py` (pure geometry, no optimisation) → `logs/interface_run.txt`, `evidence/interface.json`.

| qty | value (digits printed) |
|---|---|
| r\* | 0.3317320342762341225578155488024095382709 |
| z | 0.3268180689499140633184051253300649312206 |
| c | 0.2919411189649396619446920604622870296816 |
| s=√(1−r²) | 0.9433736573781098691990022184533651928989 |
| a=(s+z)/2 | 0.6350958631640119662587036718917150620598 |
| b=r+√(r²−((s−z)/2)²) | 0.4542511926129566135529851059221879255690 |
| d=1−√(r²−c²) | 0.8424673823535344208160175653985370577514 |
| t=r+√(r²−z²) | 0.3886186967982857037751131529620840584040 |
| L\*=2asin r\* | 0.676277968287248374762985346957 (38.7478733605°) |

centres, ordered (+−a,+−b)×4, (+−c,+−d)×4, (+s,0),(−s,0),(+z,0),(−z,0),(0,−t),(0,+t)
(`evidence/interface.json/centers`); **ordered-centre sha256 (50-digit coords) =
`cf416bd6fb998b389a82d5253e20948549567a1ca043ddcd7b0efae79984b9b6`**.

**Covering radius of the closed unit disk = 0.33173203427623412256** (= declared r\*), attained at the
in-disk Voronoi vertices and at the boundary (270.0000000000°). Verified twice: over all 292 in-disk
circumcentres and over a 200 000-point boundary sweep (`logs/interface_run.txt`).

## 2. Structural data (independently recomputed)

* **10 anchors** (exact S^1 bisector solutions): 19.37393668027073, 51.774419687402606, 90.0,
  128.2255803125974, 160.62606331972927, 199.37393668027073, 231.7744196874026, 270.0,
  308.2255803125974, 340.62606331972927 deg; **each exactly degree 2** (no third centre within
  1e-14 of r\*).
* **20 tight anchor-site edges**; owners (cyclic)
  `[(0,8),(0,4),(4,5),(1,5),(1,9),(3,9),(3,7),(6,7),(2,6),(2,8)]`. Centres 10–13 have no anchor edge.
* **10 gaps**, sum 2π exactly: 32.4004830, 38.2255803, 38.2255803, 32.4004830, **38.74787336**,
  32.4004830, 38.2255803, 38.2255803, 32.4004830, **38.74787336** (deg). **cap-active = {4, 9}**
  (gap_k − L\* = −1.61477213672e-17 for both, i.e. they are the two largest gaps and cap-active to within the ~1e-17 noise of the provided root; every other gap is at least 9.1e-3 below L\*).
* **16 in-D Voronoi vertices = 14 tight + 2 slack**:
  * tight (circumradius = r\*, residual ≤ 6e-64): (0,4,13) (0,8,10) (0,10,13) (1,5,13) (1,9,11)
    (1,11,13) (2,6,12) (2,8,10) (2,10,12) (3,7,12) (3,9,11) (3,11,12) (10,11,12) (10,11,13);
  * slack: (4,5,13), (6,7,12), circumradius 0.32082085 (= r\* − 0.01091118), positive empty-circle
    margin 0.3636.
* witness-site edge lengths are r\* to **3.9e-62**; witness ≠ centroid of its face (off by 7.3e-2).
* **all 14 tight faces acute**, circumcentre interior — the "obtuse face" mechanism is **absent**;
  this confirms the Lead's `triangle-obtuse-audit.json` independently.
* Join with `lead/catalogue-audit.json`: **not a relabelling of this complex.** Of the Lead's 16
  triples, only 6 ((1,5,13),(1,11,13),(2,6,12),(2,10,12),(10,11,12),(10,11,13)) have circumradius r\*
  with a positive empty-circle margin under this centre array; the other 10 give R−r\* between +0.214
  and +0.838 and negative empty-circle margin (e.g. (0,4,12): R−r\*=+0.3139, margin −0.512;
  (4,6,12): centre outside D). No permutation of the 14 labels (searched: the 4!·4!·2·2 signed-block
  maps and all dihedral maps) carries my set onto the Lead's set. So the Lead's index order for the
  literal centres differs from the order used in `catalogue-audit.json`; the join must be done on
  **coordinates**, not on index triples (`logs/n14faces.txt`, `evidence/interface.json`).

## 3. Stress / KKT (bearing result)

Torque/gap interface (finite-difference verified, claim C1147): with d_e = unit edge direction from
the anchor outward and t_i = (−sin θ_i, cos θ_i),

    tau_i = + 2 Σ_{e at i} alpha_e (d_e · t_i)        (DOT product)
    g_k   = Σ_{i>k} tau_i ,  g_9 ≡ 0
    cap condition for Δ_k ≤ L\*:  g_4 ≥ 0, g_9 ≥ 0

Check: rotating all anchors together gives dE/dδ = 5.4e-18 vs Στ = −3.9e-18 (dot form) and −0.3600
(cross form, wrong). Old note's inequality sign was the opposite of this; the old kernel's torque
was this same form but evaluated on the nonstationary coordinates.

**Site-equilibrium-only system** (the old kernel's): 58 of 62 edges positive-capable, **4** forced
zeros (witness-site edges 24,33,42,51).

**Correct network = site equilibrium + witness balance** (witness k has exactly its 3 face edges;
`Σ alpha_e unit(centre−witness_k) = 0`, alpha ≥ 0; 36+28 equality rows):
* per-witness the nonnegative null vector of the 3 directions is **unique up to scale** and
  **strictly positive for only 4 of 14 witnesses** (0,10,13),(1,11,13),(2,10,12),(3,11,12) — the
  others admit only the zero weight (their 3 directions do not positively span the origin);
* LP: **18 of 42 witness-site edges forced to zero**, in every feasible stress — exactly the three
  edges of the faces (0,8,10), (1,9,11), (2,8,10), (3,9,11), (10,11,12), (10,11,13); **0 of the 20
  anchor-site edges forced to zero**; 44 edges positive-capable.

**KKT LP at the stationary coordinate** (equilibrium at the 14 sites; no witness balance):
**FEASIBLE**. Witness point: 28 nonzero edges, high-precision residuals max|site equilibrium| =
2.0e-17, Στ = 2.2e-17, g_4 = 1.7e-17, g_9 = 0. Both cap multipliers are 0 (weakly active cap).

**Linear definition of the stress set for any certificate on this network:**
unknowns `alpha ∈ R^62`, `c ∈ R`; constraints

    (i)  A alpha = 0        (28 rows) equilibrium at the 14 sites
    (ii) B alpha = 0        (28 rows) equilibrium at the 14 witnesses   [missing in the old run]
    (iii) (G_k alpha) − c = 0, k ∈ {0,1,2,3,5,6,7,8}
    (iv) G_4 alpha ≥ 0, G_9 alpha ≥ 0
    (v)  alpha ≥ 0;      normalisation Σ_e alpha_e = 1  (the system is homogeneous in (alpha,c)).

Recomputed per-site residuals at the winning solution's coordinates are in `logs/n14v2.txt`.

## 4. Root precision — the interface gap that blocks an exact certificate

`lead/root-scout.json`'s `z_c_r` strings are 72 characters but **double precision** (exact decimal
expansion of binary doubles, e.g. z ends `…68905890625`). Consequences:
* the expanded configuration is an excellent diagnostic object (covering radius reproduces r\* at
  1e-17 and all structure of §2 closes);
* the cap-active set {4,9} and every KKT equality whose residual is ~1e-17 are **not certified**;
  "Δ_k = L\* exactly" cannot be asserted at this precision.
* Requested from Lead: the root box, or the root strings printed from the 70-digit `findroot` state
  without a float64 round trip. `lead/improved-upper-test.json` gives exact rational centres for an
  *upper bound* object, not for the stationary root.

## 5. Calibration

`py/calib.py` (my kernel and the old `stress_core.py` on the n12 proven candidate): normalised min
weight **0.011659921920** (published 0.01165992192009); my max uniform edge weight over the n12
nonneg equilibrium set = **0.016097** (the published 0.01166 stress is interior); old kernel's
Schur/M numbers reproduced (`logs/calib.txt`). Edge lists identical; `max|A alpha_old| = 1.0e-17`.

## 6. Files

Geometry/interface: `py/geom.py`, `py/interface.py` (+`logs/interface_run.txt`).
Stress/KKT: `py/stress2.py`, `py/final_check.py` (+`logs/final_check.txt`), `py/n14v2.py`
(+`logs/n14v2.txt`), `py/witness_balance.py`; calibration `py/calib.py`.
Superseded (kept, marked, not to be used): `step3/step4_cover*.py` (wrong-b geometry), `n14final.py`
(float64 inputs + 1e-50 tightness filter → spurious "4 anchor edges"), `n14kkt*.py`, `n14cone.py`,
`n14hess*.py`, `n14curv.py` (sign/parameterisation errors).

