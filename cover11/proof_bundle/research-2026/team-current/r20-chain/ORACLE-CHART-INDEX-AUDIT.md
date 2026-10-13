# ORACLE-CHART-INDEX-AUDIT — canonical51 graph vs the C919/C920 raw8 local chart

Scope: index/graph bookkeeping only (no re-audit of any closed cell proof, no new claim).
Evidence: `tools/oracle_support_audit.py`, `tools/oracle_index_audit.py`
→ `out/oracle_support_audit.txt`, `out/oracle_index_audit.txt`.
Sources read: `lead/FIXED-SWITCH-SOC-REDUCTION.md`, `lead/FULL-P-ORACLE-THEOREM.md`,
`lead/cosine_dbm_pilot.py` (root_angles, known_patch), `lead/interval_network_envelope.py`,
`lead/certify_canonical_local_patch.py` + `canonical_local_patch_certificate.json`,
`lead/certify_cosine_polytope.py`, `lead/cosine_envelope_lp_diagnostic.py`,
`r20-alternative/fixed_oracle_force_proposal.py`, `lead/ADAPTIVE-STRESS-FINITE-REMAINDER.md`,
`lead/NETWORK-KERNEL-LEAD-AUDIT.md`.

## 1. Verdict

The two objects are the **same fixed-angle oracle at the same exact C891 root**, written in
two different ring labellings; the transport is the ring-label shift `s ↦ (s−2) mod 9`, a
bijection of `{0..8}` (it is not an involution — its square is `s ↦ s−4` — the property that
matters is that it permutes the nine ring labels and fixes the two hub labels).
Every as-built cross-reference matches; the index-shift formula in `known_patch` and the
rotation pin in `root_angles` reproduce the canonical angles interval-exactly.

## 2. Graph comparison (as built)

| object | faces | site-site edges | anchor-tie edges | face-aux edges | free nodes | nodes |
|---|---|---|---|---|---|---|
| canonical51 oracle | 11 | 21 | 18 | 33 | 22 | 31 |
| raw carrier (C909/C912) | 9 | 19 | 18 | 27 | 20 | 29 |

As-built `rawF` in `interval_network_envelope.py:21` (and `certify_canonical_local_patch.py:21`)
is, in literal form,
`[[2,9,10],[6,9,10],[1,2,10],[2,3,9],[3,4,9],[4,5,9],[5,6,9],[6,7,10],[8,0,10]]`.
While its *literal* form differs from the published canonical face list, the read-off
convention is `shift(s) = (s−2) mod 9` for `s<9`, hubs unchanged. Under that shift every raw
face lands in the canonical list: `(2,9,10)→(0,9,10)`, `(6,9,10)→(4,9,10)`,
`(8,0,10)→(0,8,10)`, `(1,2,10)→(0,1,9)`, `(2,3,9)→(1,2,9)`, `(3,4,9)→(2,3,9)`,
`(4,5,9)→(3,4,9)`, `(5,6,9)→(4,5,10)`, `(6,7,10)→(6,7,10)`. **All 9 land in the canonical
list** (set membership verified). So: *no hub label is swapped*; the literal difference is a
ring-index convention, not a hub-index error.

Canonical faces with **no** raw counterpart: `(5,6,10)` and `(7,8,10)`. Face-incidence counts
show the effect: raw nodes 5,6,7,8 drop from 2 to 1 incident faces and node 10 from 7 to 5;
node 9 stays 6/6, nodes 0 and 4 stay 3/3, node 10's central faces stay.

## 3. The six zero-weight slack edges

The six zero-weight edges are exactly the **face-cone edges of the two missing faces**
(`(5,6,10)`, `(7,8,10)`), i.e. 2 auxiliaries × 3 edges. Their two auxiliary nodes are
"absent, not silently pinned" (`NETWORK-KERNEL-LEAD-AUDIT.md`, §Object). Accounting:

    51 − 45 = 6 edge slots = 3 per missing face × 2 faces
    22 − 20 = 2 free nodes  = the 2 auxiliary nodes of those faces
    31 − 29 = 2 nodes

Both differences are therefore the **same** pair of faces, and the numbers are consistent.
The stored weight fields (`energy_library.json`, `cosine_dbm_local92x.json`) contain **no
zero entry at all** (45/371 fields, minimum weight > 0, all nine anchors carry positive
support load): the fields are stored on the 45-edge carrier where the six slack slots do not
exist, which is the same statement.

## 4. The eight-angle chart: rotation pin and index formula

Recomputed from the exact dyadic C891 box (`repaired_tc_krawczyk.json`), 9 raw tie angles
`raw[0..8]` with `raw[k] = θ_k + a_k` (θ = ring centre azimuth, a = ring half-arc):

    raw  = [5.039855334, 5.721541464, 0.000000000, 0.766024043, 1.542466838,
            2.308490881, 2.870134724, 3.551820854, 4.295838094]   (rad, increasing)

The raw chart is the ring-centre chart **pinned to `raw[2]`**; the canonical chart is the
same chart with the azimuth origin rotated to `raw[2]`:

    can[0] = 0
    can[i] = raw[(i+2) mod 9] − raw[2]            (i = 1..6)
    can[7] = raw[0] − raw[2] + 2π
    can[8] = raw[1] − raw[2] + 2π

Verified: `can[i] − (raw[(i+2)%9] − raw[2]) = 0.0` for i = 1..6 (to 1e-14);
`can[7] = 5.039855334`, `can[8] = 5.721541464`; `can[6] = 4.295838094 = raw[8] − raw[2]`.
So **raw index 8 lands at canonical index 6** exactly as the lead stated, and the rotation
offset is the azimuth `raw[2]` of the raw site labelled 2. Consequences checked:

* `can` is strictly increasing (rotation pinned at a real site, no wrap double-count);
* the nine canonical widths are `y_i = (L − w_i)/D` with
  `w = [0.766024, 0.776443, 0.766024, 0.561644, 0.681686, 0.744017, 0.744017, 0.681686, 0.561644]`,
  `Σw = 2π`, every `w ∈ (0, L]` with `L = 2asin(19/50) = 0.779593` — so `y ≥ 0`, `Σy = 1`;
* the canonical angles are therefore `θ_i = iL − D Σ_{j<i} y_j` **with the same pin**
  `θ_0 = 0` — i.e. the raw chart's `(p_i − p_2) mod 2π` *is* the canonical simplex point.

The alignment also makes the two independent computations of the local coordinate `h_k`
agree: `certify_canonical_local_patch.py` (canonical route)
`h_k = δ_can[(k−2) mod 9] − δ_can[6]`, `k = 0..7`, and `cosine_dbm_pilot.known_patch`
(raw route, `i = (k−2) mod 9`) `h_k = (i−6)L − D·tt − (roots[i] − roots[6])` are related by
the exact identity `roots[i] − roots[6] − (δ_can[i] − δ_can[6]) = (i−6)L − D·(t_i − t_6)`
with `t_i − t_6 = Σ_{j<i} y_j − Σ_{j<6} y_j`; it holds identically at the root. Both routes
therefore evaluate the SAME function on the SAME angled tuple, in the same 8 coordinates
`{θ_i − θ_2 mod 2π : i ≠ 2}` (the 9th entry `θ_2 = 0` is pinned, and one further degree is
absorbed by `Σy = 1`). Both routes also compute all nine `h`-slots internally: the direct
loop runs `k = 0..7` while the reflected loop runs `k = 0..7` with `i = (k−2) mod 9`, and the
remaining canonical label is the pinned one. The reflection `ρ(y)_j = y_{2−j}` used by the
reflected branches is the canonical relabelling `y ↦ y((2−j) mod 9)` (circular, not
`j ↦ 2−j` on `0..8`), verified by `subset_bounds` reducing every cyclic block to either
`[-db[b][a], db[a][b]]` on a block or `[1−db[a][b], 1+db[b][a]]` on the complement.

## 5. Hub orientation

The as-built code's canonical literal says "label 9 = hub B (saved raw centre 2); label 10 =
hub A (raw 0)" (`fixed_oracle_force_proposal.py`), while the Python model builds
`(z[4],0)` as site 9 and `(z[5],0)` as site 10 with `z[4]=ρ(root 4)=0.1495`, `z[5]=ρ(root 5)=
0.2730`. The two literature statements are therefore in a *name* convention of the two hub
places; the *geometry* is unambiguous: the hub at |h| = 0.1495 forms the 4-edge fan, the hub
at |h| = 0.2730 forms the 5-edge fan. Both `interval_network_envelope.F` and the canonical
face list put the 4-edge fan on the hub labelled 9 and the 5-edge fan on the hub labelled 10.
**This is a naming convention, not an index error**, and it does not affect any weight,
angle, or oracle value.

## 6. Reflection map — VERIFIED CORRECT; my earlier flag is RETRACTED

**Retraction.** An earlier version of this section claimed an off-by-one index slip in the
reflection transport of `cosine_dbm_pilot.py:39` / `ORACLE-REFLECTION.md`, and also claimed
"`y = rho(y)` at this root with `y_1 = y_8`". **Both statements are wrong.** The lead caught
the first; the second is refuted by the data itself (`y_1 = 0.0042962643`,
`y_8 = 0.2972779593`). Corrected verification (`tools/reflection_recheck.py`,
`out/reflection_recheck.txt`), all at the exact root:

* **Gap identity:** `theta_{i+1} - theta_i = L - D*y_i`, so `y_i` owns the anchor gap
  `U_i` (anchor `i -> i+1`). Residuals <= 6.7e-16 over `i = 0..7`.
* **Anchor map:** `a(i) = (3-i) mod 9` is correct (anchor `U_i` touches sites `i, i+1`, and
  `p(i) = (4-i) mod 9` on sites satisfies `p(i) in {a(i), a(i+1)}`).
* **Transport:** with `theta'_i = theta_3 - theta_{(3-i) mod 9}` (unwrapped into `[0,2pi)`),
  the reflected coordinates satisfy `theta'_0 = 0` and
  `theta'_{i+1} - theta'_i = L - D*y_{(2-i) mod 9}`, i.e. **`y'_i = y_{(2-i) mod 9}` — the
  original source is RIGHT** (residuals <= 7e-16). The axis is the line through anchor 3
  (angle `theta_3`); there is no half-integer axis.
* My earlier alternative `theta'_i = theta_1 + theta_2 - theta_{(3-i) mod 9}` differs from the
  correct formula by up to `0.2044` rad at `i = 7` and is not even a chart formula (its
  `theta'_0` is not 0). It is discarded.
* **Cyclic convention:** with `rho(y)_i = y_{(2-i) mod 9}`, the claim `y_1 = y_8` / `y_2 = y_7`
  is FALSE; the actual coincidences are `y_1 = y_3` and `y_2 = y_4 = y_6`, while
  `y_i = y_{(2-i) mod 9}` holds for every `i` at this root (max deviation 0.0 over the two
  independent runs of the check). So the candidate's width vector is invariant under this
  reflection, which is a genuine observation about the candidate.
* **Self-consistency / why it is a true symmetry:** the site map `p(i) = (4-i) mod 9`, the
  anchor map `a(i) = (3-i) mod 9` and the incidence relation `p(i) in {a(i), a(i+1)}` all
  hold (checked for all nine `i`), so `V(y^R) = V(y)` exactly as `ORACLE-REFLECTION.md`
  states, and `y^R = y` at this particular root. No defect, no off-by-one.

**Residual naming point (cosmetic, no action required):** `ORACLE-REFLECTION.md` writes the
axis as "the line of angle `theta_3/2`". The composition derivation there is right; with the
chart pin `theta'_0 = 0` imposed, the composed rotation realised by `theta'_i = theta_3 -
theta_{3-i}` is by `theta_3`. This is a wording matter only.

No code in `lead/` was modified; this section is documentation only.

## 7. Residual interfaces (honest gaps)

1. The six zero-weight edges are **not stored as zeros** anywhere. The count
   `51 = 45 + 6` and the absence of the two auxiliaries are verified from the graph and from
   `NETWORK-KERNEL-LEAD-AUDIT.md`; their *positional identity* (which six slots) is inferred
   from the two missing faces, not read off a stored weight vector. If a downstream reasoner
   needs the exact six slot indices, they are the face-cone slots of faces `(5,6,10)` and
   `(7,8,10)` in the canonical literal order used by `fixed_oracle_force_proposal.FORCE_ORDER`.
   (One structural cross-check supports the identification: the raw carrier's four
   single-incidence sites are exactly `5, 6, 7, 8`, i.e. the two sites of each missing face
   other than the hub — so the missing faces are forced to be the two hub-10 faces whose both
   sites lie in that run.)
2. The raw chart's 8 degrees of freedom are a *chart* on `P` pinned at `raw[2]`, and the
   canonical chart is the same `P` in the rotated gauge; this file verifies the transport but
   does not re-certify the covering of `P` by the DBM leaves (that is `FULL-P-ORACLE-THEOREM.md`).
3. `canonical_local_patch_certificate.json` states its containment is conditional on the
   adaptive-ball lemma/constants; nothing here changes that status.
4. The reflection transport flagged in an earlier version of §6 is CORRECT (now verified);
   the flag is retracted. Nothing about the reflected branch is left open here.

No claim is registered; this is a documentation/index audit with the evidence logs
`out/oracle_support_audit.txt`, `out/oracle_index_audit.txt`, `out/oracle_reflection_check.txt`.
