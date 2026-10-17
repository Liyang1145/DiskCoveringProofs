/-
n11-formalization — DSH line C4, hub-leg skeleton (teammate `topo-interior`).

# DSHTopologyInteriorHubLeg — the single missing implication, reduced and typed

Scope: **local groundwork, standalone, CONDITIONAL**. This file states and reduces the one
implication the whole C4/C5 surface is missing:

> from an arbitrary `Covers c r` (the canonical labeling with the nine circle-meeting disks at
> sites `0..8`) produce, for each canonical face, a *common `r`-point* of its three sites — in
> particular for the two hub-10 fan faces `5 = [5,6,10]` and `7 = [7,8,10]`.

Nothing here proves `Covers → Feasible` (C5 is lead-side), and nothing here is unconditional:
the geometric existence content is carried by **typed, named premises** with no silent assumption.

## The reduction (this is the file's actual content)

The reduction uses the project's *nearest-site* witness route (the same route as
`FlashCoverReductionBridge.feasible_of_witness`, whose hypotheses are `hwitness` in `D` plus
"the associated sites are nearest"):

```text
VoronoiFace c f  :=  ∃ z, ‖z‖ ≤ 1 ∧ ∀ i v, dist z (c (face f v)) ≤ dist z (c i)
Covers c r       ⟹  (coverer of z)  ⟹  dist z (c ·) ≤ r  for every site that is weakly nearest
```

so `VoronoiFace c f ∧ Covers c r ⇒ FaceWitness c f r`. Both steps are kernel-proved here; the
only premise is the existence of the point `z` (the refined-dual/Voronoi vertex), which is
exactly the C3 "two-fan realization" content and is **not** proved.

## Consequences proved in this file

* `faceWitness_of_voronoiFace`, `hub10FanRealized_of_voronoiFace` — premise ⇒ C4's exact
  `FaceWitness` / `Hub10FanRealized` shapes;
* `feasible_of_source_block_and_two_voronoiFaces` — with C4's frozen interface: `0 ≤ r`, the 18
  boundary rows, the 9 source-block face witnesses, and **only the two** hub-10 fan Voronoi
  vertices produce `∃ Z, Feasible U C Z r` (and hence `V2 U ≤ r²`). So the entire remaining
  topology is two named existence statements — the six non-source rows' payment is nothing else;
* C1-side derived facts (`NineDisks`, `RingLabels` ⇒ every disk covering the origin is a hub;
  the inner ball `‖x‖ < 1 - 2r` is covered only by hubs; ring centres have norm `≥ 1 - r`);
* controls: the nearest-site premise is *not* sufficient without `Covers`
  (`nearestTriple_alone_insufficient`), and the common-`r`-point conclusion is *not* vacuous
  (`hub10_fan_common_point_can_fail`).

No `sorry`, no custom axiom, no `native_decide`, no heartbeat bump. **Status: written during the
lead's serial-lock hold, so it is NOT yet gated; it must not be cited as evidence until a green
gate log exists.**
-/
import N11Formalization.DSHTopologyInteriorInterface
import N11Formalization.DSHTopologyInteriorWitness
import N11Formalization.Assembly.BoundaryCount

set_option autoImplicit false

namespace N11Formalization.DSHTopologyInterior

open N11Formalization ResumeNetwork ResumeLocalIncidence

/-! ## 1. The two typed premises from the C1 lane

`DSHTopologyInteriorWitnessLanes` (unverified draft) declares a predicate `NineBoundary` with the
same body as `NineDisks` below; this file is intended as the *verified* home for the hub-leg
premises, so a later consolidation should delete the draft copy rather than keep two names.
The C1 lane's producer is `Assembly/BoundaryCount.card_boundaryIdx_eq_nine_or_ten`, and
`DSHTenBoundaryData.card_boundaryIdx_eq_nine_of_obligation_lt_sourceRadius` already derives the
`card = 9` form from the single `C450PerDiskObligation` premise. -/

/-- **C1 lane output**: exactly nine disks meet `S¹`. -/
def NineDisks (c : Fin 11 → Point) (r : ℝ) : Prop :=
  Fintype.card (BoundaryIdx c r) = 9

/-- **Canonical labeling**: the circle-meeting disks are exactly sites `0..8`. For an arbitrary
cover the two non-meeting disks must be *relabeled* to the frozen hub slots `9, 10`; that
relabeling is part of the C1/C5 plumbing and is therefore a typed premise here, not an
assumption. (`DSHTenBoundaryData`/`DSHTopologyOwnershipLedger` give the nine-disk side; the
labeling itself is the interface with the frozen `ResumeNetwork.face` table.) -/
def RingLabels (c : Fin 11 → Point) (r : ℝ) : Prop :=
  ∀ i : Fin 11, MeetsCircle c r i ↔ (i : ℕ) < 9

/-- A ring site meets the circle (from the labeling). -/
theorem RingLabels.ring_meets {c : Fin 11 → Point} {r : ℝ} (h : RingLabels c r) {i : Fin 11}
    (hi : (i : ℕ) < 9) : MeetsCircle c r i :=
  (h i).2 hi

/-- A hub site does not meet the circle (from the labeling). -/
theorem RingLabels.hub_not_meets {c : Fin 11 → Point} {r : ℝ} (h : RingLabels c r) {i : Fin 11}
    (hi : 9 ≤ (i : ℕ)) : ¬ MeetsCircle c r i := by
  intro hm
  have hlt : (i : ℕ) < 9 := (h i).1 hm
  omega

/-- **Every disk covering the origin is a hub** (for `r < 1/2`). This is the "hub cells cover the
inner region" statement in its first, cheapest form: a disk that covers the origin has centre
norm `≤ r`, while a circle-meeting disk has centre norm `≥ 1 - r`. -/
theorem hub_of_covers_origin {c : Fin 11 → Point} {r : ℝ} (hR : RingLabels c r) (hr : r < 1 / 2)
    {j : Fin 11} (hj : dist (0 : Point) (c j) ≤ r) : 9 ≤ (j : ℕ) := by
  by_contra h
  have hj9 : (j : ℕ) < 9 := by omega
  have hm : MeetsCircle c r j := hR.ring_meets hj9
  have hnorm : 1 - r ≤ ‖c j‖ := one_sub_le_norm_of_meetsCircle hm
  have hd : ‖c j‖ ≤ r := by
    have h : dist (0 : Point) (c j) = ‖c j‖ := dist_zero_left (c j)
    rw [h] at hj
    exact hj
  linarith

/-- The origin's coverer is a hub, with the hub's centre inside the radius-`r` ball. -/
theorem exists_hub_covering_origin {c : Fin 11 → Point} {r : ℝ} (hc : Covers c r)
    (hR : RingLabels c r) (hr : r < 1 / 2) :
    ∃ j : Fin 11, 9 ≤ (j : ℕ) ∧ ‖c j‖ ≤ r := by
  obtain ⟨j, hj⟩ := hc 0 zero_mem_unitDisk
  refine ⟨j, hub_of_covers_origin hR hr hj, ?_⟩
  have h : dist (0 : Point) (c j) = ‖c j‖ := dist_zero_left (c j)
  rw [h] at hj
  exact hj

/-- **The inner ball is covered only by hubs**: for `‖x‖ < 1 - 2r`, every coverer of `x` is a hub.
This verifies the assembly's "`U := B(0, 1-2r)` meets no ring disk" step in the frozen language;
it needs only the labeling and the boundary-centre norm bound. -/
theorem hub_coverer_of_inner_point {c : Fin 11 → Point} {r : ℝ} (hc : Covers c r)
    (hR : RingLabels c r) (hr0 : 0 ≤ r) {x : Point} (hx : ‖x‖ < 1 - 2 * r) :
    ∃ j : Fin 11, 9 ≤ (j : ℕ) ∧ dist x (c j) ≤ r := by
  have hx1 : ‖x‖ ≤ 1 := by linarith
  obtain ⟨j, hj⟩ := hc x (mem_unitDisk.mpr hx1)
  refine ⟨j, ?_, hj⟩
  by_contra h
  have hj9 : (j : ℕ) < 9 := by omega
  have hm : MeetsCircle c r j := hR.ring_meets hj9
  have hnorm : 1 - r ≤ ‖c j‖ := one_sub_le_norm_of_meetsCircle hm
  have hle : ‖c j‖ - ‖x‖ ≤ dist x (c j) := by
    rw [dist_eq_norm]
    have h1 := abs_norm_sub_norm_le x (c j)
    have h2 : -(‖x‖ - ‖c j‖) ≤ |‖x‖ - ‖c j‖| := neg_le_abs _
    linarith
  linarith

/-- Ring centres are at least `1 - r` from the origin (from the labeling). -/
theorem ring_norm_ge {c : Fin 11 → Point} {r : ℝ} (hR : RingLabels c r) {i : Fin 11}
    (hi : (i : ℕ) < 9) : 1 - r ≤ ‖c i‖ :=
  one_sub_le_norm_of_meetsCircle (hR.ring_meets hi)

/-! ## 2. The Voronoi-triple premise, and the kernel deduction to C4's `FaceWitness` -/

/-- **Typed premise (C3 point-existence half).** A point of the *closed* unit disk whose three
face sites are weakly nearest among all eleven sites. This is the refined-dual ("primal Voronoi
vertex") content; it is not derived here. -/
def IsNearestTriple (c : Fin 11 → Point) (f : Fin 11) (z : Point) : Prop :=
  ‖z‖ ≤ 1 ∧ ∀ i : Fin 11, ∀ v : Fin 3, dist z (c (face f v)) ≤ dist z (c i)

/-- The premise in existence form: canonical face `f` has a Voronoi vertex. -/
def VoronoiFace (c : Fin 11 → Point) (f : Fin 11) : Prop :=
  ∃ z : Point, IsNearestTriple c f z

/-- At a nearest triple the three face distances are equal: the point is equidistant from the
three sites (the Voronoi-vertex condition, in weak form). -/
theorem isNearestTriple_dists_eq {c : Fin 11 → Point} {f : Fin 11} {z : Point}
    (h : IsNearestTriple c f z) (v v' : Fin 3) :
    dist z (c (face f v)) = dist z (c (face f v')) :=
  le_antisymm (h.2 (face f v') v) (h.2 (face f v) v')

/-- **The kernel deduction (this is the reduction's second, fully proved step).** A covered
nearest triple pays the whole face row: the coverer at `z` has distance `≤ r`, and every face
site is weakly nearer than it, hence `≤ r` too. -/
theorem faceWitness_of_voronoiFace {c : Fin 11 → Point} {r : ℝ} (hc : Covers c r) {f : Fin 11}
    (h : VoronoiFace c f) : FaceWitness c f r := by
  obtain ⟨z, hz, hmin⟩ := h
  obtain ⟨j, hj⟩ := hc z (mem_unitDisk.mpr hz)
  exact ⟨z, fun v => by
    simpa [dist_comm] using le_trans (hmin j v) hj⟩

/-- One Voronoi vertex per canonical face pays all 33 interior rows' witnesses. -/
theorem faceWitnesses_of_voronoiFaces {c : Fin 11 → Point} {r : ℝ} (hc : Covers c r)
    (h : ∀ f : Fin 11, VoronoiFace c f) : ∀ f : Fin 11, FaceWitness c f r :=
  fun f => faceWitness_of_voronoiFace hc (h f)

/-! ## 3. The two hub-10 fan faces, in C4's exact premise/conclusion shapes -/

/-- `FaceWitness c 5 r` gives the three-site common point for the fan triple `{5,6,10}`. -/
theorem hub10FanRealized_of_faceWitness_five {c : Fin 11 → Point} {r : ℝ}
    (h : FaceWitness c 5 r) :
    ∃ z : Point, dist (c 5) z ≤ r ∧ dist (c 6) z ≤ r ∧ dist (c 10) z ≤ r := by
  obtain ⟨z, hz⟩ := h
  have e0 : face 5 0 = (5 : Fin 11) := rfl
  have e1 : face 5 1 = (6 : Fin 11) := rfl
  have e2 : face 5 2 = (10 : Fin 11) := rfl
  exact ⟨z, by simpa [e0] using hz 0, by simpa [e1] using hz 1, by simpa [e2] using hz 2⟩

/-- `FaceWitness c 7 r` gives the three-site common point for the fan triple `{7,8,10}`. -/
theorem hub10FanRealized_of_faceWitness_seven {c : Fin 11 → Point} {r : ℝ}
    (h : FaceWitness c 7 r) :
    ∃ z : Point, dist (c 7) z ≤ r ∧ dist (c 8) z ≤ r ∧ dist (c 10) z ≤ r := by
  obtain ⟨z, hz⟩ := h
  have e0 : face 7 0 = (7 : Fin 11) := rfl
  have e1 : face 7 1 = (8 : Fin 11) := rfl
  have e2 : face 7 2 = (10 : Fin 11) := rfl
  exact ⟨z, by simpa [e0] using hz 0, by simpa [e1] using hz 1, by simpa [e2] using hz 2⟩

/-- **The requested shape, from the two Voronoi vertices** (the hub-leg target of the C4 lane). -/
theorem hub10_fan_witnesses_of_voronoiFaces {c : Fin 11 → Point} {r : ℝ} (hc : Covers c r)
    (h5 : VoronoiFace c 5) (h7 : VoronoiFace c 7) :
    FaceWitness c 5 r ∧ FaceWitness c 7 r :=
  ⟨faceWitness_of_voronoiFace hc h5, faceWitness_of_voronoiFace hc h7⟩

/-- Same statement in C4's `Hub10FanRealized` premise shape (the type consumed by
`DSHTopologyInteriorWitness.hub10_fan_witnesses_of_hub10FanRealized`). -/
theorem hub10FanRealized_of_voronoiFaces {c : Fin 11 → Point} {r : ℝ} (hc : Covers c r)
    (h5 : VoronoiFace c 5) (h7 : VoronoiFace c 7) : Hub10FanRealized c r :=
  ⟨hub10FanRealized_of_faceWitness_five (faceWitness_of_voronoiFace hc h5),
    hub10FanRealized_of_faceWitness_seven (faceWitness_of_voronoiFace hc h7)⟩

/-! ## 4. Assembly: C4's frozen interface with only the two hub-10 Voronoi vertices as premises

`0 ≤ r`, the 18 boundary rows (C2's ledger output), the 9 source-block face witnesses (the source
table), and **only the two** hub-10 fan Voronoi vertices are needed. The six non-source rows are
paid by nothing else. That is the exact remaining content of line C4. -/

theorem feasible_of_source_block_and_two_voronoiFaces {U : Fin 9 → Point} {C : Fin 11 → Point}
    {r : ℝ} (hc : Covers C r) (hr : 0 ≤ r) (hb : BoundaryRows U C r)
    (hsource : ∀ g : Fin 9, FaceWitness C (faceMap g) r)
    (h5 : VoronoiFace C 5) (h7 : VoronoiFace C 7) :
    ∃ Z : Fin 11 → Point, Feasible U C Z r :=
  feasible_of_canonical_source_and_hub10_fan_witnesses hr hb hsource
    (faceWitness_of_voronoiFace hc h5) (faceWitness_of_voronoiFace hc h7)

/-- The same with the frozen `V2` consumer (frozen `ResumeNetwork.oracle_le_feasible`). -/
theorem oracle_le_of_source_block_and_two_voronoiFaces {U : Fin 9 → Point} {C : Fin 11 → Point}
    {r : ℝ} (hc : Covers C r) (hr : 0 ≤ r) (hb : BoundaryRows U C r)
    (hsource : ∀ g : Fin 9, FaceWitness C (faceMap g) r)
    (h5 : VoronoiFace C 5) (h7 : VoronoiFace C 7) : V2 U ≤ r ^ 2 :=
  oracle_le_of_source_and_hub10_fan_witnesses hr hb
    (fun g => (rawFaceWitness_iff C g r).2 (hsource g))
    (faceWitness_of_voronoiFace hc h5) (faceWitness_of_voronoiFace hc h7)

/-- Bookkeeping form: the all-rows conclusion in C4's `RowConstraint` shape. -/
theorem rowConstraints_of_source_block_and_two_voronoiFaces {U : Fin 9 → Point}
    {C : Fin 11 → Point} {r : ℝ} (hc : Covers C r) (hr : 0 ≤ r) (hb : BoundaryRows U C r)
    (hsource : ∀ g : Fin 9, FaceWitness C (faceMap g) r)
    (h5 : VoronoiFace C 5) (h7 : VoronoiFace C 7) :
    ∃ Z : Fin 11 → Point, ∀ w : InteriorRow, RowConstraint U C Z r w := by
  obtain ⟨Z, hZ⟩ := feasible_of_source_block_and_two_voronoiFaces hc hr hb hsource h5 h7
  exact ⟨Z, fun w => hZ.2 (.inr (rowIdx w))⟩

/-! ## 5. Controls

Two independent controls, each failing for a mathematical reason:

* `nearestTriple_alone_insufficient` — the nearest-site premise without `Covers` gives nothing:
  the face sites can be weakly nearest at a point and yet be farther than `r` from it. So the
  cover hypothesis in the deduction is load-bearing, not decorative;
* `hub10_fan_common_point_can_fail` — the *conclusion* shape is falsifiable: there are centres
  for which no point is within `0` of the fan triple, so a proof of the hub leg cannot be
  vacuous; the premises genuinely have to be produced from the cover. -/

theorem nearestTriple_alone_insufficient :
    ∃ (c : Fin 11 → Point) (z : Point), IsNearestTriple c 5 z ∧ ¬ (dist (c 5) z ≤ 0) := by
  refine ⟨fun _ => probePoint, 0, ?_, ?_⟩
  · refine ⟨by simp, ?_⟩
    intro i v
    simp
  · intro h
    rw [dist_zero_right] at h
    have hpos : 0 < ‖probePoint‖ := norm_pos_iff.mpr probePoint_ne
    linarith

/-- No point is within `0` of the fan triple `{5,6,10}` when the hub sits at the origin and site
`5` does not. -/
theorem hub10_fan_common_point_can_fail :
    ¬ (∃ z : Point, dist ((Function.update (0 : Fin 11 → Point) 5 probePoint) 5) z ≤ 0 ∧
        dist ((Function.update (0 : Fin 11 → Point) 5 probePoint) 6) z ≤ 0 ∧
        dist ((Function.update (0 : Fin 11 → Point) 5 probePoint) 10) z ≤ 0) := by
  rintro ⟨z, h5, _h6, h10⟩
  have h5' : probePoint = z := by simpa [Function.update] using h5
  have h10' : z = (0 : Point) := by simpa [Function.update] using h10
  exact probePoint_ne (h5'.trans h10')

/-! ## 6. Verbatim types and axiom prints -/

#check @N11Formalization.DSHTopologyInterior.NineDisks
#check @N11Formalization.DSHTopologyInterior.RingLabels
#check @N11Formalization.DSHTopologyInterior.IsNearestTriple
#check @N11Formalization.DSHTopologyInterior.VoronoiFace
#check @N11Formalization.DSHTopologyInterior.hub_of_covers_origin
#check @N11Formalization.DSHTopologyInterior.exists_hub_covering_origin
#check @N11Formalization.DSHTopologyInterior.hub_coverer_of_inner_point
#check @N11Formalization.DSHTopologyInterior.ring_norm_ge
#check @N11Formalization.DSHTopologyInterior.isNearestTriple_dists_eq
#check @N11Formalization.DSHTopologyInterior.faceWitness_of_voronoiFace
#check @N11Formalization.DSHTopologyInterior.faceWitnesses_of_voronoiFaces
#check @N11Formalization.DSHTopologyInterior.hub10FanRealized_of_faceWitness_five
#check @N11Formalization.DSHTopologyInterior.hub10FanRealized_of_faceWitness_seven
#check @N11Formalization.DSHTopologyInterior.hub10_fan_witnesses_of_voronoiFaces
#check @N11Formalization.DSHTopologyInterior.hub10FanRealized_of_voronoiFaces
#check @N11Formalization.DSHTopologyInterior.feasible_of_source_block_and_two_voronoiFaces
#check @N11Formalization.DSHTopologyInterior.oracle_le_of_source_block_and_two_voronoiFaces
#check @N11Formalization.DSHTopologyInterior.rowConstraints_of_source_block_and_two_voronoiFaces

#print axioms N11Formalization.DSHTopologyInterior.hub_of_covers_origin
#print axioms N11Formalization.DSHTopologyInterior.hub_coverer_of_inner_point
#print axioms N11Formalization.DSHTopologyInterior.isNearestTriple_dists_eq
#print axioms N11Formalization.DSHTopologyInterior.faceWitness_of_voronoiFace
#print axioms N11Formalization.DSHTopologyInterior.hub10_fan_witnesses_of_voronoiFaces
#print axioms N11Formalization.DSHTopologyInterior.hub10FanRealized_of_voronoiFaces
#print axioms N11Formalization.DSHTopologyInterior.feasible_of_source_block_and_two_voronoiFaces
#print axioms N11Formalization.DSHTopologyInterior.oracle_le_of_source_block_and_two_voronoiFaces
#print axioms N11Formalization.DSHTopologyInterior.nearestTriple_alone_insufficient
#print axioms N11Formalization.DSHTopologyInterior.hub10_fan_common_point_can_fail

end N11Formalization.DSHTopologyInterior
