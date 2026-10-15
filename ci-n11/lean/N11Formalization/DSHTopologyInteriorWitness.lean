/-
n11-formalization — DSH line C4 groundwork, part 5 (teammate `topo-interior`).

# DSHTopologyInteriorWitness — conditional scaffolding for the two hub-10 fan witnesses

Scope: **local groundwork, standalone**; lead integrates. This file does **not** prove
`Covers → Feasible`. It delivers exactly what the lead asked for: the existence of the two
hub-10 fan `FaceWitness`es for an arbitrary `c : Fin 11 → Point`, as a **conditional** statement
whose premises are typed, named and explicitly *not* assumed anywhere else.

The typed premises are the output shape of the canonical-configuration construction:

* `FanRealized c r` — the nine fan vertices of the frozen `ResumeNetwork.face` table exist as
  `r`-common points of their three incident sites (this is the two-fan half of C3);
* `CentralRealized c r` — the two central hub–hub vertices (this is the remaining half of C3);
* `BoundaryRows U c r` — the 18 boundary rows, i.e. the ownership ledger output of C2 (already
  the shape used by `DSH-TOPO-C4-INTERFACE`).

Nothing about the ten-boundary exclusion (C1) or the ownership ledger (C2) is assumed: their
output is a hypothesis, and `boundary_ledger_does_not_give_hub10_fan` shows the boundary ledger
alone does **not** give the two hub-10 fan witnesses, so the fan premise is not removable.

Structural point proved here: the two canonical faces `5 = [5,6,10]` and `7 = [7,8,10]` are
**ordinary fan faces** (`k = 5` and `k = 7` of the nine fan faces). The frozen source table
happens to realize a *different* set of nine faces (seven fan faces plus the two central ones),
which is why its own witnesses for faces 5 and 7 are the relaxed fixed rational point `O0` and
its mirror. For an arbitrary cover, once `FanRealized` holds, faces 5 and 7 are paid exactly
like every other fan face — the source's "slack" split is an artifact of its witness *choice*,
not of the cover geometry.
-/
import N11Formalization.DSHTopologyInteriorInterface
import N11Formalization.DSHTopologyInteriorMinimality

set_option autoImplicit false

namespace N11Formalization.DSHTopologyInterior

open N11Formalization ResumeNetwork ResumeLocalIncidence

/-! ## 1. Index facts: canonical face `k` (for `k : Fin 9`) is the fan face of the ring pair -/

/-- The next ring site after `k`, cyclically (`8 ↦ 0`). -/
def ringSucc (k : Fin 9) : Fin 11 := ⟨((k : ℕ) + 1) % 9, by omega⟩

/-- The hub carrying the `k`-th fan face of the frozen canonical table: hub `9` for the ring pairs
`(0,1),(1,2),(2,3),(3,4)` and hub `10` for `(4,5),(5,6),(6,7),(7,8),(8,0)`. -/
def fanHub (k : Fin 9) : Fin 11 := if (k : ℕ) ≤ 3 then 9 else 10

/-- **Index fact (kernel).** The canonical face `k` (as `Fin 11`) is exactly the fan face
`(k, k+1, fanHub k)` — so the nine canonical faces `0..8` are precisely the nine fan faces. -/
theorem fan_face_triple (k : Fin 9) :
    face ⟨k.val, by omega⟩ 0 = ⟨k.val, by omega⟩ ∧
      face ⟨k.val, by omega⟩ 1 = ringSucc k ∧
      face ⟨k.val, by omega⟩ 2 = fanHub k := by
  fin_cases k <;> decide

/-- The two hub-10 fan faces in the canonical indexing: `k = 5` and `k = 7`. -/
theorem hub10_fan_indices :
    fanHub 5 = 10 ∧ fanHub 7 = 10 ∧ ringSucc 5 = 6 ∧ ringSucc 7 = 8 ∧
      face 5 = ![5, 6, 10] ∧ face 7 = ![7, 8, 10] := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The frozen source table realizes seven fan faces and the two central faces; the fan faces it
omits are exactly `k = 5` and `k = 7`. -/
theorem fan_faces_omitted_by_source_table :
    (Finset.univ.filter (fun k : Fin 9 => ¬ ∃ g : Fin 9, faceMap g = ⟨k.val, by omega⟩)).card = 2 ∧
      (∀ k : Fin 9, (¬ ∃ g : Fin 9, faceMap g = ⟨k.val, by omega⟩) ↔ (k.val = 5 ∨ k.val = 7)) := by
  constructor
  · decide
  · intro k
    revert k
    decide

/-! ## 2. Typed premises (C3 output shape, in the exact `FaceWitness` form) -/

/-- **Typed premise — fan half of C3.** Each of the nine fan vertices exists as a point within `r`
of its three incident sites (ring `k`, ring `k+1`, hub of the `k`-th fan). -/
def FanRealized (c : Fin 11 → Point) (r : ℝ) : Prop :=
  ∀ k : Fin 9, ∃ z : Point,
    dist (c ⟨k.val, by omega⟩) z ≤ r ∧ dist (c (ringSucc k)) z ≤ r ∧ dist (c (fanHub k)) z ≤ r

/-- **Typed premise — central half of C3.** The two hub–hub vertices `{0,9,10}` and `{4,9,10}`. -/
def CentralRealized (c : Fin 11 → Point) (r : ℝ) : Prop :=
  (∃ z : Point, dist (c 0) z ≤ r ∧ dist (c 9) z ≤ r ∧ dist (c 10) z ≤ r) ∧
    (∃ z : Point, dist (c 4) z ≤ r ∧ dist (c 9) z ≤ r ∧ dist (c 10) z ≤ r)

/-- **Minimal typed premise for the two hub-10 fan faces only.** -/
def Hub10FanRealized (c : Fin 11 → Point) (r : ℝ) : Prop :=
  (∃ z : Point, dist (c 5) z ≤ r ∧ dist (c 6) z ≤ r ∧ dist (c 10) z ≤ r) ∧
    (∃ z : Point, dist (c 7) z ≤ r ∧ dist (c 8) z ≤ r ∧ dist (c 10) z ≤ r)

/-! ## 3. The requested statements: the two hub-10 fan `FaceWitness`es -/

/-- **Fan `FaceWitness` from the fan premise** (uniform over the nine fan faces). -/
theorem faceWitness_fan_of_fanRealized {c : Fin 11 → Point} {r : ℝ}
    (h : FanRealized c r) (k : Fin 9) : FaceWitness c ⟨k.val, by omega⟩ r := by
  obtain ⟨z, h1, h2, h3⟩ := h k
  refine ⟨z, fun v => ?_⟩
  have ht := fan_face_triple k
  fin_cases v
  · simpa [ht.1] using h1
  · simpa [ht.2.1] using h2
  · simpa [ht.2.2] using h3

/-- **The two hub-10 fan witnesses from the minimal premise** (the lead's requested shape). -/
theorem hub10_fan_witnesses_of_hub10FanRealized {c : Fin 11 → Point} {r : ℝ}
    (h : Hub10FanRealized c r) : FaceWitness c 5 r ∧ FaceWitness c 7 r := by
  have e50 : face 5 0 = (5 : Fin 11) := rfl
  have e51 : face 5 1 = (6 : Fin 11) := rfl
  have e52 : face 5 2 = (10 : Fin 11) := rfl
  have e70 : face 7 0 = (7 : Fin 11) := rfl
  have e71 : face 7 1 = (8 : Fin 11) := rfl
  have e72 : face 7 2 = (10 : Fin 11) := rfl
  constructor
  · obtain ⟨z, h1, h2, h3⟩ := h.1
    refine ⟨z, fun v => ?_⟩
    fin_cases v
    · simpa [e50] using h1
    · simpa [e51] using h2
    · simpa [e52] using h3
  · obtain ⟨z, h1, h2, h3⟩ := h.2
    refine ⟨z, fun v => ?_⟩
    fin_cases v
    · simpa [e70] using h1
    · simpa [e71] using h2
    · simpa [e72] using h3

/-- **The two hub-10 fan witnesses from the uniform fan premise.** -/
theorem hub10_fan_witnesses_of_fanRealized {c : Fin 11 → Point} {r : ℝ}
    (h : FanRealized c r) : FaceWitness c 5 r ∧ FaceWitness c 7 r :=
  ⟨faceWitness_fan_of_fanRealized h 5, faceWitness_fan_of_fanRealized h 7⟩

/-- The uniform premise implies the minimal one (so the two named faces are not special). -/
theorem hub10FanRealized_of_fanRealized {c : Fin 11 → Point} {r : ℝ}
    (h : FanRealized c r) : Hub10FanRealized c r := by
  obtain ⟨z5, h5a, h5b, h5c⟩ := h 5
  obtain ⟨z7, h7a, h7b, h7c⟩ := h 7
  exact ⟨⟨z5, h5a, h5b, h5c⟩, ⟨z7, h7a, h7b, h7c⟩⟩

/-- The central face `9 = [0,9,10]` as a `FaceWitness` from its three-site common point. -/
theorem faceWitness_nine_of {c : Fin 11 → Point} {r : ℝ}
    (h : ∃ z : Point, dist (c 0) z ≤ r ∧ dist (c 9) z ≤ r ∧ dist (c 10) z ≤ r) :
    FaceWitness c 9 r := by
  obtain ⟨z, h1, h2, h3⟩ := h
  have e0 : face 9 0 = (0 : Fin 11) := rfl
  have e1 : face 9 1 = (9 : Fin 11) := rfl
  have e2 : face 9 2 = (10 : Fin 11) := rfl
  refine ⟨z, fun v => ?_⟩
  fin_cases v
  · simpa [e0] using h1
  · simpa [e1] using h2
  · simpa [e2] using h3

/-- The central face `10 = [4,9,10]` as a `FaceWitness` from its three-site common point. -/
theorem faceWitness_ten_of {c : Fin 11 → Point} {r : ℝ}
    (h : ∃ z : Point, dist (c 4) z ≤ r ∧ dist (c 9) z ≤ r ∧ dist (c 10) z ≤ r) :
    FaceWitness c 10 r := by
  obtain ⟨z, h1, h2, h3⟩ := h
  have e0 : face 10 0 = (4 : Fin 11) := rfl
  have e1 : face 10 1 = (9 : Fin 11) := rfl
  have e2 : face 10 2 = (10 : Fin 11) := rfl
  refine ⟨z, fun v => ?_⟩
  fin_cases v
  · simpa [e0] using h1
  · simpa [e1] using h2
  · simpa [e2] using h3

/-- **All 11 canonical face witnesses from the two typed premises** (fan + central). -/
theorem all_faceWitnesses_of_realized {c : Fin 11 → Point} {r : ℝ}
    (hfan : FanRealized c r) (hc : CentralRealized c r) : ∀ f : Fin 11, FaceWitness c f r := by
  intro f
  fin_cases f
  · exact faceWitness_fan_of_fanRealized hfan 0
  · exact faceWitness_fan_of_fanRealized hfan 1
  · exact faceWitness_fan_of_fanRealized hfan 2
  · exact faceWitness_fan_of_fanRealized hfan 3
  · exact faceWitness_fan_of_fanRealized hfan 4
  · exact faceWitness_fan_of_fanRealized hfan 5
  · exact faceWitness_fan_of_fanRealized hfan 6
  · exact faceWitness_fan_of_fanRealized hfan 7
  · exact faceWitness_fan_of_fanRealized hfan 8
  · exact faceWitness_nine_of hc.1
  · exact faceWitness_ten_of hc.2

/-! ## 4. Conditional C5 scaffolding: typed premises ⇒ frozen `Feasible` / `V2` bound

This is the whole `Covers → Feasible` chain with the geometric existence of the canonical
configuration left as the explicit premises `FanRealized`/`CentralRealized` (C3) and
`BoundaryRows` (C2). C1 is not used here at all. -/

/-- **Conditional C5 scaffolding.** `0 ≤ r`, the 18 boundary rows (C2's ledger output) and the
11 realized dual vertices (C3's output) produce the frozen `Feasible` witness. -/
theorem feasible_of_boundary_fan_central {U : Fin 9 → Point} {C : Fin 11 → Point} {r : ℝ}
    (hr : 0 ≤ r) (hb : BoundaryRows U C r) (hfan : FanRealized C r)
    (hc : CentralRealized C r) : ∃ Z : Fin 11 → Point, Feasible U C Z r := by
  have hall := all_faceWitnesses_of_realized hfan hc
  exact feasible_of_source_and_hub10_fan_witnesses hr hb
    (fun g => (rawFaceWitness_iff C g r).2 (hall (faceMap g))) (hall 5) (hall 7)

/-- **Conditional oracle consumer**: the same premises give `V2 U ≤ r²` through the frozen
`ResumeNetwork.oracle_le_feasible`. -/
theorem oracle_le_of_boundary_fan_central {U : Fin 9 → Point} {C : Fin 11 → Point} {r : ℝ}
    (hr : 0 ≤ r) (hb : BoundaryRows U C r) (hfan : FanRealized C r)
    (hc : CentralRealized C r) : V2 U ≤ r ^ 2 := by
  obtain ⟨Z, hZ⟩ := feasible_of_boundary_fan_central hr hb hfan hc
  exact ResumeNetwork.oracle_le_feasible hZ

/-- Variant consuming the minimal two-face premise together with the seven remaining fan faces
and the two central faces, i.e. the same conclusion with the fan premise split. -/
theorem feasible_of_boundary_fan_central_split {U : Fin 9 → Point} {C : Fin 11 → Point} {r : ℝ}
    (hr : 0 ≤ r) (hb : BoundaryRows U C r)
    (hfan : ∀ k : Fin 9, k.val ≠ 5 → k.val ≠ 7 → ∃ z : Point,
      dist (C ⟨k.val, by omega⟩) z ≤ r ∧ dist (C (ringSucc k)) z ≤ r ∧ dist (C (fanHub k)) z ≤ r)
    (hhub10 : Hub10FanRealized C r) (hc : CentralRealized C r) :
    ∃ Z : Fin 11 → Point, Feasible U C Z r := by
  have hfan' : FanRealized C r := by
    intro k
    by_cases h5 : k.val = 5
    · have hk : (⟨k.val, by omega⟩ : Fin 11) = 5 := Fin.ext h5
      have hs : ringSucc k = 6 := by simp [ringSucc, h5]
      have hh : fanHub k = 10 := by simp [fanHub, h5]
      refine ⟨hhub10.1.choose, ?_, ?_, ?_⟩
      · rw [hk]; exact hhub10.1.choose_spec.1
      · rw [hs]; exact hhub10.1.choose_spec.2.1
      · rw [hh]; exact hhub10.1.choose_spec.2.2
    · by_cases h7 : k.val = 7
      · have hk : (⟨k.val, by omega⟩ : Fin 11) = 7 := Fin.ext h7
        have hs : ringSucc k = 8 := by simp [ringSucc, h7]
        have hh : fanHub k = 10 := by simp [fanHub, h7]
        refine ⟨hhub10.2.choose, ?_, ?_, ?_⟩
        · rw [hk]; exact hhub10.2.choose_spec.1
        · rw [hs]; exact hhub10.2.choose_spec.2.1
        · rw [hh]; exact hhub10.2.choose_spec.2.2
      · exact hfan k h5 h7
  exact feasible_of_boundary_fan_central hr hb hfan' hc

/-! ## 5. Negative control: the boundary ledger alone does not give the hub-10 fan witnesses -/

/-- **Control.** There is a configuration in which all 18 boundary rows hold while **both**
hub-10 fan `FaceWitness`es fail. So the fan/central realization premise is not removable and no
`Covers → Feasible` step may assume it silently: with `r = 0`, all ring centres and all anchors
at the origin and only `c 10` displaced, the boundary ledger is satisfied but `FaceWitness c 5 0`
and `FaceWitness c 7 0` are false. -/
theorem boundary_ledger_does_not_give_hub10_fan :
    ∃ (c : Fin 11 → Point) (U : Fin 9 → Point) (r : ℝ),
      BoundaryRows U c r ∧ ¬ FaceWitness c 5 r ∧ ¬ FaceWitness c 7 r := by
  refine ⟨Function.update (0 : Fin 11 → Point) 10 probePoint, fun _ => 0, 0, ?_, ?_, ?_⟩
  · intro i side
    have hi : (⟨i.val, by omega⟩ : Fin 11) ≠ 10 := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_mk] at this
      omega
    have hc0 : Function.update (0 : Fin 11 → Point) 10 probePoint ⟨i.val, by omega⟩ = 0 := by
      simp [Function.update, hi]
    simp [BoundaryRows, hc0]
  · intro h
    obtain ⟨z, hz⟩ := h
    have h5 : z = 0 := by simpa [Function.update, face] using hz 0
    have h10 : probePoint = z := by simpa [Function.update, face] using hz 2
    exact probePoint_ne (h10.trans h5)
  · intro h
    obtain ⟨z, hz⟩ := h
    have h7 : z = 0 := by simpa [Function.update, face] using hz 0
    have h10 : probePoint = z := by simpa [Function.update, face] using hz 2
    exact probePoint_ne (h10.trans h7)

/-! ## 6. Verbatim types and axiom prints -/

#check @N11Formalization.DSHTopologyInterior.ringSucc
#check @N11Formalization.DSHTopologyInterior.fanHub
#check @N11Formalization.DSHTopologyInterior.fan_face_triple
#check @N11Formalization.DSHTopologyInterior.hub10_fan_indices
#check @N11Formalization.DSHTopologyInterior.fan_faces_omitted_by_source_table
#check @N11Formalization.DSHTopologyInterior.FanRealized
#check @N11Formalization.DSHTopologyInterior.CentralRealized
#check @N11Formalization.DSHTopologyInterior.Hub10FanRealized
#check @N11Formalization.DSHTopologyInterior.faceWitness_fan_of_fanRealized
#check @N11Formalization.DSHTopologyInterior.hub10_fan_witnesses_of_hub10FanRealized
#check @N11Formalization.DSHTopologyInterior.hub10_fan_witnesses_of_fanRealized
#check @N11Formalization.DSHTopologyInterior.hub10FanRealized_of_fanRealized
#check @N11Formalization.DSHTopologyInterior.all_faceWitnesses_of_realized
#check @N11Formalization.DSHTopologyInterior.feasible_of_boundary_fan_central
#check @N11Formalization.DSHTopologyInterior.oracle_le_of_boundary_fan_central
#check @N11Formalization.DSHTopologyInterior.feasible_of_boundary_fan_central_split
#check @N11Formalization.DSHTopologyInterior.boundary_ledger_does_not_give_hub10_fan

#print axioms N11Formalization.DSHTopologyInterior.fan_face_triple
#print axioms N11Formalization.DSHTopologyInterior.fan_faces_omitted_by_source_table
#print axioms N11Formalization.DSHTopologyInterior.faceWitness_fan_of_fanRealized
#print axioms N11Formalization.DSHTopologyInterior.hub10_fan_witnesses_of_hub10FanRealized
#print axioms N11Formalization.DSHTopologyInterior.hub10_fan_witnesses_of_fanRealized
#print axioms N11Formalization.DSHTopologyInterior.all_faceWitnesses_of_realized
#print axioms N11Formalization.DSHTopologyInterior.feasible_of_boundary_fan_central
#print axioms N11Formalization.DSHTopologyInterior.oracle_le_of_boundary_fan_central
#print axioms N11Formalization.DSHTopologyInterior.feasible_of_boundary_fan_central_split
#print axioms N11Formalization.DSHTopologyInterior.boundary_ledger_does_not_give_hub10_fan

end N11Formalization.DSHTopologyInterior
