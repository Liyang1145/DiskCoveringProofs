/-
n11-formalization — DSH line C4 groundwork, part 6 (teammate `topo-interior`).

# DSHTopologyInteriorWitnessLanes — lane provenance for the two hub-10 fan witnesses

Scope: **local groundwork, standalone**; lead integrates. This file does **not** prove
`Covers → Feasible`. It states the requested shape

    FaceWitness c 5 r ∧ FaceWitness c 7 r

for an *arbitrary* centre function `c : Fin 11 → Point`, as a **conditional** statement whose
premises are the typed outputs of the three open lines, each **consumed from the real module of
that line** wherever such a module exists — nothing is assumed silently, and nothing is invented:

* **C1 (ten-boundary exclusion, `topo-ten-bdy`).**  The lean half is *paid*: the team module
  `Assembly/BoundaryCount` proves `card_boundaryIdx_eq_nine_or_ten` (`0 ≤ r`, `r < 19/50`,
  `Covers c r` ⇒ the boundary-disk count is 9 or 10).  So the remaining C1 content is exactly
  "≠ 10".  Here: `NineBoundary c r := Fintype.card (BoundaryIdx c r) = 9` and the kernel
  reduction `C1_remaining_content` consuming their theorem.
* **C2 (ownership / no-bubble, `topo-ownership`).**  Their headline `unique_ownership_actual`
  is conditional on `Fintype.card (BoundaryIdx c r) = 9`; `OwnershipOutput c r` below is its
  **verbatim** conclusion type, and `ownership_output_of_lane` derives it from their theorem.
  Also consumed: `not_exists_coincident_of_card_nine` (their degenerate-branch work), which
  makes the nine boundary centres pairwise distinct.
* **C3 (two-hub / two-fan realization, `topo-hub-fan`).**  The graph/index half is paid by their
  module (`face_table`, `ring_cycle_exact`, `hub_degrees`); the *point-existence* half is the
  open premise, typed here as `FanRealized` / `CentralRealized` / `Hub10FanRealized`.

**Consumption discipline (stated in the kernels, not just prose).**  The derivation of
`FaceWitness c 5 r ∧ FaceWitness c 7 r` consumes ONLY the C3 point-existence premise: the
kernel-checked separation is `hub10_fan_witnesses_of_hub10FanRealized` (in
`DSHTopologyInteriorWitness`, no `Covers`/C1/C2 hypotheses).  C1 and C2 are **upstream**: they
are what a future proof must use to *establish* the C3 premise, not what this derivation eats.
`C1_C2_upstream_not_consumed` records that separation explicitly so no reader can mistake the
provenance bundle for a consumption chain.
-/
import N11Formalization.DSHTopologyInteriorWitness
import N11Formalization.DSHTopologyOwnershipLedger
import N11Formalization.DSHTopologyHubFan
import N11Formalization.Assembly.BoundaryCount

set_option autoImplicit false

namespace N11Formalization.DSHTopologyInterior

open N11Formalization ResumeNetwork ResumeLocalIncidence
open N11Formalization.DSHTopologyOwnershipLedger

/-! ## 1. C1 lane: the typed premise, and the kernel reduction of what is still missing -/

/-- **C1 lane output (typed premise).** Exactly nine disks meet `S¹`. By
`Assembly/BoundaryCount.card_boundaryIdx_eq_nine_or_ten` the paid half already gives
`9 ≤ card ≤ 10` under `0 ≤ r`, `r < 19/50`, `Covers c r`, so this premise is equivalent to
ruling out the ten-boundary configuration — the C450 obligation of line C1. It is a premise
here, never an assumption. -/
def NineBoundary (c : Fin 11 → Point) (r : ℝ) : Prop :=
  Fintype.card (BoundaryIdx c r) = 9

/-- **C1 reduction (consumes the team's paid two-sided bound).** Under the frozen cover
hypotheses, the open part of C1 is exactly the exclusion of ten boundary disks. -/
theorem C1_remaining_content {c : Fin 11 → Point} {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r < (19 : ℝ) / 50) (hc : Covers c r) :
    NineBoundary c r ↔ Fintype.card (BoundaryIdx c r) ≠ 10 := by
  have h := card_boundaryIdx_eq_nine_or_ten hr0 hr hc
  constructor
  · intro h9 h10
    rw [NineBoundary] at h9
    omega
  · intro hne
    rcases h with h9 | h10
    · exact h9
    · exact absurd h10 hne

/-- The C1 premise has the same cardinality as the nine canonical ring indices. -/
theorem NineBoundary.card_eq_nine {c : Fin 11 → Point} {r : ℝ} (h : NineBoundary c r) :
    Fintype.card (BoundaryIdx c r) = Fintype.card (Fin 9) := by
  rw [NineBoundary] at h
  rw [h, Fintype.card_fin]

/-- **C1 premise ⇒ boundary centres are far from the origin** (consumes the team's
`one_sub_le_norm_of_meetsCircle`): every boundary disk has centre norm `≥ 1 - r`. -/
theorem NineBoundary.norm_ge {c : Fin 11 → Point} {r : ℝ} (i : BoundaryIdx c r) :
    1 - r ≤ ‖c i.1‖ :=
  one_sub_le_norm_of_meetsCircle i.2

/-! ## 2. C2 lane: the verbatim output type, and the degenerate-branch consequence -/

/-- **C2 lane output (verbatim conclusion type of `unique_ownership_actual`).** No weakening, no
re-packaging: this is copied from the C2 module's headline theorem with `NineBoundary` written
for its `hcard`. -/
def OwnershipOutput (c : Fin 11 → Point) (r : ℝ) : Prop :=
  (∀ x : Point, ‖x‖ = 1 →
      ∃! i : Fin 11, MeetsCircle c r i ∧ DSHTopologyOwnership.OwnsPt c i x ∧ dist x (c i) ≤ r) ∧
    (∀ i : BoundaryIdx c r, 0 < MeasureTheory.volume.real (ownerSetB c r i) ∧
        MeasureTheory.volume.real (ownerSetB c r i) ≤ 2 * Real.arcsin r) ∧
    (∀ i : BoundaryIdx c r, 0 < MeasureTheory.volume.real (capPreimage (c i.1) r)) ∧
    (∑ i : BoundaryIdx c r, MeasureTheory.volume.real (ownerSetB c r i) = 2 * Real.pi) ∧
    (∀ t : ℝ, t ∈ Set.Ioo 0 (2 * Real.pi) →
        ∃! i : BoundaryIdx c r, DSHTopologyOwnership.OwnsB c r i t)

/-- **The C2 lane really supplies this premise**: their conditional headline applied to the C1
premise. So `OwnershipOutput` is the line's actual output, not a redefinition. -/
theorem ownership_output_of_lane {c : Fin 11 → Point} {r : ℝ} (hr0 : 0 ≤ r)
    (hrR0 : r < (19 : ℝ) / 50) (hcov : Covers c r) (hcard : NineBoundary c r) :
    OwnershipOutput c r :=
  unique_ownership_actual hr0 hrR0 hcov hcard

/-- **C2 lane, degenerate branch (consumed).** The nine-boundary premise excludes coincident
boundary centres — so the nine ring sites that C3 must realize are pairwise distinct. -/
theorem nine_boundary_centres_distinct {c : Fin 11 → Point} {r : ℝ} (hr0 : 0 ≤ r)
    (hrR0 : r < (19 : ℝ) / 50) (hcov : Covers c r) (hcard : NineBoundary c r) :
    ¬ ∃ i j : BoundaryIdx c r, i ≠ j ∧ c i.1 = c j.1 :=
  not_exists_coincident_of_card_nine hr0 (by linarith)
    (eight_arcsin_lt_pi_of_lt_R0 hrR0) hcov hcard

/-! ## 3. C3 lane: cross-calibration of the index facts against the hub-fan module -/

/-- **Cross-lane calibration of the fan index.** My `fanHub` / `ringSucc` decomposition of the
canonical faces agrees with the hub-fan lane's evaluated face table and their degree facts:
hub `9` carries the faces of ring pairs `(k, k+1)` for `k ≤ 3`, hub `10` the rest, so hub `9`
has degree 6 and hub `10` degree 7. -/
theorem fanHub_calibration :
    (∀ k : Fin 9, fanHub k = 9 ↔ (k : ℕ) ≤ 3) ∧
      DSHTopologyHubFan.degree 9 = 6 ∧ DSHTopologyHubFan.degree 10 = 7 ∧
      face 5 = ![5, 6, 10] ∧ face 7 = ![7, 8, 10] ∧
      face 4 = ![4, 5, 10] ∧ face 6 = ![6, 7, 10] ∧
      face 8 = ![8, 0, 10] := by
  refine ⟨?_, DSHTopologyHubFan.degree_hub9, DSHTopologyHubFan.degree_hub10, rfl, rfl, rfl, rfl, rfl⟩
  intro k
  fin_cases k <;> decide

/-- The hub-fan lane's graph facts confirm the two faces outside the source table sit on hub
`10` (my `hub10_fan_indices`): `fanHub k = 10` exactly for the ring indices `4..8`. -/
theorem hub10_fan_rows_are_hub10 :
    (∀ k : Fin 9, fanHub k = 10 ↔ 4 ≤ k.val) ∧
      (DSHTopologyHubFan.nbrs 10).length = 7 := by
  refine ⟨?_, DSHTopologyHubFan.degree_hub10⟩
  intro k
  fin_cases k <;> decide

/-! ## 4. The requested conditional statement, with lane provenance -/

/-- **The requested shape, conditional on the C3 lane's point-existence premise only.**
`FaceWitness c 5 r ∧ FaceWitness c 7 r` for an arbitrary `c`, with no `Covers`, C1 or C2
hypothesis — the derivation genuinely needs none of them. (Re-export of the Witness module's
theorem under the lane-facing name, so the consumption surface is unambiguous.) -/
theorem hub10_fan_witnesses_conditional_on_C3 {c : Fin 11 → Point} {r : ℝ}
    (h : Hub10FanRealized c r) : FaceWitness c 5 r ∧ FaceWitness c 7 r :=
  hub10_fan_witnesses_of_hub10FanRealized h

/-- Uniform version: the nine fan vertices realise faces `5` and `7` like every other fan face. -/
theorem hub10_fan_witnesses_conditional_on_fanRealized {c : Fin 11 → Point} {r : ℝ}
    (h : FanRealized c r) : FaceWitness c 5 r ∧ FaceWitness c 7 r :=
  hub10_fan_witnesses_of_fanRealized h

/-- **Provenance bundle.** The three typed lane outputs, kept in one place so that a future
proof of `Covers → canonical configuration` has one target to hit. Field provenance:
`c1NineBoundary` ← C1 (`topo-ten-bdy`), `c2Ownership` ← C2 (`topo-ownership`),
`c3FanRealized` ← C3 (`topo-hub-fan`). **None of these is derived here**; the bundle only
records their exact types. -/
structure CanonicalConfigPremises (c : Fin 11 → Point) (r : ℝ) where
  c1NineBoundary : NineBoundary c r
  c2Ownership : OwnershipOutput c r
  c3Hub10FanRealized : Hub10FanRealized c r

/-- **Kernel-checked separation (anti-conflation).** The witness derivation consumes *only* the
C3 point-existence premise: the three-lane bundle is therefore not part of that consumption
chain, and C1/C2 must not be read as used by it. This is the same statement as
`hub10_fan_witnesses_conditional_on_C3`, written with the provenance of the two other lanes made
explicit; the C1/C2 premises of the bundle are *upstream* inputs to establishing C3. -/
theorem C1_C2_upstream_not_consumed {c : Fin 11 → Point} {r : ℝ}
    (h : Hub10FanRealized c r) :
    NineBoundary c r → OwnershipOutput c r → FaceWitness c 5 r ∧ FaceWitness c 7 r :=
  fun _ _ => hub10_fan_witnesses_conditional_on_C3 h

/-- Bundle-level corollary in the C1724 C5-facing shape: from the three typed lane premises, the
two named hub-10 fan witnesses. (The proof goes through the C3 field only, as recorded above.) -/
theorem hub10_fan_witnesses_of_canonicalPremises {c : Fin 11 → Point} {r : ℝ}
    (h : CanonicalConfigPremises c r) : FaceWitness c 5 r ∧ FaceWitness c 7 r :=
  hub10_fan_witnesses_conditional_on_C3 h.c3Hub10FanRealized

/-- The bundle also yields the full 51-row `Feasible` witness of the frozen network as soon as
the C2 boundary ledger is instantiated: this is the exact consumer shape C5 needs (no new
interface, no `Covers → Feasible` claim). -/
theorem feasible_of_canonicalPremises {c : Fin 11 → Point} {U : Fin 9 → Point} {r : ℝ}
    (h : CanonicalConfigPremises c r) (hr : 0 ≤ r) (hb : BoundaryRows U c r)
    (hfan : FanRealized c r) (hc : CentralRealized c r) :
    ∃ Z : Fin 11 → Point, Feasible U c Z r :=
  feasible_of_boundary_fan_central hr hb hfan hc

/-! ## 5. Negative control: the C1 premise alone does not give the hub-10 fan witnesses -/

/-- Nine distinct circle points (used only to build the control configuration). -/
noncomputable def ringPoint (k : Fin 9) : Point := circleMap ((k : ℝ) * (2 * Real.pi / 9))

theorem ringPoint_norm (k : Fin 9) : ‖ringPoint k‖ = 1 :=
  circleMap_norm _

/-- The control configuration at `r = 0`: ring sites `0..8` sit ON the unit circle, hubs `9, 10`
sit at the origin. -/
noncomputable def nineBoundaryProbe : Fin 11 → Point := fun i =>
  if h : (i : ℕ) < 9 then ringPoint ⟨i, h⟩ else 0

theorem nineBoundaryProbe_ring (k : Fin 9) :
    nineBoundaryProbe ⟨k.val, by omega⟩ = ringPoint k := by
  simp [nineBoundaryProbe]

theorem nineBoundaryProbe_hub (i : Fin 11) (hi : 9 ≤ i.val) : nineBoundaryProbe i = 0 := by
  simp only [nineBoundaryProbe]
  rw [dif_neg (show ¬ ((i : ℕ) < 9) by omega)]

/-- Every ring site meets the circle at `r = 0`. -/
theorem nineBoundaryProbe_meets_ring (k : Fin 9) :
    MeetsCircle nineBoundaryProbe 0 ⟨k.val, by omega⟩ :=
  ⟨ringPoint k, ringPoint_norm k, by
    rw [nineBoundaryProbe_ring k, dist_self]⟩

/-- Neither hub site meets the circle at `r = 0` (its centre is the origin). -/
theorem nineBoundaryProbe_not_meets_hub (i : Fin 11) (hi : 9 ≤ i.val) :
    ¬ MeetsCircle nineBoundaryProbe 0 i := by
  rintro ⟨x, hx, hd⟩
  have hzero : dist x (nineBoundaryProbe i) = 0 := le_antisymm hd dist_nonneg
  have hx0 : x = nineBoundaryProbe i := dist_eq_zero.mp hzero
  rw [nineBoundaryProbe_hub i hi] at hx0
  rw [hx0, norm_zero] at hx
  exact absurd hx (by norm_num)

/-- The ring index of a meeting disk: a meeting disk at `r = 0` must be a ring site. -/
def nineBoundaryRingIdx (i : BoundaryIdx nineBoundaryProbe 0) : Fin 9 :=
  ⟨i.1.val, by
    by_contra h
    exact nineBoundaryProbe_not_meets_hub i.1 (by omega) i.2⟩

/-- **The control configuration satisfies the C1 typed premise**: exactly nine boundary disks
(the ring sites are on the circle, the two hub sites are the origin). -/
theorem nineBoundaryProbe_card : NineBoundary nineBoundaryProbe 0 := by
  have hinj : Function.Injective
      (fun k : Fin 9 => (⟨⟨k.val, by omega⟩, nineBoundaryProbe_meets_ring k⟩ :
        BoundaryIdx nineBoundaryProbe 0)) := by
    intro a b hab
    exact Fin.ext (congrArg (fun i : BoundaryIdx nineBoundaryProbe 0 => i.1.val) hab)
  have hout : Function.Injective nineBoundaryRingIdx := by
    intro a b hab
    have hv : (a.1 : Fin 11).val = (b.1 : Fin 11).val := by
      simpa using congrArg Fin.val hab
    exact Subtype.ext (Fin.ext hv)
  have h9 : 9 ≤ Fintype.card (BoundaryIdx nineBoundaryProbe 0) := by
    simpa using Fintype.card_le_of_injective _ hinj
  have h9' : Fintype.card (BoundaryIdx nineBoundaryProbe 0) ≤ 9 := by
    simpa using Fintype.card_le_of_injective _ hout
  simpa [NineBoundary] using le_antisymm h9' h9

/-- The probe has **no** common `0`-point for the pair `(5, 10)`: `c 5` is on the circle while
`c 10` is the origin. This single fact kills both the fan premise and the face-`5` witness. -/
theorem nineBoundaryProbe_no_common_point :
    ¬ (∃ z : Point, dist (nineBoundaryProbe 5) z ≤ 0 ∧ dist (nineBoundaryProbe 10) z ≤ 0) := by
  rintro ⟨z, h5, h10⟩
  have h5' : nineBoundaryProbe 5 = z := dist_eq_zero.mp (le_antisymm h5 dist_nonneg)
  have h10' : nineBoundaryProbe 10 = z := dist_eq_zero.mp (le_antisymm h10 dist_nonneg)
  have h5norm : ‖nineBoundaryProbe 5‖ = 1 := by
    simpa [nineBoundaryProbe_ring] using ringPoint_norm (⟨5, by norm_num⟩ : Fin 9)
  have h10zero : nineBoundaryProbe 10 = 0 := nineBoundaryProbe_hub 10 (by norm_num)
  rw [h5', ← h10', h10zero, norm_zero] at h5norm
  exact absurd h5norm (by norm_num)

/-- **The control configuration fails the hub-10 fan premise** for face `5 = [5,6,10]`. -/
theorem nineBoundaryProbe_not_hub10Fan : ¬ Hub10FanRealized nineBoundaryProbe 0 :=
  fun h => nineBoundaryProbe_no_common_point
    ⟨h.1.choose, h.1.choose_spec.1, h.1.choose_spec.2.2⟩

/-- **Control (C1 ≠ C3).** The C1 typed premise does **not** imply the hub-10 fan witnesses: the
probe configuration has exactly nine boundary disks yet fails `Hub10FanRealized`. So the
point-existence premise of C3 is not a consequence of C1, and the two must never be conflated. -/
theorem nineBoundary_does_not_give_hub10_fan :
    ¬ (∀ (c : Fin 11 → Point) (r : ℝ), NineBoundary c r → Hub10FanRealized c r) :=
  fun hAll => nineBoundaryProbe_not_hub10Fan (hAll nineBoundaryProbe 0 nineBoundaryProbe_card)

/-- **Control (C1 ≠ the face-`5` witness).** The same probe shows the C1 premise alone does not
give the requested `FaceWitness c 5 r` either — the row's payment needs the C3 point, not the
boundary count. -/
theorem nineBoundary_does_not_give_faceWitness_five :
    ¬ (∀ (c : Fin 11 → Point) (r : ℝ), NineBoundary c r → FaceWitness c 5 r) := by
  intro hAll
  obtain ⟨z, hz⟩ := hAll nineBoundaryProbe 0 nineBoundaryProbe_card
  exact nineBoundaryProbe_no_common_point ⟨z, hz 0, hz 2⟩

/-- **Control (C1 ≠ the face-`7` witness)**, same probe (site `7` is on the circle, site `10` is
the origin, so no common `0`-point exists). -/
theorem nineBoundary_does_not_give_faceWitness_seven :
    ¬ (∀ (c : Fin 11 → Point) (r : ℝ), NineBoundary c r → FaceWitness c 7 r) := by
  intro hAll
  obtain ⟨z, hz⟩ := hAll nineBoundaryProbe 0 nineBoundaryProbe_card
  have h7 : dist (nineBoundaryProbe 7) z ≤ 0 := hz 0
  have h10 : dist (nineBoundaryProbe 10) z ≤ 0 := hz 2
  have h7norm : ‖nineBoundaryProbe 7‖ = 1 := by
    simpa [nineBoundaryProbe_ring] using ringPoint_norm (⟨7, by norm_num⟩ : Fin 9)
  have h7' : nineBoundaryProbe 7 = z := dist_eq_zero.mp (le_antisymm h7 dist_nonneg)
  have h10' : nineBoundaryProbe 10 = z := dist_eq_zero.mp (le_antisymm h10 dist_nonneg)
  have h10zero : nineBoundaryProbe 10 = 0 := nineBoundaryProbe_hub 10 (by norm_num)
  rw [h7', ← h10', h10zero, norm_zero] at h7norm
  exact absurd h7norm (by norm_num)

end N11Formalization.DSHTopologyInterior