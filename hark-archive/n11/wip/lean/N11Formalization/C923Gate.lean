import N11Formalization.C921Sem
import N11Formalization.Assembly.BoundaryCount

namespace N11Formalization.C921Sem

open N11Formalization.LeafAgg          -- leafCheck, lsum
open N11Formalization.G3LeafChecker    -- leafBound_of_check / _batch / _floorData, ...
open N11Formalization.G3ArcConstants   -- scaleD, arcLlo, arcLhi, thresh, threshSq, arc_hyp_*

namespace C923Gate
open N11Formalization N11Formalization.C921Sem

/-- The hc923 slot type, verbatim. -/
def HC923Slot (V2 : (Fin 8 → ℝ) → ℝ) : Prop :=
  ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r → ∃ y : Fin 8 → ℝ, InSimplex y ∧ V2 y ≤ r ^ 2

/-- **C923 (named, conditional)**.  `Anch c r y` = "y is the anchor/deficit vector of the
canonical representative c" (opaque; pinning it to the source anchor map is a gap).
* `rep`  : [A+B1] every cover (0≤r<19/50) has a canonical representative c' (still a cover)
           with anchors y in the closed 8-simplex;
* `relax`: [B2] one-way oracle relaxation, squared form: anchors of a cover ⇒ V2 y ≤ r²;
* `top`  : large-r residue: some simplex point has V2 ≤ (19/50)². -/
structure C923Prop (V2 : (Fin 8 → ℝ) → ℝ)
    (Anch : (Fin 11 → Point) → ℝ → (Fin 8 → ℝ) → Prop) : Prop where
  rep : ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → r < 19 / 50 → Covers c r →
    ∃ c' : Fin 11 → Point, Covers c' r ∧ ∃ y, InSimplex y ∧ Anch c' r y
  relax : ∀ (r : ℝ) (c' : Fin 11 → Point) (y : Fin 8 → ℝ), 0 ≤ r → Covers c' r →
    Anch c' r y → V2 y ≤ r ^ 2
  top : ∃ y : Fin 8 → ℝ, InSimplex y ∧ V2 y ≤ ((19 : ℝ) / 50) ^ 2

/-- Kernel-paid add-on: the representative has ≥ 9 boundary disks. -/
theorem rep_nine {V2 Anch} (h : C923Prop V2 Anch) {r : ℝ} {c : Fin 11 → Point}
    (hr0 : 0 ≤ r) (hr : r < 19 / 50) (hc : Covers c r) :
    ∃ c' : Fin 11 → Point, Covers c' r ∧ 9 ≤ Fintype.card (BoundaryIdx c' r) ∧
      ∃ y, InSimplex y ∧ Anch c' r y := by
  obtain ⟨c', hc', hy⟩ := h.rep r c hr0 hr hc
  exact ⟨c', hc', nine_le_card_boundary hr0 hr hc', hy⟩

/-- C923Prop fills the hc923 slot. -/
theorem hc923_of_C923 {V2 Anch} (h : C923Prop V2 Anch) : HC923Slot V2 := by
  intro r c hr hcov
  by_cases hs : r < 19 / 50
  · obtain ⟨c', hc', y, hyS, hA⟩ := h.rep r c hr hs hcov
    exact ⟨y, hyS, h.relax r c' y hr hc' hA⟩
  · obtain ⟨y, hyS, hV⟩ := h.top
    refine ⟨y, hyS, hV.trans ?_⟩
    have : (19 : ℝ) / 50 ≤ r := le_of_not_gt hs
    nlinarith

/-- **Wiring**: C923Prop plugged into `hbound_of_c921`. -/
theorem hbound_of_C923 {S : C891RootSpec} {V2 Anch} (h : C923Prop V2 Anch)
    (hRpin : Rstar S ≤ threshR) (hglob : ∀ y : Fin 8 → ℝ, InSimplex y → V2 y > threshR ^ 2)
    (r : ℝ) (c : Fin 11 → Point) (hr : 0 ≤ r) (hcov : Covers c r) : Rstar S ≤ r :=
  hbound_of_c921 (hc923_of_C923 h) hRpin hglob r c hr hcov

theorem n11_main_of_C923 (S : C891RootSpec) {V2 Anch}
    (hattain : ∃ c : Fin 11 → Point, Covers c (Rstar S)) (h : C923Prop V2 Anch)
    (hRpin : Rstar S ≤ threshR) (hglob : ∀ y : Fin 8 → ℝ, InSimplex y → V2 y > threshR ^ 2) :
    N11MainStatement (Rstar S) :=
  n11_main_of_c921 S hattain (hc923_of_C923 h) hRpin hglob

end C923Gate
end N11Formalization.C921Sem
