import N11Formalization.CartesianPolarFrame
import N11Formalization.PhysicalResidualFrame
import N11Formalization.ReflectionCovectorLift

/-!
Full Cartesian23 space: 22 independent center coordinates followed by radius.
The reflection permutes ring k with ring 8-k and reflects the vertical
coordinate. Both hubs and the radius are fixed. The 12D Cartesian map is
identified with the ENTIRE fixed space, not a dimension-count assertion.
-/
set_option autoImplicit false
namespace N11Formalization.CartesianReflectionSpace
open N11Formalization
noncomputable section

abbrev Full := Fin 23 → ℝ
abbrev Fixed := Fin 12 → ℝ

def reflect (x : Full) : Full :=
  ![x 16, -x 17, x 14, -x 15, x 12, -x 13, x 10, -x 11,
    x 8, -x 9, x 6, -x 7, x 4, -x 5, x 2, -x 3, x 0, -x 1,
    x 18, -x 19, x 20, -x 21, x 22]

def embed (q : Fixed) : Full :=
  ![q 0, q 1, q 2, q 3, q 4, q 5, q 6, q 7, q 8, 0,
    q 6, -q 7, q 4, -q 5, q 2, -q 3, q 0, -q 1,
    q 9, 0, q 10, 0, q 11]

def extract (x : Full) : Fixed :=
  ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 18, x 20, x 22]

def reflectLinear : Full →ₗ[ℝ] Full where
  toFun := reflect
  map_add' := by
    intro x y
    funext i
    fin_cases i <;> simp [reflect] <;> ring
  map_smul' := by
    intro r x
    funext i
    fin_cases i <;> simp [reflect, smul_eq_mul]

def embedLinear : Fixed →ₗ[ℝ] Full where
  toFun := embed
  map_add' := by
    intro x y
    funext i
    fin_cases i <;> simp [embed] <;> ring
  map_smul' := by
    intro r x
    funext i
    fin_cases i <;> simp [embed, smul_eq_mul]

def embedCLM : Fixed →L[ℝ] Full := embedLinear.toContinuousLinearMap
def reflectCLM : Full →L[ℝ] Full := reflectLinear.toContinuousLinearMap

@[simp] theorem embedCLM_apply (q : Fixed) : embedCLM q = embed q := rfl
@[simp] theorem reflectCLM_apply (x : Full) : reflectCLM x = reflect x := rfl

theorem reflect_involution (x : Full) : reflect (reflect x) = x := by
  funext i
  fin_cases i <;> simp [reflect]

theorem reflect_embed (q : Fixed) : reflect (embed q) = embed q := by
  funext i
  fin_cases i <;> simp [reflect, embed]

theorem extract_embed (q : Fixed) : extract (embed q) = q := by
  funext i
  fin_cases i <;> simp [extract, embed]

theorem embed_injective : Function.Injective embed := by
  intro q r h
  have he := congrArg extract h
  simpa only [extract_embed] using he

theorem embed_extract_of_fixed (x : Full) (hx : reflect x = x) :
    embed (extract x) = x := by
  have hs (i : Fin 23) := congrFun hx i
  have h9 := hs 9
  have h10 := hs 10
  have h11 := hs 11
  have h12 := hs 12
  have h13 := hs 13
  have h14 := hs 14
  have h15 := hs 15
  have h16 := hs 16
  have h17 := hs 17
  have h19 := hs 19
  have h21 := hs 21
  simp [reflect] at h9 h10 h11 h12 h13 h14 h15 h16 h17 h19 h21
  funext i
  fin_cases i <;> simp [embed, extract] <;> linarith

theorem fixed_iff_embed (x : Full) :
    reflect x = x ↔ ∃! q : Fixed, embed q = x := by
  constructor
  · intro hx
    refine ⟨extract x, embed_extract_of_fixed x hx, ?_⟩
    intro q hq
    have he := congrArg extract hq
    simpa only [extract_embed] using he
  · rintro ⟨q, hq, _⟩
    rw [← hq]
    exact reflect_embed q

/-- The full source center map, with actual TC centers, not an abstract symmetric surrogate. -/
def pack (u : Fin 12 → ℝ) : Full :=
  ![(ringCenter u 0) 0, (ringCenter u 0) 1,
    (ringCenter u 1) 0, (ringCenter u 1) 1,
    (ringCenter u 2) 0, (ringCenter u 2) 1,
    (ringCenter u 3) 0, (ringCenter u 3) 1,
    (ringCenter u 4) 0, (ringCenter u 4) 1,
    (ringCenter u 5) 0, (ringCenter u 5) 1,
    (ringCenter u 6) 0, (ringCenter u 6) 1,
    (ringCenter u 7) 0, (ringCenter u 7) 1,
    (ringCenter u 8) 0, (ringCenter u 8) 1,
    u 4, 0, u 5, 0, u 6]

def frameCartesian (x : Fixed) : Fixed :=
  CartesianPolarFrame.cartesian (CoupledRadialFrame.radialFrame x)

/-- Complete pointwise identity, for arbitrary independent Frame, including reflected rings. -/
theorem embedded_frame_centers (x : Fixed) (k : Fin 9) :
    !₂[(embed (frameCartesian x)) ⟨2*k.val, by omega⟩,
       (embed (frameCartesian x)) ⟨2*k.val+1, by omega⟩] =
      PhysicalResidualFrame.center x k := by
  ext i
  fin_cases k <;> fin_cases i <;>
    simp [frameCartesian, CartesianPolarFrame.cartesian, CoupledRadialFrame.radialFrame,
      WidthRadialDerivative.rhoMinus, embed, PhysicalResidualFrame.center,
      PhysicalResidualFrame.radial, PhysicalResidualFrame.widths,
      PhysicalResidualFrame.directions]

theorem embed_frame_source (u : Fin 12 → ℝ) :
    embed (frameCartesian (BoundaryChartSource.sourceFrame u)) = pack u := by
  have hc (k : Fin 9) :
      !₂[(embed (frameCartesian (BoundaryChartSource.sourceFrame u))) ⟨2*k.val, by omega⟩,
        (embed (frameCartesian (BoundaryChartSource.sourceFrame u))) ⟨2*k.val+1, by omega⟩] =
        ringCenter u k :=
    (embedded_frame_centers (BoundaryChartSource.sourceFrame u) k).trans
      (PhysicalResidualFrame.center_source u k)
  funext i
  fin_cases i
  · exact congrArg (fun p : Point => p 0) (hc 0)
  · exact congrArg (fun p : Point => p 1) (hc 0)
  · exact congrArg (fun p : Point => p 0) (hc 1)
  · exact congrArg (fun p : Point => p 1) (hc 1)
  · exact congrArg (fun p : Point => p 0) (hc 2)
  · exact congrArg (fun p : Point => p 1) (hc 2)
  · exact congrArg (fun p : Point => p 0) (hc 3)
  · exact congrArg (fun p : Point => p 1) (hc 3)
  · exact congrArg (fun p : Point => p 0) (hc 4)
  · exact congrArg (fun p : Point => p 1) (hc 4)
  · exact congrArg (fun p : Point => p 0) (hc 5)
  · exact congrArg (fun p : Point => p 1) (hc 5)
  · exact congrArg (fun p : Point => p 0) (hc 6)
  · exact congrArg (fun p : Point => p 1) (hc 6)
  · exact congrArg (fun p : Point => p 0) (hc 7)
  · exact congrArg (fun p : Point => p 1) (hc 7)
  · exact congrArg (fun p : Point => p 0) (hc 8)
  · exact congrArg (fun p : Point => p 1) (hc 8)
  all_goals simp [pack, embed, frameCartesian, CartesianPolarFrame.cartesian,
    CoupledRadialFrame.radialFrame, BoundaryChartSource.sourceFrame]

theorem source_fixed : reflect (pack SourceExactRoot.sourceRoot) =
    pack SourceExactRoot.sourceRoot := by
  rw [← embed_frame_source]
  exact reflect_embed _

/-- Actual finite-dimensional consumer of the coordinate-free lift.
Invariance and zero on every independent fixed Cartesian direction remain explicit. -/
theorem covector_zero_of_embed_zero (ℓ : Full →ₗ[ℝ] ℝ)
    (hinv : ∀ x : Full, ℓ (reflect x) = ℓ x)
    (hfix : ∀ q : Fixed, ℓ (embed q) = 0) : ℓ = 0 := by
  apply ReflectionCovectorLift.invariant_zero_of_fixed_zero reflectLinear
    reflect_involution ℓ hinv
  intro x hx
  change reflect x = x at hx
  rw [← embed_extract_of_fixed x hx]
  exact hfix _

end
end N11Formalization.CartesianReflectionSpace
#check @N11Formalization.CartesianReflectionSpace.fixed_iff_embed
#check @N11Formalization.CartesianReflectionSpace.embed_frame_source
#check @N11Formalization.CartesianReflectionSpace.covector_zero_of_embed_zero
#print axioms N11Formalization.CartesianReflectionSpace.embed_frame_source
#print axioms N11Formalization.CartesianReflectionSpace.covector_zero_of_embed_zero
