import N11Formalization.SourceActiveHarmonicSolve
import N11Formalization.ResumeLinearSolveEnclosure

/-! Fin20 certification layout for the ACTUAL harmonic solve: slots0..10 are
correct Fin11 sites and slots11..19 are source face auxiliaries. The exact
matrix/solution/sourceH identity is paid, not a numerical equality premise.
The final interval consumer retains its rational enclosure/contraction checks:
no actual numerical enclosure is claimed until those checks are instantiated. -/
set_option autoImplicit false
namespace N11Formalization.SourceActiveFiniteSystem
open N11Formalization HarmonicSourceTransport SourceActiveLaplacian
open SourceActiveHarmonicSolve RatInterval
noncomputable section

def nodeEquiv : SrcFree ≃ Fin 20 := finSumFinEquiv
def matrix20 : Matrix (Fin 20) (Fin 20) ℝ :=
  fun i j => A (nodeEquiv.symm i) (nodeEquiv.symm j)
def rhs20 (j : Fin 9) : Fin 20 → ℝ := fun i => rhs (nodeEquiv.symm i) j
def H20 (j : Fin 9) : Fin 20 → ℝ := fun i => activeH (nodeEquiv.symm i) j

theorem site_slot (i : Fin 11) :
    nodeEquiv (.inl i)=Fin.castAdd 9 i := rfl

theorem face_slot (f : Fin 9) :
    nodeEquiv (.inr f)=Fin.natAdd 11 f := rfl

theorem matrix20_action (x : Fin 20 → ℝ) (i : Fin 20) :
    matrix20.mulVec x i=A.mulVec (fun v => x (nodeEquiv v)) (nodeEquiv.symm i) := by
  have h := nodeEquiv.symm.sum_comp
    (fun v : SrcFree => A (nodeEquiv.symm i) v*x (nodeEquiv v))
  simpa only [matrix20,Matrix.mulVec,dotProduct,Equiv.apply_symm_apply] using h

theorem H20_solve (j : Fin 9) : matrix20.mulVec (H20 j)=rhs20 j := by
  funext i
  rw [matrix20_action]
  have h := congrFun (activeH_solve j) (nodeEquiv.symm i)
  simpa only [H20,rhs20,Equiv.symm_apply_apply] using h

theorem matrix20_injective : Function.Injective matrix20.mulVec := by
  intro x y hxy
  have h : A.mulVec (fun v => x (nodeEquiv v))=
      A.mulVec (fun v => y (nodeEquiv v)) := by
    funext v
    have hh := congrFun hxy (nodeEquiv v)
    simpa only [matrix20_action,Equiv.symm_apply_apply] using hh
  have hh := A_mulVec_injective h
  funext i
  have hi := congrFun hh (nodeEquiv.symm i)
  simpa only [Equiv.apply_symm_apply] using hi

theorem H20_unique (j : Fin 9) (x : Fin 20 → ℝ)
    (hx : matrix20.mulVec x=rhs20 j) : x=H20 j :=
  matrix20_injective (hx.trans (H20_solve j).symm)

theorem H20_actual_site (j : Fin 9) (i : Fin 11) :
    H20 j (Fin.castAdd 9 i)=
      SourcePositiveHarmonicConsumer.sourceH (srcNode (.inl i)) j := by
  change activeH (nodeEquiv.symm (nodeEquiv (.inl i))) j=_
  rw [Equiv.symm_apply_apply]
  rfl

theorem H20_actual_face (j : Fin 9) (f : Fin 9) :
    H20 j (Fin.natAdd 11 f)=
      SourcePositiveHarmonicConsumer.sourceH (srcNode (.inr f)) j := by
  change activeH (nodeEquiv.symm (nodeEquiv (.inr f))) j=_
  rw [Equiv.symm_apply_apply]
  rfl

/-- A real actual-H coordinate consumer. The solution-equation/source-identity
premises are eliminated; actual rational enclosure and contraction readouts
remain honestly explicit and are NOT claimed paid by this theorem. -/
theorem H20_coordinates_of_certificate
    (j : Fin 9) (C : Matrix (Fin 20) (Fin 20) ℚ)
    (AB : Fin 20 → Fin 20 → RatInterval) (bB : Fin 20 → RatInterval)
    (y : Fin 20 → ℚ) (q err : ℝ) (hq : 0≤q) (hq1 : q<1) (herr : 0≤err)
    (hA : ∀ i k,(AB i k).Mem (matrix20 i k))
    (hb : ∀ i,(bB i).Mem (rhs20 j i))
    (hrow : ∀ i,∑ k : Fin 20,
      max |((krawczykMat C AB i k).lo : ℝ)| |((krawczykMat C AB i k).hi : ℝ)|≤q)
    (hresidual : ∀ i,
      max |((ResumeLinearSolveEnclosure.residualBox C AB bB y i).lo : ℝ)|
        |((ResumeLinearSolveEnclosure.residualBox C AB bB y i).hi : ℝ)|≤err)
    (i : Fin 20) :
    (y i : ℝ)-err/(1-q)≤H20 j i ∧ H20 j i≤(y i : ℝ)+err/(1-q) :=
  ResumeLinearSolveEnclosure.solution_coordinates matrix20 C AB bB (rhs20 j) (H20 j)
    y q err hq1 herr
    (ResumeLinearSolveInterval.residual_bound matrix20 C AB q hq hA hrow)
    hA hb hresidual (H20_solve j) i

end
end N11Formalization.SourceActiveFiniteSystem
#check @N11Formalization.SourceActiveFiniteSystem.H20_solve
#check @N11Formalization.SourceActiveFiniteSystem.H20_actual_site
#check @N11Formalization.SourceActiveFiniteSystem.H20_actual_face
#check @N11Formalization.SourceActiveFiniteSystem.H20_coordinates_of_certificate
#print axioms N11Formalization.SourceActiveFiniteSystem.H20_solve
#print axioms N11Formalization.SourceActiveFiniteSystem.H20_coordinates_of_certificate
