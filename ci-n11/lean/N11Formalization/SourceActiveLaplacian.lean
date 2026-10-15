import N11Formalization.SourceH0PinnedReduction

/-! The ACTUAL20-node source free Laplacian is nonsingular. All45 source
weights are positive; its incidence is bound to the CORRECT Fin11 source
graph, not an abstract connectivity hypothesis. Source ring sites are grounded
by spokes, each auxiliary by a ring vertex, and both hubs by central face0.
The22-node canonical matrix still has two unweighted auxiliary null rows.
No invertibility, graph connectivity or numerical solve premise is supplied. -/
set_option autoImplicit false
namespace N11Formalization.SourceActiveLaplacian
open N11Formalization ResumeLocalIncidence HarmonicSourceTransport
noncomputable section

def spokeSite (k : Fin 9) (s : Fin 2) : Fin 11 :=
  ⟨(if s=0 then k else k+1).val,by omega⟩

def incidenceZ : SourceEdge → SrcFree → ℤ
  | .inl (k,s), v => if v=.inl (spokeSite k s) then 1 else 0
  | .inr (f,t), v =>
      (if v=.inl (sourceFaces f t) then 1 else 0)-
      (if v=.inr f then 1 else 0)

theorem incidenceZ_binding :
    ∀ e : SourceEdge, ∀ v : SrcFree,incidenceZ e v=srcIncZ e v := by decide

def B (e : SourceEdge) (v : SrcFree) : ℝ := (incidenceZ e v : ℝ)

theorem B_binding (e : SourceEdge) (v : SrcFree) : B e v=srcInc e v := by
  unfold B srcInc
  rw [incidenceZ_binding]

theorem B_canonical (e : SourceEdge) (v : SrcFree) :
    B e v=ResumeDirichlet.incidence (edgeMap e) (srcNode v) :=
  (B_binding e v).trans (incidence_edgeMap_eq_srcInc e v).symm

def gradient (x : SrcFree → ℝ) (e : SourceEdge) : ℝ := ∑ v : SrcFree,B e v*x v

theorem gradient_spoke (x : SrcFree → ℝ) (k : Fin 9) (s : Fin 2) :
    gradient x (.inl (k,s))=x (.inl (spokeSite k s)) := by
  simp [gradient,B,incidenceZ,cast_ite_int,Fintype.sum_sum_type]

theorem gradient_face (x : SrcFree → ℝ) (f : Fin 9) (t : Fin 3) :
    gradient x (.inr (f,t))=x (.inl (sourceFaces f t))-x (.inr f) := by
  simp [gradient,B,incidenceZ,cast_ite_int,Fintype.sum_sum_type,sub_mul,
    Finset.sum_sub_distrib]

/-- Concrete graph anchoring proof, no assumed connectivity. -/
theorem grounded_kernel (x : SrcFree → ℝ) (hx : ∀ e,gradient x e=0) : x=0 := by
  have hr (k : Fin 9) : x (.inl ⟨k.val,by omega⟩)=0 := by
    have h := hx (.inl (k,0))
    rw [gradient_spoke] at h
    exact h
  have hsite (i : Fin 11) (hi : i.val<9) : x (.inl i)=0 := by
    have h := hr (⟨i.val,hi⟩ : Fin 9)
    exact h
  have hfirst : ∀ f : Fin 9,(sourceFaces f 0).val<9 := by decide
  have ha (f : Fin 9) : x (.inr f)=0 := by
    have h := hx (.inr (f,0))
    rw [gradient_face,hsite _ (hfirst f)] at h
    linarith
  have hh9 : x (.inl (9 : Fin 11))=0 := by
    have h := hx (.inr (0,1))
    rw [gradient_face,ha] at h
    simpa [sourceFaces] using h
  have hh10 : x (.inl (10 : Fin 11))=0 := by
    have h := hx (.inr (0,2))
    rw [gradient_face,ha] at h
    simpa [sourceFaces] using h
  funext v
  rcases v with i | f
  · by_cases hi : i.val<9
    · exact hsite i hi
    · have hcases : i=9 ∨ i=10 := by
        have hlt := i.isLt
        have h9 : i.val=9 ∨ i.val=10 := by omega
        rcases h9 with h9 | h10
        · exact Or.inl (Fin.ext h9)
        · exact Or.inr (Fin.ext h10)
      rcases hcases with rfl | rfl
      · exact hh9
      · exact hh10
  · exact ha f

def A : Matrix SrcFree SrcFree ℝ :=
  LaplacianSchurBridge.freeBlock SourceSignedStressAssembly.stress B

theorem A_symmetric (v w : SrcFree) : A v w=A w v := by
  unfold A LaplacianSchurBridge.freeBlock
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem A_mulVec (x : SrcFree → ℝ) (v : SrcFree) :
    A.mulVec x v=∑ e : SourceEdge,SourceSignedStressAssembly.stress e*B e v*gradient x e := by
  simp only [Matrix.mulVec,dotProduct,A,LaplacianSchurBridge.freeBlock,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [gradient,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  ring

theorem quadratic_energy (x : SrcFree → ℝ) :
    (∑ v : SrcFree,x v*A.mulVec x v)=
      ∑ e : SourceEdge,SourceSignedStressAssembly.stress e*(gradient x e)^2 := by
  simp_rw [A_mulVec,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  have he :
      (∑ v : SrcFree,x v*(SourceSignedStressAssembly.stress e*B e v*gradient x e))=
        SourceSignedStressAssembly.stress e*gradient x e*(∑ v : SrcFree,B e v*x v) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [he]
  change SourceSignedStressAssembly.stress e*gradient x e*gradient x e=
    SourceSignedStressAssembly.stress e*(gradient x e)^2
  ring

theorem A_kernel_zero (x : SrcFree → ℝ) (hx : A.mulVec x=0) : x=0 := by
  have henergy : ∑ e : SourceEdge,SourceSignedStressAssembly.stress e*(gradient x e)^2=0 := by
    rw [← quadratic_energy,hx]
    simp
  have ht (e : SourceEdge) :
      SourceSignedStressAssembly.stress e*(gradient x e)^2=0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun e _ =>
      mul_nonneg (SourceBoundaryStressPositive.stress_pos e).le (sq_nonneg _))).mp
        henergy e (Finset.mem_univ e)
  apply grounded_kernel x
  intro e
  have hsq : (gradient x e)^2=0 :=
    (mul_eq_zero.mp (ht e)).resolve_left (ne_of_gt (SourceBoundaryStressPositive.stress_pos e))
  exact eq_zero_of_pow_eq_zero hsq

/-- The source's ACTUAL20 free block is injective, unlike the canonical22 block. -/
theorem A_mulVec_injective : Function.Injective A.mulVec := by
  intro x y hxy
  have hz : A.mulVec (x-y)=0 := by
    rw [Matrix.mulVec_sub,hxy,sub_self]
  exact sub_eq_zero.mp (A_kernel_zero _ hz)

theorem A_isUnit : IsUnit A := Matrix.mulVec_injective_iff_isUnit.mp A_mulVec_injective

theorem A_det_ne_zero : A.det≠0 := ((Matrix.isUnit_iff_isUnit_det A).mp A_isUnit).ne_zero

end
end N11Formalization.SourceActiveLaplacian
#check @N11Formalization.SourceActiveLaplacian.incidenceZ_binding
#check @N11Formalization.SourceActiveLaplacian.grounded_kernel
#check @N11Formalization.SourceActiveLaplacian.A_mulVec_injective
#check @N11Formalization.SourceActiveLaplacian.A_det_ne_zero
#print axioms N11Formalization.SourceActiveLaplacian.A_det_ne_zero
