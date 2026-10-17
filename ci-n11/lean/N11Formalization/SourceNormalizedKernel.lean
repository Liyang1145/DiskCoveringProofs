import N11Formalization.SourceB41ActualContraction

/-! Exact source homogeneous stresses from the proved actual
selected41 solve. No midpoint N, inverse-equality or BN=0 premise is supplied.
Must be gated only after SourceB41ActualContraction has actually built. -/
set_option autoImplicit false
namespace N11Formalization.SourceNormalizedKernel
open N11Formalization SourceN2 SourceB41Proposal SourceB41ActualContraction
noncomputable section

def columnEquiv : (Fin 41 ⊕ Fin 4) ≃ Fin 45 :=
  Equiv.ofBijective (Sum.elim dep freeCol) columns_bijective

@[simp] theorem columnEquiv_dep (i : Fin 41) : columnEquiv (.inl i) = dep i := rfl
@[simp] theorem columnEquiv_free (a : Fin 4) : columnEquiv (.inr a) = freeCol a := rfl

def rhs (a : Fin 4) (i : Fin 41) : ℝ :=
  -srcB2 SourceExactRoot.sourceRoot i (freeCol a)

def dependentColumn (a : Fin 4) : Fin 41 → ℝ := M⁻¹.mulVec (rhs a)

theorem dependentColumn_solve (a : Fin 4) : M.mulVec (dependentColumn a) = rhs a := by
  unfold dependentColumn
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr M_det_ne_zero),Matrix.one_mulVec]

def N (e : Fin 45) (a : Fin 4) : ℝ :=
  match columnEquiv.symm e with
  | .inl i => dependentColumn a i
  | .inr b => if b = a then 1 else 0

@[simp] theorem N_dep (i : Fin 41) (a : Fin 4) :
    N (dep i) a = dependentColumn a i := by
  rw [← columnEquiv_dep]
  simp only [N,Equiv.symm_apply_apply]

@[simp] theorem N_free (b a : Fin 4) :
    N (freeCol b) a = if b = a then 1 else 0 := by
  rw [← columnEquiv_free]
  simp only [N,Equiv.symm_apply_apply]

theorem all_B_rows (i : Fin 41) (a : Fin 4) :
    ∑ e : Fin 45, srcB2 SourceExactRoot.sourceRoot i e * N e a = 0 := by
  have hs := columnEquiv.sum_comp
    (fun e : Fin 45 => srcB2 SourceExactRoot.sourceRoot i e * N e a)
  rw [← hs,Fintype.sum_sum_type]
  simp only [columnEquiv_dep,columnEquiv_free,N_dep,N_free]
  have hd := congrFun (dependentColumn_solve a) i
  change (∑ j : Fin 41,
    srcB2 SourceExactRoot.sourceRoot i (dep j)*dependentColumn a j) =
    -srcB2 SourceExactRoot.sourceRoot i (freeCol a) at hd
  rw [hd]
  simp

theorem column_sum_zero (a : Fin 4) : ∑ e : Fin 45, N e a = 0 := by
  have h := all_B_rows 40 a
  simpa only [SourceBMatrixIntervals.actual_mass_row,one_mul] using h

/-- Free-coordinate readout proves linear independence of the four exact
homogeneous columns. No numerical rank or approximate equality premise. -/
theorem coefficients_zero (t : Fin 4 → ℝ)
    (ht : ∀ e : Fin 45, ∑ a : Fin 4, N e a*t a = 0) : t = 0 := by
  funext b
  have h := ht (freeCol b)
  simp only [N_free] at h
  simpa using h

def combine (t : Fin 4 → ℝ) (e : Fin 45) : ℝ := ∑ a : Fin 4, N e a*t a

theorem combine_free (t : Fin 4 → ℝ) (b : Fin 4) : combine t (freeCol b) = t b := by
  simp [combine,N_free]

theorem combine_B_rows (t : Fin 4 → ℝ) (i : Fin 41) :
    ∑ e : Fin 45, srcB2 SourceExactRoot.sourceRoot i e*combine t e = 0 := by
  simp only [combine,Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc,← Finset.sum_mul,all_B_rows,zero_mul]
  exact Finset.sum_const_zero

theorem zero_free_kernel (v : Fin 45 → ℝ)
    (hv : ∀ i : Fin 41, ∑ e : Fin 45, srcB2 SourceExactRoot.sourceRoot i e*v e = 0)
    (hf : ∀ b : Fin 4, v (freeCol b) = 0) : v = 0 := by
  have hd : M.mulVec (fun j : Fin 41 => v (dep j)) = 0 := by
    funext i
    have h := hv i
    have hs := columnEquiv.sum_comp
      (fun e : Fin 45 => srcB2 SourceExactRoot.sourceRoot i e*v e)
    rw [← hs,Fintype.sum_sum_type] at h
    simp only [columnEquiv_dep,columnEquiv_free,hf,mul_zero,Finset.sum_const_zero,
      add_zero] at h
    exact h
  have hd0 : (fun j : Fin 41 => v (dep j)) = 0 :=
    M_mulVec_injective (hd.trans (Matrix.mulVec_zero M).symm)
  funext e
  rcases h : columnEquiv.symm e with j | b
  · have he : e = dep j := by
      have hh := congrArg columnEquiv h
      simpa only [Equiv.apply_symm_apply,columnEquiv_dep] using hh
    rw [he]
    exact congrFun hd0 j
  · have he : e = freeCol b := by
      have hh := congrArg columnEquiv h
      simpa only [Equiv.apply_symm_apply,columnEquiv_free] using hh
    rw [he]
    exact hf b

/-- Every actual normalized homogeneous stress is uniquely reconstructed from
its four free coordinates. This is spanning, not just four independent columns. -/
theorem kernel_representation (v : Fin 45 → ℝ)
    (hv : ∀ i : Fin 41, ∑ e : Fin 45, srcB2 SourceExactRoot.sourceRoot i e*v e = 0) :
    v = combine (fun b : Fin 4 => v (freeCol b)) := by
  apply sub_eq_zero.mp
  apply zero_free_kernel
  · intro i
    simp only [Pi.sub_apply,mul_sub,Finset.sum_sub_distrib,hv,
      combine_B_rows,sub_self]
  · intro b
    simp only [Pi.sub_apply,combine_free,sub_self]

end
end N11Formalization.SourceNormalizedKernel
#check @N11Formalization.SourceNormalizedKernel.all_B_rows
#check @N11Formalization.SourceNormalizedKernel.column_sum_zero
#check @N11Formalization.SourceNormalizedKernel.coefficients_zero
#check @N11Formalization.SourceNormalizedKernel.kernel_representation
#print axioms N11Formalization.SourceNormalizedKernel.all_B_rows
#print axioms N11Formalization.SourceNormalizedKernel.kernel_representation
