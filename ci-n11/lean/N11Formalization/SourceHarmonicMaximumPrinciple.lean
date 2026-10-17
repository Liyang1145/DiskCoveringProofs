import N11Formalization.SourceActiveAffineResponse
import N11Formalization.SourceActiveFiniteSystem

/-! Analytic maximum principle for the SAME actual20-node harmonic matrix.
The concrete corrected Fin11 incidence, all45 positive source stresses and
actual column balance discharge every geometric/positivity premise. Negative
parts are a test vector, not a replacement of the actual harmonic solution.
No N/G/coercivity/global optimality statement is inferred from these signs. -/
set_option autoImplicit false
namespace N11Formalization.SourceHarmonicMaximumPrinciple
open N11Formalization ResumeLocalIncidence HarmonicSourceTransport
open SourceActiveLaplacian SourceActiveHarmonicSolve SourceActiveAffineResponse
open SourceActiveFiniteSystem SourceResponseFluxIdentity
noncomputable section

theorem negative_part_product (x y : ℝ) :
    (min x 0 - min y 0) ^ 2 ≤ (x - y) * (min x 0 - min y 0) := by
  by_cases hx : x ≤ 0
  · rw [min_eq_left hx]
    by_cases hy : y ≤ 0
    · rw [min_eq_left hy]
      nlinarith
    · rw [min_eq_right (le_of_not_ge hy)]
      have hxy := mul_nonpos_of_nonpos_of_nonneg hx (le_of_not_ge hy)
      nlinarith
  · rw [min_eq_right (le_of_not_ge hx)]
    by_cases hy : y ≤ 0
    · rw [min_eq_left hy]
      have hxy := mul_nonpos_of_nonneg_of_nonpos (le_of_not_ge hx) hy
      nlinarith
    · rw [min_eq_right (le_of_not_ge hy)]
      simp

theorem anchorRow_spoke (k : Fin 9) (s : Fin 2) (j : Fin 9) :
    anchorRow (.inl (k,s)) j = if siteMap k = j then -1 else 0 := by
  have hnext : ResumeNetwork.anchorIndex (siteMap (k+1)) 0 = siteMap k := by
    fin_cases k <;> decide
  by_cases hs : s = 0
  · simp [anchorRow,edgeMap,ResumeAnchorFlux.anchorIncidence,
      ResumeNetwork.anchorIndex,hs]
  · simp only [anchorRow,edgeMap,if_neg hs,ResumeAnchorFlux.anchorIncidence,hnext]

theorem K_spoke (k : Fin 9) (s : Fin 2) (j : Fin 9) :
    K (.inl (k,s)) j =
      activeH (.inl (spokeSite k s)) j - (if siteMap k = j then 1 else 0) := by
  change anchorRow (.inl (k,s)) j +
    SourceActiveLaplacian.gradient (fun v => activeH v j) (.inl (k,s)) = _
  rw [anchorRow_spoke,gradient_spoke]
  split_ifs <;> ring

theorem K_face (f : Fin 9) (t : Fin 3) (j : Fin 9) :
    K (.inr (f,t)) j =
      activeH (.inl (sourceFaces f t)) j - activeH (.inr f) j := by
  change anchorRow (.inr (f,t)) j +
    SourceActiveLaplacian.gradient (fun v => activeH v j) (.inr (f,t)) = _
  rw [gradient_face]
  simp [anchorRow,edgeMap,ResumeAnchorFlux.anchorIncidence]

def negativeColumn (j : Fin 9) (v : SrcFree) : ℝ := min (activeH v j) 0

theorem negative_gradient_bound (j : Fin 9) (e : SourceEdge) :
    (SourceActiveLaplacian.gradient (negativeColumn j) e)^2 ≤
      K e j * SourceActiveLaplacian.gradient (negativeColumn j) e := by
  rcases e with ⟨k,s⟩ | ⟨f,t⟩
  · rw [gradient_spoke,K_spoke]
    unfold negativeColumn
    have hb : min (if siteMap k = j then (1 : ℝ) else 0) 0 = 0 := by
      split_ifs <;> norm_num
    have h := negative_part_product (activeH (.inl (spokeSite k s)) j)
      (if siteMap k = j then 1 else 0)
    rw [hb,sub_zero] at h
    exact h
  · rw [gradient_face,K_face]
    exact negative_part_product _ _

theorem negative_test_zero (j : Fin 9) :
    ∑ e : SourceEdge, SourceSignedStressAssembly.stress e * K e j *
      SourceActiveLaplacian.gradient (negativeColumn j) e = 0 := by
  have hsum :
      (∑ e : SourceEdge, SourceSignedStressAssembly.stress e * K e j *
        SourceActiveLaplacian.gradient (negativeColumn j) e) =
      ∑ v : SrcFree, negativeColumn j v *
        ∑ e : SourceEdge, (SourceSignedStressAssembly.stress e * B e v) * K e j := by
    simp only [SourceActiveLaplacian.gradient,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hsum]
  simp only [active_balance,mul_zero,Finset.sum_const_zero]

theorem negativeColumn_zero (j : Fin 9) : negativeColumn j = 0 := by
  have hnonneg (e : SourceEdge) :
      0 ≤ SourceSignedStressAssembly.stress e * K e j *
        SourceActiveLaplacian.gradient (negativeColumn j) e := by
    have hg := (sq_nonneg _).trans (negative_gradient_bound j e)
    have h := mul_nonneg (SourceBoundaryStressPositive.stress_pos e).le hg
    simpa only [mul_assoc] using h
  have hterm (e : SourceEdge) :
      SourceSignedStressAssembly.stress e * K e j *
        SourceActiveLaplacian.gradient (negativeColumn j) e = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => hnonneg e)).mp
      (negative_test_zero j) e (Finset.mem_univ e)
  apply grounded_kernel
  intro e
  have hz : K e j * SourceActiveLaplacian.gradient (negativeColumn j) e = 0 := by
    apply (mul_eq_zero.mp _).resolve_left
      (ne_of_gt (SourceBoundaryStressPositive.stress_pos e))
    simpa only [mul_assoc] using hterm e
  have hg := negative_gradient_bound j e
  rw [hz] at hg
  have hsq : (SourceActiveLaplacian.gradient (negativeColumn j) e)^2 = 0 :=
    le_antisymm hg (sq_nonneg _)
  exact eq_zero_of_pow_eq_zero hsq

/-- ALL180 entries of the actual sourceH restriction are nonnegative. -/
theorem activeH_nonneg (v : SrcFree) (j : Fin 9) : 0 ≤ activeH v j := by
  have h := congrFun (negativeColumn_zero j) v
  change min (activeH v j) 0 = 0 at h
  rw [← h]
  exact min_le_left _ _

theorem activeH_le_one (v : SrcFree) (j : Fin 9) : activeH v j ≤ 1 := by
  have h : activeH v j ≤ ∑ k : Fin 9, activeH v k :=
    Finset.single_le_sum (fun k _ => activeH_nonneg v k) (Finset.mem_univ j)
  rw [activeH_affine] at h
  exact h

theorem H20_bounds (i : Fin 20) (j : Fin 9) :
    0 ≤ H20 j i ∧ H20 j i ≤ 1 :=
  ⟨activeH_nonneg (nodeEquiv.symm i) j, activeH_le_one (nodeEquiv.symm i) j⟩

theorem actual_response_anchor_flux (i j : Fin 9) :
    sourceResponse i j =
      ∑ e : SourceEdge, SourceSignedStressAssembly.stress e * anchorRow e i * K e j := by
  rw [response_active]
  exact LaplacianSchurBridge.gram_eq_anchor_flux
    SourceSignedStressAssembly.stress B anchorRow activeH active_balance i j

/-- Actual response has nonpositive off-diagonal entries, analytically.
No rational midpoint or interval-sign premise is used. -/
theorem response_offdiag_nonpos (i j : Fin 9) (hij : i ≠ j) :
    sourceResponse i j ≤ 0 := by
  rw [actual_response_anchor_flux]
  apply Finset.sum_nonpos
  intro e _
  rcases e with ⟨k,s⟩ | ⟨f,t⟩
  · rw [anchorRow_spoke,K_spoke]
    by_cases hki : siteMap k = i
    · have hkj : siteMap k ≠ j := fun hj => hij (hki.symm.trans hj)
      simp only [if_pos hki,if_neg hkj,sub_zero,mul_neg,mul_one]
      exact mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (SourceBoundaryStressPositive.stress_pos _).le)
        (activeH_nonneg _ _)
    · simp only [if_neg hki,mul_zero,zero_mul,le_refl]
  · simp [anchorRow,edgeMap,ResumeAnchorFlux.anchorIncidence]

theorem actual_pair_weight_nonneg (i j : Fin 9) (hij : i < j) :
    0 ≤ -sourceResponse i j :=
  neg_nonneg.mpr (response_offdiag_nonpos i j (ne_of_lt hij))

/-- The SAME actual36-pair weights are nonnegative and their energy bounds the
51-edge oracle for EVERY angular tuple; no source-response sign premise. -/
theorem actual_positive_pair_oracle (θ : Fin 9 → ℝ) :
    (∀ i j : Fin 9, i < j → 0 ≤ -sourceResponse i j) ∧
      (2 * ∑ i : Fin 9, ∑ j : Fin 9, if i < j then
        -sourceResponse i j * (1 - Real.cos (θ i - θ j)) else 0) ≤
          ResumeNetwork.V2 (fun j => circleMap (θ j)) :=
  ⟨actual_pair_weight_nonneg, actual_pair_le_oracle θ⟩

end
end N11Formalization.SourceHarmonicMaximumPrinciple
#check @N11Formalization.SourceHarmonicMaximumPrinciple.H20_bounds
#check @N11Formalization.SourceHarmonicMaximumPrinciple.response_offdiag_nonpos
#check @N11Formalization.SourceHarmonicMaximumPrinciple.actual_positive_pair_oracle
#print axioms N11Formalization.SourceHarmonicMaximumPrinciple.activeH_nonneg
#print axioms N11Formalization.SourceHarmonicMaximumPrinciple.actual_positive_pair_oracle
