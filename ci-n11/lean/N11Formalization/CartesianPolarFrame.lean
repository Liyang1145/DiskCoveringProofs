import N11Formalization.CoupledRadialFrame

/-!
Independent reflection-fixed Cartesian coordinates: four ring pairs contribute
eight Cartesian coordinates; ring4, two hubs and R each contribute one.
This is a genuine 12D coordinate change, not a TC chart dimension count.
The explicit derivative has four invertible polar blocks and four identity
coordinates. Source radial nondegeneracy is proved from the frozen exact root.
-/
set_option autoImplicit false
namespace N11Formalization.CartesianPolarFrame
open N11Formalization CoupledRadialFrame BoundaryChartSource
noncomputable section

def cartesian (y : Frame) : Frame :=
  ![y 0 * Real.cos (y 5), y 0 * Real.sin (y 5),
    y 1 * Real.cos (y 6), y 1 * Real.sin (y 6),
    y 2 * Real.cos (y 7), y 2 * Real.sin (y 7),
    y 3 * Real.cos (y 8), y 3 * Real.sin (y 8),
    y 4, y 9, y 10, y 11]

def polarBlock (r c s : ℝ) (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![c * v 0 - r * s * v 1, s * v 0 + r * c * v 1]

def polarBlockInv (r c s : ℝ) (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![c * v 0 + s * v 1, (-s * v 0 + c * v 1) / r]

theorem polarBlock_left_inverse (r c s : ℝ) (hr : r ≠ 0)
    (hcs : s^2 + c^2 = 1) (v : Fin 2 → ℝ) :
    polarBlockInv r c s (polarBlock r c s v) = v := by
  funext i
  fin_cases i
  · simp only [polarBlockInv, polarBlock, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hi : (⟨0, by omega⟩ : Fin 2) = 0 := by apply Fin.ext; rfl
    rw [hi]
    have h0 : c * (c * v 0 - r * s * v 1) + s * (s * v 0 + r * c * v 1) =
        (s^2 + c^2) * v 0 := by ring
    simpa [hcs] using h0
  · simp only [polarBlockInv, polarBlock, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hi : (⟨1, by omega⟩ : Fin 2) = 1 := by apply Fin.ext; rfl
    rw [hi]
    apply (div_eq_iff hr).mpr
    have h1 : -s * (c * v 0 - r * s * v 1) + c * (s * v 0 + r * c * v 1) =
        r * (s^2 + c^2) * v 1 := by ring
    simpa [hcs, mul_comm] using h1

theorem polarBlock_right_inverse (r c s : ℝ) (hr : r ≠ 0)
    (hcs : s^2 + c^2 = 1) (v : Fin 2 → ℝ) :
    polarBlock r c s (polarBlockInv r c s v) = v := by
  funext i
  fin_cases i <;> simp only [polarBlockInv, polarBlock,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  · field_simp
    have hi : (⟨0, by omega⟩ : Fin 2) = 0 := by apply Fin.ext; rfl
    rw [hi]
    have h0 : c * (c * v 0 + s * v 1) - s * (-s * v 0 + c * v 1) =
        (s^2 + c^2) * v 0 := by ring
    simpa [hcs, mul_comm] using h0
  · field_simp
    have hi : (⟨1, by omega⟩ : Fin 2) = 1 := by apply Fin.ext; rfl
    rw [hi]
    have h1 : s * (c * v 0 + s * v 1) + c * (-s * v 0 + c * v 1) =
        (s^2 + c^2) * v 1 := by ring
    simpa [hcs, mul_comm] using h1

def jacobian (y v : Frame) : Frame :=
  ![Real.cos (y 5) * v 0 - y 0 * Real.sin (y 5) * v 5,
    Real.sin (y 5) * v 0 + y 0 * Real.cos (y 5) * v 5,
    Real.cos (y 6) * v 1 - y 1 * Real.sin (y 6) * v 6,
    Real.sin (y 6) * v 1 + y 1 * Real.cos (y 6) * v 6,
    Real.cos (y 7) * v 2 - y 2 * Real.sin (y 7) * v 7,
    Real.sin (y 7) * v 2 + y 2 * Real.cos (y 7) * v 7,
    Real.cos (y 8) * v 3 - y 3 * Real.sin (y 8) * v 8,
    Real.sin (y 8) * v 3 + y 3 * Real.cos (y 8) * v 8,
    v 4, v 9, v 10, v 11]

def inverseJacobian (y v : Frame) : Frame :=
  ![Real.cos (y 5) * v 0 + Real.sin (y 5) * v 1,
    Real.cos (y 6) * v 2 + Real.sin (y 6) * v 3,
    Real.cos (y 7) * v 4 + Real.sin (y 7) * v 5,
    Real.cos (y 8) * v 6 + Real.sin (y 8) * v 7,
    v 8,
    (-Real.sin (y 5) * v 0 + Real.cos (y 5) * v 1) / y 0,
    (-Real.sin (y 6) * v 2 + Real.cos (y 6) * v 3) / y 1,
    (-Real.sin (y 7) * v 4 + Real.cos (y 7) * v 5) / y 2,
    (-Real.sin (y 8) * v 6 + Real.cos (y 8) * v 7) / y 3,
    v 9, v 10, v 11]

def jacobianLinear (y : Frame) : Frame →ₗ[ℝ] Frame where
  toFun := jacobian y
  map_add' := by
    intro v w
    funext i
    fin_cases i <;> simp [jacobian, Fin.reduceFinMk] <;> ring
  map_smul' := by
    intro r v
    funext i
    fin_cases i <;>
      simp [jacobian, Fin.reduceFinMk, smul_eq_mul, RingHom.id_apply] <;> ring

def jacobianCLM (y : Frame) : Frame →L[ℝ] Frame :=
  (jacobianLinear y).toContinuousLinearMap

theorem jacobian_left_inverse (y : Frame)
    (hr : ∀ j : Fin 4, y ⟨j,by omega⟩ ≠ 0) (v : Frame) :
    inverseJacobian y (jacobian y v) = v := by
  have h0 := polarBlock_left_inverse (y 0) (Real.cos (y 5)) (Real.sin (y 5))
    (hr 0) (Real.sin_sq_add_cos_sq (y 5)) ![v 0, v 5]
  have h1 := polarBlock_left_inverse (y 1) (Real.cos (y 6)) (Real.sin (y 6))
    (hr 1) (Real.sin_sq_add_cos_sq (y 6)) ![v 1, v 6]
  have h2 := polarBlock_left_inverse (y 2) (Real.cos (y 7)) (Real.sin (y 7))
    (hr 2) (Real.sin_sq_add_cos_sq (y 7)) ![v 2, v 7]
  have h3 := polarBlock_left_inverse (y 3) (Real.cos (y 8)) (Real.sin (y 8))
    (hr 3) (Real.sin_sq_add_cos_sq (y 8)) ![v 3, v 8]
  funext i
  fin_cases i
  · exact congrFun h0 0
  · exact congrFun h1 0
  · exact congrFun h2 0
  · exact congrFun h3 0
  · rfl
  · exact congrFun h0 1
  · exact congrFun h1 1
  · exact congrFun h2 1
  · exact congrFun h3 1
  · rfl
  · rfl
  · rfl

theorem jacobian_right_inverse (y : Frame)
    (hr : ∀ j : Fin 4, y ⟨j,by omega⟩ ≠ 0) (v : Frame) :
    jacobian y (inverseJacobian y v) = v := by
  have h0 := polarBlock_right_inverse (y 0) (Real.cos (y 5)) (Real.sin (y 5))
    (hr 0) (Real.sin_sq_add_cos_sq (y 5)) ![v 0, v 1]
  have h1 := polarBlock_right_inverse (y 1) (Real.cos (y 6)) (Real.sin (y 6))
    (hr 1) (Real.sin_sq_add_cos_sq (y 6)) ![v 2, v 3]
  have h2 := polarBlock_right_inverse (y 2) (Real.cos (y 7)) (Real.sin (y 7))
    (hr 2) (Real.sin_sq_add_cos_sq (y 7)) ![v 4, v 5]
  have h3 := polarBlock_right_inverse (y 3) (Real.cos (y 8)) (Real.sin (y 8))
    (hr 3) (Real.sin_sq_add_cos_sq (y 8)) ![v 6, v 7]
  funext i
  fin_cases i
  · exact congrFun h0 0
  · exact congrFun h0 1
  · exact congrFun h1 0
  · exact congrFun h1 1
  · exact congrFun h2 0
  · exact congrFun h2 1
  · exact congrFun h3 0
  · exact congrFun h3 1
  · rfl
  · rfl
  · rfl
  · rfl

def jacobianEquiv (y : Frame) (hr : ∀ j : Fin 4, y ⟨j,by omega⟩ ≠ 0) :
    Frame ≃ₗ[ℝ] Frame where
  toFun := jacobian y
  invFun := inverseJacobian y
  left_inv := jacobian_left_inverse y hr
  right_inv := jacobian_right_inverse y hr
  map_add' := (jacobianLinear y).map_add
  map_smul' := (jacobianLinear y).map_smul

def jacobianCLE (y : Frame) (hr : ∀ j : Fin 4, y ⟨j,by omega⟩ ≠ 0) :
    Frame ≃L[ℝ] Frame := (jacobianEquiv y hr).toContinuousLinearEquiv

theorem cartesian_smooth (y : Frame) : ContDiffAt ℝ 1 cartesian y := by
  rw [contDiffAt_pi]
  intro i
  fin_cases i <;> simp [cartesian] <;> fun_prop

private def coord (i : Fin 12) : Frame →L[ℝ] ℝ := ContinuousLinearMap.proj i

private def cosineRow (y : Frame) (a b : Fin 12) : Frame →L[ℝ] ℝ :=
  y a • (-Real.sin (y b) • coord b) + Real.cos (y b) • coord a

private def sineRow (y : Frame) (a b : Fin 12) : Frame →L[ℝ] ℝ :=
  y a • (Real.cos (y b) • coord b) + Real.sin (y b) • coord a

private theorem cosine_derivative (y : Frame) (a b : Fin 12) :
    HasFDerivAt (fun x : Frame => x a * Real.cos (x b)) (cosineRow y a b) y := by
  have h := (coord a).hasFDerivAt (x := y) |>.mul (coord b).hasFDerivAt.cos
  change HasFDerivAt (fun x : Frame => x a * Real.cos (x b)) (cosineRow y a b) y at h
  exact h

private theorem sine_derivative (y : Frame) (a b : Fin 12) :
    HasFDerivAt (fun x : Frame => x a * Real.sin (x b)) (sineRow y a b) y := by
  have h := (coord a).hasFDerivAt (x := y) |>.mul (coord b).hasFDerivAt.sin
  change HasFDerivAt (fun x : Frame => x a * Real.sin (x b)) (sineRow y a b) y at h
  exact h

private def derivativeRows (y : Frame) : Fin 12 → (Frame →L[ℝ] ℝ) :=
  ![cosineRow y 0 5, sineRow y 0 5, cosineRow y 1 6, sineRow y 1 6,
    cosineRow y 2 7, sineRow y 2 7, cosineRow y 3 8, sineRow y 3 8,
    coord 4, coord 9, coord 10, coord 11]

theorem cartesian_hasFDerivAt (y : Frame) :
    HasFDerivAt cartesian (jacobianCLM y) y := by
  have hpi : HasFDerivAt cartesian (ContinuousLinearMap.pi (derivativeRows y)) y := by
    apply hasFDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact cosine_derivative y 0 5
    · exact sine_derivative y 0 5
    · exact cosine_derivative y 1 6
    · exact sine_derivative y 1 6
    · exact cosine_derivative y 2 7
    · exact sine_derivative y 2 7
    · exact cosine_derivative y 3 8
    · exact sine_derivative y 3 8
    · exact (coord 4).hasFDerivAt
    · exact (coord 9).hasFDerivAt
    · exact (coord 10).hasFDerivAt
    · exact (coord 11).hasFDerivAt
  have he : jacobianCLM y = ContinuousLinearMap.pi (derivativeRows y) := by
    apply ContinuousLinearMap.ext
    intro v
    funext i
    change jacobian y v i = (derivativeRows y i) v
    fin_cases i <;>
      simp [jacobian, derivativeRows, cosineRow, sineRow, coord, smul_eq_mul] <;> ring
  rw [he]
  exact hpi

theorem source_rho_pos (k : Fin 9) : 0 < rhoK SourceExactRoot.sourceRoot k := by
  have ha := SourceWidthNondegenerate.source_width_bounds k
  exact WidthRadialDerivative.rhoMinus_pos _ _
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ha.2⟩)
    (SourceWidthNondegenerate.source_radicand_pos k).le
    (by linarith [FanFoutPos.radius_sq_lt _ SourceExactRoot.sourceRoot_mem])

def sourceRho : Frame := radialFrame sourcePoint

theorem source_radial_ne (j : Fin 4) : sourceRho ⟨j,by omega⟩ ≠ 0 := by
  have he (i : Fin 4) : sourceRho (⟨i.val,by omega⟩ : Fin 12) =
      rhoK SourceExactRoot.sourceRoot (⟨i.val,by omega⟩ : Fin 9) := by
    fin_cases i <;> simp [sourceRho, radialFrame, sourcePoint, sourceFrame,
      rhoK, WidthRadialDerivative.rhoMinus, angleVec]
  rw [he]
  exact ne_of_gt (source_rho_pos ⟨j,by omega⟩)

def sourceJacobian : Frame ≃L[ℝ] Frame := jacobianCLE sourceRho source_radial_ne

theorem source_strict_derivative :
    HasStrictFDerivAt cartesian (sourceJacobian : Frame →L[ℝ] Frame) sourceRho := by
  have h := (cartesian_smooth sourceRho).hasStrictFDerivAt'
    (cartesian_hasFDerivAt sourceRho) (by norm_num)
  exact h

def sourceInverse : Frame → Frame :=
  HasStrictFDerivAt.localInverse cartesian sourceJacobian sourceRho source_strict_derivative

theorem sourceInverse_apply_image :
    sourceInverse (cartesian sourceRho) = sourceRho :=
  source_strict_derivative.localInverse_apply_image

theorem sourceInverse_left :
    ∀ᶠ y in nhds sourceRho, sourceInverse (cartesian y) = y :=
  source_strict_derivative.eventually_left_inverse

theorem sourceInverse_right :
    ∀ᶠ q in nhds (cartesian sourceRho), cartesian (sourceInverse q) = q :=
  source_strict_derivative.eventually_right_inverse

theorem sourceInverse_strict_derivative :
    HasStrictFDerivAt sourceInverse (sourceJacobian.symm : Frame →L[ℝ] Frame)
      (cartesian sourceRho) := source_strict_derivative.to_localInverse

end
end N11Formalization.CartesianPolarFrame
#check @N11Formalization.CartesianPolarFrame.source_strict_derivative
#check @N11Formalization.CartesianPolarFrame.sourceInverse_strict_derivative
#print axioms N11Formalization.CartesianPolarFrame.source_strict_derivative
#print axioms N11Formalization.CartesianPolarFrame.sourceInverse_strict_derivative
