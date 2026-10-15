import Mathlib
import N11Formalization.PhysicalResidualFrame
import N11Formalization.Smoothness
import N11Formalization.F1.BallD35C13
import N11Formalization.NondegProof
set_option autoImplicit false
namespace N11Formalization.PhysicalFrameSmooth
open N11Formalization PhysicalResidualFrame BoundaryChartSource
noncomputable section

private theorem cd_coord (i : Fin 12) (x : Fin 12 → ℝ) :
    ContDiffAt ℝ 1 (fun y : Fin 12 → ℝ => y i) x := contDiffAt_coord i x

private theorem cd_widths (k : Fin 9) (x : Fin 12 → ℝ) :
    ContDiffAt ℝ 1 (fun y => widths y k) x := by
  fin_cases k <;> simp [widths] <;> fun_prop

private theorem cd_directions (k : Fin 9) (x : Fin 12 → ℝ) :
    ContDiffAt ℝ 1 (fun y => directions y k) x := by
  fin_cases k <;> simp [directions] <;> fun_prop

private theorem cd_radial (k : Fin 9) (x : Fin 12 → ℝ)
    (h : (x 11)^2 - Real.sin (widths x k)^2 ≠ 0) :
    ContDiffAt ℝ 1 (fun y => radial y k) x := by
  have hc := contDiffAt_cos_comp (cd_widths k x)
  have hs := contDiffAt_sin_comp (cd_widths k x)
  exact hc.sub ((((cd_coord 11 x).pow 2).sub (hs.pow 2)).sqrt h)

private theorem cd_center (k : Fin 9) (x : Fin 12 → ℝ)
    (h : (x 11)^2 - Real.sin (widths x k)^2 ≠ 0) :
    ContDiffAt ℝ 1 (fun y => center y k) x := by
  rw [contDiffAt_piLp 2]
  intro q
  fin_cases q
  · change ContDiffAt ℝ 1 (fun y => radial y k * Real.cos (directions y k)) x
    exact (cd_radial k x h).mul (contDiffAt_cos_comp (cd_directions k x))
  · change ContDiffAt ℝ 1 (fun y => radial y k * Real.sin (directions y k)) x
    exact (cd_radial k x h).mul (contDiffAt_sin_comp (cd_directions k x))

private theorem cd_endpoint (k : Fin 9) (x : Fin 12 → ℝ) :
    ContDiffAt ℝ 1 (fun y => endpoint y k) x := by
  rw [contDiffAt_piLp 2]
  intro q
  fin_cases q
  · change ContDiffAt ℝ 1 (fun y => Real.cos (directions y k + widths y k)) x
    exact contDiffAt_cos_comp ((cd_directions k x).add (cd_widths k x))
  · change ContDiffAt ℝ 1 (fun y => Real.sin (directions y k + widths y k)) x
    exact contDiffAt_sin_comp ((cd_directions k x).add (cd_widths k x))

private theorem cd_pin (k : Fin 9) (x : Fin 12 → ℝ)
    (h : ∀ j, (x 11)^2 - Real.sin (widths x j)^2 ≠ 0) :
    ContDiffAt ℝ 1 (fun y => pin y k) x :=
  ((cd_center k x (h k)).add (cd_center (k+1) x (h (k+1)))).sub (cd_endpoint k x)

private theorem cd_hubA (x : Fin 12 → ℝ) : ContDiffAt ℝ 1 hubA x := by
  rw [contDiffAt_piLp 2]
  intro q
  fin_cases q
  · exact cd_coord 9 x
  · exact contDiffAt_const

private theorem cd_hubB (x : Fin 12 → ℝ) : ContDiffAt ℝ 1 hubB x := by
  rw [contDiffAt_piLp 2]
  intro q
  fin_cases q
  · exact cd_coord 10 x
  · exact contDiffAt_const

private theorem cd_centralPin (x : Fin 12 → ℝ)
    (h : (x 11)^2 - ((x 10-x 9)/2)^2 ≠ 0) :
    ContDiffAt ℝ 1 centralPin x := by
  rw [contDiffAt_piLp 2]
  intro q
  fin_cases q
  · change ContDiffAt ℝ 1 (fun y => (y 9+y 10)/2) x
    exact ((cd_coord 9 x).add (cd_coord 10 x)).div_const 2
  · change ContDiffAt ℝ 1 (fun y => Real.sqrt ((y 11)^2-((y 10-y 9)/2)^2)) x
    exact (((cd_coord 11 x).pow 2).sub
      ((((cd_coord 10 x).sub (cd_coord 9 x)).div_const 2).pow 2)).sqrt h

/-- Independent frame differentiability at the source root: nonzero square-root radicands
and distance arguments are supplied by the already certified source closed ball. -/
theorem sourceRoot_frame_smooth :
    ContDiffAt ℝ 1 residualFrame (sourceFrame SourceExactRoot.sourceRoot) := by
  let u := SourceExactRoot.sourceRoot
  let x := sourceFrame u
  have hb := TCChartStationarityRoot.sourceRoot_mem_ball
  have hr : ∀ k : Fin 9, (x 11)^2 - Real.sin (widths x k)^2 ≠ 0 := by
    intro k
    rw [show x 11 = u 6 from rfl]
    rw [show widths x k = angleVec u k from congrFun (widths_source u) k]
    exact rho_of_ball hb k
  have hw : (x 11)^2-((x 10-x 9)/2)^2 ≠ 0 := radW_of_ball hb
  obtain ⟨h1,h2,h3,h8,hc⟩ := nd_all_via_dist
  have hn1 : pin x 1 ≠ hubB x := by
    simpa only [x, pin_source, hubB_source] using h1 u hb
  have hn2 : pin x 2 ≠ hubA x := by
    simpa only [x, pin_source, hubA_source] using h2 u hb
  have hn3 : pin x 3 ≠ hubA x := by
    simpa only [x, pin_source, hubA_source] using h3 u hb
  have hn8 : pin x 8 ≠ hubB x := by
    simpa only [x, pin_source, hubB_source] using h8 u hb
  have hnc : centralPin x ≠ center x 6 := by
    simpa only [x, centralPin_source, center_source] using hc u hb
  rw [contDiffAt_pi]
  intro q
  fin_cases q
  · exact ((cd_pin 1 x hr).dist ℝ (cd_hubB x) hn1).sub (cd_coord 11 x)
  · exact ((cd_pin 2 x hr).dist ℝ (cd_hubA x) hn2).sub (cd_coord 11 x)
  · exact ((cd_pin 3 x hr).dist ℝ (cd_hubA x) hn3).sub (cd_coord 11 x)
  · exact ((cd_pin 8 x hr).dist ℝ (cd_hubB x) hn8).sub (cd_coord 11 x)
  · exact ((cd_centralPin x hw).dist ℝ (cd_center 6 x (hr 6)) hnc).sub (cd_coord 11 x)

/-- The actual independent-frame objective is differentiable, without a smoothness premise. -/
theorem sourceRoot_objective_differentiable :
    DifferentiableAt ℝ (objectiveFrame SourceExactRoot.sourceRoot)
      (sourceFrame SourceExactRoot.sourceRoot) := by
  have hc : ContDiffAt ℝ 1 (objectiveFrame SourceExactRoot.sourceRoot)
      (sourceFrame SourceExactRoot.sourceRoot) := by
    have hs := ContDiffAt.sum (s := (Finset.univ : Finset (Fin 5))) (fun k _ =>
      ((contDiffAt_pi.mp sourceRoot_frame_smooth) k).const_smul
        (last5 SourceExactRoot.sourceRoot k))
    exact (cd_coord 11 _).sub hs
  exact hc.differentiableAt (by norm_num)

/-- Fully instantiated dual factorization for the actual width/direction-frame objective.
No physical differentiability or chart-stationarity premise remains. This is still not
an equation in independent Cartesian center coordinates or a B2 force theorem. -/
theorem sourceRoot_objective_dual :
    ∀ v : Fin 12 → ℝ,
      fderiv ℝ (objectiveFrame SourceExactRoot.sourceRoot)
          (sourceFrame SourceExactRoot.sourceRoot) v =
        ∑ j : Fin 5,
          BoundaryChartDual.multiplier (fun i =>
            fderiv ℝ (objectiveFrame SourceExactRoot.sourceRoot)
              (sourceFrame SourceExactRoot.sourceRoot) (Pi.single i 1)) j *
            BoundaryChartLinear.boundary v j :=
  PhysicalResidualFrame.sourceRoot_dual sourceRoot_objective_differentiable.hasFDerivAt

end
end N11Formalization.PhysicalFrameSmooth
#print N11Formalization.PhysicalFrameSmooth.sourceRoot_frame_smooth
#print axioms N11Formalization.PhysicalFrameSmooth.sourceRoot_frame_smooth
#print N11Formalization.PhysicalFrameSmooth.sourceRoot_objective_dual
#print axioms N11Formalization.PhysicalFrameSmooth.sourceRoot_objective_dual
