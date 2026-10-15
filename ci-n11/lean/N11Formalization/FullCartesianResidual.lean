import N11Formalization.CartesianReflectionSpace
import N11Formalization.HorizontalTruePin
import N11Formalization.TrueCartesianDualConsumer

/-!
Genuine residuals on ALL independent Cartesian23 center/radius coordinates.
No projection onto the fixed subspace is used to define the pins or lengths.
The central true intersection is constructed independently from the two hubs.
Complete restriction to the width/direction Frame is proved before any
covector reflection lift is used.
-/
set_option autoImplicit false
namespace N11Formalization.FullCartesianResidual
open N11Formalization CartesianReflectionSpace TrueCirclePinSmooth
noncomputable section

def ring (x : Full) (k : Fin 9) : Point :=
  !₂[x ⟨2*k.val,by omega⟩, x ⟨2*k.val+1,by omega⟩]
def hubA (x : Full) : Point := !₂[x 18,x 19]
def hubB (x : Full) : Point := !₂[x 20,x 21]
def radius (x : Full) : ℝ := x 22
def ringData (k : Fin 9) (x : Full) : Data :=
  ![(ring x k) 0,(ring x k) 1,(ring x (k+1)) 0,(ring x (k+1)) 1,radius x]
def centralData (x : Full) : Data := ![x 18,x 19,x 20,x 21,x 22]
def ringPin (k : Fin 9) (x : Full) : Point :=
  pinData (sourceSeed k) (ringData k x)
def centralPin (x : Full) : Point := pinData HorizontalTruePin.up (centralData x)

def sourcePoint : Full := pack SourceExactRoot.sourceRoot

theorem ring_pack (u : Fin 12 → ℝ) (k : Fin 9) :
    ring (pack u) k = ringCenter u k := by
  ext i
  fin_cases k <;> fin_cases i <;> rfl
theorem hubA_pack (u : Fin 12 → ℝ) : hubA (pack u) = hub0 u := rfl
theorem hubB_pack (u : Fin 12 → ℝ) : hubB (pack u) = hub1 u := rfl
theorem radius_pack (u : Fin 12 → ℝ) : radius (pack u) = u 6 := rfl

theorem ring_frame (x : Fixed) (k : Fin 9) :
    ring (embed (frameCartesian x)) k = PhysicalResidualFrame.center x k :=
  embedded_frame_centers x k

theorem hubA_frame (x : Fixed) :
    hubA (embed (frameCartesian x)) = PhysicalResidualFrame.hubA x := by
  ext i
  fin_cases i <;> simp [hubA, embed, frameCartesian, CartesianPolarFrame.cartesian,
    CoupledRadialFrame.radialFrame, PhysicalResidualFrame.hubA]
theorem hubB_frame (x : Fixed) :
    hubB (embed (frameCartesian x)) = PhysicalResidualFrame.hubB x := by
  ext i
  fin_cases i <;> simp [hubB, embed, frameCartesian, CartesianPolarFrame.cartesian,
    CoupledRadialFrame.radialFrame, PhysicalResidualFrame.hubB]
theorem radius_frame (x : Fixed) : radius (embed (frameCartesian x)) = x 11 := by
  simp [radius, embed, frameCartesian, CartesianPolarFrame.cartesian,
    CoupledRadialFrame.radialFrame]

theorem ringData_source (k : Fin 9) : ringData k sourcePoint = sourceData k := by
  unfold ringData sourcePoint
  rw [ring_pack, ring_pack, radius_pack]
  rfl

theorem ringData_frame (x : Fixed) (k : Fin 9) :
    ringData k (embed (frameCartesian x)) = TruePinFrameDifferential.frameData k x := by
  unfold ringData
  rw [ring_frame, ring_frame, radius_frame]
  rfl

theorem ringPin_frame (x : Fixed) (k : Fin 9) :
    ringPin k (embed (frameCartesian x)) = TruePinFrameDifferential.framePin k x := by
  rw [ringPin, ringData_frame]
  rfl

/-- The central contact is paid independently, with a full function identity. -/
theorem centralPin_frame (x : Fixed) :
    centralPin (embed (frameCartesian x)) = PhysicalResidualFrame.centralPin x := by
  have he : centralData (embed (frameCartesian x)) = ![x 9,0,x 10,0,x 11] := by
    funext i
    fin_cases i <;> simp [centralData, embed, frameCartesian, CartesianPolarFrame.cartesian,
      CoupledRadialFrame.radialFrame]
  rw [centralPin, he]
  exact HorizontalTruePin.horizontal_pin _ _ _

theorem ring_smooth (k : Fin 9) (x : Full) :
    ContDiffAt ℝ 1 (fun y : Full => ring y k) x := by
  rw [contDiffAt_piLp 2]
  intro i
  fin_cases i <;> simp [ring] <;> fun_prop
theorem hubA_smooth (x : Full) : ContDiffAt ℝ 1 hubA x := by
  rw [contDiffAt_piLp 2]
  intro i
  fin_cases i <;> simp [hubA] <;> fun_prop
theorem hubB_smooth (x : Full) : ContDiffAt ℝ 1 hubB x := by
  rw [contDiffAt_piLp 2]
  intro i
  fin_cases i <;> simp [hubB] <;> fun_prop
theorem radius_smooth (x : Full) : ContDiffAt ℝ 1 radius x := by
  change ContDiffAt ℝ 1 (fun y : Full => y 22) x
  fun_prop
theorem ringData_smooth (k : Fin 9) (x : Full) :
    ContDiffAt ℝ 1 (ringData k) x := by
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · exact ((contDiffAt_piLp 2).mp (ring_smooth k x)) 0
  · exact ((contDiffAt_piLp 2).mp (ring_smooth k x)) 1
  · exact ((contDiffAt_piLp 2).mp (ring_smooth (k+1) x)) 0
  · exact ((contDiffAt_piLp 2).mp (ring_smooth (k+1) x)) 1
  · exact radius_smooth x
theorem centralData_smooth (x : Full) : ContDiffAt ℝ 1 centralData x := by
  rw [contDiffAt_pi]
  intro i
  fin_cases i <;> simp [centralData] <;> fun_prop

theorem ringPin_source (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    ringPin k sourcePoint = Uvec SourceExactRoot.sourceRoot k := by
  rw [ringPin, ringData_source]
  exact source_pinData_eq k hk
theorem ringPin_source_smooth (k : Fin 9) (hk : k=1 ∨ k=2 ∨ k=3 ∨ k=8) :
    ContDiffAt ℝ 1 (ringPin k) sourcePoint := by
  have h := source_pinData_smooth k hk
  rw [← ringData_source k] at h
  exact h.comp sourcePoint (ringData_smooth k sourcePoint)

theorem centralPin_source :
    centralPin sourcePoint = wPoint SourceExactRoot.sourceRoot :=
  HorizontalTruePin.source_central_pin
theorem centralPin_source_smooth : ContDiffAt ℝ 1 centralPin sourcePoint :=
  HorizontalTruePin.source_central_smooth.comp sourcePoint (centralData_smooth sourcePoint)

def residualFull (x : Full) : Fin 5 → ℝ :=
  ![dist (ringPin 1 x) (hubB x) - radius x,
    dist (ringPin 2 x) (hubA x) - radius x,
    dist (ringPin 3 x) (hubA x) - radius x,
    dist (ringPin 8 x) (hubB x) - radius x,
    dist (centralPin x) (ring x 6) - radius x]

theorem residualFull_frame (x : Fixed) :
    residualFull (embed (frameCartesian x)) = TrueResidualFrame.residualTrue x := by
  simp only [residualFull, ringPin_frame, hubA_frame, hubB_frame,
    radius_frame, centralPin_frame, ring_frame]
  rfl

theorem residualFull_source_smooth : ContDiffAt ℝ 1 residualFull sourcePoint := by
  obtain ⟨h1,h2,h3,h8,hc⟩ := nd_all_via_dist
  have hb := TCChartStationarityRoot.sourceRoot_mem_ball
  have hp1 : ringPin 1 sourcePoint ≠ hubB sourcePoint := by
    rw [ringPin_source 1 (by simp)]
    exact h1 _ hb
  have hp2 : ringPin 2 sourcePoint ≠ hubA sourcePoint := by
    rw [ringPin_source 2 (by simp)]
    exact h2 _ hb
  have hp3 : ringPin 3 sourcePoint ≠ hubA sourcePoint := by
    rw [ringPin_source 3 (by simp)]
    exact h3 _ hb
  have hp8 : ringPin 8 sourcePoint ≠ hubB sourcePoint := by
    rw [ringPin_source 8 (by simp)]
    exact h8 _ hb
  have hpc : centralPin sourcePoint ≠ ring sourcePoint 6 := by
    rw [centralPin_source]
    simpa only [sourcePoint, ring_pack] using hc _ hb
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · exact ((ringPin_source_smooth 1 (by simp)).dist ℝ (hubB_smooth sourcePoint) hp1).sub
      (radius_smooth sourcePoint)
  · exact ((ringPin_source_smooth 2 (by simp)).dist ℝ (hubA_smooth sourcePoint) hp2).sub
      (radius_smooth sourcePoint)
  · exact ((ringPin_source_smooth 3 (by simp)).dist ℝ (hubA_smooth sourcePoint) hp3).sub
      (radius_smooth sourcePoint)
  · exact ((ringPin_source_smooth 8 (by simp)).dist ℝ (hubB_smooth sourcePoint) hp8).sub
      (radius_smooth sourcePoint)
  · exact (centralPin_source_smooth.dist ℝ (ring_smooth 6 sourcePoint) hpc).sub
      (radius_smooth sourcePoint)

def objectiveFull (x : Full) : ℝ :=
  radius x - ∑ j : Fin 5, last5 SourceExactRoot.sourceRoot j * residualFull x j

theorem objectiveFull_frame (x : Fixed) :
    objectiveFull (embed (frameCartesian x)) = TrueResidualFrame.objectiveTrue x := by
  simp only [objectiveFull, residualFull_frame, radius_frame, TrueResidualFrame.objectiveTrue]

theorem objectiveFull_source_smooth : ContDiffAt ℝ 1 objectiveFull sourcePoint := by
  exact (radius_smooth sourcePoint).sub
    (ContDiffAt.sum (s := (Finset.univ : Finset (Fin 5))) (fun j _ =>
      ((contDiffAt_pi.mp residualFull_source_smooth) j).const_smul
        (last5 SourceExactRoot.sourceRoot j)))

end
end N11Formalization.FullCartesianResidual
#check @N11Formalization.FullCartesianResidual.objectiveFull_frame
#check @N11Formalization.FullCartesianResidual.objectiveFull_source_smooth
#print axioms N11Formalization.FullCartesianResidual.objectiveFull_frame
#print axioms N11Formalization.FullCartesianResidual.objectiveFull_source_smooth
