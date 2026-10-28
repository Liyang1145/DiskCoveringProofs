import N11Formalization.SourceAllFaceBalance
import N11Formalization.PhysicalBoundaryStationarity
import N11Formalization.SourceN2GeomEdge

/-! Actual45-edge signed source coefficient assembly. The nine face blocks
and18 tie spokes preserve exact total mass1, and all18 auxiliary B2 rows hold
for the assembled coefficients. Tie weights may still be negative; centre
rows and positive-stress/global conclusions are NOT inferred. -/
set_option autoImplicit false
namespace N11Formalization.SourceSignedStressAssembly
open N11Formalization ResumeLocalIncidence
noncomputable section

def tieRep (k : Fin 9) : Fin 5 := ![0,1,2,3,3,2,1,0,4] k
def tieOrbitSize (j : Fin 5) : ℝ := ![2,2,2,2,1] j
def tieWeight (k : Fin 9) : ℝ :=
  PhysicalBoundaryStationarity.tieWeight (tieRep k)/tieOrbitSize (tieRep k)
def split (k : Fin 9) (s : Fin 2) : ℝ :=
  if s=0 then SourceBoundaryTieDerivative.eta k else 1-SourceBoundaryTieDerivative.eta k
def spokeCoefficient (k : Fin 9) (s : Fin 2) : ℝ := tieWeight k*split k s
def stress : SourceEdge → ℝ
  | .inl (k,s) => spokeCoefficient k s
  | .inr (f,t) => SourceAllFaceBalance.coefficient f t

theorem split_pos (k : Fin 9) (s : Fin 2) : 0<split k s := by
  unfold split
  split_ifs
  · exact (SourceBoundaryWeights.eta_bounds k).1
  · exact sub_pos.mpr (SourceBoundaryWeights.eta_bounds k).2

theorem split_sum (k : Fin 9) : ∑ s : Fin 2,split k s=1 := by
  rw [Fin.sum_univ_two]
  have h0 : split k 0=SourceBoundaryTieDerivative.eta k := rfl
  have h1 : split k 1=1-SourceBoundaryTieDerivative.eta k := by
    unfold split
    rw [if_neg (by decide : ¬ ((1 : Fin 2)=0))]
  rw [h0,h1]
  ring

theorem tieOrbitSize_pos (j : Fin 5) : 0<tieOrbitSize j := by
  fin_cases j <;> norm_num [tieOrbitSize]

theorem spoke_positive_iff (k : Fin 9) (s : Fin 2) :
    0<spokeCoefficient k s ↔ 0<PhysicalBoundaryStationarity.tieWeight (tieRep k) := by
  have hp := split_pos k s
  have hd := tieOrbitSize_pos (tieRep k)
  unfold spokeCoefficient tieWeight
  constructor
  · intro h
    exact (div_pos_iff_of_pos_right hd).mp ((mul_pos_iff_of_pos_right hp).mp h)
  · intro h
    exact mul_pos (div_pos h hd) hp

theorem tieWeight_mass :
    ∑ k : Fin 9,tieWeight k=∑ j : Fin 5,PhysicalBoundaryStationarity.tieWeight j := by
  simp [tieWeight,tieRep,tieOrbitSize,Fin.sum_univ_succ]
  ring

theorem spoke_mass :
    ∑ k : Fin 9,∑ s : Fin 2,spokeCoefficient k s=
      ∑ j : Fin 5,PhysicalBoundaryStationarity.tieWeight j := by
  simp only [spokeCoefficient,← Finset.mul_sum,split_sum,mul_one]
  exact tieWeight_mass

/-- The concrete45 coefficients have exact SIGNED mass1, not yet nonnegative. -/
theorem stress_mass_one : ∑ s : SourceEdge,stress s=1 := by
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,stress]
  rw [spoke_mass,SourceAllFaceBalance.coefficient_mass]
  have h := PhysicalBoundaryStationarity.signed_mass_one
  linarith

theorem face_coefficient_pos (f : Fin 9) (t : Fin 3) : 0<stress (.inr (f,t)) :=
  SourceAllFaceBalance.coefficient_pos f t

/-- No extra positivity premise is silently discharged: source stress positive
iff the five signed physical tie weights are positive. -/
theorem stress_positive_iff :
    (∀ s : SourceEdge,0<stress s) ↔
      (∀ j : Fin 5,0<PhysicalBoundaryStationarity.tieWeight j) := by
  constructor
  · intro h j
    let k : Fin 9 := ![0,1,2,3,8] j
    have hk : tieRep k=j := by fin_cases j <;> rfl
    have hp := (spoke_positive_iff k 0).mp (h (.inl (k,0)))
    rwa [hk] at hp
  · intro h s
    rcases s with ⟨k,q⟩ | ⟨f,t⟩
    · exact (spoke_positive_iff k q).mpr (h _)
    · exact face_coefficient_pos f t

private theorem auxiliary_spoke_zero (f k : Fin 9) (c s : Fin 2) :
    SourceN2.srcB2 SourceExactRoot.sourceRoot
      (⟨22+2*f.val+c.val,by omega⟩ : Fin 41) (SourceN2.spokeFlat k s)=0 := by
  have hmass : 22+2*f.val+c.val≠40 := by omega
  have hV : 9+(k.val+s.val)%9≠9+(22+2*f.val+c.val)/2 := by
    have hmod : (k.val+s.val)%9<9 := Nat.mod_lt _ (by decide)
    omega
  have hW : k.val≠9+(22+2*f.val+c.val)/2 := by omega
  simp only [SourceN2.srcB2,Fin.val_mk,hmass,if_false,
    SourceN2GeomEdge.srcEdgeV2_spoke,SourceN2GeomEdge.srcEdgeW2_spoke,hV,hW,add_zero]

/-- All18 actual auxiliary rows as FULL45-edge sums with the actual signed
tie spokes present. The spokes do not touch auxiliary nodes; centre rows
are a separate, still unpaid consequence of physical stationarity. -/
theorem full_auxiliary_B2_rows (f : Fin 9) (c : Fin 2) :
    ∑ s : SourceEdge, SourceN2.srcB2 SourceExactRoot.sourceRoot
      (⟨22+2*f.val+c.val,by omega⟩ : Fin 41) (HarmonicSourceTransport.srcFlat s)*stress s=0 := by
  have h := SourceAllFaceBalance.full_auxiliary_B2_rows f c
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,
    SourceAllFaceBalance.faceOnlyStress,HarmonicSourceTransport.srcFlat,
    mul_zero,Finset.sum_const_zero,zero_add] at h
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,stress,
    HarmonicSourceTransport.srcFlat,auxiliary_spoke_zero,zero_mul,
    Finset.sum_const_zero,zero_add]
  exact h

end
end N11Formalization.SourceSignedStressAssembly
#check @N11Formalization.SourceSignedStressAssembly.stress_mass_one
#check @N11Formalization.SourceSignedStressAssembly.stress_positive_iff
#check @N11Formalization.SourceSignedStressAssembly.full_auxiliary_B2_rows
#print axioms N11Formalization.SourceSignedStressAssembly.stress_mass_one
#print axioms N11Formalization.SourceSignedStressAssembly.full_auxiliary_B2_rows
