import N11Formalization.SourceFineStressGridReadout
import N11Formalization.SourceCompactStressIntervals

/-! Strictly narrower common-grid enclosures of SAME actual45 stress.
Containment of the fine expression, refinement of the old compact enclosure,
and a uniform width bound are kernel-paid. No coercivity is asserted. -/
set_option autoImplicit false
namespace N11Formalization.SourceFineCompactStressIntervals
open N11Formalization RatInterval ResumeLocalIncidence HarmonicSourceTransport
open SourceFineStressIntervals SourceFineStressGridReadout
noncomputable section

def loN : Fin 45 → ℤ :=
  ![2795158,3274979,2641026,3462423,4975411,3011168,2894180,2749356,
    2749356,2894180,3011168,4975411,3462423,2641026,3274979,2795158,
    1946618,1946618,1320534,687879,894595,1320534,687879,894595,
    2867741,4141888,5691721,976249,802336,1281104,363754,293440,332268,
    293440,363754,332268,802336,976249,1281104,4141888,2867741,5691721,
    1602755,1602755,1984942]
def hiN : Fin 45 → ℤ :=
  ![2795349,3275202,2641223,3462681,4975574,3011267,2894270,2749442,
    2749442,2894270,3011267,4975574,3462681,2641223,3275202,2795349,
    1946831,1946831,1320535,687893,894610,1320535,687893,894610,
    2867856,4142003,5691722,976276,802363,1281105,363762,293448,332269,
    293448,363762,332269,802363,976276,1281105,4142003,2867856,5691722,
    1602795,1602795,1984943]

def compact (e : SourceEdge) : RatInterval :=
  intv ((loN (srcFlat e) : ℚ)/100000000) ((hiN (srcFlat e) : ℚ)/100000000)

private theorem slope5_eq : slopeI 5=intv (32095133/100000000) (32095135/100000000) := slope3_eq
private theorem slope6_eq : slopeI 6=intv (19424295/100000000) (19424297/100000000) := slope2_eq
private theorem slope7_eq : slopeI 7=intv (25465527/100000000) (25465529/100000000) := slope1_eq
private theorem slope8_eq : slopeI 8=intv (29836980/100000000) (29836982/100000000) := slope0_eq
private theorem succ4 : (4 : Fin 9)+1=5 := by decide

macro "fine_compact_spoke_eval" : tactic =>
  `(tactic|
    (simp only [Contains,compact,loN,hiN,srcFlat,SourceN2.spokeFlat,
      stressI,spokeI,div,inv,spokeDen,SourceSignedStressAssembly.tieRep,
      SourceStressIntervals.tieOrbitQ,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Fin.reduceFinMk]
     simp [Fin.ext_iff,nd_fin_succ_0,nd_fin_succ_1,nd_fin_succ_2,
      nd_fin_succ_3,succ4,nd_fin_succ_5,nd_fin_succ_6,nd_fin_succ_7,nd_fin_succ_8,
      slope0_eq,slope1_eq,slope2_eq,slope3_eq,slope4_eq,
      slope5_eq,slope6_eq,slope7_eq,slope8_eq,
      num0_eq,num1_eq,num2_eq,num3_eq,num4_eq]
     norm_num [RatInterval.mul,RatInterval.neg,RatInterval.ofRat,intv]))

macro "fine_compact_face_eval" : tactic =>
  `(tactic|
    (simp only [Contains,compact,loN,hiN,srcFlat,SourceN2.faceFlatEdge,stressI,
      faceI,div,inv,representativeI,SourceAllFaceBalance.repIndex,
      SourceAllFaceBalance.vertexPerm,SourceFaceReflection.swapVertex,
      SourceStressIntervals.faceOrbitQ,
      SourceRefinedFanCoefficientBounds.ABox,SourceRefinedFanCoefficientBounds.BBox,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Fin.reduceFinMk,
      SourceStressGridReadout.centralA_eq,SourceStressGridReadout.centralB_eq]
     nd_eval))

private theorem spoke_contains (k : Fin 9) (s : Fin 2) :
    Contains (compact (.inl (k,s))) (stressI (.inl (k,s))) := by
  fin_cases k <;> fin_cases s <;> fine_compact_spoke_eval

private theorem face_contains (f : Fin 9) (t : Fin 3) :
    Contains (compact (.inr (f,t))) (stressI (.inr (f,t))) := by
  fin_cases f <;> fin_cases t <;> fine_compact_face_eval

theorem compact_contains (e : SourceEdge) : Contains (compact e) (stressI e) := by
  rcases e with ⟨k,s⟩ | ⟨f,t⟩
  · exact spoke_contains k s
  · exact face_contains f t

/-- No fine-expression, derivative, numerical endpoint or stress premise. -/
theorem compact_mem (e : SourceEdge) :
    (compact e).Mem (SourceSignedStressAssembly.stress e) :=
  mem_of_contains (compact_contains e) (stressI_mem e)

private theorem table_refinement (i : Fin 45) :
    SourceCompactStressIntervals.loN i ≤ loN i ∧
    hiN i ≤ SourceCompactStressIntervals.hiN i := by
  fin_cases i <;> norm_num [loN,hiN,
    SourceCompactStressIntervals.loN,SourceCompactStressIntervals.hiN]

theorem refines_old (e : SourceEdge) :
    Contains (SourceCompactStressIntervals.compact e) (compact e) := by
  have h := table_refinement (srcFlat e)
  change ((SourceCompactStressIntervals.loN (srcFlat e) : ℚ)/100000000 ≤
    (loN (srcFlat e) : ℚ)/100000000) ∧
    ((hiN (srcFlat e) : ℚ)/100000000 ≤
      (SourceCompactStressIntervals.hiN (srcFlat e) : ℚ)/100000000)
  constructor
  · exact div_le_div_of_nonneg_right (by exact_mod_cast h.1) (by norm_num)
  · exact div_le_div_of_nonneg_right (by exact_mod_cast h.2) (by norm_num)

private theorem width_table (i : Fin 45) : hiN i-loN i ≤ 258 := by
  fin_cases i <;> norm_num [loN,hiN]

/-- Uniform actual-stress enclosure width <=258/10^8. -/
theorem width_bound (e : SourceEdge) :
    (compact e).hi-(compact e).lo ≤ (258 : ℚ)/100000000 := by
  change (hiN (srcFlat e) : ℚ)/100000000-
    (loN (srcFlat e) : ℚ)/100000000 ≤ _
  rw [← sub_div]
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast width_table (srcFlat e)) (by norm_num)

private theorem anchor_upper_grid (k : Fin 9) :
    (compact (.inl (k,0))).hi+(compact (.inl (k,1))).hi ≤ (2 : ℚ)/25 := by
  fin_cases k <;> norm_num [compact,hiN,srcFlat,SourceN2.spokeFlat,intv]

/-- Actual source anchor diagonal: two true carrying spoke loads.
The former coarse-box test failed; the finer input pays the exact2/25 bound. -/
theorem actual_anchor_diagonal (k : Fin 9) :
    SourceSignedStressAssembly.stress (.inl (k,0))+
      SourceSignedStressAssembly.stress (.inl (k,1)) ≤ (2 : ℝ)/25 := by
  have h0 := (compact_mem (.inl (k,0))).2
  have h1 := (compact_mem (.inl (k,1))).2
  have hg : ((compact (.inl (k,0))).hi : ℝ)+
      ((compact (.inl (k,1))).hi : ℝ) ≤ (2 : ℝ)/25 := by
    have hh : (((compact (.inl (k,0))).hi+
        (compact (.inl (k,1))).hi : ℚ) : ℝ) ≤ ((2/25 : ℚ) : ℝ) :=
      Rat.cast_le.mpr (anchor_upper_grid k)
    simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_ofNat] using hh
  exact (add_le_add h0 h1).trans hg

end
end N11Formalization.SourceFineCompactStressIntervals
#check @N11Formalization.SourceFineCompactStressIntervals.compact_mem
#check @N11Formalization.SourceFineCompactStressIntervals.refines_old
#check @N11Formalization.SourceFineCompactStressIntervals.width_bound
#check @N11Formalization.SourceFineCompactStressIntervals.actual_anchor_diagonal
#print axioms N11Formalization.SourceFineCompactStressIntervals.compact_mem
#print axioms N11Formalization.SourceFineCompactStressIntervals.actual_anchor_diagonal
