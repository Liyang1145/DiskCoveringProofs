import N11Formalization.SourceChartIsometry
import N11Formalization.SourceActiveMatrixIntervals
import N11Formalization.SourceFineStressIntervals

/-! SAME root/chart interval expression for arbitrary pinned-coordinate
boxes. No per-cell/cluster membership or norm magnitude is assumed paid here.
Actual DBM rows and finite readouts are supplied by a subsequent packet. -/
set_option autoImplicit false
namespace N11Formalization.Patch120IntervalCore
open N11Formalization RatInterval SourceChartIsometry
noncomputable section

def LI : RatInterval := intv Patch120K5.Lq Patch120K5.LQ
def PI : RatInterval := piI
def DI : RatInterval := sub (mul (ofRat 9) LI) (mul (ofRat 2) PI)

theorem LI_mem : LI.Mem Patch120K5Actual.L := by
  have h := Patch120K5Consumer.inCertBox_L
  norm_num only [Rat.cast_div,Rat.cast_ofNat] at h
  exact h
theorem PI_mem : PI.Mem Real.pi := ⟨piLo_lt_pi.le,pi_lt_piHi.le⟩
theorem DI_mem : DI.Mem Patch120K5Actual.D :=
  sub_mem (mul_mem (ofRat_mem 9) LI_mem) (mul_mem (ofRat_mem 2) PI_mem)

def deltaI (i : Fin 9) : RatInterval :=
  let a0 := ndBox 0
  let a1 := ndBox 1
  let a2 := ndBox 2
  let a3 := ndBox 3
  let s3 := add (add a0 a1) a2
  let s4 := add s3 a3
  ![sub (mul (ofRat 2) s3) (mul (ofRat 2) PI),
    sub (mul (ofRat 2) s4) (mul (ofRat 2) PI),
    neg (mul (ofRat 2) s4),neg (mul (ofRat 2) s3),
    neg (mul (ofRat 2) (add a0 a1)),neg (mul (ofRat 2) a0),ofRat 0,
    mul (ofRat 2) a0,mul (ofRat 2) (add a0 a1)] i

theorem deltaI_mem (i : Fin 9) :
    (deltaI i).Mem (Patch120K5Actual.delta SourceExactRoot.sourceRoot i) := by
  have hb (j : Fin 12) : (ndBox j).Mem (SourceExactRoot.sourceRoot j) :=
    ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball j
  have h3 := add_mem (add_mem (hb 0) (hb 1)) (hb 2)
  have h4 := add_mem h3 (hb 3)
  have h01 := add_mem (hb 0) (hb 1)
  have h2 := ofRat_mem (2 : ℚ)
  fin_cases i
  all_goals simp only [deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
    Fin.reduceFinMk,Patch120K5Actual.delta]
  · convert sub_mem (mul_mem h2 h3) (mul_mem h2 PI_mem) using 1 <;>
      simp only [Rat.cast_ofNat,angleVec,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val,Fin.reduceFinMk] <;> ring
  · convert sub_mem (mul_mem h2 h4) (mul_mem h2 PI_mem) using 1 <;>
      simp only [Rat.cast_ofNat,angleVec,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val,Fin.reduceFinMk] <;> ring
  · convert neg_mem (mul_mem h2 h4) using 1 <;>
      simp only [Rat.cast_ofNat,angleVec,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val,Fin.reduceFinMk] <;> ring
  · convert neg_mem (mul_mem h2 h3) using 1 <;>
      simp only [Rat.cast_ofNat,angleVec,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val,Fin.reduceFinMk] <;> ring
  · convert neg_mem (mul_mem h2 h01) using 1 <;>
      simp only [Rat.cast_ofNat,angleVec,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val,Fin.reduceFinMk] <;> ring
  · convert neg_mem (mul_mem h2 (hb 0)) using 1 <;>
      simp only [Rat.cast_ofNat,angleVec,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val,Fin.reduceFinMk] <;> ring
  · simpa only [Rat.cast_zero] using ofRat_mem (0 : ℚ)
  · convert mul_mem h2 (hb 0) using 1 <;>
      simp only [Rat.cast_ofNat,angleVec,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val,Fin.reduceFinMk] <;> ring
  · convert mul_mem h2 h01 using 1 <;>
      simp only [Rat.cast_ofNat,angleVec,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val,Fin.reduceFinMk] <;> ring

def xInput (U : Fin 9 → RatInterval) (i : Fin 9) : RatInterval :=
  if i=6 then ofRat 0 else sub
    (sub (mul (ofRat ((i.val : ℚ)-6)) LI) (mul DI (U i))) (deltaI i)

theorem xInput_mem (U : Fin 9 → RatInterval) (y : Fin 9 → ℝ)
    (hU : ∀ i : Fin 9,i≠6 →
      (U i).Mem (FlashLeafSplit.tlift y (Patch120K5.f9 i)-FlashLeafSplit.tlift y 6))
    (i : Fin 9) : (xInput U i).Mem (displacement y i) := by
  by_cases hi : i=6
  · subst i
    simp only [xInput,ite_true,displacement_pin]
    simpa only [Rat.cast_zero] using ofRat_mem (0 : ℚ)
  · simp only [xInput,if_neg hi]
    rw [displacement_eq_h]
    have hn : (ofRat ((i.val : ℚ)-6)).Mem ((i.val : ℝ)-6) := by
      simpa only [Rat.cast_sub,Rat.cast_natCast,Rat.cast_ofNat] using
        ofRat_mem ((i.val : ℚ)-6)
    exact sub_mem (sub_mem (mul_mem hn LI_mem) (mul_mem DI_mem (hU i hi))) (deltaI_mem i)

end
end N11Formalization.Patch120IntervalCore
#check @N11Formalization.Patch120IntervalCore.xInput_mem
#print axioms N11Formalization.Patch120IntervalCore.xInput_mem
