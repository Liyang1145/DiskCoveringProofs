import N11Formalization.SharedMomentFactorRationalNodes
import N11Formalization.MetricSectorRationalNodes
import N11Formalization.MetricAreaMaskedRationalCertificate

/-! Complete rational production of the actual masked shared-moment dual.
Finite incidence balance, Taylor interval nodes, sector square/sine brackets
and a strict rational total are the only certificate checks. Genuine area,
station, shared-side, endpoint-copy and selected-ear identities enter through
the existing actual geometric consumer. No numeric class table is asserted. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualSharedMomentRationalCertificate

open ActualCoverStructuralReduction ActualFiniteNearestRefinement
open ActualBoundaryNineTies ActualSharedMomentData ActualSharedMomentDual
open ActualEdgeFlagSums ActualRefinementDoubleCounting ActualQ1CoreFans
open ActualRingLinkBoundaryData ActualEarOwnedWidth
open SharedMomentFactorGridCertificate SharedMomentFactorRationalNodes
open CompactSimplexGridCertificate MetricAreaRationalCertificate

structure CoeffQ {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r) where
  mu : Fin 11 → ℚ
  faceMask : R.Index → Fin 3 → ℚ
  switchMask : Fin 9 → ℚ
  sideFirst : Finset (Fin 11) → ℚ
  sideSecond : Finset (Fin 11) → ℚ
  leftFirst : Fin 9 → ℚ
  leftSecond : Fin 9 → ℚ
  rightFirst : Fin 9 → ℚ
  rightSecond : Fin 9 → ℚ
  width : ℚ

def CoeffQ.toReal {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : CoeffQ R) : Coefficients R where
  mu := fun i => (D.mu i : ℝ)
  faceMask := fun A s => (D.faceMask A s : ℝ)
  switchMask := fun k => (D.switchMask k : ℝ)
  sideFirst := fun e => (D.sideFirst e : ℝ)
  sideSecond := fun e => (D.sideSecond e : ℝ)
  leftFirst := fun k => (D.leftFirst k : ℝ)
  leftSecond := fun k => (D.leftSecond k : ℝ)
  rightFirst := fun k => (D.rightFirst k : ℝ)
  rightSecond := fun k => (D.rightSecond k : ℝ)
  width := (D.width : ℝ)

def edgeSumQ {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    (f : R.Index → Fin 3 → ℚ) (e : Finset (Fin 11)) : ℚ :=
  ∑ p ∈ edgeFlags R e, f p.1 p.2

def switchSumQ (g : Fin 9 → ℚ) (e : Finset (Fin 11)) : ℚ :=
  ∑ k : Fin 9, if cycleEdge k=e then g k else 0

def MaskBalancedQ {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    (f : R.Index → Fin 3 → ℚ) (g : Fin 9 → ℚ) : Prop :=
  ∀ e ∈ edges R, edgeSumQ R f e+switchSumQ g e=0

theorem edgeSumQ_cast {c : Fin 11 → Point} {r : ℝ} (R : Refinement c r)
    (f : R.Index → Fin 3 → ℚ) (e : Finset (Fin 11)) :
    (edgeSumQ R f e : ℝ)=edgeSum R (fun A s => (f A s : ℝ)) e := by
  simp only [edgeSumQ,edgeSum,Rat.cast_sum]

theorem switchSumQ_cast (g : Fin 9 → ℚ) (e : Finset (Fin 11)) :
    (switchSumQ g e : ℝ)=switchSum (fun k => (g k : ℝ)) e := by
  unfold switchSumQ switchSum
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : cycleEdge k=e <;> simp [hk]

theorem maskBalanced_of_rational {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : CoeffQ R) (hm : MaskBalancedQ R D.faceMask D.switchMask) :
    MaskBalanced R D.toReal.faceMask D.toReal.switchMask := by
  intro e he
  have hh : ((edgeSumQ R D.faceMask e+switchSumQ D.switchMask e : ℚ) : ℝ)=0 :=
    by exact_mod_cast hm e he
  simpa only [Rat.cast_add,edgeSumQ_cast,switchSumQ_cast,CoeffQ.toReal] using hh

def faceP {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : CoeffQ R) (kap : Finset (Fin 11) → ℚ) (A : R.Index) (s : Fin 3) : ℚ :=
  -D.mu (R.labels A s)-kap (flagEdge R A s)

def faceQ {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : CoeffQ R) (A : R.Index) (s : Fin 3) : ℚ :=
  D.faceMask A s*D.sideSecond (flagEdge R A s)

def faceB {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : CoeffQ R) (A : R.Index) (s : Fin 3) : ℚ :=
  D.faceMask A s*D.sideFirst (flagEdge R A s)

def switchP {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : CoeffQ R) (kap : Finset (Fin 11) → ℚ) (k : Fin 9) : ℚ :=
  (∑ i ∈ cycleEdge k, D.mu i)-kap (cycleEdge k)

def switchQ {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : CoeffQ R) (k : Fin 9) : ℚ := D.switchMask k*D.sideSecond (cycleEdge k)

def switchB {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : CoeffQ R) (k : Fin 9) : ℚ := D.switchMask k*D.sideFirst (cycleEdge k)

def switchD2 {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : CoeffQ R) (k : Fin 9) : ℚ := D.leftSecond k+D.rightSecond (k-1)

def switchD1 {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : CoeffQ R) (k : Fin 9) : ℚ := D.leftFirst k+D.rightFirst (k-1)

def sectorC {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : CoeffQ R) (ear : Fin 9) (eta : ℚ) (k : Fin 9) : ℚ :=
  D.width+if k ∈ outsideGaps ear then eta else 0

theorem face_factor_eq_objective {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : CoeffQ R) (kap : Finset (Fin 11) → ℚ) (A : R.Index) (a : Fin 3 → ℝ) (y : ℝ) :
    ActualSharedMomentMaskedDual.faceFactor D.toReal (fun e => (kap e : ℝ)) A a y=
      faceObjective (fun s => (faceP D kap A s : ℝ)) (fun s => (faceQ D A s : ℝ))
        (fun s => (faceB D A s : ℝ)) a y := by
  simp only [ActualSharedMomentMaskedDual.faceFactor,ActualSharedMomentDual.faceFactor,
    faceObjective,faceQuadratic,faceLinear,CompactQuadraticMomentMaximum.quad,
    Fin.sum_univ_three,faceP,faceQ,faceB,CoeffQ.toReal]
  push_cast
  ring

theorem switch_factor_eq_objective {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : CoeffQ R) (kap : Finset (Fin 11) → ℚ) (k : Fin 9) (t y : ℝ) :
    ActualSharedMomentMaskedDual.switchFactor D.toReal (fun e => (kap e : ℝ)) k t y=
      switchObjective (switchP D kap k) (switchQ D k) (switchB D k)
        (switchD2 D k) (switchD1 D k) t y := by
  simp only [ActualSharedMomentMaskedDual.switchFactor,ActualSharedMomentDual.switchFactor,
    switchObjective,switchQuadratic,switchLinear,CompactQuadraticMomentMaximum.quad,
    switchP,switchQ,switchB,switchD2,switchD1,CoeffQ.toReal]
  push_cast
  ring

theorem sectorC_cast {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : CoeffQ R) (ear : Fin 9) (eta : ℚ) (k : Fin 9) :
    (sectorC D ear eta k : ℝ)=D.toReal.width+if k ∈ outsideGaps ear then (eta : ℝ) else 0 := by
  by_cases hk : k ∈ outsideGaps ear <;> simp [sectorC,CoeffQ.toReal,hk]

def sectorErrorQ (C mu dL dR bL bR U : ℚ) (N : Fin 3 → ℕ) : ℚ :=
  (1+(19/25)*|C|+|mu|)*U/(N 0)+
    (1+(19/25)*|C|+2*|dL|+|bL|)/(N 1)+
    (1+(19/25)*|C|+2*|dR|+|bR|)/(N 2)

theorem sectorErrorQ_cast (C mu dL dR bL bR U : ℚ) (N : Fin 3 → ℕ) :
    (sectorErrorQ C mu dL dR bL bR U N : ℝ)=
      MetricSectorBoxCertificate.sectorGridError C mu dL dR bL bR U N := by
  rw [MetricSectorBoxCertificate.sectorGridError_eq]
  unfold sectorErrorQ MetricSectorBoxCertificate.angleLipschitz
    MetricSectorBoxCertificate.radiusLipschitz
  push_cast
  rfl

def stationCoeffQ {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r} (D : CoeffQ R) : ℚ :=
  ∑ i : Fin 11, (if i.val < 9 then 1 else 2)*D.mu i

theorem stationConstant_cast {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : CoeffQ R) : stationConstant D.toReal.mu=Real.pi*(stationCoeffQ D : ℝ) := by
  unfold stationConstant stationCoeffQ CoeffQ.toReal
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val < 9 <;> simp [hi] <;> ring

def constantCoeffQ {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : CoeffQ R) (kap : Finset (Fin 11) → ℚ) (eta : ℚ) : ℚ :=
  stationCoeffQ D+(∑ e ∈ edges R, kap e)-2*D.width-2*eta

def constantUpperQ {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : CoeffQ R) (kap : Finset (Fin 11) → ℚ) (eta : ℚ) : ℚ :=
  piProductUpper (constantCoeffQ D kap eta)+2*(108/125)*eta

theorem dualConstant_upper {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : CoeffQ R) (kap : Finset (Fin 11) → ℚ) (eta : ℚ) (heta : 0 ≤ eta) :
    ActualSharedMomentMaskedDual.dualConstant D.toReal (fun e => (kap e : ℝ)) eta ≤
      (constantUpperQ D kap eta : ℝ) := by
  have hp := pi_product_upper (constantCoeffQ D kap eta)
  have hb := mul_le_mul_of_nonneg_right
    MetricAreaMaskedRationalCertificate.arcsin_19_25_le_108_125
    (show (0 : ℝ) ≤ eta by exact_mod_cast heta)
  have he : ActualSharedMomentMaskedDual.dualConstant D.toReal (fun e => (kap e : ℝ)) eta=
      (constantCoeffQ D kap eta : ℝ)*Real.pi+2*Real.arcsin (19/25)*(eta : ℝ) := by
    unfold ActualSharedMomentMaskedDual.dualConstant
    rw [stationConstant_cast]
    unfold constantCoeffQ CoeffQ.toReal
    push_cast
    ring
  rw [he]
  unfold constantUpperQ
  push_cast
  linarith only [hp,hb]

def totalUpperQ {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (D : CoeffQ R) (kap : Finset (Fin 11) → ℚ) (ear : Fin 9) (eta Uface Uswitch Usector : ℚ)
    (Nface Nswitch : ℕ) (Nsector : Fin 3 → ℕ)
    (faceMax : R.Index → ℚ) (switchMax sectorMax : Fin 9 → ℚ) : ℚ :=
  constantUpperQ D kap eta+
    (∑ A : R.Index, (faceMax A+faceGridErrorQ (faceP D kap A) (faceQ D A) (faceB D A)
      Uface RatInterval.piLo Nface))+
    (∑ k : Fin 9, (switchMax k+switchGridErrorQ (switchP D kap k) (switchQ D k) (switchB D k)
      Uswitch Nswitch))+
    (∑ k : Fin 9, (sectorMax k+sectorErrorQ (sectorC D ear eta k) (D.mu (nextSite k))
      (D.leftSecond k) (D.rightSecond k) (D.leftFirst k) (D.rightFirst k) Usector Nsector))

/-- All remaining certificate conditions are finite rational checks.
The actual masked dual internally supplies the geometric identities and
the selected-ear width budget, including its proved arcsin constant. -/
theorem exclude_of_rational_certificate {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (v : NineTies c r) (E : EarData R) (D : CoeffQ R)
    (hm : MaskBalancedQ R D.faceMask D.switchMask)
    (kap : Finset (Fin 11) → ℚ) (hkap : ∀ e ∈ edges R, 0 ≤ kap e)
    (eta : ℚ) (heta : 0 ≤ eta)
    (Uface Uswitch Usector : ℚ)
    (hUface : RatInterval.piHi ≤ Uface) (hUswitch : RatInterval.piHi/2 ≤ Uswitch)
    (hUsector : RatInterval.piHi ≤ Usector)
    (Nface Nswitch : ℕ) (hNface : 0 < Nface) (hNswitch : 0 < Nswitch)
    (Nsector : Fin 3 → ℕ) (hNsector : ∀ j, 0 < Nsector j)
    (faceMax : R.Index → ℚ) (switchMax sectorMax : Fin 9 → ℚ)
    (hface : ∀ (A : R.Index) (k : Index Nface),
      faceUpperQ (faceP D kap A) (faceQ D A) (faceB D A) (faceNodeQ Uface Nface k) ≤ faceMax A)
    (hswitch : ∀ (i : Fin 9) (k : Fin (Nswitch+1)),
      switchUpperQ (switchP D kap i) (switchQ D i) (switchB D i) (switchD2 D i) (switchD1 D i)
        (nodeQ Uswitch Nswitch k) ≤ switchMax i)
    (B : Fin 9 → (∀ j, Fin (Nsector j+1)) → MetricSectorRationalNodes.NodeBounds)
    (hB : ∀ (i : Fin 9) (k : ∀ j, Fin (Nsector j+1)),
      MetricSectorRationalNodes.NodeValid (MetricSectorRationalNodes.sectorGridVectorQ Usector Nsector k 0)
        (MetricSectorRationalNodes.sectorGridVectorQ Usector Nsector k 1)
        (MetricSectorRationalNodes.sectorGridVectorQ Usector Nsector k 2) (B i k))
    (hsector : ∀ (i : Fin 9) (k : ∀ j, Fin (Nsector j+1)),
      MetricSectorRationalNodes.sectorUpperQ (sectorC D E.center eta i) (D.mu (nextSite i))
        (D.leftSecond i) (D.rightSecond i) (D.leftFirst i) (D.rightFirst i)
        (MetricSectorRationalNodes.sectorGridVectorQ Usector Nsector k 0)
        (MetricSectorRationalNodes.sectorGridVectorQ Usector Nsector k 1)
        (MetricSectorRationalNodes.sectorGridVectorQ Usector Nsector k 2) (B i k) ≤ sectorMax i)
    (hstrict : totalUpperQ D kap E.center eta Uface Uswitch Usector Nface Nswitch Nsector
      faceMax switchMax sectorMax < RatInterval.piLo) : False := by
  classical
  have htotal : (totalUpperQ D kap E.center eta Uface Uswitch Usector Nface Nswitch Nsector
      faceMax switchMax sectorMax : ℝ) < Real.pi :=
    (show (totalUpperQ D kap E.center eta Uface Uswitch Usector Nface Nswitch Nsector
      faceMax switchMax sectorMax : ℝ) < (RatInterval.piLo : ℝ)
      by exact_mod_cast hstrict).trans RatInterval.piLo_lt_pi
  have hconstant := dualConstant_upper D kap eta heta
  have hsum : ActualSharedMomentMaskedDual.dualConstant D.toReal (fun e => (kap e : ℝ)) eta+
      (∑ A : R.Index, ((faceMax A+faceGridErrorQ (faceP D kap A) (faceQ D A) (faceB D A)
        Uface RatInterval.piLo Nface : ℚ) : ℝ))+
      (∑ k : Fin 9, ((switchMax k+switchGridErrorQ (switchP D kap k) (switchQ D k) (switchB D k)
        Uswitch Nswitch : ℚ) : ℝ))+
      (∑ k : Fin 9, ((sectorMax k+sectorErrorQ (sectorC D E.center eta k) (D.mu (nextSite k))
        (D.leftSecond k) (D.rightSecond k) (D.leftFirst k) (D.rightFirst k) Usector Nsector : ℚ) : ℝ)) < Real.pi := by
    unfold totalUpperQ at htotal
    simp only [Rat.cast_add,Rat.cast_sum] at htotal ⊢
    linarith only [hconstant,htotal]
  apply ActualSharedMomentMaskedDual.exclude_of_full_domain_masked_moment_certificate
    h hr R v E D.toReal (maskBalanced_of_rational D hm) (fun e => (kap e : ℝ))
    (fun e he => by exact_mod_cast hkap e he) (eta : ℝ) (by exact_mod_cast heta)
    (fun A => ((faceMax A+faceGridErrorQ (faceP D kap A) (faceQ D A) (faceB D A)
      Uface RatInterval.piLo Nface : ℚ) : ℝ))
    (fun k => ((switchMax k+switchGridErrorQ (switchP D kap k) (switchQ D k) (switchB D k)
      Uswitch Nswitch : ℚ) : ℝ))
    (fun k => ((sectorMax k+sectorErrorQ (sectorC D E.center eta k) (D.mu (nextSite k))
      (D.leftSecond k) (D.rightSecond k) (D.leftFirst k) (D.rightFirst k) Usector Nsector : ℚ) : ℝ))
    ?_ ?_ ?_ hsum
  · intro A a ha hsum y hy
    rw [face_factor_eq_objective]
    exact face_full_domain_upper_of_rational_certificate (faceP D kap A) (faceQ D A) (faceB D A)
      Uface (faceMax A) hUface Nface hNface (hface A) a ha hsum y hy
  · intro i t ht y hy
    rw [switch_factor_eq_objective]
    exact switch_full_domain_upper_of_rational_certificate (switchP D kap i) (switchQ D i)
      (switchB D i) (switchD2 D i) (switchD1 D i) Uswitch (switchMax i)
      hUswitch Nswitch hNswitch (hswitch i) t ht y hy
  · intro i a ha u hu w hw
    have hUr : Real.pi ≤ (Usector : ℝ) :=
      RatInterval.pi_lt_piHi.le.trans (by exact_mod_cast hUsector)
    have hnodes : ∀ k : ∀ j, Fin (Nsector j+1),
        MetricSectorBoxCertificate.sectorBoxObjective
          (D.toReal.width+if i ∈ outsideGaps E.center then (eta : ℝ) else 0)
          (D.toReal.mu (nextSite i)) (D.toReal.leftSecond i) (D.toReal.rightSecond i)
          (D.toReal.leftFirst i) (D.toReal.rightFirst i)
          (CompactBoxGridCertificate.gridVector (MetricSectorBoxCertificate.sectorBoxSides Usector)
            Nsector k) ≤ (sectorMax i : ℝ) := by
      intro k
      rw [← sectorC_cast D E.center eta i]
      exact MetricSectorRationalNodes.grid_node_upper_of_rational
        (sectorC D E.center eta i) (D.mu (nextSite i)) (D.leftSecond i) (D.rightSecond i)
        (D.leftFirst i) (D.rightFirst i) Usector (sectorMax i) Nsector k (B i k) (hB i k) (hsector i k)
    have hh := ActualSharedMomentMaskedDual.sector_factor_upper_of_grid D.toReal E.center (eta : ℝ) i
      hUr Nsector hNsector hnodes a ha u hu w hw
    simpa only [Rat.cast_add,sectorErrorQ_cast,sectorC_cast,CoeffQ.toReal] using hh

end N11Formalization.ActualSharedMomentRationalCertificate
#check @N11Formalization.ActualSharedMomentRationalCertificate.exclude_of_rational_certificate
#print axioms N11Formalization.ActualSharedMomentRationalCertificate.maskBalanced_of_rational
#print axioms N11Formalization.ActualSharedMomentRationalCertificate.face_factor_eq_objective
#print axioms N11Formalization.ActualSharedMomentRationalCertificate.switch_factor_eq_objective
#print axioms N11Formalization.ActualSharedMomentRationalCertificate.dualConstant_upper
#print axioms N11Formalization.ActualSharedMomentRationalCertificate.exclude_of_rational_certificate
