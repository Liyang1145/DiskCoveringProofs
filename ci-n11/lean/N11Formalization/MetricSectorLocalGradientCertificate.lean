import N11Formalization.MetricSectorRationalCellCertificate
import N11Formalization.SharedMomentFactorLocalGradientCertificate

/-! Signed local sector gradients on cells with certified positive chord
and arcsine denominator. Positivity is a finite leaf check. The certificate
also retains the earlier closed-domain bound for cells containing zero chord. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.MetricSectorLocalGradientCertificate
open RationalBoxSubdivision RationalTrigCellBounds RationalTrigLocalLipschitz
open MetricSectorRationalCellCertificate MetricSectorLocalCertificate
open MetricSectorCompactRegularity MetricSectorBoxCertificate MetricSectorRationalNodes
open ActualCircleSegmentAlgebra ActualSectorAreaEnvelope

def chordSq (x : Fin 3 → ℝ) : ℝ := x 1^2+x 2^2-2*x 1*x 2*Real.cos (x 0)
def chordGradient (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![2*x 1*x 2*Real.sin (x 0),2*x 1-2*x 2*Real.cos (x 0),2*x 2-2*x 1*Real.cos (x 0)]

def denominator (x : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (chordSq x)*Real.sqrt (1-(19/50 : ℝ)^2*chordSq x/4)

def widthNumerator (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![(19/50 : ℝ)*x 1*x 2*Real.sin (x 0),
    (19/50 : ℝ)*(x 1-x 2*Real.cos (x 0)),
    (19/50 : ℝ)*(x 2-x 1*Real.cos (x 0))]

def widthGradient (x : Fin 3 → ℝ) (s : Fin 3) : ℝ := widthNumerator x s/denominator x

theorem chord_path_hasDerivAt (a : ℝ → Fin 3 → ℝ) (da : Fin 3 → ℝ) (t : ℝ)
    (ha : ∀ s, HasDerivAt (fun z => a z s) (da s) t) :
    HasDerivAt (fun z => chordSq (a z)) (∑ s : Fin 3, chordGradient (a t) s*da s) t := by
  have hc := (Real.hasDerivAt_cos (a t 0)).comp t (ha 0)
  have hh := ((ha 1).pow 2).add ((ha 2).pow 2) |>.sub
    ((((ha 1).const_mul 2).mul (ha 2)).mul hc)
  convert! hh using 1
  simp [chordGradient,Fin.sum_univ_three,Function.comp_apply,Pi.mul_apply]
  ring

/-- The public chain rule requires positivity only at the differentiated
point; leaf certificates below prove it throughout the closed cell. -/
theorem width_path_hasDerivAt (a : ℝ → Fin 3 → ℝ) (da : Fin 3 → ℝ) (t : ℝ)
    (ha : ∀ s, HasDerivAt (fun z => a z s) (da s) t)
    (hq : 0 < chordSq (a t)) (hu : 0 < 1-(19/50 : ℝ)^2*chordSq (a t)/4) :
    HasDerivAt (fun z => sectorWidth (a z 0) (a z 1) (a z 2))
      (∑ s : Fin 3, widthGradient (a t) s*da s) t := by
  have hq' := chord_path_hasDerivAt a da t ha
  have hr := (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp t hq'
  have hsquare : ((19/50 : ℝ)*Real.sqrt (chordSq (a t))/2)^2=
      (19/50 : ℝ)^2*chordSq (a t)/4 := by
    have hs := Real.sq_sqrt hq.le
    nlinarith only [hs]
  have hn : (19/50 : ℝ)*Real.sqrt (chordSq (a t))/2 ≠ -1 := by
    intro hn
    rw [hn] at hsquare
    norm_num at hsquare
    linarith only [hu,hsquare]
  have hp : (19/50 : ℝ)*Real.sqrt (chordSq (a t))/2 ≠ 1 := by
    intro hp
    rw [hp] at hsquare
    norm_num at hsquare
    linarith only [hu,hsquare]
  have harg := (hr.const_mul (19/50 : ℝ)).div_const 2
  have hh := ((Real.hasDerivAt_arcsin hn hp).comp t harg).const_mul 2
  have hroot : Real.sqrt (chordSq (a t)) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hq)
  have hunit : Real.sqrt (1-(19/50 : ℝ)^2*chordSq (a t)/4) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hu)
  convert! hh using 1
  rw [hsquare]
  simp [widthGradient,widthNumerator,denominator,chordGradient,Fin.sum_univ_three]
  field_simp [hroot,hunit] <;> ring

def triangleGradient (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![(19/50 : ℝ)^2*x 1*x 2*Real.cos (x 0)/2,
    (19/50 : ℝ)^2*x 2*Real.sin (x 0)/2,(19/50 : ℝ)^2*x 1*Real.sin (x 0)/2]

def penaltyGradient (mu dL dR bL bR : ℝ) (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![-mu,-2*dL*x 1-bL,-2*dR*x 2-bR]

def sectorGradient (C mu dL dR bL bR : ℝ) (x : Fin 3 → ℝ) (s : Fin 3) : ℝ :=
  triangleGradient x s+(C+(1-Real.cos (sectorWidth (x 0) (x 1) (x 2)))/2)*widthGradient x s+
    penaltyGradient mu dL dR bL bR x s

theorem sector_path_hasDerivAt (C mu dL dR bL bR : ℝ)
    (a : ℝ → Fin 3 → ℝ) (da : Fin 3 → ℝ) (t : ℝ)
    (ha : ∀ s, HasDerivAt (fun z => a z s) (da s) t)
    (hq : 0 < chordSq (a t)) (hu : 0 < 1-(19/50 : ℝ)^2*chordSq (a t)/4) :
    HasDerivAt (fun z => sectorBoxObjective C mu dL dR bL bR (a z))
      (∑ s : Fin 3, sectorGradient C mu dL dR bL bR (a t) s*da s) t := by
  have hw := width_path_hasDerivAt a da t ha hq hu
  have hs := (Real.hasDerivAt_sin (a t 0)).comp t (ha 0)
  have ht := ((((ha 1).const_mul ((19/50 : ℝ)^2)).mul (ha 2)).mul hs).div_const 2
  have hseg := (hw.sub ((Real.hasDerivAt_sin (sectorWidth (a t 0) (a t 1) (a t 2))).comp t hw)).div_const 2
  have hh := ((((((ht.add hseg).add (hw.const_mul C)).sub ((ha 0).const_mul mu)).sub
    (((ha 1).pow 2).const_mul dL)).sub (((ha 2).pow 2).const_mul dR)).sub
    ((ha 1).const_mul bL)).sub ((ha 2).const_mul bR)
  convert! hh using 1
  simp [sectorGradient,triangleGradient,penaltyGradient,Fin.sum_univ_three,
    Function.comp_apply,Pi.mul_apply]
  ring

structure GradientBounds where
  denLo : ℚ
  denHi : ℚ

structure GradientValid (B : Cell (Fin 3)) (K : CellBounds) (D : GradientBounds) : Prop where
  bounds : BoundsValid B K
  chord_positive : 0 < K.chordLo
  denominator_positive : 0 < D.denLo
  denominatorHi_nonneg : 0 ≤ D.denHi
  squareLo : D.denLo^2 ≤ 1-(19/50 : ℚ)^2*(qCell B).hi/4
  squareHi : 1-(19/50 : ℚ)^2*(qCell B).lo/4 ≤ D.denHi^2

theorem unit_root_bounds {B : Cell (Fin 3)} {K : CellBounds} {D : GradientBounds}
    (hD : GradientValid B K D) {x : Fin 3 → ℝ} (hx : Mem B x) :
    (D.denLo : ℝ) ≤ Real.sqrt (1-(19/50 : ℝ)^2*chordSq x/4) ∧
      Real.sqrt (1-(19/50 : ℝ)^2*chordSq x/4) ≤ (D.denHi : ℝ) := by
  have hq := qCell_mem hD.bounds.valid.radii hx
  have hl : (D.denLo : ℝ)^2 ≤ (1-(19/50 : ℚ)^2*(qCell B).hi/4 : ℚ) := by
    exact_mod_cast hD.squareLo
  have hh : (1-(19/50 : ℚ)^2*(qCell B).lo/4 : ℚ) ≤ (D.denHi : ℝ)^2 := by
    exact_mod_cast hD.squareHi
  push_cast at hl hh
  have hlo : (D.denLo : ℝ)^2 ≤ 1-(19/50 : ℝ)^2*chordSq x/4 := by
    unfold chordSq
    nlinarith only [hl,hq.2]
  have hhi : 1-(19/50 : ℝ)^2*chordSq x/4 ≤ (D.denHi : ℝ)^2 := by
    unfold chordSq
    nlinarith only [hh,hq.1]
  exact ⟨Real.le_sqrt_of_sq_le hlo,Real.sqrt_le_iff.mpr
    ⟨by exact_mod_cast hD.denominatorHi_nonneg,hhi⟩⟩

theorem point_positive {B : Cell (Fin 3)} {K : CellBounds} {D : GradientBounds}
    (hD : GradientValid B K D) {x : Fin 3 → ℝ} (hx : Mem B x) :
    0 < chordSq x ∧ 0 < 1-(19/50 : ℝ)^2*chordSq x/4 := by
  have hc := chord_bounds_of_cell hD.bounds hx
  have hd := unit_root_bounds hD hx
  have hp : (0 : ℝ) < K.chordLo := by exact_mod_cast hD.chord_positive
  have hdp : (0 : ℝ) < D.denLo := by exact_mod_cast hD.denominator_positive
  exact ⟨Real.sqrt_pos.mp (hp.trans_le hc.1),Real.sqrt_pos.mp (hdp.trans_le hd.1)⟩

def reciprocalCell (K : CellBounds) (D : GradientBounds) : RatInterval :=
  ⟨1/(K.chordHi*D.denHi),1/(K.chordLo*D.denLo)⟩

theorem reciprocalCell_mem {B : Cell (Fin 3)} {K : CellBounds} {D : GradientBounds}
    (hD : GradientValid B K D) {x : Fin 3 → ℝ} (hx : Mem B x) :
    (reciprocalCell K D).Mem (1/denominator x) := by
  have hc := chord_bounds_of_cell hD.bounds hx
  have hd := unit_root_bounds hD hx
  have hp : (0 : ℝ) < K.chordLo := by exact_mod_cast hD.chord_positive
  have hdp : (0 : ℝ) < D.denLo := by exact_mod_cast hD.denominator_positive
  have hroot : (0 : ℝ) < Real.sqrt (chordSq x) := hp.trans_le hc.1
  have hunit : (0 : ℝ) < Real.sqrt (1-(19/50 : ℝ)^2*chordSq x/4) := hdp.trans_le hd.1
  have hchi : (0 : ℝ) < K.chordHi := hroot.trans_le hc.2
  have hlo : (K.chordLo : ℝ)*D.denLo ≤ denominator x := by
    unfold denominator
    exact (mul_le_mul_of_nonneg_left hd.1 hp.le).trans
      (mul_le_mul_of_nonneg_right hc.1 hunit.le)
  have hhi : denominator x ≤ (K.chordHi : ℝ)*D.denHi := by
    unfold denominator
    exact (mul_le_mul_of_nonneg_right hc.2 hunit.le).trans
      (mul_le_mul_of_nonneg_left hd.2 hchi.le)
  have hden : 0 < denominator x := by unfold denominator; exact mul_pos hroot hunit
  change ((1/(K.chordHi*D.denHi) : ℚ) : ℝ) ≤ _ ∧ _ ≤ ((1/(K.chordLo*D.denLo) : ℚ) : ℝ)
  push_cast
  exact ⟨one_div_le_one_div_of_le hden hhi,one_div_le_one_div_of_le (mul_pos hp hdp) hlo⟩

def widthNumeratorCell (B : Cell (Fin 3)) : Fin 3 → RatInterval :=
  ![(((RatInterval.ofRat (19/50)).mul (B 1)).mul (B 2)).mul (sinCell (B 0)),
    (RatInterval.ofRat (19/50)).mul ((B 1).sub ((B 2).mul (cosCell (B 0)))),
    (RatInterval.ofRat (19/50)).mul ((B 2).sub ((B 1).mul (cosCell (B 0))))]

def widthGradientCell (B : Cell (Fin 3)) (K : CellBounds) (D : GradientBounds) (s : Fin 3) : RatInterval :=
  (widthNumeratorCell B s).mul (reciprocalCell K D)

theorem width_numerator_mem {B : Cell (Fin 3)} {x : Fin 3 → ℝ} (hx : Mem B x) (s : Fin 3) :
    (widthNumeratorCell B s).Mem (widthNumerator x s) := by
  have hr : (RatInterval.ofRat (19/50)).Mem (19/50 : ℝ) := by
    convert RatInterval.ofRat_mem (19/50 : ℚ) using 1 <;> norm_num
  fin_cases s
  · exact RatInterval.mul_mem (RatInterval.mul_mem (RatInterval.mul_mem hr (hx 1)) (hx 2)) (sinCell_mem (hx 0))
  · exact RatInterval.mul_mem hr (RatInterval.sub_mem (hx 1) (RatInterval.mul_mem (hx 2) (cosCell_mem (hx 0))))
  · exact RatInterval.mul_mem hr (RatInterval.sub_mem (hx 2) (RatInterval.mul_mem (hx 1) (cosCell_mem (hx 0))))

theorem width_gradient_mem {B : Cell (Fin 3)} {K : CellBounds} {D : GradientBounds}
    (hD : GradientValid B K D) {x : Fin 3 → ℝ} (hx : Mem B x) (s : Fin 3) :
    (widthGradientCell B K D s).Mem (widthGradient x s) := by
  convert RatInterval.mul_mem (width_numerator_mem hx s) (reciprocalCell_mem hD hx) using 1
  · rfl
  · unfold widthGradient
    ring

def widthCell (K : CellBounds) : RatInterval := ⟨2*K.halfWidthLo,2*K.halfWidthHi⟩

def HCell (C : ℚ) (K : CellBounds) : RatInterval :=
  (RatInterval.ofRat C).add
    ((RatInterval.ofRat (1/2)).mul ((RatInterval.ofRat 1).sub (cosCell (widthCell K))))

theorem HCell_mem (C : ℚ) {B : Cell (Fin 3)} {K : CellBounds}
    (hK : BoundsValid B K) {x : Fin 3 → ℝ} (hx : Mem B x) :
    (HCell C K).Mem ((C : ℝ)+(1-Real.cos (sectorWidth (x 0) (x 1) (x 2)))/2) := by
  have hw : (widthCell K).Mem (sectorWidth (x 0) (x 1) (x 2)) := width_bounds_of_cell hK hx
  have hh := RatInterval.add_mem (RatInterval.ofRat_mem C)
    (RatInterval.mul_mem (RatInterval.ofRat_mem (1/2 : ℚ))
      (RatInterval.sub_mem (RatInterval.ofRat_mem 1) (cosCell_mem hw)))
  convert hh using 1
  · rfl
  · norm_num
    ring

def triangleGradientCell (B : Cell (Fin 3)) : Fin 3 → RatInterval :=
  ![(((RatInterval.ofRat ((19/50)^2/2)).mul (B 1)).mul (B 2)).mul (cosCell (B 0)),
    ((RatInterval.ofRat ((19/50)^2/2)).mul (B 2)).mul (sinCell (B 0)),
    ((RatInterval.ofRat ((19/50)^2/2)).mul (B 1)).mul (sinCell (B 0))]

def penaltyGradientCell (mu dL dR bL bR : ℚ) (B : Cell (Fin 3)) : Fin 3 → RatInterval :=
  ![RatInterval.ofRat (-mu),((RatInterval.ofRat (-2*dL)).mul (B 1)).sub (RatInterval.ofRat bL),
    ((RatInterval.ofRat (-2*dR)).mul (B 2)).sub (RatInterval.ofRat bR)]

def sectorGradientCell (C mu dL dR bL bR : ℚ) (B : Cell (Fin 3))
    (K : CellBounds) (D : GradientBounds) (s : Fin 3) : RatInterval :=
  ((triangleGradientCell B s).add ((HCell C K).mul (widthGradientCell B K D s))).add
    (penaltyGradientCell mu dL dR bL bR B s)

theorem triangle_gradient_mem {B : Cell (Fin 3)} {x : Fin 3 → ℝ} (hx : Mem B x) (s : Fin 3) :
    (triangleGradientCell B s).Mem (triangleGradient x s) := by
  have hr : (RatInterval.ofRat ((19/50)^2/2)).Mem ((19/50 : ℝ)^2/2) := by
    convert RatInterval.ofRat_mem ((19/50 : ℚ)^2/2) using 1 <;> norm_num
  fin_cases s
  · convert RatInterval.mul_mem (RatInterval.mul_mem (RatInterval.mul_mem hr (hx 1)) (hx 2)) (cosCell_mem (hx 0)) using 1
    · rfl
    · simp [triangleGradient]
      ring
  · convert RatInterval.mul_mem (RatInterval.mul_mem hr (hx 2)) (sinCell_mem (hx 0)) using 1
    · rfl
    · simp [triangleGradient]
      ring
  · convert RatInterval.mul_mem (RatInterval.mul_mem hr (hx 1)) (sinCell_mem (hx 0)) using 1
    · rfl
    · simp [triangleGradient]
      ring

theorem penalty_gradient_mem (mu dL dR bL bR : ℚ)
    {B : Cell (Fin 3)} {x : Fin 3 → ℝ} (hx : Mem B x) (s : Fin 3) :
    (penaltyGradientCell mu dL dR bL bR B s).Mem (penaltyGradient mu dL dR bL bR x s) := by
  have hl : (RatInterval.ofRat (-2*dL)).Mem (-2*(dL : ℝ)) := by
    convert RatInterval.ofRat_mem (-2*dL) using 1 <;> push_cast <;> rfl
  have hr : (RatInterval.ofRat (-2*dR)).Mem (-2*(dR : ℝ)) := by
    convert RatInterval.ofRat_mem (-2*dR) using 1 <;> push_cast <;> rfl
  fin_cases s
  · convert RatInterval.ofRat_mem (-mu) using 1 <;> simp [penaltyGradientCell,penaltyGradient]
  · exact RatInterval.sub_mem (RatInterval.mul_mem hl (hx 1)) (RatInterval.ofRat_mem bL)
  · exact RatInterval.sub_mem (RatInterval.mul_mem hr (hx 2)) (RatInterval.ofRat_mem bR)

theorem sector_gradient_mem (C mu dL dR bL bR : ℚ)
    {B : Cell (Fin 3)} {K : CellBounds} {D : GradientBounds} (hD : GradientValid B K D)
    {x : Fin 3 → ℝ} (hx : Mem B x) (s : Fin 3) :
    (sectorGradientCell C mu dL dR bL bR B K D s).Mem (sectorGradient C mu dL dR bL bR x s) :=
  RatInterval.add_mem (RatInterval.add_mem (triangle_gradient_mem hx s)
    (RatInterval.mul_mem (HCell_mem C hD.bounds hx) (width_gradient_mem hD hx s)))
    (penalty_gradient_mem mu dL dR bL bR hx s)

def gradientErrorQ (C mu dL dR bL bR : ℚ) (B : Cell (Fin 3))
    (K : CellBounds) (D : GradientBounds) : ℚ :=
  ∑ s : Fin 3, absBoundQ (sectorGradientCell C mu dL dR bL bR B K D s)*
    RationalBoxSubdivision.halfWidth B s

def gradientUpperQ (C mu dL dR bL bR : ℚ) (B : Cell (Fin 3))
    (K : CellBounds) (D : GradientBounds) (N : NodeBounds) : ℚ :=
  sectorUpperQ C mu dL dR bL bR (RationalBoxSubdivision.midpoint B 0)
    (RationalBoxSubdivision.midpoint B 1) (RationalBoxSubdivision.midpoint B 2) N+
      gradientErrorQ C mu dL dR bL bR B K D

theorem local_change_upper (C mu dL dR bL bR : ℚ)
    {B : Cell (Fin 3)} {K : CellBounds} {D : GradientBounds} (hD : GradientValid B K D)
    {x : Fin 3 → ℝ} (hx : Mem B x) :
    sectorBoxObjective C mu dL dR bL bR x-
      sectorBoxObjective C mu dL dR bL bR (fun s => (RationalBoxSubdivision.midpoint B s : ℝ)) ≤
        (gradientErrorQ C mu dL dR bL bR B K D : ℝ) := by
  let m (s : Fin 3) : ℝ := RationalBoxSubdivision.midpoint B s
  let path (t : ℝ) (s : Fin 3) := m s+t*(x s-m s)
  let rate (t : ℝ) := ∑ s : Fin 3, sectorGradient C mu dL dR bL bR (path t) s*(x s-m s)
  have hm : Mem B m := RationalBoxSubdivision.midpoint_mem hD.bounds.valid.intervals
  have hpath (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : Mem B (path t) :=
    SharedMomentFactorLocalGradientCertificate.segment_mem hm hx ht
  have hd (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      HasDerivAt (fun z => sectorBoxObjective C mu dL dR bL bR (path z)) (rate t) t := by
    have hp := point_positive hD (hpath t ht)
    apply sector_path_hasDerivAt C mu dL dR bL bR path (fun s => x s-m s) t ?_ hp.1 hp.2
    intro s
    simpa only [path,one_mul,id_eq] using! ((hasDerivAt_id t).mul_const (x s-m s)).const_add (m s)
  have hb (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ‖rate t‖ ≤ ∑ s : Fin 3, (absBoundQ (sectorGradientCell C mu dL dR bL bR B K D s) : ℝ)*|x s-m s| := by
    rw [Real.norm_eq_abs]
    unfold rate
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro s _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right
      (abs_of_mem (sector_gradient_mem C mu dL dR bL bR hD (hpath t ht) s)) (abs_nonneg _)
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hd t ht).hasDerivWithinAt) hb (convex_Icc (0 : ℝ) 1)
    (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1) (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)
  have hp0 : path 0=m := by funext s; simp only [path,zero_mul,add_zero]
  have hp1 : path 1=x := by funext s; dsimp [path]; ring
  have hdif : |sectorBoxObjective C mu dL dR bL bR x-sectorBoxObjective C mu dL dR bL bR m| ≤
      ∑ s : Fin 3, (absBoundQ (sectorGradientCell C mu dL dR bL bR B K D s) : ℝ)*|x s-m s| := by
    simpa only [hp0,hp1,Real.norm_eq_abs,sub_zero,abs_one,mul_one] using hh
  have herr : (∑ s : Fin 3, (absBoundQ (sectorGradientCell C mu dL dR bL bR B K D s) : ℝ)*|x s-m s|) ≤
      (gradientErrorQ C mu dL dR bL bR B K D : ℝ) := by
    unfold gradientErrorQ
    push_cast
    apply Finset.sum_le_sum
    intro s _
    exact mul_le_mul_of_nonneg_left (RationalBoxSubdivision.distance_le_halfWidth hx s)
      (by exact_mod_cast absBoundQ_nonneg (sectorGradientCell C mu dL dR bL bR B K D s))
  exact (le_abs_self _).trans (hdif.trans herr)

theorem cell_upper_of_rational_certificate (C mu dL dR bL bR M : ℚ)
    {B : Cell (Fin 3)} {K : CellBounds} {D : GradientBounds} (hD : GradientValid B K D)
    (N : NodeBounds)
    (hnode : NodeValid (RationalBoxSubdivision.midpoint B 0) (RationalBoxSubdivision.midpoint B 1)
      (RationalBoxSubdivision.midpoint B 2) N)
    (hupper : gradientUpperQ C mu dL dR bL bR B K D N ≤ M) :
    ∀ x, Mem B x → sectorBoxObjective C mu dL dR bL bR x ≤ (M : ℝ) := by
  intro x hx
  have hd := local_change_upper C mu dL dR bL bR hD hx
  have hm := sector_upper_of_node C mu dL dR bL bR hnode
  have hu : (gradientUpperQ C mu dL dR bL bR B K D N : ℝ) ≤ (M : ℝ) := by exact_mod_cast hupper
  unfold gradientUpperQ at hu
  push_cast at hu
  change sectorBoxObjective C mu dL dR bL bR (fun s => (RationalBoxSubdivision.midpoint B s : ℝ)) ≤ _ at hm
  linarith only [hd,hm,hu]

structure PositiveCertificate (C mu dL dR bL bR M : ℚ) (B : Cell (Fin 3)) where
  cell_bounds : CellBounds
  denominator_bounds : GradientBounds
  valid : GradientValid B cell_bounds denominator_bounds
  midpoint_bounds : NodeBounds
  midpoint_valid : NodeValid (RationalBoxSubdivision.midpoint B 0)
    (RationalBoxSubdivision.midpoint B 1) (RationalBoxSubdivision.midpoint B 2) midpoint_bounds
  upper : gradientUpperQ C mu dL dR bL bR B cell_bounds denominator_bounds midpoint_bounds ≤ M

theorem PositiveCertificate.sound {C mu dL dR bL bR M : ℚ} {B : Cell (Fin 3)}
    (cert : PositiveCertificate C mu dL dR bL bR M B) :
    ∀ x, Mem B x → sectorBoxObjective C mu dL dR bL bR x ≤ (M : ℝ) :=
  cell_upper_of_rational_certificate C mu dL dR bL bR M cert.valid cert.midpoint_bounds
    cert.midpoint_valid cert.upper

/-- The fallback includes every zero-chord cell; positivity is required
only by the alternative gradient leaf. -/
def Leaf (C mu dL dR bL bR M : ℚ) (B : Cell (Fin 3)) : Prop :=
  Nonempty (MetricSectorLocalCertificate.Certificate C mu dL dR bL bR M B) ∨
    Nonempty (PositiveCertificate C mu dL dR bL bR M B)

theorem leaf_sound {C mu dL dR bL bR M : ℚ} {B : Cell (Fin 3)}
    (hleaf : Leaf C mu dL dR bL bR M B) :
    ∀ x, Mem B x → sectorBoxObjective C mu dL dR bL bR x ≤ (M : ℝ) := by
  change Nonempty (MetricSectorLocalCertificate.Certificate C mu dL dR bL bR M B) ∨
    Nonempty (PositiveCertificate C mu dL dR bL bR M B) at hleaf
  rcases hleaf with hglobal | hlocal
  · rcases hglobal with ⟨cert⟩
    exact cert.sound
  · rcases hlocal with ⟨cert⟩
    exact cert.sound

theorem subdivision_upper_of_rational_certificate {C mu dL dR bL bR M : ℚ} {B : Cell (Fin 3)}
    (tree : RationalBoxSubdivision.Certificate (Leaf C mu dL dR bL bR M) B) :
    ∀ x, Mem B x → sectorBoxObjective C mu dL dR bL bR x ≤ (M : ℝ) := by
  apply certificate_sound tree
  intro D hD x hx
  exact leaf_sound hD x hx

end N11Formalization.MetricSectorLocalGradientCertificate
#print axioms N11Formalization.MetricSectorLocalGradientCertificate.chord_path_hasDerivAt
#print axioms N11Formalization.MetricSectorLocalGradientCertificate.width_path_hasDerivAt
#print axioms N11Formalization.MetricSectorLocalGradientCertificate.sector_path_hasDerivAt
#print axioms N11Formalization.MetricSectorLocalGradientCertificate.unit_root_bounds
#print axioms N11Formalization.MetricSectorLocalGradientCertificate.point_positive
#print axioms N11Formalization.MetricSectorLocalGradientCertificate.reciprocalCell_mem
#print axioms N11Formalization.MetricSectorLocalGradientCertificate.width_gradient_mem
#print axioms N11Formalization.MetricSectorLocalGradientCertificate.HCell_mem
#print axioms N11Formalization.MetricSectorLocalGradientCertificate.sector_gradient_mem
#print axioms N11Formalization.MetricSectorLocalGradientCertificate.local_change_upper
#print axioms N11Formalization.MetricSectorLocalGradientCertificate.cell_upper_of_rational_certificate
#print axioms N11Formalization.MetricSectorLocalGradientCertificate.PositiveCertificate.sound
#print axioms N11Formalization.MetricSectorLocalGradientCertificate.leaf_sound
#print axioms N11Formalization.MetricSectorLocalGradientCertificate.subdivision_upper_of_rational_certificate
