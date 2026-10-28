import N11Formalization.RationalTrigLocalLipschitz
import N11Formalization.SharedMomentActiveRadiusCertificate

/-! Signed whole-cell angular gradients at one fixed target maximizer.
The radius interval encloses every maximizer, including ties; the objective
is compared with its midpoint at that same radius. The final consumer still
covers every original radius in the closed unit interval. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SharedMomentFactorLocalGradientCertificate
open CompactQuadraticMomentMaximum CompactQuadraticArgmaxRange
open SharedMomentFactorGridCertificate SharedMomentFactorRationalNodes
open SharedMomentFactorIntervalCertificate RationalBoxSubdivision
open RationalTrigCellBounds RationalTrigLocalLipschitz

def next (s : Fin 3) : Fin 3 := ![1,2,0] s
def prev (s : Fin 3) : Fin 3 := ![2,0,1] s

def faceQuadraticGradient (q a : Fin 3 → ℝ) (s : Fin 3) : ℝ :=
  2*(19/50 : ℝ)^2*Real.cos (a s)*Real.sin (a (next s))*Real.sin (a (prev s))+
    2*q s*Real.sin (a s)*Real.cos (a s)

def faceGradient (p q b a : Fin 3 → ℝ) (y : ℝ) (s : Fin 3) : ℝ :=
  p s+faceQuadraticGradient q a s*y^2+b s*Real.cos (a s)*y

/-- Public chain rule for an arbitrary real path, used also for the two
triangle-plane velocities. No angle or radius-domain assumption is needed. -/
theorem face_path_hasDerivAt (p q b : Fin 3 → ℝ)
    (a : ℝ → Fin 3 → ℝ) (da : Fin 3 → ℝ) (y t : ℝ)
    (ha : ∀ s, HasDerivAt (fun x => a x s) (da s) t) :
    HasDerivAt (fun x => faceObjective p q b (a x) y)
      (∑ s : Fin 3, faceGradient p q b (a t) y s*da s) t := by
  have hs (s : Fin 3) := (Real.hasDerivAt_sin (a t s)).comp t (ha s)
  have hp := HasDerivAt.fun_sum (u := Finset.univ) (fun s _ => (ha s).const_mul (p s))
  have hq := HasDerivAt.fun_sum (u := Finset.univ) (fun s _ => ((hs s).pow 2).const_mul (q s))
  have hb := HasDerivAt.fun_sum (u := Finset.univ) (fun s _ => (hs s).const_mul (b s))
  have hc := (((hs 0).const_mul (2*(19/50 : ℝ)^2)).mul (hs 1)).mul (hs 2)
  have hh := hp.add (((hc.add hq).mul_const (y^2)).add (hb.mul_const y))
  convert! hh using 1
  simp [Fin.sum_univ_three,faceGradient,faceQuadraticGradient,next,prev,
    Function.comp_apply,Pi.mul_apply]
  ring

theorem face_coordinate_hasDerivAt (p q b a : Fin 3 → ℝ) (y t : ℝ) (s : Fin 3) :
    HasDerivAt (fun x => faceObjective p q b (Function.update a s x) y)
      (faceGradient p q b (Function.update a s t) y s) t := by
  have hh := face_path_hasDerivAt p q b (fun x => Function.update a s x)
    (fun j => if j=s then 1 else 0) y t (by
      intro j
      by_cases hj : j=s
      · subst j
        simpa only [Function.update_self,ite_true] using! hasDerivAt_id t
      · simpa only [Function.update_of_ne hj,if_neg hj] using! hasDerivAt_const t (a j))
  simpa only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,if_true] using hh

def faceQuadraticGradientCell (q : Fin 3 → ℚ) (B : Cell (Fin 3)) (s : Fin 3) : RatInterval :=
  ((((RatInterval.ofRat (2*(19/50 : ℚ)^2)).mul (cosCell (B s))).mul
    (sinCell (B (next s)))).mul (sinCell (B (prev s)))).add
    (((RatInterval.ofRat (2*q s)).mul (sinCell (B s))).mul (cosCell (B s)))

def faceGradientCell (p q b : Fin 3 → ℚ) (B : Cell (Fin 3))
    (Y : RatInterval) (s : Fin 3) : RatInterval :=
  ((RatInterval.ofRat (p s)).add ((faceQuadraticGradientCell q B s).mul (squareCell Y))).add
    (((RatInterval.ofRat (b s)).mul (cosCell (B s))).mul Y)

theorem face_quadratic_gradient_mem (q : Fin 3 → ℚ)
    {B : Cell (Fin 3)} {a : Fin 3 → ℝ} (ha : RationalBoxSubdivision.Mem B a) (s : Fin 3) :
    (faceQuadraticGradientCell q B s).Mem
      (faceQuadraticGradient (fun i => (q i : ℝ)) a s) := by
  have hc : (RatInterval.ofRat (2*(19/50 : ℚ)^2)).Mem (2*(19/50 : ℝ)^2) := by
    convert RatInterval.ofRat_mem (2*(19/50 : ℚ)^2) using 1 <;> norm_num
  have hq : (RatInterval.ofRat (2*q s)).Mem (2*(q s : ℝ)) := by
    convert RatInterval.ofRat_mem (2*q s) using 1 <;> push_cast <;> rfl
  exact RatInterval.add_mem
    (RatInterval.mul_mem (RatInterval.mul_mem (RatInterval.mul_mem hc (cosCell_mem (ha s)))
      (sinCell_mem (ha (next s)))) (sinCell_mem (ha (prev s))))
    (RatInterval.mul_mem (RatInterval.mul_mem hq (sinCell_mem (ha s))) (cosCell_mem (ha s)))

theorem face_gradient_mem (p q b : Fin 3 → ℚ)
    {B : Cell (Fin 3)} {a : Fin 3 → ℝ} {Y : RatInterval} {y : ℝ}
    (ha : RationalBoxSubdivision.Mem B a) (hy : Y.Mem y) (s : Fin 3) :
    (faceGradientCell p q b B Y s).Mem
      (faceGradient (fun i => (p i : ℝ)) (fun i => (q i : ℝ)) (fun i => (b i : ℝ)) a y s) :=
  RatInterval.add_mem (RatInterval.add_mem (RatInterval.ofRat_mem (p s))
    (RatInterval.mul_mem (face_quadratic_gradient_mem q ha s) (squareCell_mem hy)))
    (RatInterval.mul_mem (RatInterval.mul_mem (RatInterval.ofRat_mem (b s)) (cosCell_mem (ha s))) hy)

theorem segment_mem {B : Cell (Fin 3)} {a a' : Fin 3 → ℝ}
    (ha : RationalBoxSubdivision.Mem B a) (ha' : RationalBoxSubdivision.Mem B a')
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    RationalBoxSubdivision.Mem B (fun s => a s+t*(a' s-a s)) := by
  intro s
  have htl : 0 ≤ 1-t := sub_nonneg.mpr ht.2
  have hl0 := mul_nonneg htl (sub_nonneg.mpr (ha s).1)
  have hl1 := mul_nonneg ht.1 (sub_nonneg.mpr (ha' s).1)
  have hh0 := mul_nonneg htl (sub_nonneg.mpr (ha s).2)
  have hh1 := mul_nonneg ht.1 (sub_nonneg.mpr (ha' s).2)
  constructor <;> nlinarith only [hl0,hl1,hh0,hh1]

/-- The fixed-radius face difference uses the signed derivative enclosure
on the entire segment; the radius need not maximize either endpoint. -/
theorem face_fixed_radius_difference (p q b : Fin 3 → ℚ)
    {B : Cell (Fin 3)} {a a' : Fin 3 → ℝ} {Y : RatInterval} {y : ℝ}
    (ha : RationalBoxSubdivision.Mem B a) (ha' : RationalBoxSubdivision.Mem B a')
    (hy : Y.Mem y) :
    |faceObjective (fun i => (p i : ℝ)) (fun i => (q i : ℝ)) (fun i => (b i : ℝ)) a' y-
      faceObjective (fun i => (p i : ℝ)) (fun i => (q i : ℝ)) (fun i => (b i : ℝ)) a y| ≤
      ∑ s : Fin 3, (absBoundQ (faceGradientCell p q b B Y s) : ℝ)*|a' s-a s| := by
  let path (t : ℝ) (s : Fin 3) := a s+t*(a' s-a s)
  let rate (t : ℝ) := ∑ s : Fin 3,
    faceGradient (fun i => (p i : ℝ)) (fun i => (q i : ℝ)) (fun i => (b i : ℝ)) (path t) y s*
      (a' s-a s)
  have hd (t : ℝ) : HasDerivAt
      (fun t => faceObjective (fun i => (p i : ℝ)) (fun i => (q i : ℝ))
        (fun i => (b i : ℝ)) (path t) y) (rate t) t := by
    apply face_path_hasDerivAt
    intro s
    simpa only [path,one_mul,id_eq] using!
      ((hasDerivAt_id t).mul_const (a' s-a s)).const_add (a s)
  have hb (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ‖rate t‖ ≤ ∑ s : Fin 3, (absBoundQ (faceGradientCell p q b B Y s) : ℝ)*|a' s-a s| := by
    rw [Real.norm_eq_abs]
    unfold rate
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro s _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right
      (abs_of_mem (face_gradient_mem p q b (segment_mem ha ha' ht) hy s)) (abs_nonneg _)
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (_ : t ∈ Set.Icc (0 : ℝ) 1) => (hd t).hasDerivWithinAt) hb
    (convex_Icc (0 : ℝ) 1) (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
    (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1)
  have hp0 : path 0=a := by funext s; simp only [path,zero_mul,add_zero]
  have hp1 : path 1=a' := by funext s; dsimp [path]; ring
  simpa only [hp0,hp1,Real.norm_eq_abs,sub_zero,abs_one,mul_one] using hh

def faceRadiusCell (q b : Fin 3 → ℚ) (B : Cell (Fin 3)) : RatInterval :=
  ⟨lowerArgQ (faceQuadraticCell q B).lo (faceLinearCell b B).lo,
    upperArgQ (faceQuadraticCell q B).hi (faceLinearCell b B).hi⟩

def faceGradientErrorQ (p q b : Fin 3 → ℚ) (B : Cell (Fin 3)) : ℚ :=
  ∑ s : Fin 3, absBoundQ (faceGradientCell p q b B (faceRadiusCell q b B) s)*
    RationalBoxSubdivision.halfWidth B s

def faceGradientUpperQ (p q b : Fin 3 → ℚ) (B : Cell (Fin 3)) : ℚ :=
  faceUpperQ p q b (RationalBoxSubdivision.midpoint B)+faceGradientErrorQ p q b B

theorem face_envelope_le_gradient_upper (p q b : Fin 3 → ℚ)
    {B : Cell (Fin 3)} {a : Fin 3 → ℝ} (ha : RationalBoxSubdivision.Mem B a) :
    faceEnvelope (fun i => (p i : ℝ)) (fun i => (q i : ℝ)) (fun i => (b i : ℝ)) a ≤
      (faceGradientUpperQ p q b B : ℝ) := by
  have hA := SharedMomentFactorIntervalCertificate.face_quadratic_mem q ha
  have hB := SharedMomentFactorIntervalCertificate.face_linear_mem b ha
  obtain ⟨y,hy,heq,hyLo,hyHi⟩ := maximum_attained_with_rational_enclosure _ _
    (faceQuadraticCell q B).lo (faceQuadraticCell q B).hi
    (faceLinearCell b B).lo (faceLinearCell b B).hi hA.1 hA.2 hB.1 hB.2
  have hyY : (faceRadiusCell q b B).Mem y := ⟨hyLo,hyHi⟩
  have hvalid : RationalBoxSubdivision.Valid B := fun s => RatInterval.valid_of_mem (ha s)
  have hmidmem := RationalBoxSubdivision.midpoint_mem hvalid
  have hd := face_fixed_radius_difference p q b hmidmem ha hyY
  have herr : (∑ s : Fin 3, (absBoundQ (faceGradientCell p q b B (faceRadiusCell q b B) s) : ℝ)*
      |a s-(RationalBoxSubdivision.midpoint B s : ℝ)|) ≤ (faceGradientErrorQ p q b B : ℝ) := by
    unfold faceGradientErrorQ
    push_cast
    apply Finset.sum_le_sum
    intro s _
    exact mul_le_mul_of_nonneg_left (RationalBoxSubdivision.distance_le_halfWidth ha s)
      (by exact_mod_cast absBoundQ_nonneg (faceGradientCell p q b B (faceRadiusCell q b B) s))
  have hm := faceObjective_le_envelope (fun i => (p i : ℝ)) (fun i => (q i : ℝ))
    (fun i => (b i : ℝ)) (fun i => (RationalBoxSubdivision.midpoint B i : ℝ)) hy
  have hn := face_upper_of_node p q b (RationalBoxSubdivision.midpoint B)
  have he : faceObjective (fun i => (p i : ℝ)) (fun i => (q i : ℝ))
      (fun i => (b i : ℝ)) a y=faceEnvelope (fun i => (p i : ℝ))
        (fun i => (q i : ℝ)) (fun i => (b i : ℝ)) a := by
    unfold faceObjective faceEnvelope
    rw [heq]
  have hda := (le_abs_self _).trans hd
  rw [he] at hda
  unfold faceGradientUpperQ
  push_cast
  linarith only [hda,herr,hm,hn]

theorem face_upper_of_gradient_certificate (p q b : Fin 3 → ℚ) (B : Cell (Fin 3))
    (M : ℚ) (hbound : faceGradientUpperQ p q b B ≤ M) :
    ∀ a, RationalBoxSubdivision.Mem B a → ∀ y ∈ Set.Icc (0 : ℝ) 1,
      faceObjective (fun i => (p i : ℝ)) (fun i => (q i : ℝ)) (fun i => (b i : ℝ)) a y ≤ (M : ℝ) := by
  intro a ha y hy
  exact ((faceObjective_le_envelope _ _ _ a hy).trans
    (face_envelope_le_gradient_upper p q b ha)).trans (by exact_mod_cast hbound)

def switchGradient (p q b t y : ℝ) : ℝ :=
  p+((19/50 : ℝ)^2*Real.cos (2*t)+2*q*Real.sin t*Real.cos t)*y^2+b*Real.cos t*y

theorem switch_hasDerivAt (p q b d2 d1 y t : ℝ) :
    HasDerivAt (fun x => switchObjective p q b d2 d1 x y) (switchGradient p q b t y) t := by
  have hs := Real.hasDerivAt_sin t
  have hs2 := (Real.hasDerivAt_sin (2*t)).comp t ((hasDerivAt_id t).const_mul 2)
  have hA := ((hs2.const_mul ((19/50 : ℝ)^2/2)).add ((hs.fun_pow 2).const_mul q)).add_const d2
  have hB := (hs.const_mul b).add_const d1
  have hh := ((hasDerivAt_id t).const_mul p).add ((hA.mul_const (y^2)).add (hB.mul_const y))
  convert! hh using 1
  · funext x
    simp only [Pi.add_apply,Pi.mul_apply,Pi.pow_apply,Function.comp_apply,id_eq]
    unfold switchObjective quad switchQuadratic switchLinear
    ring
  · unfold switchGradient
    norm_num
    ring

def switchQuadraticGradientCell (q : ℚ) (B : Cell (Fin 1)) : RatInterval :=
  ((RatInterval.ofRat ((19/50 : ℚ)^2)).mul (cosCell ((RatInterval.ofRat 2).mul (B 0)))).add
    (((RatInterval.ofRat (2*q)).mul (sinCell (B 0))).mul (cosCell (B 0)))

def switchGradientCell (p q b : ℚ) (B : Cell (Fin 1)) (Y : RatInterval) : RatInterval :=
  ((RatInterval.ofRat p).add ((switchQuadraticGradientCell q B).mul (squareCell Y))).add
    (((RatInterval.ofRat b).mul (cosCell (B 0))).mul Y)

theorem switch_gradient_mem (p q b : ℚ) {B : Cell (Fin 1)} {Y : RatInterval} {t y : ℝ}
    (ht : (B 0).Mem t) (hy : Y.Mem y) :
    (switchGradientCell p q b B Y).Mem (switchGradient p q b t y) := by
  have h2t : ((RatInterval.ofRat 2).mul (B 0)).Mem (2*t) :=
    RatInterval.mul_mem (by simpa using RatInterval.ofRat_mem (2 : ℚ)) ht
  have hc : (RatInterval.ofRat ((19/50 : ℚ)^2)).Mem ((19/50 : ℝ)^2) := by
    convert RatInterval.ofRat_mem ((19/50 : ℚ)^2) using 1 <;> norm_num
  have hq : (RatInterval.ofRat (2*q)).Mem (2*(q : ℝ)) := by
    convert RatInterval.ofRat_mem (2*q) using 1 <;> push_cast <;> rfl
  exact RatInterval.add_mem (RatInterval.add_mem (RatInterval.ofRat_mem p)
    (RatInterval.mul_mem (RatInterval.add_mem (RatInterval.mul_mem hc (cosCell_mem h2t))
      (RatInterval.mul_mem (RatInterval.mul_mem hq (sinCell_mem ht)) (cosCell_mem ht)))
      (squareCell_mem hy)))
    (RatInterval.mul_mem (RatInterval.mul_mem (RatInterval.ofRat_mem b) (cosCell_mem ht)) hy)

def switchRadiusCell (q b d2 d1 : ℚ) (B : Cell (Fin 1)) : RatInterval :=
  ⟨lowerArgQ (switchQuadraticCell q d2 B).lo (switchLinearCell b d1 B).lo,
    upperArgQ (switchQuadraticCell q d2 B).hi (switchLinearCell b d1 B).hi⟩

def switchGradientUpperQ (p q b d2 d1 : ℚ) (B : Cell (Fin 1)) : ℚ :=
  switchUpperQ p q b d2 d1 (RationalBoxSubdivision.midpoint B 0)+
    absBoundQ (switchGradientCell p q b B (switchRadiusCell q b d2 d1 B))*
      RationalBoxSubdivision.halfWidth B 0

theorem switch_envelope_le_gradient_upper (p q b d2 d1 : ℚ)
    {B : Cell (Fin 1)} {t : ℝ} (ht : (B 0).Mem t) :
    switchEnvelope p q b d2 d1 t ≤ (switchGradientUpperQ p q b d2 d1 B : ℝ) := by
  have hA := SharedMomentFactorIntervalCertificate.switch_quadratic_mem q d2 ht
  have hB := SharedMomentFactorIntervalCertificate.switch_linear_mem b d1 ht
  obtain ⟨y,hy,heq,hyLo,hyHi⟩ := maximum_attained_with_rational_enclosure _ _
    (switchQuadraticCell q d2 B).lo (switchQuadraticCell q d2 B).hi
    (switchLinearCell b d1 B).lo (switchLinearCell b d1 B).hi hA.1 hA.2 hB.1 hB.2
  have hyY : (switchRadiusCell q b d2 d1 B).Mem y := ⟨hyLo,hyHi⟩
  have hx : RationalBoxSubdivision.Mem B (fun _ => t) := by
    intro i
    fin_cases i
    exact ht
  have hvalid : RationalBoxSubdivision.Valid B := fun i => RatInterval.valid_of_mem (hx i)
  have hmid := RationalBoxSubdivision.midpoint_mem hvalid
  have hd := image_sub_le_of_derivative_mem
    (I := B 0) (J := switchGradientCell p q b B (switchRadiusCell q b d2 d1 B))
    (fun x _ => switch_hasDerivAt p q b d2 d1 y x)
    (fun x hx => switch_gradient_mem p q b hx hyY) (hmid 0) ht
  have herr := mul_le_mul_of_nonneg_left (RationalBoxSubdivision.distance_le_halfWidth hx 0)
    (show (0 : ℝ) ≤ (absBoundQ (switchGradientCell p q b B (switchRadiusCell q b d2 d1 B)) : ℝ)
      by exact_mod_cast absBoundQ_nonneg (switchGradientCell p q b B (switchRadiusCell q b d2 d1 B)))
  have hm := switchObjective_le_envelope p q b d2 d1 (RationalBoxSubdivision.midpoint B 0) hy
  have hn := switch_upper_of_node p q b d2 d1 (RationalBoxSubdivision.midpoint B 0)
  have he : switchObjective p q b d2 d1 t y=switchEnvelope p q b d2 d1 t := by
    unfold switchObjective switchEnvelope
    rw [heq]
  have hda := (le_abs_self _).trans hd
  rw [he] at hda
  unfold switchGradientUpperQ
  push_cast
  linarith only [hda,herr,hm,hn]

theorem switch_upper_of_gradient_certificate (p q b d2 d1 : ℚ) (B : Cell (Fin 1))
    (M : ℚ) (hbound : switchGradientUpperQ p q b d2 d1 B ≤ M) :
    ∀ t, (B 0).Mem t → ∀ y ∈ Set.Icc (0 : ℝ) 1,
      switchObjective p q b d2 d1 t y ≤ (M : ℝ) := by
  intro t ht y hy
  exact ((switchObjective_le_envelope _ _ _ _ _ t hy).trans
    (switch_envelope_le_gradient_upper p q b d2 d1 ht)).trans (by exact_mod_cast hbound)

end N11Formalization.SharedMomentFactorLocalGradientCertificate
#print axioms N11Formalization.SharedMomentFactorLocalGradientCertificate.face_path_hasDerivAt
#print axioms N11Formalization.SharedMomentFactorLocalGradientCertificate.face_coordinate_hasDerivAt
#print axioms N11Formalization.SharedMomentFactorLocalGradientCertificate.face_quadratic_gradient_mem
#print axioms N11Formalization.SharedMomentFactorLocalGradientCertificate.face_gradient_mem
#print axioms N11Formalization.SharedMomentFactorLocalGradientCertificate.segment_mem
#print axioms N11Formalization.SharedMomentFactorLocalGradientCertificate.face_fixed_radius_difference
#print axioms N11Formalization.SharedMomentFactorLocalGradientCertificate.face_envelope_le_gradient_upper
#print axioms N11Formalization.SharedMomentFactorLocalGradientCertificate.face_upper_of_gradient_certificate
#print axioms N11Formalization.SharedMomentFactorLocalGradientCertificate.switch_hasDerivAt
#print axioms N11Formalization.SharedMomentFactorLocalGradientCertificate.switch_gradient_mem
#print axioms N11Formalization.SharedMomentFactorLocalGradientCertificate.switch_envelope_le_gradient_upper
#print axioms N11Formalization.SharedMomentFactorLocalGradientCertificate.switch_upper_of_gradient_certificate
