import N11Formalization.ActualHubOneTurn

/-! Actual angular packing at every site of the nearest-triangle refinement.
Each positive triangle sector is split at the principal-angle cut. Real
interval packing is produced from the actual disjoint triangle interiors. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualSiteAnglePacking
open ActualFiniteNearestRefinement ActualSiteAngleChain ActualHubOneTurn
open ActualAnglePhase ActualMetricAngleAtoms ActualFaceCircumradiusAtoms FlashTiling

def pieceLeft {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) (k : Fin 2) : ℝ :=
  if Wrapped R A s then
    if k=0 then directionAngle (slotStart R A s) else -Real.pi
  else if k=0 then directionAngle (slotStart R A s) else directionAngle (slotEnd R A s)

def pieceRight {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) (k : Fin 2) : ℝ :=
  if Wrapped R A s then if k=0 then Real.pi else directionAngle (slotEnd R A s)
  else directionAngle (slotEnd R A s)

theorem piece_bounds {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) (k : Fin 2) :
    -Real.pi ≤ pieceLeft R A s k ∧ pieceLeft R A s k ≤ pieceRight R A s k ∧
      pieceRight R A s k ≤ Real.pi := by
  have ha : -Real.pi < directionAngle (slotStart R A s) ∧
      directionAngle (slotStart R A s) ≤ Real.pi := circleAngle_mem_Ioc _
  have hb : -Real.pi < directionAngle (slotEnd R A s) ∧
      directionAngle (slotEnd R A s) ≤ Real.pi := circleAngle_mem_Ioc _
  unfold pieceLeft pieceRight
  by_cases hw : Wrapped R A s
  · simp only [if_pos hw]
    split_ifs <;> exact ⟨by linarith,by linarith,by linarith⟩
  · have hn : directionAngle (slotStart R A s) ≤ directionAngle (slotEnd R A s) :=
      le_of_not_gt hw
    simp only [if_neg hw]
    split_ifs <;> exact ⟨by linarith,by linarith,by linarith⟩

theorem piece_mass {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) :
    (∑ k : Fin 2, (pieceRight R A s k-pieceLeft R A s k))=faceAngle R A s := by
  rw [Fin.sum_univ_two,actual_slot_real_lift]
  unfold pieceLeft pieceRight slotDelta
  by_cases hw : Wrapped R A s <;> simp [hw] <;> ring

/-- A strict point in either split interval is a strict actual radial cone direction. -/
theorem piece_strict_cone {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (A : R.Index) (s : Fin 3) (k : Fin 2) {z : ℝ}
    (hl : pieceLeft R A s k<z) (hr : z<pieceRight R A s k) :
    0 < det2 (slotStart R A s) (circleMap z) ∧
      0 < det2 (circleMap z) (slotEnd R A s) := by
  let a := directionAngle (slotStart R A s)
  let b := directionAngle (slotEnd R A s)
  have ha : -Real.pi < a ∧ a ≤ Real.pi := circleAngle_mem_Ioc _
  have hb : -Real.pi < b ∧ b ≤ Real.pi := circleAngle_mem_Ioc _
  have hsin : 0 < Real.sin (z-a) ∧ 0 < Real.sin (b-z) := by
    by_cases hw : Wrapped R A s
    · have hgap : Real.pi < a-b := actual_wrapped_gap R A s hw
      have ha0 : 0 < a := by linarith
      have hb0 : b < 0 := by linarith
      by_cases hk : k=0
      · simp only [pieceLeft,pieceRight,if_pos hw,if_pos hk] at hl hr
        change a<z at hl
        change z<Real.pi at hr
        constructor
        · apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
        · rw [← Real.sin_add_two_pi (b-z)]
          apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
      · simp only [pieceLeft,pieceRight,if_pos hw,if_neg hk] at hl hr
        change -Real.pi<z at hl
        change z<b at hr
        constructor
        · rw [← Real.sin_add_two_pi (z-a)]
          apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
        · apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
    · have he := actual_slot_real_lift R A s
      rw [if_neg hw,add_zero] at he
      change faceAngle R A s=b-a at he
      have hgap : b-a<Real.pi := by rw [← he]; exact (actual_face_angle_strict R A s).2
      by_cases hk : k=0
      · simp only [pieceLeft,pieceRight,if_neg hw,if_pos hk] at hl hr
        change a<z at hl
        change z<b at hr
        constructor <;> apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
      · simp only [pieceLeft,pieceRight,if_neg hw,if_neg hk] at hl hr
        change b<z at hl
        change z<b at hr
        linarith
  obtain ⟨hu,hv⟩ := actual_slot_rays_ne_zero R A s
  constructor
  · rw [direction_representation hu,det2_smul_left,ActualRingShoelacePositive.det_circleMap]
    exact mul_pos (norm_pos_iff.mpr hu) hsin.1
  · rw [direction_representation hv,det2_smul,ActualRingShoelacePositive.det_circleMap]
    exact mul_pos (norm_pos_iff.mpr hv) hsin.2

theorem actual_cone_slot_unique {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) {A B : R.Index} {s t : Fin 3} {d : Point}
    (hsite : R.labels A s=R.labels B t)
    (hud : 0 < det2 (slotStart R A s) d) (hdv : 0 < det2 d (slotEnd R A s))
    (hxd : 0 < det2 (slotStart R B t) d) (hdy : 0 < det2 d (slotEnd R B t)) :
    A=B ∧ s=t := by
  by_cases hAB : A=B
  · subst B
    exact ⟨rfl,Refinement.labels_injective R A hsite⟩
  · have hdisj := Refinement.triangles_interior_disjoint R hAB
    rw [actual_hull_at_slot R A s,actual_hull_at_slot R B t,← hsite] at hdisj
    have hcone : Disjoint
        (interior (convexHull ℝ ({c (R.labels A s),
          c (R.labels A s)+slotStart R A s,c (R.labels A s)+slotEnd R A s} : Set Point)))
        (interior (convexHull ℝ ({c (R.labels A s),
          c (R.labels A s)+slotStart R B t,c (R.labels A s)+slotEnd R B t} : Set Point))) := by
      simpa only [slotStart,slotEnd,← hsite,add_sub_cancel] using hdisj
    exact (strict_cones_disjoint (actual_slot_det_positive R A s)
      (actual_slot_det_positive R B t) hcone hud hdv hxd hdy).elim

def intervalLeft {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (i : Fin 11) (p : (R.Index × Fin 3) × Fin 2) : ℝ :=
  if R.labels p.1.1 p.1.2=i then pieceLeft R p.1.1 p.1.2 p.2 else 0

def intervalRight {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (i : Fin 11) (p : (R.Index × Fin 3) × Fin 2) : ℝ :=
  if R.labels p.1.1 p.1.2=i then pieceRight R p.1.1 p.1.2 p.2 else 0

theorem actual_intervals_disjoint {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (i : Fin 11) :
    Pairwise (fun p q : (R.Index × Fin 3) × Fin 2 =>
      Disjoint (Set.Ioc (intervalLeft R i p) (intervalRight R i p))
        (Set.Ioc (intervalLeft R i q) (intervalRight R i q))) := by
  classical
  rintro ⟨⟨A,s⟩,k⟩ ⟨⟨B,t⟩,l⟩ hpq
  apply Set.disjoint_left.mpr
  intro z hz hp
  have hAi : R.labels A s=i := by
    by_contra hn
    simp [intervalLeft,intervalRight,hn] at hz
  have hBi : R.labels B t=i := by
    by_contra hn
    simp [intervalLeft,intervalRight,hn] at hp
  simp only [intervalLeft,intervalRight,if_pos hAi,if_pos hBi] at hz hp
  let w := (max (pieceLeft R A s k) (pieceLeft R B t l)+z)/2
  have hwA : pieceLeft R A s k<w := by
    have hm := max_lt hz.1 hp.1
    have hle := le_max_left (pieceLeft R A s k) (pieceLeft R B t l)
    dsimp [w]
    linarith
  have hwB : pieceLeft R B t l<w := by
    have hm := max_lt hz.1 hp.1
    have hle := le_max_right (pieceLeft R A s k) (pieceLeft R B t l)
    dsimp [w]
    linarith
  have hwz : w<z := by dsimp [w]; linarith [max_lt hz.1 hp.1]
  have hconeA := piece_strict_cone R A s k hwA (hwz.trans_le hz.2)
  have hconeB := piece_strict_cone R B t l hwB (hwz.trans_le hp.2)
  obtain ⟨hAB,hst⟩ := actual_cone_slot_unique R (hAi.trans hBi.symm)
    hconeA.1 hconeA.2 hconeB.1 hconeB.2
  subst B
  subst t
  have hkl : k≠l := fun he => hpq (by rw [he])
  fin_cases k <;> fin_cases l <;> simp only [ne_eq,not_true_eq_false] at hkl
  all_goals
    by_cases hw : Wrapped R A s
    · have hh : directionAngle (slotEnd R A s)<directionAngle (slotStart R A s) := hw
      simp [pieceLeft,pieceRight,hw] at hz hp <;> linarith
    · simp [pieceLeft,pieceRight,hw] at hz hp <;> linarith

/-- Every actual site's full real angle mass is at most one turn.
No cover/radius or degree premise is required beyond the actual Refinement. -/
theorem actual_site_face_sum_le_two_pi {c : Fin 11 → Point} {r : ℝ}
    (R : Refinement c r) (i : Fin 11) : siteFaceSum R i ≤ 2*Real.pi := by
  classical
  let a := fun p : (R.Index × Fin 3) × Fin 2 => intervalLeft R i p+Real.pi
  let b := fun p : (R.Index × Fin 3) × Fin 2 => intervalRight R i p+Real.pi
  have hab (p : (R.Index × Fin 3) × Fin 2) : a p ≤ b p := by
    dsimp [a,b,intervalLeft,intervalRight]
    split_ifs
    · linarith [(piece_bounds R p.1.1 p.1.2 p.2).2.1]
    · rfl
  have hsub (p : (R.Index × Fin 3) × Fin 2) : Set.Ioc (a p) (b p) ⊆ Set.Ioc 0 (2*Real.pi) := by
    intro z hz
    dsimp [a,b,intervalLeft,intervalRight] at hz
    split_ifs at hz
    · have hp := piece_bounds R p.1.1 p.1.2 p.2
      exact ⟨by linarith [hz.1,hp.1],by linarith [hz.2,hp.2.2]⟩
    · exact ⟨by linarith [hz.1,Real.pi_pos],by linarith [hz.2,Real.pi_pos]⟩
  have hdisj : Pairwise (fun p q => Disjoint (Set.Ioc (a p) (b p)) (Set.Ioc (a q) (b q))) := by
    intro p q hpq
    apply Set.disjoint_left.mpr
    intro z hz hp
    apply Set.disjoint_left.mp (actual_intervals_disjoint R i hpq)
      (show z-Real.pi ∈ Set.Ioc (intervalLeft R i p) (intervalRight R i p) from
        ⟨by dsimp [a] at hz; linarith [hz.1],by dsimp [b] at hz; linarith [hz.2]⟩)
      (show z-Real.pi ∈ Set.Ioc (intervalLeft R i q) (intervalRight R i q) from
        ⟨by dsimp [a] at hp; linarith [hp.1],by dsimp [b] at hp; linarith [hp.2]⟩)
  have hbound := ActualHubAngleSum.sum_interval_lengths_le_period a b hab hdisj hsub
  have hmass : (∑ p : (R.Index × Fin 3) × Fin 2, (b p-a p))=siteFaceSum R i := by
    rw [Fintype.sum_prod_type]
    change (∑ p : R.Index × Fin 3, ∑ k : Fin 2,
      ((intervalRight R i (p,k)+Real.pi)-(intervalLeft R i (p,k)+Real.pi))) = _
    rw [Fintype.sum_prod_type]
    unfold siteFaceSum
    apply Finset.sum_congr rfl
    intro A hA
    apply Finset.sum_congr rfl
    intro s hs
    dsimp [intervalLeft,intervalRight]
    by_cases hi : R.labels A s=i
    · simp only [if_pos hi]
      simpa only [add_sub_add_right_eq_sub] using piece_mass R A s
    · simp [hi]
  rwa [hmass] at hbound
end N11Formalization.ActualSiteAnglePacking
#print axioms N11Formalization.ActualSiteAnglePacking.actual_site_face_sum_le_two_pi

