import N11Formalization.ResumeIntervalMatrix
import N11Formalization.ResumeCoercivityCertificate

namespace N11Formalization.ResumeIntervalAugmented
open Finset Matrix RatInterval ResumeIntervalMatrix ResumeCoercivityCertificate

def augmentedBox {n k : ℕ} (H : Fin n → Fin n → RatInterval)
    (G : Fin n → Fin k → RatInterval) (t μ : ℚ) (i j : Fin n) : RatInterval :=
  ((H i j).add ((ofRat (2*t)).mul (isum (fun a => (G i a).mul (G j a))))).sub
    (ofRat (if i=j then μ else 0))

theorem augmented_mem {n k : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin n) (Fin k) ℝ) (HB : Fin n → Fin n → RatInterval)
    (GB : Fin n → Fin k → RatInterval) (t μ : ℚ)
    (hH : ∀ i j, Mem (HB i j) (H i j)) (hG : ∀ i a, Mem (GB i a) (G i a)) :
    ∀ i j, Mem (augmentedBox HB GB t μ i j) (augmented H G t μ i j) := by
  intro i j
  have hg := isum_mem (fun a => (GB i a).mul (GB j a)) (fun a => G i a*G j a)
    (fun a => mul_mem (hG i a) (hG j a))
  have hr := sub_mem (add_mem (hH i j) (mul_mem (ofRat_mem (2*t)) hg))
    (ofRat_mem (if i=j then μ else 0))
  simpa only [augmentedBox, augmented, Rat.cast_mul, Rat.cast_ofNat,
    apply_ite, Rat.cast_zero] using hr

theorem augmented_symmetric {n k : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin n) (Fin k) ℝ) (t μ : ℝ) (hH : ∀ i j, H i j=H j i) :
    ∀ i j, augmented H G t μ i j=augmented H G t μ j i := by
  intro i j
  simp only [augmented, hH i j, mul_comm (G i _) (G j _)]
  by_cases he : i=j
  · subst j; rfl
  · simp [he, Ne.symm he]

/-- A finite enclosure certificate directly yields the actual H/G coercivity
inequality. Membership is still required of actual H and G, not midpoint data. -/
theorem coercivity_of_boxes {n k : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (G : Matrix (Fin n) (Fin k) ℝ) (HB : Fin n → Fin n → RatInterval)
    (GB : Fin n → Fin k → RatInterval) (C : Matrix (Fin n) (Fin n) ℚ)
    (t μ η : ℚ) (hη : 0 < η) (hs : ∀ i j, H i j=H j i)
    (hH : ∀ i j, Mem (HB i j) (H i j)) (hG : ∀ i a, Mem (GB i a) (G i a))
    (hrow : ∀ i, η+(∑ j, if j=i then 0 else
      (congruenceBox C (augmentedBox HB GB t μ) i j).abs.hi)
      ≤ (congruenceBox C (augmentedBox HB GB t μ) i i).lo) (x : Fin n → ℝ) :
    (μ:ℝ)*(∑ i,x i^2) ≤ (∑ i,∑ j,H i j*x i*x j)
      +2*(t:ℝ)*(∑ a,(∑ i,G i a*x i)^2) := by
  have hh := nonneg_of_computed_congruence (augmented H G t μ) C
    (augmentedBox HB GB t μ) η hη (augmented_symmetric H G t μ hs)
    (augmented_mem H G HB GB t μ hH hG) hrow x
  have he := augmented_expansion H G (t : ℝ) (μ : ℝ) x
  linarith [hh, he]

#print axioms augmented_mem
#print axioms coercivity_of_boxes
end N11Formalization.ResumeIntervalAugmented
