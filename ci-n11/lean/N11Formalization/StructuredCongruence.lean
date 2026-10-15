import N11Formalization.ResumeSchurEnergy
import N11Formalization.ResumeCoercivityCertificate
import N11Formalization.ResumeIntervalMatrix

/-! Exact correlation-preserving congruence algebra. Symmetric zero-row-sum
H is a signed pair form, and the G Gram factor is transformed BEFORE products.
These generic identities supply no numerical positivity by themselves. -/
set_option autoImplicit false
namespace N11Formalization.StructuredCongruence
open Finset Matrix
noncomputable section

theorem pair_bilinear (H : Fin 9 → Fin 9 → ℝ)
    (hs : ∀ i j,H i j=H j i) (hr : ∀ i,∑ j : Fin 9,H i j=0)
    (x y : Fin 9 → ℝ) :
    (∑ i : Fin 9,∑ j : Fin 9,H i j*x i*y j)=
      ∑ i : Fin 9,∑ j : Fin 9,if i<j then -H i j*(x i-x j)*(y i-y j) else 0 := by
  have hx : (∑ i : Fin 9,∑ j : Fin 9,H i j*x i*y i)=0 := by
    simp_rw [← Finset.sum_mul,hr,zero_mul]
    exact Finset.sum_const_zero
  have hy : (∑ i : Fin 9,∑ j : Fin 9,H i j*x j*y j)=0 := by
    rw [Finset.sum_comm]
    simp_rw [hs,← Finset.sum_mul,hr,zero_mul]
    exact Finset.sum_const_zero
  have hc : (∑ i : Fin 9,∑ j : Fin 9,H i j*x j*y i)=
      ∑ i : Fin 9,∑ j : Fin 9,H i j*x i*y j := by
    rw [Finset.sum_comm]
    simp_rw [hs]
  have hf :
      (∑ i : Fin 9,∑ j : Fin 9,-H i j*(x i-x j)*(y i-y j))=
        2*(∑ i : Fin 9,∑ j : Fin 9,H i j*x i*y j) := by
    have he (i j : Fin 9) :
        -H i j*(x i-x j)*(y i-y j)=
          -(H i j*x i*y i)+H i j*x i*y j+H i j*x j*y i-H i j*x j*y j := by ring
    simp_rw [he]
    simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.sum_neg_distrib]
    rw [hx,hy,hc]
    ring
  have hp := ResumeSchurEnergy.sum_symmetric_pairs
    (fun i j => -H i j*(x i-x j)*(y i-y j))
    (fun i j => by rw [hs i j]; ring) (fun i => by simp)
  linarith

/-- Matrix congruence equals the underlying bilinear form on its columns. -/
theorem congruence_entry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (C.transpose*A*C) i j=
      ∑ k : Fin n,∑ l : Fin n,A k l*C k i*C l j := by
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

def extendColumn (C : Matrix (Fin 8) (Fin 8) ℝ) (i : Fin 8) (k : Fin 9) : ℝ :=
  if h : k.val<8 then C ⟨k.val,h⟩ i else 0

theorem extendColumn_castSucc (C : Matrix (Fin 8) (Fin 8) ℝ) (i k : Fin 8) :
    extendColumn C i k.castSucc=C k i := by simp [extendColumn]
theorem extendColumn_last (C : Matrix (Fin 8) (Fin 8) ℝ) (i : Fin 8) :
    extendColumn C i 8=0 := by simp [extendColumn]

def transformedG (G : Fin 9 → Fin 4 → ℝ) (C : Matrix (Fin 8) (Fin 8) ℝ)
    (i : Fin 8) (a : Fin 4) : ℝ :=
  ∑ k : Fin 8,C k i*G k.castSucc a

theorem augmented_structured_entry (H : Fin 9 → Fin 9 → ℝ)
    (G : Fin 9 → Fin 4 → ℝ) (C : Matrix (Fin 8) (Fin 8) ℝ)
    (hs : ∀ k l,H k l=H l k) (hr : ∀ k,∑ l : Fin 9,H k l=0)
    (t μ : ℝ) (i j : Fin 8) :
    (C.transpose*ResumeCoercivityCertificate.augmented
      (fun k l : Fin 8 => H k.castSucc l.castSucc)
      (fun k a => G k.castSucc a) t μ*C) i j=
    (∑ k : Fin 9,∑ l : Fin 9,if k<l then -H k l*
      (extendColumn C i k-extendColumn C i l)*
      (extendColumn C j k-extendColumn C j l) else 0)+
      2*t*(∑ a : Fin 4,transformedG G C i a*transformedG G C j a)-
      μ*(∑ k : Fin 8,C k i*C k j) := by
  have hh := pair_bilinear H hs hr (extendColumn C i) (extendColumn C j)
  have hpin :
      (∑ k : Fin 9,∑ l : Fin 9,H k l*extendColumn C i k*extendColumn C j l)=
      ∑ k : Fin 8,∑ l : Fin 8,H k.castSucc l.castSucc*C k i*C l j := by
    rw [show
      (∑ k : Fin 9,∑ l : Fin 9,H k l*extendColumn C i k*extendColumn C j l)=
        (∑ k : Fin 8,∑ l : Fin 9,H k.castSucc l*extendColumn C i k.castSucc*
          extendColumn C j l)+(∑ l : Fin 9,H 8 l*extendColumn C i 8*extendColumn C j l)
      from Fin.sum_univ_castSucc _]
    simp only [extendColumn_last,mul_zero,zero_mul,Finset.sum_const_zero,add_zero]
    apply Finset.sum_congr rfl
    intro k _
    rw [show
      (∑ l : Fin 9,H k.castSucc l*extendColumn C i k.castSucc*extendColumn C j l)=
        (∑ l : Fin 8,H k.castSucc l.castSucc*extendColumn C i k.castSucc*
          extendColumn C j l.castSucc)+H k.castSucc 8*extendColumn C i k.castSucc*
            extendColumn C j 8 from Fin.sum_univ_castSucc _]
    simp only [extendColumn_last,extendColumn_castSucc,mul_zero,add_zero]
  rw [hpin] at hh
  rw [congruence_entry]
  simp only [ResumeCoercivityCertificate.augmented,sub_mul,add_mul,
    Finset.sum_sub_distrib,Finset.sum_add_distrib]
  have hdiag :
      (∑ k : Fin 8,∑ l : Fin 8,(if k=l then μ else 0)*C k i*C l j)=
        μ*(∑ k : Fin 8,C k i*C k j) := by
    simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hg :
      (∑ k : Fin 8,∑ l : Fin 8,2*t*(∑ a : Fin 4,G k.castSucc a*G l.castSucc a)*
        C k i*C l j)=
      2*t*(∑ a : Fin 4,transformedG G C i a*transformedG G C j a) := by
    simp only [transformedG,Finset.sum_mul,Finset.mul_sum]
    conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_rhs => arg 2; ext a; rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hh,hdiag,hg]

end
end N11Formalization.StructuredCongruence
#check @N11Formalization.StructuredCongruence.pair_bilinear
#check @N11Formalization.StructuredCongruence.augmented_structured_entry
#print axioms N11Formalization.StructuredCongruence.augmented_structured_entry
