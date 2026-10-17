import N11Formalization.HarmonicLiftExistence

set_option autoImplicit false
noncomputable section
namespace N11Formalization.LaplacianSchurBridge
open Finset

/-! Fixed signs: `a` is the actual signed anchor incidence (negative on spokes).
C = B^T W a is the actual free-anchor Laplacian block, not its negative.
Balance reads A H = -C. Source Y solving A Y = C gives the balanced H = -Y.
No invertibility or positivity is needed for these algebraic identities. -/

variable {E V J : Type*} [Fintype E] [Fintype V] [Fintype J]

def freeBlock (α : E → ℝ) (B : E → V → ℝ) (v w : V) : ℝ :=
  ∑ e, α e * B e v * B e w

def crossBlock (α : E → ℝ) (B : E → V → ℝ) (a : E → J → ℝ) (v : V) (j : J) : ℝ :=
  ∑ e, α e * B e v * a e j

def anchorBlock (α : E → ℝ) (a : E → J → ℝ) (i j : J) : ℝ :=
  ∑ e, α e * a e i * a e j

def edgeCoeff (B : E → V → ℝ) (a : E → J → ℝ) (H : V → J → ℝ) (e : E) (j : J) : ℝ :=
  a e j + ∑ v, B e v * H v j

def gram (α : E → ℝ) (K : E → J → ℝ) (i j : J) : ℝ :=
  ∑ e, α e * K e i * K e j

def Balanced (α : E → ℝ) (B : E → V → ℝ) (a : E → J → ℝ) (H : V → J → ℝ) : Prop :=
  ∀ v j, ∑ e, (α e * B e v) * edgeCoeff B a H e j = 0

theorem normal_eq_expansion (α : E → ℝ) (B : E → V → ℝ)
    (a : E → J → ℝ) (H : V → J → ℝ) (v : V) (j : J) :
    (∑ e, (α e * B e v) * edgeCoeff B a H e j) =
      crossBlock α B a v j + ∑ w, freeBlock α B v w * H w j := by
  simp only [edgeCoeff, mul_add, Finset.sum_add_distrib, Finset.mul_sum, crossBlock]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  simp only [freeBlock, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun e _ => by ring)

theorem balanced_iff_normal_eq (α : E → ℝ) (B : E → V → ℝ)
    (a : E → J → ℝ) (H : V → J → ℝ) :
    Balanced α B a H ↔
      ∀ v j, (∑ w, freeBlock α B v w * H w j) = -crossBlock α B a v j := by
  simp only [Balanced, normal_eq_expansion, add_eq_zero_iff_eq_neg]
  constructor
  · intro h v j
    linarith [h v j]
  · intro h v j
    linarith [h v j]

/-- Flux reduction at coefficient level includes all mixed response entries. -/
theorem gram_eq_anchor_flux (α : E → ℝ) (B : E → V → ℝ)
    (a : E → J → ℝ) (H : V → J → ℝ) (hbal : Balanced α B a H) (i j : J) :
    gram α (edgeCoeff B a H) i j = ∑ e, α e * a e i * edgeCoeff B a H e j := by
  simp only [Balanced] at hbal
  have hsplit : gram α (edgeCoeff B a H) i j =
      (∑ e, α e * a e i * edgeCoeff B a H e j) +
      ∑ v, H v i * ∑ e, (α e * B e v) * edgeCoeff B a H e j := by
    calc
      _ = (∑ e, α e * a e i * edgeCoeff B a H e j) +
          ∑ e, ∑ v, H v i * ((α e * B e v) * edgeCoeff B a H e j) := by
        unfold gram
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro e _
        have hs : (∑ v, H v i * ((α e * B e v) * edgeCoeff B a H e j)) =
            (∑ v, B e v * H v i) * (α e * edgeCoeff B a H e j) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun v _ => by ring)
        rw [hs]
        change α e * (a e i + ∑ v, B e v * H v i) * edgeCoeff B a H e j = _
        ring
      _ = (∑ e, α e * a e i * edgeCoeff B a H e j) +
          ∑ v, H v i * ∑ e, (α e * B e v) * edgeCoeff B a H e j := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
  rw [hsplit]
  simp only [hbal, mul_zero, Finset.sum_const_zero, add_zero]

/-- A balanced representative has precisely the Schur-shaped response D + C^T H.
The displayed C is the signed actual free-anchor block. -/
theorem gram_eq_schur (α : E → ℝ) (B : E → V → ℝ)
    (a : E → J → ℝ) (H : V → J → ℝ) (hbal : Balanced α B a H) (i j : J) :
    gram α (edgeCoeff B a H) i j =
      anchorBlock α a i j + ∑ v, crossBlock α B a v i * H v j := by
  rw [gram_eq_anchor_flux α B a H hbal i j]
  simp only [edgeCoeff, mul_add, Finset.mul_sum, Finset.sum_add_distrib, anchorBlock]
  rw [Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  simp only [crossBlock, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun e _ => by ring)

/-- Exactly the source equation A Y=C; its negative is balanced, without any inverse. -/
theorem balanced_neg_of_source_solve (α : E → ℝ) (B : E → V → ℝ)
    (a : E → J → ℝ) (Y : V → J → ℝ)
    (hY : ∀ v j, ∑ w, freeBlock α B v w * Y w j = crossBlock α B a v j) :
    Balanced α B a (fun v j => -Y v j) := by
  apply (balanced_iff_normal_eq α B a _).mpr
  intro v j
  simp only [mul_neg, Finset.sum_neg_distrib, hY]

/-- Source Schur complement equals the Gram response of the correctly signed harmonic lift. -/
theorem source_schur_eq_gram (α : E → ℝ) (B : E → V → ℝ)
    (a : E → J → ℝ) (Y : V → J → ℝ)
    (hY : ∀ v j, ∑ w, freeBlock α B v w * Y w j = crossBlock α B a v j) (i j : J) :
    anchorBlock α a i j - ∑ v, crossBlock α B a v i * Y v j =
      gram α (edgeCoeff B a (fun v j => -Y v j)) i j := by
  rw [gram_eq_schur α B a _ (balanced_neg_of_source_solve α B a Y hY) i j]
  simp only [mul_neg, Finset.sum_neg_distrib, sub_eq_add_neg]

/-- The source sign calibration: one spoke with actual free/anchor signs (+1,-1). -/
theorem one_spoke_source_sign {α : ℝ} (hα : α ≠ 0) :
    (∀ v j : Fin 1,
      ∑ w : Fin 1, freeBlock (fun _ : Fin 1 => α) (fun (_ : Fin 1) (_ : Fin 1) => 1) v w * (-1)
        = crossBlock (fun _ : Fin 1 => α) (fun (_ : Fin 1) (_ : Fin 1) => 1) (fun (_ : Fin 1) (_ : Fin 1) => -1) v j) ∧
    Balanced (fun _ : Fin 1 => α) (fun (_ : Fin 1) (_ : Fin 1) => 1) (fun (_ : Fin 1) (_ : Fin 1) => -1) (fun (_ : Fin 1) (_ : Fin 1) => 1) ∧
    ¬ Balanced (fun _ : Fin 1 => α) (fun (_ : Fin 1) (_ : Fin 1) => 1) (fun (_ : Fin 1) (_ : Fin 1) => -1) (fun (_ : Fin 1) (_ : Fin 1) => -1) := by
  constructor
  · intro v j
    simp [freeBlock, crossBlock]
  constructor
  · simp [Balanced, edgeCoeff]
  · intro h
    have h0 := h 0 0
    simp [edgeCoeff] at h0
    exact hα (by linarith)

end N11Formalization.LaplacianSchurBridge
#check @N11Formalization.LaplacianSchurBridge.normal_eq_expansion
#check @N11Formalization.LaplacianSchurBridge.balanced_iff_normal_eq
#check @N11Formalization.LaplacianSchurBridge.source_schur_eq_gram
#print axioms N11Formalization.LaplacianSchurBridge.normal_eq_expansion
#print axioms N11Formalization.LaplacianSchurBridge.balanced_iff_normal_eq
#print axioms N11Formalization.LaplacianSchurBridge.gram_eq_anchor_flux
#print axioms N11Formalization.LaplacianSchurBridge.gram_eq_schur
#print axioms N11Formalization.LaplacianSchurBridge.balanced_neg_of_source_solve
#print axioms N11Formalization.LaplacianSchurBridge.source_schur_eq_gram
#print axioms N11Formalization.LaplacianSchurBridge.one_spoke_source_sign
