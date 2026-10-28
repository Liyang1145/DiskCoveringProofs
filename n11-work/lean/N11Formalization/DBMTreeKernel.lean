import N11Formalization.FlashLeafSplit

/-! Integer row checks → actual real continuous-cell coverage.
Node counts and witnesses are parameters here; no claim about the source tree until instantiated.
The reverse-id rank proves termination, without assuming exact tree topology.
-/
set_option autoImplicit false
namespace N11Formalization.DBMTreeKernel

structure Node (N : ℕ) where
  db : Fin 10 → Fin 10 → ℤ
  terminal : Bool
  i : Fin 10
  j : Fin 10
  m : ℤ
  left : Fin N
  right : Fin N

def Valid {N : ℕ} (data : Fin N → Node N) (n : Fin N) : Prop :=
  (data n).terminal = true ∨
    (n.val < (data n).left.val ∧ n.val < (data n).right.val ∧
    ∀ a b : Fin 10,
      min ((data n).db a b) ((data n).db a (data n).i + (data n).m +
        (data n).db (data n).j b) ≤ (data (data n).left).db a b ∧
      min ((data n).db a b) ((data n).db a (data n).j - (data n).m +
        (data n).db (data n).i b) ≤ (data (data n).right).db a b)

instance {N : ℕ} (data : Fin N → Node N) (n : Fin N) : Decidable (Valid data n) := by
  unfold Valid
  infer_instance

noncomputable def matrix {N : ℕ} (data : Fin N → Node N) (scale : ℤ)
    (n : Fin N) (a b : Fin 10) : ℝ := (data n).db a b / (scale : ℝ)

private theorem bound_of_int_min (scale : ℤ) (hs : 0 < scale)
    (x u v : ℝ) (p q w m target : ℤ)
    (hx : x ≤ (p : ℝ) / scale) (hu : u ≤ (q : ℝ) / scale)
    (hv : v ≤ (w : ℝ) / scale)
    (heq : x = u + v + (m : ℝ) / scale)
    (hint : min p (q + m + w) ≤ target) : x ≤ (target : ℝ) / scale := by
  have hsR : (0 : ℝ) < (scale : ℝ) := by exact_mod_cast hs
  rcases le_total p (q + m + w) with h | h
  · have hh : p ≤ target := by simpa [min_eq_left h] using hint
    have hhR : (p : ℝ) ≤ (target : ℝ) := by exact_mod_cast hh
    exact hx.trans (div_le_div_of_nonneg_right hhR hsR.le)
  · have hh : q + m + w ≤ target := by simpa [min_eq_right h] using hint
    have hhR : (q : ℝ) + m + w ≤ (target : ℝ) := by exact_mod_cast hh
    have hhdiv := div_le_div_of_nonneg_right hhR hsR.le
    have hsum : u + v + (m : ℝ) / scale ≤ ((q : ℝ) + m + w) / scale := by
      rw [add_div, add_div]
      linarith
    rw [heq]
    exact hsum.trans hhdiv

/-- A checked split covers every real parent point, including the split equality. -/
theorem step_cover {N : ℕ} (data : Fin N → Node N) (scale : ℤ) (hs : 0 < scale)
    (n : Fin N) (hn : Valid data n) (hleaf : (data n).terminal ≠ true)
    (t : Fin 10 → ℝ) (ht : FlashLeafSplit.Cell (matrix data scale n) t) :
    FlashLeafSplit.Cell (matrix data scale (data n).left) t ∨
    FlashLeafSplit.Cell (matrix data scale (data n).right) t := by
  have hr := (hn.resolve_left hleaf).2.2
  by_cases h : t (data n).j - t (data n).i ≤ ((data n).m : ℝ) / scale
  · left
    intro a b
    apply le_trans ?_ (le_refl (matrix data scale (data n).left a b))
    have hl : t b - t a ≤ ((data n).db a (data n).i : ℝ) / scale +
        ((data n).db (data n).j b : ℝ) / scale + ((data n).m : ℝ) / scale := by
      have h1 := ht a (data n).i
      have h2 := ht (data n).j b
      unfold matrix at h1 h2
      linarith
    unfold matrix
    rcases le_total ((data n).db a b)
        ((data n).db a (data n).i + (data n).m + (data n).db (data n).j b) with hm | hm
    · have hh := (hr a b).1
      rw [min_eq_left hm] at hh
      have hhR : ((data n).db a b : ℝ) ≤ ((data (data n).left).db a b : ℝ) := by exact_mod_cast hh
      exact (ht a b).trans (div_le_div_of_nonneg_right hhR (by exact_mod_cast hs.le))
    · have hh := (hr a b).1
      rw [min_eq_right hm] at hh
      have hhR : ((data n).db a (data n).i : ℝ) + (data n).m + (data n).db (data n).j b ≤
          ((data (data n).left).db a b : ℝ) := by exact_mod_cast hh
      have hdiv := div_le_div_of_nonneg_right hhR (show (0 : ℝ) ≤ (scale : ℝ) by exact_mod_cast hs.le)
      rw [add_div, add_div] at hdiv
      linarith
  · right
    intro a b
    have h' : t (data n).i - t (data n).j ≤ -((data n).m : ℝ) / scale := by
      rw [neg_div]; linarith
    have hl : t b - t a ≤ ((data n).db a (data n).j : ℝ) / scale +
        ((data n).db (data n).i b : ℝ) / scale - ((data n).m : ℝ) / scale := by
      have h1 := ht a (data n).j
      have h2 := ht (data n).i b
      unfold matrix at h1 h2
      linarith
    unfold matrix
    rcases le_total ((data n).db a b)
        ((data n).db a (data n).j - (data n).m + (data n).db (data n).i b) with hm | hm
    · have hh := (hr a b).2
      rw [min_eq_left hm] at hh
      have hhR : ((data n).db a b : ℝ) ≤ ((data (data n).right).db a b : ℝ) := by exact_mod_cast hh
      exact (ht a b).trans (div_le_div_of_nonneg_right hhR (by exact_mod_cast hs.le))
    · have hh := (hr a b).2
      rw [min_eq_right hm] at hh
      have hhR : ((data n).db a (data n).j : ℝ) - (data n).m + (data n).db (data n).i b ≤
          ((data (data n).right).db a b : ℝ) := by exact_mod_cast hh
      have hdiv := div_le_div_of_nonneg_right hhR (show (0 : ℝ) ≤ (scale : ℝ) by exact_mod_cast hs.le)
      rw [add_div, sub_div] at hdiv
      linarith

/-- One integer interface promotes discrete row checks to continuous leaf coverage. -/
theorem terminal_cover {N : ℕ} (data : Fin N → Node N) (scale : ℤ) (hs : 0 < scale)
    (hv : ∀ n, Valid data n) (t : Fin 10 → ℝ) (n : Fin N)
    (ht : FlashLeafSplit.Cell (matrix data scale n) t) :
    ∃ l : Fin N, (data l).terminal = true ∧ FlashLeafSplit.Cell (matrix data scale l) t := by
  have hmain : ∀ k : ℕ, ∀ n : Fin N, N - n.val = k →
      FlashLeafSplit.Cell (matrix data scale n) t →
      ∃ l : Fin N, (data l).terminal = true ∧ FlashLeafSplit.Cell (matrix data scale l) t := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro n hk hcell
      by_cases hleaf : (data n).terminal = true
      · exact ⟨n, hleaf, hcell⟩
      · have hn := (hv n).resolve_left hleaf
        have hl : N - (data n).left.val < k := by have := (data n).left.isLt; omega
        have hr : N - (data n).right.val < k := by have := (data n).right.isLt; omega
        rcases step_cover data scale hs n (hv n) hleaf t hcell with hc | hc
        · exact ih _ hl _ rfl hc
        · exact ih _ hr _ rfl hc
  exact hmain _ n rfl ht

end N11Formalization.DBMTreeKernel
#check @N11Formalization.DBMTreeKernel.terminal_cover
#print axioms N11Formalization.DBMTreeKernel.step_cover
#print axioms N11Formalization.DBMTreeKernel.terminal_cover
