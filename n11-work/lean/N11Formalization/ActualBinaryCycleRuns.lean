import N11Formalization.ActualPeriodicMidpointOrder

/-! A binary nine-cycle with exactly two changes is two complementary
cyclic runs. Pure finite cyclic arithmetic, no geometric assumption. -/
set_option autoImplicit false
namespace N11Formalization.ActualBinaryCycleRuns
open ActualPeriodicMidpointOrder ActualBoundaryCyclicOrder

def indexAt (k : Fin 9) (n : ℕ) : Fin 9 := k+slot n

theorem at_zero (k : Fin 9) : indexAt k 0 = k := by simp [indexAt,slot]

theorem at_succ_previous (k : Fin 9) (n : ℕ) : indexAt k (n+1)-1 = indexAt k n := by
  rw [indexAt,slot_succ]
  change k+(slot n+1)-1 = k+slot n
  rw [← add_assoc,add_sub_cancel_right]

theorem at_small_eq_iff (a b : Fin 9) {n : ℕ} (hn : n < 9) :
    indexAt a n = b ↔ n = (b-a).val := by
  have hs : (slot n).val = n := Nat.mod_eq_of_lt hn
  constructor
  · intro he
    have hh := congrArg (fun k : Fin 9 => k-a) he
    change a+slot n-a=b-a at hh
    rw [add_sub_cancel_left] at hh
    have hv := congrArg Fin.val hh
    rwa [hs] at hv
  · intro he
    have hh : slot n = b-a := Fin.ext (by rw [hs,he])
    rw [indexAt,hh,add_sub_cancel]

theorem at_small_base_iff (a : Fin 9) {n : ℕ} (hn : n < 9) :
    indexAt a n = a ↔ n=0 := by
  rw [at_small_eq_iff a a hn,sub_self]
  rfl

theorem interval_constant {f : Fin 9 → Bool} {a b : Fin 9}
    (h : ∀ i : Fin 9, i ≠ a → i ≠ b → f i = f (i-1)) :
    ∀ n : ℕ, n < (b-a).val → f (indexAt a n) = f a := by
  intro n
  induction n with
  | zero =>
    intro _
    rw [at_zero]
  | succ n ih =>
    intro hn
    have hn9 : n+1 < 9 := hn.trans (b-a).isLt
    have hna : indexAt a (n+1) ≠ a := by
      intro he
      have hh := (at_small_base_iff a hn9).mp he
      omega
    have hnb : indexAt a (n+1) ≠ b := by
      intro he
      have hh := (at_small_eq_iff a b hn9).mp he
      omega
    rw [h _ hna hnb,at_succ_previous]
    exact ih (by omega)

theorem second_interval_constant {f : Fin 9 → Bool} {a b : Fin 9}
    (h : ∀ i : Fin 9, i ≠ a → i ≠ b → f i = f (i-1)) :
    ∀ n : ℕ, (b-a).val ≤ n → n < 9 → f (indexAt a n) = f b := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hmn hn9
    by_cases he : n = (b-a).val
    · rw [(at_small_eq_iff a b hn9).mpr he]
    · have hn0 : 0 < n := by omega
      have hna : indexAt a n ≠ a := by
        intro he
        have hh := (at_small_base_iff a hn9).mp he
        omega
      have hnb : indexAt a n ≠ b := by
        intro he
        have hh := (at_small_eq_iff a b hn9).mp he
        omega
      have heq : n = (n-1)+1 := by omega
      rw [h _ hna hnb,heq,at_succ_previous]
      exact ih (n-1) (by omega) (by omega) (by omega)

theorem two_changes_runs {f : Fin 9 → Bool} {a b : Fin 9} (hab : a ≠ b)
    (h : ∀ i : Fin 9, f (i-1) ≠ f i ↔ i=a ∨ i=b) :
    (b-a).val ≠ 0 ∧ f b = !f a ∧
      ∀ i : Fin 9, f (i+a) = if i.val < (b-a).val then f a else !f a := by
  have hmne : (b-a).val ≠ 0 := by
    intro he
    have hz : b-a=0 := Fin.ext he
    exact hab (sub_eq_zero.mp hz).symm
  have hmpos : 0 < (b-a).val := Nat.pos_of_ne_zero hmne
  have hconst : ∀ i : Fin 9, i ≠ a → i ≠ b → f i = f (i-1) := by
    intro i hia hib
    have he : ¬ f (i-1) ≠ f i := by rw [h]; exact not_or.mpr ⟨hia,hib⟩
    exact (not_ne_iff.mp he).symm
  have hprev : f (b-1) = f a := by
    have hn : (b-a).val-1 < (b-a).val := by omega
    have hh := interval_constant hconst ((b-a).val-1) hn
    have hp : indexAt a ((b-a).val-1) = b-1 := by
      have he : indexAt a (b-a).val = b := (at_small_eq_iff a b (b-a).isLt).mpr rfl
      have heq : (b-a).val = ((b-a).val-1)+1 := by omega
      rw [heq] at he
      have ht := at_succ_previous a ((b-a).val-1)
      rw [he] at ht
      exact ht.symm
    rwa [hp] at hh
  have hfb : f b = !f a := by
    apply Bool.eq_not_iff.mpr
    have hh := (h b).mpr (Or.inr rfl)
    rw [hprev] at hh
    exact hh.symm
  refine ⟨hmne,hfb,?_⟩
  intro i
  have hi : indexAt a i.val = i+a := by rw [indexAt,slot_at,add_comm]
  rw [← hi]
  by_cases hm : i.val < (b-a).val
  · rw [if_pos hm]
    exact interval_constant hconst i.val hm
  · rw [if_neg hm,← hfb]
    exact second_interval_constant hconst i.val (Nat.le_of_not_gt hm) i.isLt

end N11Formalization.ActualBinaryCycleRuns
#check @N11Formalization.ActualBinaryCycleRuns.two_changes_runs
#print axioms N11Formalization.ActualBinaryCycleRuns.two_changes_runs
