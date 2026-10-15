import N11Formalization.ActualBinaryCycleRuns

/-! Generic positive-length finite binary cycle: exactly two changes
produce two complementary cyclic runs. Reusable for the real8/9 cycles. -/
set_option autoImplicit false
namespace N11Formalization.ActualFiniteBinaryCycleRuns
variable {N : ℕ} [NeZero N]

def slot (n : ℕ) : Fin N := ⟨n%N,Nat.mod_lt _ (NeZero.pos N)⟩
def indexAt (a : Fin N) (n : ℕ) : Fin N := a+slot n

theorem slot_at (i : Fin N) : slot i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)

theorem slot_succ (n : ℕ) : slot (n+1)=(slot n : Fin N)+1 := by
  apply Fin.ext
  change (n+1)%N=(n%N+1%N)%N
  exact Nat.add_mod _ _ _

theorem at_zero (a : Fin N) : indexAt a 0=a := by simp [indexAt,slot]

theorem at_succ_previous (a : Fin N) (n : ℕ) : indexAt a (n+1)-1=indexAt a n := by
  rw [indexAt,slot_succ]
  rw [← add_assoc,add_sub_cancel_right]
  rfl

theorem at_eq_iff (a b : Fin N) {n : ℕ} (hn : n<N) :
    indexAt a n=b ↔ n=(b-a).val := by
  have hs : (slot n : Fin N).val=n := Nat.mod_eq_of_lt hn
  constructor
  · intro he
    have hh := congrArg (fun k : Fin N => k-a) he
    change a+slot n-a=b-a at hh
    rw [add_sub_cancel_left] at hh
    have hv := congrArg Fin.val hh
    rwa [hs] at hv
  · intro he
    have hh : (slot n : Fin N)=b-a := Fin.ext (by rw [hs,he])
    rw [indexAt,hh,add_sub_cancel]

theorem at_base_iff (a : Fin N) {n : ℕ} (hn : n<N) :
    indexAt a n=a ↔ n=0 := by
  rw [at_eq_iff a a hn,sub_self]
  rfl

theorem first_run {f : Fin N → Bool} {a b : Fin N}
    (h : ∀ i : Fin N, i≠a → i≠b → f i=f (i-1)) :
    ∀ n : ℕ, n < (b-a).val → f (indexAt a n)=f a := by
  intro n
  induction n with
  | zero => intro _; rw [at_zero]
  | succ n ih =>
    intro hn
    have hnN : n+1<N := hn.trans (b-a).isLt
    have hna : indexAt a (n+1)≠a := by intro he; have := (at_base_iff a hnN).mp he; omega
    have hnb : indexAt a (n+1)≠b := by intro he; have := (at_eq_iff a b hnN).mp he; omega
    rw [h _ hna hnb,at_succ_previous]
    exact ih (by omega)

theorem second_run {f : Fin N → Bool} {a b : Fin N}
    (h : ∀ i : Fin N, i≠a → i≠b → f i=f (i-1)) :
    ∀ n : ℕ, (b-a).val ≤ n → n<N → f (indexAt a n)=f b := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hmn hnN
    by_cases he : n=(b-a).val
    · rw [(at_eq_iff a b hnN).mpr he]
    · have hn0 : 0<n := by omega
      have hna : indexAt a n≠a := by intro he; have := (at_base_iff a hnN).mp he; omega
      have hnb : indexAt a n≠b := by intro he; have := (at_eq_iff a b hnN).mp he; omega
      have heq : n=(n-1)+1 := by omega
      rw [h _ hna hnb,heq,at_succ_previous]
      exact ih (n-1) (by omega) (by omega) (by omega)

theorem two_changes_runs {f : Fin N → Bool} {a b : Fin N} (hab : a≠b)
    (h : ∀ i : Fin N, f (i-1)≠f i ↔ i=a ∨ i=b) :
    (b-a).val ≠ 0 ∧ f b= !f a ∧
      ∀ i : Fin N, f (i+a)=if i.val < (b-a).val then f a else !f a := by
  have hmne : (b-a).val≠0 := by
    intro he
    have hz : b-a=0 := Fin.ext he
    exact hab (sub_eq_zero.mp hz).symm
  have hmpos := Nat.pos_of_ne_zero hmne
  have hconst : ∀ i : Fin N, i≠a → i≠b → f i=f (i-1) := by
    intro i hia hib
    have he : ¬f (i-1)≠f i := by rw [h]; exact not_or.mpr ⟨hia,hib⟩
    exact (not_ne_iff.mp he).symm
  have hprev : f (b-1)=f a := by
    have hh := first_run hconst ((b-a).val-1) (by omega)
    have hp : indexAt a ((b-a).val-1)=b-1 := by
      have he : indexAt a (b-a).val=b := (at_eq_iff a b (b-a).isLt).mpr rfl
      have heq : (b-a).val=((b-a).val-1)+1 := by omega
      rw [heq] at he
      have ht := at_succ_previous a ((b-a).val-1)
      rw [he] at ht
      exact ht.symm
    rwa [hp] at hh
  have hfb : f b= !f a := by
    apply Bool.eq_not_iff.mpr
    have hh := (h b).mpr (Or.inr rfl)
    rw [hprev] at hh
    exact hh.symm
  refine ⟨hmne,hfb,?_⟩
  intro i
  have hi : indexAt a i.val=i+a := by rw [indexAt,slot_at,add_comm]
  rw [← hi]
  by_cases hm : i.val < (b-a).val
  · rw [if_pos hm]; exact first_run hconst i.val hm
  · rw [if_neg hm,← hfb]; exact second_run hconst i.val (Nat.le_of_not_gt hm) i.isLt

end N11Formalization.ActualFiniteBinaryCycleRuns
#check @N11Formalization.ActualFiniteBinaryCycleRuns.two_changes_runs
#print axioms N11Formalization.ActualFiniteBinaryCycleRuns.two_changes_runs
