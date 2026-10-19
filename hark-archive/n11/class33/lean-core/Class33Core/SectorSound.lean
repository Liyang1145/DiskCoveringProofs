import Class33Core.SectorKernel
/- Generic soundness of the token checker `chk` (pure structural; core-Lean tested).
   BCert is the Box-level mirror of RationalBoxSubdivision.Certificate. -/
namespace Class33Core.SectorKernel
inductive BCert (leaf : Box → Prop) : Box → Prop
  | accept {B : Box} : leaf B → BCert leaf B
  | split {B BL BR : Box} (d : Nat) (t : Rat) : splitBox B d t = some (BL, BR) →
      BCert leaf BL → BCert leaf BR → BCert leaf B

theorem chk_sound (c : Co) (M : Rat) (leaf : Box → Prop)
    (hleaf : ∀ (B : Box) (K : KB), leafOK c M B K = true → leaf B) :
    ∀ (n : Nat) (B : Box) (toks : List Tok) (e : List Box) (r : List Tok) (e' : List Box),
      chk c M n B toks e = some (r, e') → (∀ b ∈ e, BCert leaf b) →
        BCert leaf B ∧ (∀ b ∈ e', b ∈ e) := by
  intro n
  induction n with
  | zero => intro B toks e r e' h; simp [chk] at h
  | succ n ih =>
    intro B toks e r e' h he
    cases toks with
    | nil => simp [chk] at h
    | cons t rest =>
      cases t with
      | L cl ch hl hh =>
        simp only [chk] at h
        by_cases hk : leafOK c M B ⟨cl, ch, hl, hh⟩ = true
        · rw [if_pos hk] at h
          cases h
          exact ⟨BCert.accept (hleaf B _ hk), fun b hb => hb⟩
        · rw [if_neg hk] at h; cases h
      | P =>
        simp only [chk] at h
        cases e with
        | nil => simp at h
        | cons b e1 =>
          simp only at h
          by_cases hb : B = b
          · rw [if_pos hb] at h
            cases h
            subst hb
            exact ⟨he _ (List.mem_cons_self), fun x hx => List.mem_cons_of_mem _ hx⟩
          · rw [if_neg hb] at h; cases h
      | S d t =>
        simp only [chk] at h
        cases hs : splitBox B d t with
        | none => rw [hs] at h; cases h
        | some p =>
          obtain ⟨BL, BR⟩ := p
          rw [hs] at h
          simp only at h
          cases h1 : chk c M n BL rest e with
          | none => rw [h1] at h; cases h
          | some q1 =>
            obtain ⟨r1, e1⟩ := q1
            rw [h1] at h
            simp only at h
            obtain ⟨hL, he1⟩ := ih BL rest e r1 e1 h1 he
            obtain ⟨hR, he2⟩ := ih BR r1 e1 r e' h (fun b hb => he b (he1 b hb))
            exact ⟨BCert.split d t hs hL hR, fun b hb => he1 b (he2 b hb)⟩
end Class33Core.SectorKernel
