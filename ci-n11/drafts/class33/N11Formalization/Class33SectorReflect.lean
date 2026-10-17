import N11Formalization.SharedMomentEfficientFactorCertificate

/-! Class33 DRAFT (uncompiled in the WIP toolchain; the generic `chk_sound` part is the verbatim
core-Lean-tested proof): reflective checker for sector trees.  A tree is a pre-order token list
(`S d t` split dim d at t, `L` leaf with explicit `CellBounds`, `P` stub whose box is proved by a part).
`efficient_of_chk` turns a successful `chkAll` + proved stub boxes into `EfficientSectorCertificate`.
Only WIP definitions are used for the leaf test (`BoundsValid`, `sectorDirectUpperQ`), so no
interval arithmetic is re-implemented; the kernel evaluates `decide` on them. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.Class33SectorReflect
open RationalBoxSubdivision SharedMomentFiniteFactorCertificate SharedMomentEfficientFactorCertificate
open MetricSectorRationalCellCertificate MetricSectorRationalNodes ActualSharedMomentAdaptiveCertificate

structure Box where
  a0 : ℚ
  a1 : ℚ
  u0 : ℚ
  u1 : ℚ
  v0 : ℚ
  v1 : ℚ
  deriving DecidableEq

structure Co where
  C : ℚ
  mu : ℚ
  dL : ℚ
  dR : ℚ
  bL : ℚ
  bR : ℚ

inductive Tok where
  | S (d : ℕ) (t : ℚ)
  | L (cl ch hl hh : ℚ)
  | P

def boxCell (B : Box) : Cell (Fin 3) := ![⟨B.a0,B.a1⟩,⟨B.u0,B.u1⟩,⟨B.v0,B.v1⟩]

abbrev validP (B : Box) (K : CellBounds) : Prop :=
  B.a0 ≤ B.a1 ∧ B.u0 ≤ B.u1 ∧ B.v0 ≤ B.v1 ∧ 0 ≤ B.u0 ∧ B.u1 ≤ 1 ∧ 0 ≤ B.v0 ∧ B.v1 ≤ 1 ∧
  0 ≤ K.chordLo ∧ 0 ≤ K.chordHi ∧ K.chordLo^2 ≤ (qCell (boxCell B)).lo ∧
  (qCell (boxCell B)).hi ≤ K.chordHi^2 ∧
  0 ≤ K.halfWidthLo ∧ K.halfWidthLo ≤ 1 ∧ 0 ≤ K.halfWidthHi ∧ K.halfWidthHi ≤ 1 ∧
  sinHiNLag K.halfWidthLo ≤ (19/100)*K.chordLo ∧ (19/100)*K.chordHi ≤ sinLoNLag K.halfWidthHi

theorem boundsValid_of_validP {B : Box} {K : CellBounds} (h : validP B K) :
    BoundsValid (boxCell B) K := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17⟩ := h
  refine ⟨⟨?_,⟨h4,h5,h6,h7⟩⟩,h8,h9,h10,h11,⟨h12,h13⟩,⟨h14,h15⟩,h16,h17⟩
  intro i
  fin_cases i
  · exact h1
  · exact h2
  · exact h3

def leafOK (c : Co) (M : ℚ) (B : Box) (K : CellBounds) : Bool :=
  decide (validP B K) && decide (sectorDirectUpperQ c.C c.mu c.dL c.dR c.bL c.bR (boxCell B) K ≤ M)

theorem leaf_sound (c : Co) (M : ℚ) (B : Box) (K : CellBounds) (h : leafOK c M B K = true) :
    EfficientSectorLeaf c.C c.mu c.dL c.dR c.bL c.bR M (boxCell B) := by
  unfold leafOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact Or.inl (Or.inr ⟨K, boundsValid_of_validP h.1, h.2⟩)

def splitBox (B : Box) (d : ℕ) (t : ℚ) : Option (Box × Box) :=
  match d with
  | 0 => if B.a0 ≤ t ∧ t ≤ B.a1 then some ({ B with a1 := t }, { B with a0 := t }) else none
  | 1 => if B.u0 ≤ t ∧ t ≤ B.u1 then some ({ B with u1 := t }, { B with u0 := t }) else none
  | 2 => if B.v0 ≤ t ∧ t ≤ B.v1 then some ({ B with v1 := t }, { B with v0 := t }) else none
  | _ => none

def chk (c : Co) (M : ℚ) : ℕ → Box → List Tok → List Box → Option (List Tok × List Box)
  | 0, _, _, _ => none
  | _+1, _, [], _ => none
  | _+1, B, Tok.L cl ch hl hh :: r, e =>
      if leafOK c M B ⟨cl, ch, hl, hh⟩ then some (r, e) else none
  | _+1, B, Tok.P :: r, e => match e with
      | [] => none
      | b :: e' => if B = b then some (r, e') else none
  | n+1, B, Tok.S d t :: r, e =>
      match splitBox B d t with
      | none => none
      | some (BL, BR) =>
        match chk c M n BL r e with
        | none => none
        | some (r', e') => chk c M n BR r' e'

def chkAll (c : Co) (M : ℚ) (B : Box) (toks : List Tok) (e : List Box) : Bool :=
  match chk c M (toks.length + 1) B toks e with
  | some ([], []) => true
  | _ => false

inductive BCert (leaf : Box → Prop) : Box → Prop
  | accept {B : Box} : leaf B → BCert leaf B
  | split {B BL BR : Box} (d : ℕ) (t : ℚ) : splitBox B d t = some (BL, BR) →
      BCert leaf BL → BCert leaf BR → BCert leaf B

theorem chk_sound (c : Co) (M : ℚ) (leaf : Box → Prop)
    (hleaf : ∀ (B : Box) (K : CellBounds), leafOK c M B K = true → leaf B) :
    ∀ (n : ℕ) (B : Box) (toks : List Tok) (e : List Box) (r : List Tok) (e' : List Box),
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

theorem chkAll_sound (c : Co) (M : ℚ) (leaf : Box → Prop)
    (hleaf : ∀ (B : Box) (K : CellBounds), leafOK c M B K = true → leaf B)
    (B : Box) (toks : List Tok) (e : List Box) (h : chkAll c M B toks e = true)
    (he : ∀ b ∈ e, BCert leaf b) : BCert leaf B := by
  unfold chkAll at h
  cases hc : chk c M (toks.length + 1) B toks e with
  | none => rw [hc] at h; cases h
  | some p =>
    obtain ⟨r, e'⟩ := p
    exact (chk_sound c M leaf hleaf _ B toks e r e' hc he).1

/-- the Box-level tree is a `RationalBoxSubdivision.Certificate` on the corresponding cell. -/
theorem boxCell_left (B : Box) (d : Fin 3) (t : ℚ) (BL : Box)
    (h : (d = 0 ∧ BL = { B with a1 := t }) ∨ (d = 1 ∧ BL = { B with u1 := t }) ∨
      (d = 2 ∧ BL = { B with v1 := t })) :
    leftChild (boxCell B) d t = boxCell BL := by
  funext j
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> fin_cases j <;>
    simp [leftChild, boxCell, Function.update]

theorem boxCell_right (B : Box) (d : Fin 3) (t : ℚ) (BR : Box)
    (h : (d = 0 ∧ BR = { B with a0 := t }) ∨ (d = 1 ∧ BR = { B with u0 := t }) ∨
      (d = 2 ∧ BR = { B with v0 := t })) :
    rightChild (boxCell B) d t = boxCell BR := by
  funext j
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> fin_cases j <;>
    simp [rightChild, boxCell, Function.update]

theorem splitBox_spec {B BL BR : Box} {d : ℕ} {t : ℚ} (h : splitBox B d t = some (BL, BR)) :
    (d = 0 ∧ B.a0 ≤ t ∧ t ≤ B.a1 ∧ BL = { B with a1 := t } ∧ BR = { B with a0 := t }) ∨
    (d = 1 ∧ B.u0 ≤ t ∧ t ≤ B.u1 ∧ BL = { B with u1 := t } ∧ BR = { B with u0 := t }) ∨
    (d = 2 ∧ B.v0 ≤ t ∧ t ≤ B.v1 ∧ BL = { B with v1 := t } ∧ BR = { B with v0 := t }) := by
  unfold splitBox at h
  split at h
  · split at h
    · rename_i hc; cases h; exact Or.inl ⟨rfl, hc.1, hc.2, rfl, rfl⟩
    · cases h
  · split at h
    · rename_i hc; cases h; exact Or.inr (Or.inl ⟨rfl, hc.1, hc.2, rfl, rfl⟩)
    · cases h
  · split at h
    · rename_i hc; cases h; exact Or.inr (Or.inr ⟨rfl, hc.1, hc.2, rfl, rfl⟩)
    · cases h
  · cases h

theorem bcert_cert {P : Cell (Fin 3) → Prop} {B : Box}
    (h : BCert (fun B => P (boxCell B)) B) : Certificate P (boxCell B) := by
  induction h with
  | accept hp => exact Certificate.accept hp
  | @split B BL BR d t hs hL hR ihL ihR =>
    rcases splitBox_spec hs with ⟨rfl, h1, h2, rfl, rfl⟩ | ⟨rfl, h1, h2, rfl, rfl⟩ | ⟨rfl, h1, h2, rfl, rfl⟩
    · exact Certificate.split (0 : Fin 3) t h1 h2
        (by rw [boxCell_left B 0 t _ (Or.inl ⟨rfl, rfl⟩)]; exact ihL)
        (by rw [boxCell_right B 0 t _ (Or.inl ⟨rfl, rfl⟩)]; exact ihR)
    · exact Certificate.split (1 : Fin 3) t h1 h2
        (by rw [boxCell_left B 1 t _ (Or.inr (Or.inl ⟨rfl, rfl⟩))]; exact ihL)
        (by rw [boxCell_right B 1 t _ (Or.inr (Or.inl ⟨rfl, rfl⟩))]; exact ihR)
    · exact Certificate.split (2 : Fin 3) t h1 h2
        (by rw [boxCell_left B 2 t _ (Or.inr (Or.inr ⟨rfl, rfl⟩))]; exact ihL)
        (by rw [boxCell_right B 2 t _ (Or.inr (Or.inr ⟨rfl, rfl⟩))]; exact ihR)

def rootBox : Box := ⟨0, RatInterval.piHi, 0, 1, 0, 1⟩

/-- a list of (box, tokens) parts all check. -/
def partsOK (c : Co) (M : ℚ) (parts : List (Box × List Tok)) : Bool :=
  parts.all (fun p => chkAll c M p.1 p.2 [])

theorem partsOK_append (c : Co) (M : ℚ) (l1 l2 : List (Box × List Tok)) :
    partsOK c M (l1 ++ l2) = (partsOK c M l1 && partsOK c M l2) := by
  unfold partsOK
  rw [List.all_append]

theorem partsOK_sound (c : Co) (M : ℚ) (parts : List (Box × List Tok)) (h : partsOK c M parts = true) :
    ∀ b ∈ parts.map Prod.fst,
      BCert (fun B => EfficientSectorLeaf c.C c.mu c.dL c.dR c.bL c.bR M (boxCell B)) b := by
  intro b hb
  rw [List.mem_map] at hb
  obtain ⟨p, hp, rfl⟩ := hb
  unfold partsOK at h
  rw [List.all_eq_true] at h
  exact chkAll_sound c M _ (fun B K hk => leaf_sound c M B K hk) p.1 p.2 [] (h p hp)
    (fun b hb => by simp at hb)

theorem efficient_of_chk (c : Co) (M : ℚ) (skel : List Tok) (partBoxes : List Box)
    (hparts : ∀ b ∈ partBoxes,
      BCert (fun B => EfficientSectorLeaf c.C c.mu c.dL c.dR c.bL c.bR M (boxCell B)) b)
    (hskel : chkAll c M rootBox skel partBoxes = true) :
    EfficientSectorCertificate c.C c.mu c.dL c.dR c.bL c.bR M :=
  EfficientSectorCertificate.mixed (boxCell rootBox) (by intro i; fin_cases i <;> exact ⟨le_rfl, le_rfl⟩)
    (bcert_cert (chkAll_sound c M _ (fun B K hk => leaf_sound c M B K hk) rootBox skel partBoxes
      hskel hparts))

end N11Formalization.Class33SectorReflect
#print axioms N11Formalization.Class33SectorReflect.efficient_of_chk
