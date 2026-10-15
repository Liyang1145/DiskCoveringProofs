import N11Formalization.ConvexMinorantCore
import N11Formalization.Terminal2162Minorants

/-! Finite rational line packets -> real continuum cosine minorants.
All arc shifts / signed pi endpoints / Taylor inequalities are explicit
kernel-checkable packet inputs. No numerical stationary point is assumed. -/
set_option autoImplicit false
namespace N11Formalization.CosineLinePacket
open N11Formalization
noncomputable section

def piLower (x : ℚ) : ℚ :=
  ConvexMinorantCore.endpointLo RatInterval.piLo RatInterval.piHi x
def piUpper (x : ℚ) : ℚ := -piLower (-x)

theorem piLower_le (x : ℚ) : (piLower x : ℝ)≤(x : ℝ)*Real.pi :=
  ConvexMinorantCore.endpointLo_sound RatInterval.piLo RatInterval.piHi x Real.pi
    ⟨RatInterval.piLo_lt_pi.le,RatInterval.pi_lt_piHi.le⟩
theorem le_piUpper (x : ℚ) : (x : ℝ)*Real.pi≤(piUpper x : ℝ) := by
  have h := piLower_le (-x)
  simp only [Rat.cast_neg,neg_mul] at h
  simp only [piUpper,Rat.cast_neg]
  linarith

def IncArc (a b : ℚ) (m : ℤ) : Prop :=
  piUpper (2*(m : ℚ)-1/2)≤a ∧ b≤piLower (2*(m : ℚ)+1/2)
def DecArc (a b : ℚ) (m : ℤ) : Prop :=
  piUpper (2*(m : ℚ)+1/2)≤a ∧ b≤piLower (2*(m : ℚ)+3/2)
instance (a b : ℚ) (m : ℤ) : Decidable (IncArc a b m) := by unfold IncArc; infer_instance
instance (a b : ℚ) (m : ℤ) : Decidable (DecArc a b m) := by unfold DecArc; infer_instance

theorem incArc_sound (a b : ℚ) (m : ℤ) (h : IncArc a b m) :
    MonotoneOn Real.sin (Set.Icc (a : ℝ) (b : ℝ)) := by
  have hl := (le_piUpper (2*(m : ℚ)-1/2)).trans ((Rat.cast_le (K := ℝ)).mpr h.1)
  have hh := ((Rat.cast_le (K := ℝ)).mpr h.2).trans (piLower_le (2*(m : ℚ)+1/2))
  push_cast at hl hh
  apply FlashCosineSupport.monotone_sin_arc (m := m)
  · nlinarith only [hl]
  · nlinarith only [hh]
theorem decArc_sound (a b : ℚ) (m : ℤ) (h : DecArc a b m) :
    AntitoneOn Real.sin (Set.Icc (a : ℝ) (b : ℝ)) := by
  have hl := (le_piUpper (2*(m : ℚ)+1/2)).trans ((Rat.cast_le (K := ℝ)).mpr h.1)
  have hh := ((Rat.cast_le (K := ℝ)).mpr h.2).trans (piLower_le (2*(m : ℚ)+3/2))
  push_cast at hl hh
  apply FlashCosineSupport.antitone_sin_arc (m := m)
  · nlinarith only [hl]
  · nlinarith only [hh]

inductive Rule
  | tangent | decreasing | left | right
  deriving DecidableEq, Repr
structure Packet where
  a : ℚ
  b : ℚ
  s : ℚ
  c : ℚ
  t : ℚ
  e : ℚ
  shift : ℤ
  rule : Rule

def Valid (p : Packet) : Prop :=
  p.a ≤ p.b ∧ match p.rule with
  | .tangent =>
    IncArc p.a p.b p.shift ∧ p.a ≤ p.t ∧ p.t ≤ p.b ∧ 0 ≤ p.e ∧
      p.s-p.e ≤ sinLoNLag p.t ∧ sinHiNLag p.t ≤ p.s+p.e ∧
      p.c ≤ 1-cosHiNLag p.t-p.s*p.t-p.e*(p.b-p.a)
  | .decreasing =>
    DecArc p.a p.b p.shift ∧ p.c ≤ 1-cosHiNLag p.a-p.s*p.a ∧
      p.c ≤ 1-cosHiNLag p.b-p.s*p.b
  | .left =>
    IncArc p.a p.b p.shift ∧ p.s ≤ sinLoNLag p.a ∧ p.c ≤ 1-cosHiNLag p.a-p.s*p.a
  | .right =>
    IncArc p.a p.b p.shift ∧ sinHiNLag p.b ≤ p.s ∧ p.c ≤ 1-cosHiNLag p.b-p.s*p.b
instance (p : Packet) : Decidable (Valid p) := by
  unfold Valid
  cases p.rule <;> infer_instance

theorem minorant (p : Packet) (hp : Valid p) :
    ∀ z∈Set.Icc (p.a : ℝ) (p.b : ℝ),(p.s : ℝ)*z+(p.c : ℝ)≤1-Real.cos z := by
  rcases p with ⟨a,b,s,c,t,e,m,rule⟩
  cases rule <;> simp only [Valid] at hp
  · rcases hp with ⟨_,ha,htl,hth,he,hl,hh,hc⟩
    exact FlashCosineLeaf284Energy.rational_inc (incArc_sound a b m ha) ⟨htl,hth⟩ he hl hh hc
  · rcases hp with ⟨_,ha,hl,hh⟩
    exact FlashCosineLeaf284Energy.rational_dec (decArc_sound a b m ha) hl hh
  · rcases hp with ⟨hab,ha,hs,hc⟩
    exact Terminal2162Minorants.rational_inc_left hab (incArc_sound a b m ha) hs hc
  · rcases hp with ⟨hab,ha,hs,hc⟩
    exact Terminal2162Minorants.rational_dec_right
      (Terminal2162Minorants.right_sin_bound hab (incArc_sound a b m ha) hs) hc

end
end N11Formalization.CosineLinePacket
#check @N11Formalization.CosineLinePacket.incArc_sound
#check @N11Formalization.CosineLinePacket.decArc_sound
#check @N11Formalization.CosineLinePacket.minorant
#print axioms N11Formalization.CosineLinePacket.minorant
