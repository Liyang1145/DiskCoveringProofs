import N11Formalization.ActualBoundaryCyclicOrder

/-! A natural-indexed strictly increasing lift of ALL periodic sorted ring
midpoints, valid beyond a single cut. Quotient/remainder are not source
geometry assumptions and allow a uniform4-cap cluster/locality producer. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualPeriodicMidpointOrder
open ActualRingDirectionOrder ActualBoundaryArcFrame ActualBoundaryCyclicOrder

def slot (n : ℕ) : Fin 9 := ⟨n%9,Nat.mod_lt _ (by decide)⟩
def turn (n : ℕ) : ℤ := (n/9:ℕ)
def liftMidpoint (c : Fin 11 → Point) (n : ℕ) : ℝ :=
  arcCenter c (slot n) (turn n)

theorem index_decomposition (n : ℕ) : n = (slot n).val+9*(n/9) := by
  dsimp [slot]
  omega

theorem slot_at (i : Fin 9) : slot i.val = i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

theorem turn_at (i : Fin 9) : turn i.val = 0 := by
  simp [turn,Nat.div_eq_of_lt i.isLt]

theorem lift_at (c : Fin 11 → Point) (i : Fin 9) :
    liftMidpoint c i.val = arcCenter c i 0 := by
  rw [liftMidpoint,slot_at,turn_at]

theorem slot_succ (n : ℕ) : slot (n+1) = nextRing (slot n) := by
  apply Fin.ext
  simp only [slot,nextRing,Fin.val_add,Fin.val_one]
  omega

theorem turn_succ (n : ℕ) :
    turn (n+1) = turn n+nextShift (slot n) := by
  have hn := index_decomposition n
  have hs := (slot n).isLt
  by_cases h8 : slot n = 8
  · have hv := congrArg (fun q : Fin 9 => q.val) h8
    change n%9 = 8 at hv
    simp only [nextShift,if_pos h8,turn]
    have hd : (n+1)/9 = n/9+1 := by omega
    rw [hd]
    push_cast
    ring
  · have hv : n%9 ≠ 8 := fun he => h8 (Fin.ext he)
    simp only [nextShift,if_neg h8,add_zero,turn]
    congr 1
    omega

theorem liftMidpoint_strictMono {c : Fin 11 → Point}
    (ho : StrictMono (midpointAngle c)) : StrictMono (liftMidpoint c) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hh := next_center_gt ho (slot n)
  rw [liftMidpoint,liftMidpoint,slot_succ,turn_succ]
  simp only [arcCenter,Int.cast_add,Int.cast_zero,zero_mul,add_zero] at hh ⊢
  nlinarith

theorem slot_period (n k : ℕ) : slot (n+9*k) = slot n := by
  apply Fin.ext
  simp [slot]

theorem turn_period (n k : ℕ) : turn (n+9*k) = turn n+(k:ℤ) := by
  have hd : (n+9*k)/9 = n/9+k := by omega
  simp only [turn,hd,Int.natCast_add]

theorem lift_period (c : Fin 11 → Point) (n k : ℕ) :
    liftMidpoint c (n+9*k) = liftMidpoint c n+(k:ℝ)*period := by
  rw [liftMidpoint,slot_period,turn_period,liftMidpoint]
  simp only [arcCenter,Int.cast_add,Int.cast_natCast]
  ring

theorem slot_four_injective (n : ℕ) : Function.Injective (fun a : Fin 4 => slot (n+a.val)) := by
  intro a b he
  have hv := congrArg (fun q : Fin 9 => q.val) he
  change (n+a.val)%9 = (n+b.val)%9 at hv
  have ha := a.isLt
  have hb := b.isLt
  apply Fin.ext
  omega

def fourSlots (n : ℕ) : Finset (Fin 9) := Finset.univ.image (fun a : Fin 4 => slot (n+a.val))

theorem fourSlots_card (n : ℕ) : (fourSlots n).card = 4 := by
  rw [fourSlots,Finset.card_image_of_injective _ (slot_four_injective n)]
  simp

end N11Formalization.ActualPeriodicMidpointOrder
#check @N11Formalization.ActualPeriodicMidpointOrder.liftMidpoint_strictMono
#print axioms N11Formalization.ActualPeriodicMidpointOrder.liftMidpoint_strictMono
