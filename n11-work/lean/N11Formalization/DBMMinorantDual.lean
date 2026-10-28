import N11Formalization.ConvexMinorantCore

/-! Generic REAL source-cell row transport / signed endpoint duality.
Fin9 CLOSED simplex, DBM t_j-t_i upper orientation, actual scale4096.
All coefficient/dual inequalities are explicit numeric certificate inputs. -/
set_option autoImplicit false
namespace N11Formalization.DBMMinorantDual
open N11Formalization Finset FlashCosine
open _root_.N11Formalization.ConvexMinorantCore
noncomputable section

def rowA (i j : Fin 10) (q : Fin 9) : ℚ :=
  (if q.val < j.val then 1 else 0)-(if q.val < i.val then 1 else 0)
def db (n : Fin 5011) (i j : Fin 10) : ℚ :=
  ((DBMSourceTree.data n).db i j : ℚ)/4096
def rho {m : ℕ} (rowFrom rowTo : Fin m → Fin 10) (lam : Fin m → ℚ) (q : Fin 9) : ℚ :=
  ∑ a : Fin m,lam a*rowA (rowFrom a) (rowTo a) q
def lamB {m : ℕ} (n : Fin 5011) (rowFrom rowTo : Fin m → Fin 10) (lam : Fin m → ℚ) : ℚ :=
  ∑ a : Fin m,lam a*db n (rowFrom a) (rowTo a)
def lower {m : ℕ} (w s c : Fin 36 → ℚ) (n : Fin 5011)
    (rowFrom rowTo : Fin m → Fin 10) (lam : Fin m → ℚ) (rmin : ℚ) : ℚ :=
  f0Lo w s c-lamB n rowFrom rowTo lam+rmin

theorem row_sum (i j : Fin 10) (y : Fin 9 → ℝ) :
    (∑ q : Fin 9,(rowA i j q : ℝ)*y q)=
      FlashLeafSplit.tlift y j-FlashLeafSplit.tlift y i := by
  have he (q : Fin 9) : (rowA i j q : ℝ)*y q=
      (if q.val < j.val then y q else 0)-(if q.val < i.val then y q else 0) := by
    unfold rowA
    split_ifs <;> norm_num
  simp only [he,Finset.sum_sub_distrib,FlashLeafSplit.tlift,Finset.sum_filter]

theorem rows_of_cell (n : Fin 5011) (y : Fin 9 → ℝ)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (i j : Fin 10) :
    (∑ q : Fin 9,(rowA i j q : ℝ)*y q)≤(db n i j : ℝ) := by
  rw [row_sum]
  have h := hc i j
  simpa only [db,DBMTreeKernel.matrix,Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat,
    Int.cast_ofNat] using h

theorem reduced_cost {m : ℕ} (w s : Fin 36 → ℚ)
    (rowFrom rowTo : Fin m → Fin 10) (lam : Fin m → ℚ) (rmin : ℚ)
    (hr : ∀ q : Fin 9,rmin≤endpointLo Dq DQ (g w s q)+rho rowFrom rowTo lam q)
    (q : Fin 9) :
    (rmin : ℝ)≤Dc*(g w s q : ℝ)+
      ∑ a : Fin m,(lam a : ℝ)*(rowA (rowFrom a) (rowTo a) q : ℝ) := by
  have h : (rmin : ℝ)≤(endpointLo Dq DQ (g w s q) : ℝ)+(rho rowFrom rowTo lam q : ℝ) := by
    simpa only [Rat.cast_add] using (Rat.cast_le (K := ℝ)).mpr (hr q)
  have he : (endpointLo Dq DQ (g w s q) : ℝ)≤Dc*(g w s q : ℝ) := by
    simpa only [mul_comm] using endpointLo_sound Dq DQ (g w s q) Dc D_mem
  have h' := h.trans (add_le_add he (le_rfl : (rho rowFrom rowTo lam q : ℝ)≤_))
  simpa only [rho,Rat.cast_sum,Rat.cast_mul] using h'

theorem affine_lower_of_dual {m : ℕ} (w s c : Fin 36 → ℚ) (n : Fin 5011)
    (rowFrom rowTo : Fin m → Fin 10) (lam : Fin m → ℚ) (rmin : ℚ)
    (hlam : ∀ a,0≤lam a)
    (hr : ∀ q : Fin 9,rmin≤endpointLo Dq DQ (g w s q)+rho rowFrom rowTo lam q)
    (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) :
    (lower w s c n rowFrom rowTo lam rmin : ℝ)≤affine w s c y := by
  have h := lp_step9 (fun a => rowA (rowFrom a) (rowTo a))
    (fun a => db n (rowFrom a) (rowTo a)) lam (fun q => Dc*(g w s q : ℝ)) (rmin : ℝ) y
    (fun a => by exact_mod_cast hlam a)
    (fun a => rows_of_cell n y hc (rowFrom a) (rowTo a)) hy0 hy1
    (reduced_cost w s rowFrom rowTo lam rmin hr)
  simp_rw [mul_assoc] at h
  rw [← Finset.mul_sum] at h
  have hf := affine_f0_lower w s c y
  have he : (lower w s c n rowFrom rowTo lam rmin : ℝ)=
      (f0Lo w s c : ℝ)-(∑ a : Fin m,(lam a : ℝ)*(db n (rowFrom a) (rowTo a) : ℝ))+
        (rmin : ℝ) := by
    simp only [lower,lamB,Rat.cast_add,Rat.cast_sub,Rat.cast_sum,Rat.cast_mul]
  rw [he]
  linarith

theorem radius_of_dual {m : ℕ} (b : Fin 7 → ℚ) (w s c A B : Fin 36 → ℚ)
    (n : Fin 5011) (rowFrom rowTo : Fin m → Fin 10) (lam : Fin m → ℚ) (rmin : ℚ)
    (hb0 : ∀ f,0≤b f) (hb1 : ∑ f,b f=1)
    (hw0 : ∀ k,0≤w k) (hw : ∀ k,w k ≤ mixWeight b k)
    (hminor : ∀ k,∀ z∈Set.Icc (A k : ℝ) (B k : ℝ),
      (s k : ℝ)*z+(c k : ℝ)≤1-Real.cos z)
    (hlam : ∀ a,0≤lam a)
    (hr : ∀ q : Fin 9,rmin≤endpointLo Dq DQ (g w s q)+rho rowFrom rowTo lam q)
    (hcheck : FlashCosineLeaf284Bridge.T^2<lower w s c n rowFrom rowTo lam rmin)
    (y : Fin 9 → ℝ) (hy0 : ∀ q,0≤y q) (hy1 : ∑ q,y q=1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y))
    (hz : ∀ k,zval y (FlashCosineLeaf284Bridge.iOf k) (FlashCosineLeaf284Bridge.jOf k)
      ∈Set.Icc (A k : ℝ) (B k : ℝ))
    (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius<r := by
  have hnum : (FlashCosineLeaf284Bridge.T : ℝ)^2<
      (lower w s c n rowFrom rowTo lam rmin : ℝ) := by exact_mod_cast hcheck
  exact radius_of_minorants b w s c A B hb0 hb1 hw0 hw hminor y hz
    (hnum.trans_le (affine_lower_of_dual w s c n rowFrom rowTo lam rmin hlam hr y hy0 hy1 hc))
    C Z r hf

end
end N11Formalization.DBMMinorantDual
#check @N11Formalization.DBMMinorantDual.row_sum
#check @N11Formalization.DBMMinorantDual.rows_of_cell
#check @N11Formalization.DBMMinorantDual.affine_lower_of_dual
#check @N11Formalization.DBMMinorantDual.radius_of_dual
#print axioms N11Formalization.DBMMinorantDual.affine_lower_of_dual
#print axioms N11Formalization.DBMMinorantDual.radius_of_dual
