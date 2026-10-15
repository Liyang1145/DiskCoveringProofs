import N11Formalization.C450OuterGeometry

/-! Real closed-interval quadratic soundness for grouped C450 packets.
Numeric packet validity and actual geometry remain separate obligations. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450QuadraticBounds

def quad (B C x : ℝ) : ℝ := x^2+2*B*x+C
def vertex (lo hi B : ℝ) : ℝ := min hi (max lo (-B))
def minimum (lo hi B C : ℝ) : ℝ := quad B C (vertex lo hi B)

theorem upper {lo hi x B C K : ℝ}
    (hx0 : lo ≤ x) (hx1 : x ≤ hi)
    (hlo : quad B C lo ≤ K) (hhi : quad B C hi ≤ K) :
    quad B C x ≤ K := by
  by_cases heq : lo = hi
  · have hx : x = lo := by linarith
    rw [hx]
    exact hlo
  · have hlt : lo < hi := (lt_or_eq_of_le (hx0.trans hx1)).resolve_right heq
    have hd : 0 < hi-lo := sub_pos.mpr hlt
    have hleft := mul_le_mul_of_nonneg_left hlo (sub_nonneg.mpr hx1)
    have hright := mul_le_mul_of_nonneg_left hhi (sub_nonneg.mpr hx0)
    have hp := mul_nonneg (sub_nonneg.mpr hx0) (sub_nonneg.mpr hx1)
    have hp3 := mul_nonneg hp hd.le
    have hid :
        (hi-x)*quad B C lo+(x-lo)*quad B C hi =
          (hi-lo)*quad B C x+(x-lo)*(hi-x)*(hi-lo) := by
      unfold quad
      ring
    have hlower :
        (hi-lo)*quad B C x ≤ (hi-x)*quad B C lo+(x-lo)*quad B C hi := by
      rw [hid]
      exact le_add_of_nonneg_right hp3
    have hupper := add_le_add hleft hright
    have hs : (hi-x)*K+(x-lo)*K = (hi-lo)*K := by ring
    rw [hs] at hupper
    exact (mul_le_mul_iff_of_pos_left hd).mp (hlower.trans hupper)

theorem minimum_le {lo hi x B C : ℝ} (hx0 : lo ≤ x) (hx1 : x ≤ hi) :
    minimum lo hi B C ≤ quad B C x := by
  have horder : lo ≤ hi := hx0.trans hx1
  by_cases hleft : -B ≤ lo
  · have hv : vertex lo hi B = lo := by
      unfold vertex
      rw [max_eq_left hleft,min_eq_right horder]
    unfold minimum
    rw [hv]
    have hf : 0 ≤ x+lo+2*B := by linarith
    have hp := mul_nonneg (sub_nonneg.mpr hx0) hf
    unfold quad
    nlinarith only [hp]
  · have hlo : lo ≤ -B := (lt_of_not_ge hleft).le
    by_cases hright : hi ≤ -B
    · have hv : vertex lo hi B = hi := by
        unfold vertex
        rw [max_eq_right hlo,min_eq_left hright]
      unfold minimum
      rw [hv]
      have hf : x+hi+2*B ≤ 0 := by linarith
      have hp := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hx1) hf
      unfold quad
      nlinarith only [hp]
    · have hhi : -B ≤ hi := (lt_of_not_ge hright).le
      have hv : vertex lo hi B = -B := by
        unfold vertex
        rw [max_eq_right hlo,min_eq_right hhi]
      unfold minimum
      rw [hv]
      unfold quad
      nlinarith only [sq_nonneg (x+B)]

theorem lower {lo hi x B C K : ℝ} (hx0 : lo ≤ x) (hx1 : x ≤ hi)
    (hmin : K ≤ minimum lo hi B C) : K ≤ quad B C x :=
  hmin.trans (minimum_le hx0 hx1)

def minimumQ (lo hi B C : ℚ) : ℚ :=
  (min hi (max lo (-B)))^2+2*B*(min hi (max lo (-B)))+C

theorem minimum_cast (lo hi B C : ℚ) :
    (minimumQ lo hi B C:ℝ) = minimum (lo:ℝ) (hi:ℝ) (B:ℝ) (C:ℝ) := by
  simp [minimumQ,minimum,vertex,quad,Rat.cast_min,Rat.cast_max]

end N11Formalization.C450QuadraticBounds
#check @N11Formalization.C450QuadraticBounds.upper
#check @N11Formalization.C450QuadraticBounds.lower
#print axioms N11Formalization.C450QuadraticBounds.upper
#print axioms N11Formalization.C450QuadraticBounds.minimum_le
#print axioms N11Formalization.C450QuadraticBounds.lower
#print axioms N11Formalization.C450QuadraticBounds.minimum_cast
