import N11Formalization.IntervalsHighLag
import N11Formalization.MetricAreaRationalCertificate

/-! Lane A: monotonicity of the factorial Taylor upper cosine bracket.

The derivative of `cosT 14 x + x^28/28!` is `-sinT 14 x`.  On `[0, π/2]`
we prove `0 ≤ sinT 14 x` from the degree-29 Lagrange remainder and the chord
bound `sin x ≥ 2x/π`.  Hence the real bracket is antitone there.  The rational
grid has 2049 points; the first 2048 lie beyond `π/2` only at the final point,
so all adjacent steps except the last follow from the real theorem.  The last
step is one exact rational comparison. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3Cos

open N11Formalization
open N11Formalization.MetricAreaRationalCertificate

theorem sinT_succ (m : ℕ) (x : ℝ) :
    sinT (m + 1) x = sinT m x + (-1 : ℝ) ^ m * x ^ (2 * m + 1) /
      ((Nat.factorial (2 * m + 1) : ℕ) : ℝ) := by
  simp [sinT, Finset.sum_range_succ]

/-- The real factorial Taylor upper cosine bracket. -/
def cosHiReal (x : ℝ) : ℝ :=
  cosT 14 x + x ^ 28 / ((Nat.factorial 28 : ℕ) : ℝ)

theorem hasDerivAt_cosHiReal (x : ℝ) :
    HasDerivAt cosHiReal (-(sinT 14 x)) x := by
  have h1 : HasDerivAt (fun y : ℝ => cosT 14 y) (-(sinT 13 x)) x :=
    hasDerivAt_cosT_succ 13 x
  have h2 : HasDerivAt (fun y : ℝ => y ^ 28 / ((Nat.factorial 28 : ℕ) : ℝ))
      (28 * x ^ 27 / ((Nat.factorial 28 : ℕ) : ℝ)) x := by
    have h := (hasDerivAt_pow 28 x).div_const ((Nat.factorial 28 : ℕ) : ℝ)
    simpa using h
  refine (h1.add h2).congr_deriv ?_
  have hsin : sinT 14 x = sinT 13 x -
      x ^ 27 / ((Nat.factorial 27 : ℕ) : ℝ) := by
    rw [sinT_succ]
    norm_num
    ring
  have hfac : ((Nat.factorial 28 : ℕ) : ℝ) =
      28 * ((Nat.factorial 27 : ℕ) : ℝ) := by
    rw [show (28 : ℕ) = 27 + 1 by norm_num, Nat.factorial_succ]
    push_cast
    ring
  rw [hsin, hfac]
  field_simp
  ring

/-- The degree-27 Taylor partial sum of sine is nonnegative on the quarter
circle.  The constant `1/2` is deliberately very loose. -/
theorem sinT14_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 2) :
    0 ≤ sinT 14 x := by
  have hb := sin_bound_abs 14 x
  have hsin : 2 / Real.pi * x ≤ Real.sin x := Real.mul_le_sin hx0 hx
  have herr : Real.sin x - x ^ 29 / ((Nat.factorial 29 : ℕ) : ℝ) ≤
      sinT 14 x := by
    have h := (abs_le.mp hb).2
    rw [abs_of_nonneg hx0] at h
    linarith
  have hx2 : x ≤ 2 := by linarith [hx, Real.pi_le_four]
  have hpow : x ^ 28 ≤ 2 ^ 28 := pow_le_pow_left₀ hx0 hx2 28
  have hq : x ^ 29 / ((Nat.factorial 29 : ℕ) : ℝ) ≤ x * (1 / 2 : ℝ) := by
    rw [pow_succ]
    have hf : (0 : ℝ) ≤ ((Nat.factorial 29 : ℕ) : ℝ) := by positivity
    have hdiv := div_le_div_of_nonneg_right hpow hf
    have hsmall : (2 : ℝ) ^ 28 / ((Nat.factorial 29 : ℕ) : ℝ) ≤ 1 / 2 := by
      norm_num [Nat.factorial]
    calc x ^ 28 * x / ((Nat.factorial 29 : ℕ) : ℝ)
        = (x ^ 28 / ((Nat.factorial 29 : ℕ) : ℝ)) * x := by ring
      _ ≤ (1 / 2) * x := mul_le_mul_of_nonneg_right (hdiv.trans hsmall) hx0
      _ = x * (1 / 2) := by ring
  have hpi : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
    have hp := Real.pi_le_four
    have hpos := Real.pi_pos
    field_simp
    linarith
  have hcoef : 0 ≤ 2 / Real.pi - 1 / 2 := sub_nonneg.mpr hpi
  have hlower : x * (2 / Real.pi - 1 / 2) ≤
      Real.sin x - x ^ 29 / ((Nat.factorial 29 : ℕ) : ℝ) := by
    linarith [hsin, hq]
  exact (mul_nonneg hx0 hcoef).trans (hlower.trans herr)

theorem cosHiReal_antitoneOn : AntitoneOn cosHiReal (Set.Icc 0 (Real.pi / 2)) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) ?_ ?_ ?_
  · exact (fun x _ => (hasDerivAt_cosHiReal x).continuousAt.continuousWithinAt)
  · intro x _
    exact (hasDerivAt_cosHiReal x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_cosHiReal x).deriv]
    exact neg_nonpos.mpr (sinT14_nonneg (le_of_lt hx.1) (le_of_lt hx.2))

theorem cosHiNLag_cast (q : ℚ) :
    ((cosHiNLag q : ℚ) : ℝ) = cosT 14 (q : ℝ) + |(q : ℝ)| ^ 28 /
      ((Nat.factorial 28 : ℕ) : ℝ) := by
  simp only [cosHiNLag, Rat.cast_add, Rat.cast_pow, Rat.cast_abs,
    cosTQ_cast, Rat.cast_div, Rat.cast_natCast]

/-- Rational antitone monotonicity of the upper cosine bracket on `[0, π/2]`. -/
theorem cosHiNLag_antitone {a b : ℚ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : (b : ℝ) ≤ Real.pi / 2) : cosHiNLag b ≤ cosHiNLag a := by
  have hR : ((cosHiNLag b : ℚ) : ℝ) ≤ ((cosHiNLag a : ℚ) : ℝ) := by
    rw [cosHiNLag_cast, cosHiNLag_cast]
    have haR : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
    have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    have hmem_a : (a : ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨haR, habR.trans hb⟩
    have hmem_b : (b : ℝ) ∈ Set.Icc 0 (Real.pi / 2) := ⟨haR.trans habR, hb⟩
    have h := cosHiReal_antitoneOn hmem_a hmem_b habR
    simpa [cosHiReal, abs_of_nonneg haR, abs_of_nonneg (haR.trans habR)] using h
  exact_mod_cast hR

/-- The final grid step crosses `π/2` by less than a grid spacing; it is checked
exactly rather than inferred from the real antitone theorem. -/
theorem cosHiNLag_grid_last :
    cosHiNLag (N11Formalization.MetricAreaRationalCertificate.nodeQ RatInterval.piHi 2048
        (2048 : Fin 2049) / 2) ≤
      cosHiNLag (N11Formalization.MetricAreaRationalCertificate.nodeQ RatInterval.piHi 2048
        (2047 : Fin 2049) / 2) := by
  norm_num [cosHiNLag, cosTQ, N11Formalization.MetricAreaRationalCertificate.nodeQ,
    RatInterval.piHi, Finset.sum_range_succ]

def gridArg (n : ℕ) : ℚ :=
  RatInterval.piHi * ((min n 2048 : ℕ) : ℚ) / 2048 / 2

def gridCos (n : ℕ) : ℚ := cosHiNLag (gridArg n)

/-- `gridArg` agrees with the certificate's `nodeQ` expression on the grid. -/
theorem gridArg_eq_nodeQ {n : ℕ} (hn : n ≤ 2048) :
    gridArg n = N11Formalization.MetricAreaRationalCertificate.nodeQ
      RatInterval.piHi 2048 (⟨n, Nat.lt_succ_of_le hn⟩ : Fin 2049) / 2 := by
  unfold gridArg N11Formalization.MetricAreaRationalCertificate.nodeQ
  rw [Nat.min_eq_right hn]

/-- The final grid step in the `gridArg` coordinate, matching the last case of
`gridCos_succ_le` syntactically. -/
theorem cosHiNLag_gridArg_last : cosHiNLag (gridArg 2048) ≤
    cosHiNLag (gridArg 2047) := by
  rw [gridArg_eq_nodeQ (le_refl 2048), gridArg_eq_nodeQ (by norm_num)]
  exact cosHiNLag_grid_last

theorem gridArg_mono {m n : ℕ} (hmn : m ≤ n) : gridArg m ≤ gridArg n := by
  unfold gridArg
  have hm : ((min m 2048 : ℕ) : ℚ) ≤ ((min n 2048 : ℕ) : ℚ) := by
    have hm' : min m 2048 ≤ min n 2048 := by omega
    exact_mod_cast hm'
  have hp : 0 ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
  calc
    RatInterval.piHi * ((min m 2048 : ℕ) : ℚ) / 2048 / 2
        = RatInterval.piHi * ((min m 2048 : ℕ) : ℚ) / (2048 * 2) := by ring
    _ ≤ RatInterval.piHi * ((min n 2048 : ℕ) : ℚ) / (2048 * 2) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hm hp) (by norm_num)
    _ = RatInterval.piHi * ((min n 2048 : ℕ) : ℚ) / 2048 / 2 := by ring

theorem gridCos_succ_le (n : ℕ) : gridCos (n + 1) ≤ gridCos n := by
  by_cases hn : n < 2047
  · have hb : ((gridArg (n + 1) : ℚ) : ℝ) ≤ Real.pi / 2 := by
      have hle : gridArg (n + 1) ≤ RatInterval.piLo / 2 := by
        unfold gridArg
        have hmn : min (n + 1) 2048 ≤ 2047 := by omega
        have hq : ((min (n + 1) 2048 : ℕ) : ℚ) ≤ (2047 : ℚ) :=
          Nat.cast_le.mpr hmn
        have hp : 0 ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
        have hpi : RatInterval.piHi * 2047 / 2048 / 2 ≤ RatInterval.piLo / 2 := by
          norm_num [RatInterval.piHi, RatInterval.piLo]
        calc
          RatInterval.piHi * ((min (n + 1) 2048 : ℕ) : ℚ) / 2048 / 2
              ≤ RatInterval.piHi * (2047 : ℚ) / 2048 / 2 := by
                rw [show RatInterval.piHi * ((min (n + 1) 2048 : ℕ) : ℚ) / 2048 / 2
                    = RatInterval.piHi * ((min (n + 1) 2048 : ℕ) : ℚ) / (2048 * 2) by ring]
                rw [show RatInterval.piHi * (2047 : ℚ) / 2048 / 2
                    = RatInterval.piHi * (2047 : ℚ) / (2048 * 2) by ring]
                exact div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hq hp) (by norm_num)
          _ ≤ RatInterval.piLo / 2 := hpi
      have hleR : ((gridArg (n + 1) : ℚ) : ℝ) ≤
          (((RatInterval.piLo / 2 : ℚ)) : ℝ) := by exact_mod_cast hle
      exact hleR.trans RatInterval.pi_div_two_lo_lt.le
    have ha : 0 ≤ gridArg n := by
      unfold gridArg
      have hp : 0 ≤ RatInterval.piHi := by norm_num [RatInterval.piHi]
      positivity
    exact cosHiNLag_antitone ha (gridArg_mono (Nat.le_succ n)) hb
  · by_cases hlast : n = 2047
    · subst n
      simpa [gridCos] using cosHiNLag_gridArg_last
    · have hnge : 2048 ≤ n := by omega
      have h1 : gridArg (n + 1) = gridArg n := by
        unfold gridArg
        have hs : min (n + 1) 2048 = 2048 := Nat.min_eq_right (by omega)
        have ht : min n 2048 = 2048 := Nat.min_eq_right (by omega)
        rw [hs, ht]
      rw [gridCos, gridCos, h1]
      exact le_rfl

/-- Adjacent grid monotonicity of `cosHiNLag` on all 2048 steps. -/
theorem gridCos_antitone : Antitone gridCos := by
  refine antitone_nat_of_succ_le ?_
  exact gridCos_succ_le

/-- Full grid monotonicity, the form consumed by the degree-three concavity
reduction. -/
theorem cosHiNLag_grid_antitone {k l : Fin 2049} (hkl : k ≤ l) :
    cosHiNLag (N11Formalization.MetricAreaRationalCertificate.nodeQ
        RatInterval.piHi 2048 l / 2) ≤
      cosHiNLag (N11Formalization.MetricAreaRationalCertificate.nodeQ
        RatInterval.piHi 2048 k / 2) := by
  have hk : N11Formalization.MetricAreaRationalCertificate.nodeQ
        RatInterval.piHi 2048 k / 2 = gridArg (k : ℕ) := by
    simpa using (gridArg_eq_nodeQ (show (k : ℕ) ≤ 2048 by omega)).symm
  have hl : N11Formalization.MetricAreaRationalCertificate.nodeQ
        RatInterval.piHi 2048 l / 2 = gridArg (l : ℕ) := by
    simpa using (gridArg_eq_nodeQ (show (l : ℕ) ≤ 2048 by omega)).symm
  rw [hk, hl]
  exact gridCos_antitone (show (k : ℕ) ≤ (l : ℕ) from hkl)

end N11Formalization.SevenClassQ0Deg3Cos
#check @N11Formalization.SevenClassQ0Deg3Cos.sinT14_nonneg
#check @N11Formalization.SevenClassQ0Deg3Cos.cosHiNLag_antitone
#check @N11Formalization.SevenClassQ0Deg3Cos.cosHiNLag_grid_antitone
#print axioms N11Formalization.SevenClassQ0Deg3Cos.cosHiNLag_grid_antitone
