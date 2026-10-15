import N11Formalization.FlashTenBoundary
open scoped Interval
open MeasureTheory
namespace N11Formalization

noncomputable def angPt (θ : ℝ) : Point := !₂[Real.cos θ, Real.sin θ]

theorem probe_cos {s t : ℝ} (ht0 : 0 ≤ t) (htπ : t ≤ Real.pi) (hs : |s| ≤ Real.pi) :
    Real.cos t ≤ Real.cos s ↔ |s| ≤ t := by
  constructor
  · intro h
    by_contra hcon
    have hcon' : t < |s| := not_le.mp hcon
    have hlt : Real.cos |s| < Real.cos t := Real.cos_lt_cos_of_nonneg_of_le_pi ht0 hs hcon'
    rw [Real.cos_abs] at hlt
    linarith
  · intro h
    rcases lt_or_eq_of_le h with hlt | heq
    · have hlt' : Real.cos t < Real.cos |s| :=
        Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg s) htπ hlt
      rw [Real.cos_abs] at hlt'
      linarith
    · rw [← heq, Real.cos_abs]

theorem probe_distsq (ρ φ θ : ℝ) :
    dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) ^ 2
      = 1 + ρ ^ 2 - 2 * ρ * Real.cos (θ - φ) := by
  have h1 : dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) ^ 2
      = (Real.cos θ - ρ * Real.cos φ) ^ 2 + (Real.sin θ - ρ * Real.sin φ) ^ 2 := by
    rw [dist_eq_norm, EuclideanSpace.norm_eq, Fin.sum_univ_two]
    simp [angPt]
    rw [Real.sq_sqrt (by positivity)]
  rw [h1, Real.cos_sub]
  rw [show (Real.cos θ - ρ * Real.cos φ) ^ 2 + (Real.sin θ - ρ * Real.sin φ) ^ 2
      = (Real.cos θ ^ 2 + Real.sin θ ^ 2) + ρ ^ 2 * (Real.cos φ ^ 2 + Real.sin φ ^ 2)
        - 2 * ρ * (Real.cos θ * Real.cos φ + Real.sin θ * Real.sin φ) from by ring]
  rw [Real.cos_sq_add_sin_sq θ, Real.cos_sq_add_sin_sq φ]
  ring

-- (3) 源不等价：dist ≤ r ⟺ cos t ≤ cos(θ-φ) ⟺ |θ-φ| ≤ t（单区间；wrap 由 |θ-φ| ≤ π 排除，t=π 统一）
theorem probe_arc_iff {ρ r φ θ t : ℝ} (hρ : 0 < ρ) (hr : 0 ≤ r)
    (ht0 : 0 ≤ t) (htπ : t ≤ Real.pi) (hcos : Real.cos t = (1 + ρ ^ 2 - r ^ 2) / (2 * ρ))
    (hθ : |θ - φ| ≤ Real.pi) :
    dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) ≤ r ↔ |θ - φ| ≤ t := by
  have hd0 : (0 : ℝ) ≤ dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) := dist_nonneg
  have h2ρ : 0 < 2 * ρ := by linarith
  have hsq : dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) ≤ r
      ↔ dist (angPt θ) (!₂[ρ * Real.cos φ, ρ * Real.sin φ]) ^ 2 ≤ r ^ 2 := by
    rw [sq_le_sq, abs_of_nonneg hd0, abs_of_nonneg hr]
  have hiff : (1 + ρ ^ 2 - 2 * ρ * Real.cos (θ - φ) ≤ r ^ 2)
      ↔ (Real.cos t ≤ Real.cos (θ - φ)) := by
    rw [hcos, div_le_iff₀ h2ρ]
    constructor <;> intro h <;> linarith
  rw [hsq, probe_distsq, hiff]
  exact probe_cos ht0 htπ hθ

-- (4) 三角多项式在单区间 [φ-t, φ+t] 上的积分闭式（= 源文"弧积分除以 2"的两倍）
theorem probe_integral_trig (a0 a1 a2 a3 φ t : ℝ) :
    ∫ θ in (φ - t)..(φ + t), (a0 + a1 * Real.cos θ + a2 * Real.cos (2 * θ)
        + a3 * Real.cos (3 * θ))
      = 2 * (a0 * t + a1 * Real.sin t * Real.cos φ
          + a2 * Real.sin (2 * t) * Real.cos (2 * φ) / 2
          + a3 * Real.sin (3 * t) * Real.cos (3 * φ) / 3) := by
  have hderiv : ∀ x ∈ [[(φ - t), (φ + t)]],
      HasDerivAt (fun θ : ℝ => a0 * θ + a1 * Real.sin θ
          + (a2 / 2) * Real.sin (2 * θ) + (a3 / 3) * Real.sin (3 * θ))
        (a0 + a1 * Real.cos x + a2 * Real.cos (2 * x) + a3 * Real.cos (3 * x)) x := by
    intro x _
    have d0 : HasDerivAt (fun θ : ℝ => a0 * θ) a0 x := by
      simpa using (hasDerivAt_id x).const_mul a0
    have d1 : HasDerivAt (fun θ : ℝ => a1 * Real.sin θ) (a1 * Real.cos x) x :=
      (Real.hasDerivAt_sin x).const_mul a1
    have d2 : HasDerivAt (fun θ : ℝ => (a2 / 2) * Real.sin (2 * θ))
        ((a2 / 2) * (Real.cos (2 * x) * 2)) x :=
      ((Real.hasDerivAt_sin (2 * x)).comp x
        (by simpa using (hasDerivAt_id x).const_mul (2 : ℝ))).const_mul (a2 / 2)
    have d3 : HasDerivAt (fun θ : ℝ => (a3 / 3) * Real.sin (3 * θ))
        ((a3 / 3) * (Real.cos (3 * x) * 3)) x :=
      ((Real.hasDerivAt_sin (3 * x)).comp x
        (by simpa using (hasDerivAt_id x).const_mul (3 : ℝ))).const_mul (a3 / 3)
    have hfun : ((fun θ : ℝ => a0 * θ) + (fun θ : ℝ => a1 * Real.sin θ)
          + (fun θ : ℝ => (a2 / 2) * Real.sin (2 * θ))
          + (fun θ : ℝ => (a3 / 3) * Real.sin (3 * θ)))
        = fun θ : ℝ => a0 * θ + a1 * Real.sin θ
            + (a2 / 2) * Real.sin (2 * θ) + (a3 / 3) * Real.sin (3 * θ) := rfl
    have hval : a0 + a1 * Real.cos x + (a2 / 2) * (Real.cos (2 * x) * 2)
          + (a3 / 3) * (Real.cos (3 * x) * 3)
        = a0 + a1 * Real.cos x + a2 * Real.cos (2 * x) + a3 * Real.cos (3 * x) := by ring
    have total := ((d0.add d1).add d2).add d3
    rw [hfun, hval] at total
    exact total
  have hint : IntervalIntegrable (fun θ : ℝ => a0 + a1 * Real.cos θ + a2 * Real.cos (2 * θ)
      + a3 * Real.cos (3 * θ)) volume (φ - t) (φ + t) := by
    apply Continuous.intervalIntegrable
    continuity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  rw [show (2:ℝ) * (φ + t) = 2 * φ + 2 * t from by ring,
      show (2:ℝ) * (φ - t) = 2 * φ - 2 * t from by ring,
      show (3:ℝ) * (φ + t) = 3 * φ + 3 * t from by ring,
      show (3:ℝ) * (φ - t) = 3 * φ - 3 * t from by ring,
      ]
  simp only [Real.sin_add, Real.sin_sub]
  ring

end N11Formalization
