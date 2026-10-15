import N11Formalization.TCSystem
import N11Formalization.SourceIdentity

open Metric

namespace N11Formalization

def hubOf (a : Fin 12) (u : Fin 12 → ℝ) : Point := !₂[u a, 0]

theorem hubOf_coord0 (a : Fin 12) (u : Fin 12 → ℝ) : (hubOf a u).ofLp 0 = u a := rfl
theorem hubOf_coord1 (a : Fin 12) (u : Fin 12 → ℝ) : (hubOf a u).ofLp 1 = 0 := rfl
theorem hub0_eq_hubOf (u : Fin 12 → ℝ) : hub0 u = hubOf 4 u := rfl
theorem hub1_eq_hubOf (u : Fin 12 → ℝ) : hub1 u = hubOf 5 u := rfl

theorem ofLp_eq_ofLp_iff {p q : Point} (h : p.ofLp = q.ofLp) : p = q :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).injective h

-- 5) 用 dist_point_eq_sqrt + 坐标平滑性证明 dist 的平滑性
example {n : WithTop ℕ∞} (k : Fin 9) (a : Fin 12) (x : Fin 12 → ℝ)
    (hrho : ∀ j : Fin 9, rhoK x j ≠ 0) (h : Uvec x k ≠ hubOf a x) :
    ContDiffAt ℝ n (fun u : Fin 12 → ℝ => dist (Uvec u k) (hubOf a u)) x := by
  have hrew : (fun u : Fin 12 → ℝ => dist (Uvec u k) (hubOf a u))
      = fun u => Real.sqrt (((Uvec u k).ofLp 0 - (hubOf a u).ofLp 0) ^ 2
          + ((Uvec u k).ofLp 1 - (hubOf a u).ofLp 1) ^ 2) := by
    funext u
    rw [dist_point_eq_sqrt]
  rw [hrew]
  refine ContDiffAt.sqrt ?_ ?_
  · simp only [Uvec_coord0, Uvec_coord1, ringCenter_coord0, ringCenter_coord1,
      arcEnd_coord0, arcEnd_coord1, hubOf_coord0, hubOf_coord1]
    fun_prop (disch := first | assumption)
  · intro hzero
    apply h
    have h2 : ((Uvec x k).ofLp 0 - (hubOf a x).ofLp 0) ^ 2 = 0
        ∧ ((Uvec x k).ofLp 1 - (hubOf a x).ofLp 1) ^ 2 = 0 :=
      (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp hzero
    refine ofLp_eq_ofLp_iff ?_
    funext i
    fin_cases i
    · exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2.1)
    · exact sub_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2.2)

end N11Formalization
