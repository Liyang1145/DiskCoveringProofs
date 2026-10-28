import N11Formalization.DSHTenBoundaryMain

/-!
# DSH-TOPO-C1 negative controls for the ten-boundary exclusion

Purpose (handoff §2C item 1 / task-1): the ten-boundary exclusion

```
Covers c r → r ≤ 19/50 → Fintype.card (BoundaryIdx c r) ≠ 10
```

must **fail for the right mathematical reason** when a hypothesis is weakened.  Two proved
controls pin that down:

* **`counting_cannot_exclude_ten`** — the arc-counting necessary condition
  `2π ≤ card · 2 arcsin r` (the project's `card_mul_two_arcsin_ge_two_pi`) is *satisfied with
  slack* at `r = 19/50` for `card = 10`: `2π < 10 · 2 arcsin(19/50)`.  So no counting /
  arc-length-capacity argument can exclude ten boundary disks here; the exclusion must come from
  the *weighted two-circle* per-disk bound (the certificate), i.e. from the coupling of the two
  circles through a common centre.

* **`ten_boundary_without_cover`** — "exactly ten boundary disks" is *not* by itself absurd:
  there is an explicit 11-disk configuration at `r = 19/50` with exactly ten disks meeting `S¹`
  and *no* cover of the closed unit disk (witness `(-1,0)`).  So the cover hypothesis is
  essential, exactly as the reduction uses it.

Both are unconditional, sorry-free, and use only `Mathlib`/project lemmas.

**Scope label: module/standalone.** Not root-integrated.
-/

set_option autoImplicit false
noncomputable section

namespace N11Formalization

/-! ## 1. Control: counting / arc capacity cannot exclude ten boundary disks at `R = 19/50` -/

/-- `π < 19/5` (mild, from the project's rational upper bound `RatInterval.piHi`). -/
theorem pi_lt_nineteen_fifths : Real.pi < 19 / 5 := by
  have h := RatInterval.pi_lt_piHi
  have h' : ((RatInterval.piHi : ℚ) : ℝ) < 19 / 5 := by norm_num [RatInterval.piHi]
  linarith

/-- `π/10 < arcsin(19/50)`: the counting threshold `sin(π/10) ≈ 0.309 < 0.38`. -/
theorem pi_div_ten_lt_arcsin_R : Real.pi / 10 < Real.arcsin (19 / 50) := by
  refine (Real.lt_arcsin_iff_sin_lt ?_ ?_).mpr ?_
  · constructor <;> linarith [Real.pi_pos]
  · norm_num
  · have h1 : Real.sin (Real.pi / 10) < Real.pi / 10 := Real.sin_lt (by positivity)
    have h2 : Real.pi / 10 < 19 / 50 := by linarith [Real.pi_pos, pi_lt_nineteen_fifths]
    linarith

/-- **Control.**  The necessary arc-counting inequality `2π ≤ card · 2 arcsin r` is satisfied
with slack at `r = 19/50` with `card = 10`.  Hence the ten-boundary exclusion cannot be obtained
from arc capacity/counting: its content is strictly more than "`10 · 2 arcsin R` misses `2π`". -/
theorem counting_cannot_exclude_ten : 2 * Real.pi < 10 * (2 * Real.arcsin (19 / 50)) := by
  have h := pi_div_ten_lt_arcsin_R
  linarith

/-! ## 2. Cardinality lemma: ten boundary disks, computed -/

/-- If exactly the indices `< 10` meet the circle, the subtype has cardinality `10`. -/
theorem card_boundaryIdx_eq_ten_of_val_lt (c : Fin 11 → Point) (r : ℝ)
    (h : ∀ i : Fin 11, MeetsCircle c r i ↔ (i : ℕ) < 10) :
    Fintype.card (BoundaryIdx c r) = 10 := by
  let f : BoundaryIdx c r → Fin 10 := fun i => ⟨i.1.val, (h i.1).mp i.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have hval : a.1.val = b.1.val := congrArg (fun j : Fin 10 => j.val) hab
      exact Subtype.ext (Fin.ext hval)
    · intro j
      refine ⟨⟨⟨j.val, by omega⟩, (h ⟨j.val, by omega⟩).mpr j.isLt⟩, ?_⟩
      exact Fin.ext rfl
  rw [Fintype.card_congr (Equiv.ofBijective f hf), Fintype.card_fin]

/-! ## 3. Control: ten boundary disks without any cover (the cover hypothesis is essential) -/

/-- The degenerate configuration: ten coincident centres at `(1,0) ∈ S¹` and the eleventh at
the origin. -/
def tenCollinearCenters : Fin 11 → Point :=
  fun i => if (i : ℕ) < 10 then angPt 0 else 0

/-- Exactly the ten non-origin disks meet the unit circle at `r = 19/50`. -/
theorem meetsCircle_tenCollinearCenters (i : Fin 11) :
    MeetsCircle tenCollinearCenters (19 / 50) i ↔ (i : ℕ) < 10 := by
  constructor
  · intro hm
    by_contra hv
    push Not at hv
    have hi : (i : ℕ) = 10 := by omega
    have hci : tenCollinearCenters i = 0 := by
      simp only [tenCollinearCenters]
      rw [if_neg (by omega : ¬ (i : ℕ) < 10)]
    obtain ⟨x, hx, hd⟩ := hm
    rw [hci, dist_zero_right, hx] at hd
    norm_num at hd
  · intro hv
    refine ⟨angPt 0, norm_angPt 0, ?_⟩
    have hci : tenCollinearCenters i = angPt 0 := by
      simp only [tenCollinearCenters]
      rw [if_pos hv]
    rw [hci, dist_self]
    norm_num

/-- **Control.**  At `r = 19/50` there is an 11-disk configuration with exactly ten disks
meeting `S¹` that does **not** cover the closed unit disk: the cover hypothesis is essential, so
the ten-boundary exclusion is not a statement about counts alone. -/
theorem ten_boundary_without_cover :
    ∃ c : Fin 11 → Point,
      ¬ Covers c (19 / 50) ∧ Fintype.card (BoundaryIdx c (19 / 50)) = 10 := by
  refine ⟨tenCollinearCenters, ?_, ?_⟩
  · -- witness `(-1,0)` is at distance `2` from `(1,0)` and `1` from the origin
    intro hc
    have hmem : (-(angPt 0) : Point) ∈ unitDisk := by
      simp [mem_unitDisk, norm_neg, norm_angPt]
    obtain ⟨i, hi⟩ := hc (-(angPt 0)) hmem
    by_cases hv : (i : ℕ) < 10
    · have hci : tenCollinearCenters i = angPt 0 := by
        simp only [tenCollinearCenters]
        rw [if_pos hv]
      rw [hci] at hi
      have hdist : dist (-(angPt 0)) (angPt 0) = 2 := by
        rw [dist_eq_norm]
        have h2 : -(angPt 0) - angPt 0 = -(angPt 0 + angPt 0) := by
          rw [sub_eq_add_neg, neg_add]
        rw [h2, norm_neg, ← two_smul ℝ (angPt 0), norm_smul, norm_angPt, mul_one]
        norm_num
      rw [hdist] at hi
      norm_num at hi
    · have hi10 : (i : ℕ) = 10 := by omega
      have hci : tenCollinearCenters i = 0 := by
        simp only [tenCollinearCenters]
        rw [if_neg (by omega : ¬ (i : ℕ) < 10)]
      rw [hci] at hi
      have hdist : dist (-(angPt 0)) (0 : Point) = 1 := by
        rw [dist_eq_norm, sub_zero, norm_neg, norm_angPt]
      rw [hdist] at hi
      norm_num at hi
  · exact card_boundaryIdx_eq_ten_of_val_lt _ _ meetsCircle_tenCollinearCenters

end N11Formalization

end

#print axioms N11Formalization.pi_lt_nineteen_fifths
#print axioms N11Formalization.pi_div_ten_lt_arcsin_R
#print axioms N11Formalization.counting_cannot_exclude_ten
#print axioms N11Formalization.card_boundaryIdx_eq_ten_of_val_lt
#print axioms N11Formalization.meetsCircle_tenCollinearCenters
#print axioms N11Formalization.ten_boundary_without_cover
#check @N11Formalization.counting_cannot_exclude_ten
#check @N11Formalization.ten_boundary_without_cover
