/-
DCPN11/Problem.lean  —  faithful statement of the disk-covering problem.

STATUS: written against Mathlib (tag v4.35.0) but NOT YET COMPILED: the sandbox used
for this first pass could not host the Mathlib olean cache (see STATUS.md). Proofs marked
`-- draft` are intended to be complete but are not machine-checked; nothing here may be
cited as verified until `lake build` succeeds.

Source: docs/MATHEMATICAL_GUIDE.md, N11-GLOBAL-OPTIMALITY-THEOREM.md §Theorem:
  D = {x ∈ ℝ² : |x| ≤ 1},
  r_D(n) = inf {r ≥ 0 : D ⊆ ⋃ of n closed radius-r disks with arbitrary centres in ℝ²}.
We model ℝ² as `ℂ` (its `dist` is the Euclidean distance).
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.MetricSpace.ProperSpace

open Metric Set

namespace DCP

/-- The closed unit disk `D ⊂ ℝ² ≅ ℂ`. -/
def D : Set ℂ := closedBall 0 1

/-- The `n` closed disks of radius `r` centred at `c i` cover `D`. Centres are arbitrary,
repetitions and degenerate positions are allowed. -/
def Covers {n : ℕ} (c : Fin n → ℂ) (r : ℝ) : Prop :=
  D ⊆ ⋃ i, closedBall (c i) r

/-- Admissible radii for `n` disks. -/
def admissibleRadii (n : ℕ) : Set ℝ :=
  {r | 0 ≤ r ∧ ∃ c : Fin n → ℂ, Covers c r}

/-- `r_D(n)`: the infimal covering radius of the unit disk by `n` congruent closed disks. -/
noncomputable def rD (n : ℕ) : ℝ := sInf (admissibleRadii n)

/-- Covering radius of one configuration: `max_{x ∈ D} min_i |x - c_i|`
(as an `iSup`/`iInf`; `r_D(n)` equals the infimum of this over configurations, see
`rD_eq_inf_coverRadius` in `Basic.lean`, which is still `sorry`). -/
noncomputable def coverRadius {n : ℕ} (c : Fin n → ℂ) : ℝ :=
  ⨆ x : D, ⨅ i, dist (x : ℂ) (c i)

/-! ## Elementary facts (draft proofs) -/

variable {n : ℕ}

theorem Covers.mono {c : Fin n → ℂ} {r s : ℝ} (h : Covers c r) (hrs : r ≤ s) : Covers c s := by
  -- draft
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.1 (h hx)
  exact mem_iUnion.2 ⟨i, closedBall_subset_closedBall hrs hi⟩

theorem zero_mem_D : (0 : ℂ) ∈ D := mem_closedBall_self zero_le_one

theorem Covers.nonneg {c : Fin n → ℂ} {r : ℝ} (h : Covers c r) : 0 ≤ r := by
  -- draft
  obtain ⟨i, hi⟩ := mem_iUnion.1 (h zero_mem_D)
  exact dist_nonneg.trans (mem_closedBall.1 hi)

/-- One disk of radius 1 at the origin covers `D`. -/
theorem covers_one (hn : 1 ≤ n) : Covers (fun _ : Fin n => (0 : ℂ)) 1 := by
  -- draft
  intro x hx
  exact mem_iUnion.2 ⟨⟨0, hn⟩, hx⟩

theorem admissibleRadii_nonempty (hn : 1 ≤ n) : (admissibleRadii n).Nonempty :=
  ⟨1, zero_le_one, _, covers_one hn⟩

theorem admissibleRadii_bddBelow : BddBelow (admissibleRadii n) :=
  ⟨0, fun _ hr => hr.1⟩

theorem rD_le {c : Fin n → ℂ} {r : ℝ} (h : Covers c r) : rD n ≤ r :=
  csInf_le admissibleRadii_bddBelow ⟨h.nonneg, c, h⟩

theorem le_rD (hn : 1 ≤ n) {t : ℝ} (H : ∀ (r : ℝ) (c : Fin n → ℂ), Covers c r → t ≤ r) :
    t ≤ rD n :=
  le_csInf (admissibleRadii_nonempty hn) (fun r ⟨_, c, hc⟩ => H r c hc)

theorem rD_nonneg : 0 ≤ rD n := Real.sInf_nonneg (fun _ hr => hr.1)

theorem rD_le_one (hn : 1 ≤ n) : rD n ≤ 1 := rD_le (covers_one hn)

/-- More disks never hurt: `r_D` is antitone on `n ≥ 1`. -/
theorem rD_antitone {m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) : rD n ≤ rD m := by
  -- draft: pad a cover by m disks with copies of its first disk
  refine le_rD hm (fun r c hc => ?_)
  refine rD_le (c := fun i : Fin n => if h : i.val < m then c ⟨i.val, h⟩ else c ⟨0, hm⟩) ?_
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hc hx)
  refine mem_iUnion.2 ⟨⟨i.val, lt_of_lt_of_le i.isLt hmn⟩, ?_⟩
  simpa [i.isLt] using hi

/-- Equality from matching bounds (used for the main theorem). -/
theorem rD_eq_of_bounds (hn : 1 ≤ n) {t : ℝ} (c₀ : Fin n → ℂ) (hup : Covers c₀ t)
    (hlow : ∀ (r : ℝ) (c : Fin n → ℂ), Covers c r → t ≤ r) : rD n = t :=
  le_antisymm (rD_le hup) (le_rD hn hlow)

/-- The infimum is attained (compactness). Proof plan: a centre with `‖c‖ > 2` meets no point
of `D` at radius `≤ 1`, so WLOG all centres lie in `closedBall 0 2`; the set
`{(c, r) | Covers c r}` is closed (intersection over `x ∈ D` of finite unions of closed sets);
intersect with `closedBall 0 2 ^ n × [0,1]` (compact, `ProperSpace ℂ`) and minimise `r`. -/
theorem exists_optimal_cover (hn : 1 ≤ n) : ∃ c : Fin n → ℂ, Covers c (rD n) := by
  sorry

/-- `r_D(n) = inf_c max_{x ∈ D} min_i |x - c_i|` (the source's covering-radius formulation). -/
theorem rD_eq_inf_coverRadius (hn : 1 ≤ n) :
    rD n = ⨅ c : Fin n → ℂ, coverRadius c := by
  sorry

end DCP
