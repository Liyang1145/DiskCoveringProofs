/-
DCPN11/LowerBound.lean  —  every 11-disk cover has radius ≥ R* (C923 + C921 + C922).

STATUS: NOT YET COMPILED (see STATUS.md).
Source: N11-GLOBAL-OPTIMALITY-THEOREM.md §"Lower-bound proof" steps 1-4 and
UNRESTRICTED-PROOF-ASSEMBLY.md §§1-8. Each `sorry` below is one named obligation of the
source chain; the comment says which file/section discharges it there.
-/
import DCPN11.Problem
import DCPN11.Candidate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

open Real Metric Set

noncomputable section

namespace DCP.N11

/-- The comparison radius `R0 = 19/50` of all metric certificates. -/
def R0 : ℝ := 19 / 50

/-! ## Elementary numerics (draft proofs) -/

/-- `8 asin(19/50) < π`: eight boundary arcs cannot cover `S¹` (assembly §1). -/
theorem eight_arcsin_R0_lt_pi : 8 * arcsin R0 < π := by
  -- draft: 19/50 < sin(π/8) = √(2-√2)/2 since √2 < 1.4224, and `arcsin` is strictly monotone.
  have hs2 : √2 < 1.4224 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h8 : R0 < sin (π / 8) := by
    rw [Real.sin_pi_div_eight, R0]
    have : (0.76 : ℝ) < √(2 - √2) := by
      rw [Real.lt_sqrt (by norm_num)]; linarith
    linarith
  have hπ8 : arcsin (sin (π / 8)) = π / 8 :=
    Real.arcsin_sin (by linarith [pi_pos]) (by linarith [pi_pos])
  have := Real.arcsin_lt_arcsin (by rw [R0]; norm_num) (Real.sin_le_one _) h8
  linarith

/-- `D0 = 9L - 2π > 0` with `L = 2 asin(19/50)` (simplex chart is well defined, §6). -/
theorem D0_pos : 0 < 9 * (2 * arcsin R0) - 2 * π := by
  -- draft: sin(π/9) < π/9 < 0.35 < 0.38, hence π/9 < asin(0.38).
  have hπ := pi_lt_d2
  have hlt : sin (π / 9) < R0 := by
    have := Real.sin_lt (by positivity : 0 < π / 9)
    rw [R0]; linarith
  have h9 : arcsin (sin (π / 9)) = π / 9 :=
    Real.arcsin_sin (by linarith [pi_pos]) (by linarith [pi_pos])
  have := Real.arcsin_lt_arcsin (Real.neg_one_le_sin _) (by rw [R0]; norm_num) hlt
  linarith

/-! ## Step 1 (assembly §1): exactly nine boundary disks -/

/-- Disk `i` meets the unit circle. -/
def MeetsCircle {n : ℕ} (c : Fin n → ℂ) (r : ℝ) (i : Fin n) : Prop :=
  ∃ x : ℂ, ‖x‖ = 1 ∧ dist x (c i) ≤ r

/-- A boundary disk cannot cover the origin when `r < 1/2` (centre norm `≥ 1 - r > r`). -/
theorem boundary_disk_misses_origin {n : ℕ} {c : Fin n → ℂ} {r : ℝ} (hr : r < 1 / 2)
    {i : Fin n} (hi : MeetsCircle c r i) : r < dist 0 (c i) := by
  -- draft
  obtain ⟨x, hx, hxc⟩ := hi
  have h1 : ‖x‖ ≤ ‖x - c i‖ + ‖c i‖ := norm_le_norm_sub_add x (c i)
  rw [dist_eq_norm] at hxc
  rw [dist_comm, dist_eq_norm, sub_zero]
  linarith

/-- Not all eleven disks are boundary disks (someone covers the origin). -/
theorem not_all_boundary {c : Fin 11 → ℂ} {r : ℝ} (hc : Covers c r) (hr : r < 1 / 2) :
    ∃ i, ¬ MeetsCircle c r i := by
  -- draft
  obtain ⟨i, hi⟩ := mem_iUnion.1 (hc zero_mem_D)
  refine ⟨i, fun hb => ?_⟩
  have := boundary_disk_misses_origin hr hb
  rw [mem_closedBall] at hi
  linarith

/-- At least nine boundary disks: each meets `S¹` in an arc of angular width `≤ 2 asin r`,
and `8 · 2 asin(R0) < 2π` (`eight_arcsin_R0_lt_pi`). Source: assembly §1. -/
theorem at_least_nine_boundary {c : Fin 11 → ℂ} {r : ℝ} (hc : Covers c r) (hr : r ≤ R0) :
    9 ≤ (Finset.univ.filter fun i => MeetsCircle c r i).card := by
  sorry

/-- **C450** (weighted two-circle capacity): ten boundary disks plus one other disk cannot
cover `D` at radius `≤ 19/50`. Source: solo-20260922/M10-038-EXCLUSION.md, DUAL-MANIFEST.json,
36 rational eccentricity intervals, ~198,000 kernel boxes. LARGE CERTIFIED COMPUTATION. -/
theorem C450_no_ten_boundary {c : Fin 11 → ℂ} {r : ℝ} (hc : Covers c r) (hr : r ≤ R0) :
    (Finset.univ.filter fun i => MeetsCircle c r i).card ≠ 10 := by
  sorry

theorem exactly_nine_boundary {c : Fin 11 → ℂ} {r : ℝ} (hc : Covers c r) (hr : r ≤ R0) :
    (Finset.univ.filter fun i => MeetsCircle c r i).card = 9 := by
  -- draft: 9 ≤ card ≤ 10 (`not_all_boundary`), card ≠ 10 (C450)
  have h9 := at_least_nine_boundary hc hr
  have h10 := C450_no_ten_boundary hc hr
  have hr2 : r < 1 / 2 := by rw [R0] at hr; linarith
  obtain ⟨j, hj⟩ := not_all_boundary hc hr2
  have hle : (Finset.univ.filter fun i => MeetsCircle c r i).card ≤ 10 := by
    have hsub : (Finset.univ.filter fun i => MeetsCircle c r i) ⊆ Finset.univ.erase j := by
      intro i hi; simp only [Finset.mem_filter] at hi
      exact Finset.mem_erase.2 ⟨fun h => hj (h ▸ hi.2), Finset.mem_univ _⟩
    simpa using Finset.card_le_card hsub
  omega

/-! ## Steps 1-6 (assembly §§1-6): reduction to the canonical oracle (C923)

The intermediate objects (owned arcs, clipped Voronoi cells, the embedded dual disk, ears,
hub fans) are not yet given Lean definitions; the obligations are listed in order:

* §1  inner-root replacement preserves coverage and arcs; hubs indispensable
      (INNER-ROOT-DOMINANCE.md, N11-LOW-RADIUS-REDUCTION.md).
* §2  nine connected owned arcs with distinct two-site switches
      (UPSTREAM-ARC-TOPOLOGY-AUDIT.md, VORONOI-BOUNDARY-REDUCTION.md).
* §3  the two hub cells share a positive edge (uses the C450 per-disk atom);
      ring locality: every ring-ring contact has label distance ≤ 2
      (HUB-ADJACENCY-DUAL.md, RING-LOCALITY.md).
* §4  embedded straight dual disk; 3-cliques are consecutive triples
      [machine-checked: `DCPCore.clique_consecutive`]; skip-one chords cut empty ears;
      q ≤ 1 (TWO-TRIPLE-CAPACITY.md, FIVE-RING-STAR-EXCLUSION.md); two complementary hub
      fans with degree sum 13 - q (DUAL-DISK-INTERFACE-AUDIT.md,
      BOUNDARY-SWITCH-ANGLE-PROOF.md).
* §5  metric exclusions of degree 3, q1 (4,8),(5,7),(6,6), q0 (4,9),(5,8)
      [ledger completeness machine-checked: `DCPCore.degreePairs_eq`,
      `DCPCore.only_q0_6_7_survives`]; each exclusion itself is a LARGE CERTIFIED
      COMPUTATION (q1_final_replay.json, upstream_replay_r23.json).
* §6  the surviving q0(6,7) cover yields 51 edge constraints of length ≤ r on the canonical
      graph [graph machine-checked: `DCPCore.oracle_edges_literal`], hence V(U(y)) ≤ r
      (FIXED-SWITCH-SOC-REDUCTION.md, EXACT-ORACLE-INDEX-MAP.md). -/

/-- Anchor chart: `L = 2 asin(19/50)`, `D0 = 9L - 2π`. -/
def Lw : ℝ := 2 * arcsin R0
def D0 : ℝ := 9 * Lw - 2 * π

/-- The closed 8-simplex of normalised width deficits. -/
def Simplex9 : Set (Fin 9 → ℝ) := {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1}

/-- `θ_i = i L - D0 Σ_{j<i} y_j`. -/
def anchorAngle (y : Fin 9 → ℝ) (i : Fin 9) : ℝ :=
  (i : ℝ) * Lw - D0 * ∑ j : Fin 9, if j < i then y j else 0

def anchor (y : Fin 9 → ℝ) (i : Fin 9) : ℂ := pt (cos (anchorAngle y i)) (sin (anchorAngle y i))

/-- The 51 edges (node numbering: 0..8 anchors, 9..19 sites, 20..30 face witnesses);
identical to `DCPCore.oracleEdges` / `oracle_edges()` in the checker. -/
def oracleEdges : List (Fin 31 × Fin 31) :=
  [(9, 0), (9, 8), (10, 1), (10, 0), (11, 2), (11, 1), (12, 3), (12, 2), (13, 4), (13, 3),
   (14, 5), (14, 4), (15, 6), (15, 5), (16, 7), (16, 6), (17, 8), (17, 7), (18, 20), (9, 20),
   (10, 20), (18, 21), (10, 21), (11, 21), (18, 22), (11, 22), (12, 22), (18, 23), (12, 23),
   (13, 23), (19, 24), (13, 24), (14, 24), (19, 25), (14, 25), (15, 25), (19, 26), (15, 26),
   (16, 26), (19, 27), (16, 27), (17, 27), (19, 28), (17, 28), (9, 28), (18, 29), (19, 29),
   (9, 29), (18, 30), (19, 30), (13, 30)]

def nodePos (U : Fin 9 → ℂ) (w : Fin 22 → ℂ) (v : Fin 31) : ℂ :=
  if h : v.val < 9 then U ⟨v.val, h⟩ else w ⟨v.val - 9, by omega⟩

/-- Oracle value `V(U)`: least `t` such that the 22 free nodes can be placed with every
oracle edge of length `≤ t`. -/
def oracleV (U : Fin 9 → ℂ) : ℝ :=
  sInf {t : ℝ | ∃ w : Fin 22 → ℂ, ∀ e ∈ oracleEdges, dist (nodePos U w e.1) (nodePos U w e.2) ≤ t}

/-- **C923** (unrestricted reduction, assembly §§1-6). Every 11-disk cover at radius
`r < R*` (hence `r < 19/50` by C922) yields a point of the simplex whose oracle value is at
most `r`. (The source states the reduction under this hypothesis; we keep it.) -/
theorem C923_reduction {c : Fin 11 → ℂ} {r : ℝ} (hc : Covers c r) (hr : r < Rstar) :
    ∃ y ∈ Simplex9, oracleV (anchor y) ≤ r := by
  sorry

/-- **C921** (full closed simplex lower bound): `V(U(y)) ≥ R*` for all `y`. Source:
cosine_dbm_local920.json (SHA256 6706b426…), 2505 exact DBM splits, 2386 Schur-energy leaves
(371 exact rational stress fields), 120 local leaves inside the C919/C920 stress balls.
LARGE CERTIFIED COMPUTATION. -/
theorem C921_oracle_lower {y : Fin 9 → ℝ} (hy : y ∈ Simplex9) : Rstar ≤ oracleV (anchor y) := by
  sorry

/-- Lower bound: any 11-disk cover has `r ≥ R*`. -/
theorem lower_bound (r : ℝ) (c : Fin 11 → ℂ) (hc : Covers c r) : Rstar ≤ r := by
  -- draft: if r < R* then r < 19/50 (C922), reduce (C923) and contradict C921.
  by_contra hlt
  push_neg at hlt
  obtain ⟨y, hy, hV⟩ := C923_reduction hc hlt
  have := C921_oracle_lower hy
  linarith

end DCP.N11
