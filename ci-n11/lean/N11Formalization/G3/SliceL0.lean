/-
  G3 first slice, level L0 -- the leaf-obligation DERIVATION plus concrete data checks.

  Provenance (read-only sources; no source file is modified):
    * the per-leaf obligation and its derivation: derivative of
      team-current/lead/certify_cosine_polytope.py::certify (lines 29-36) and
      team-current/lead/cosine_polytope.py::domain_rows;
    * the data (lambda, beta, stored energy_lower, Schur weight W_0) are literals
      below, extracted verbatim from team-current/lead/cosine_dbm_local920.json
      (sha256 6706b42690a1d99d8f49523ff0d7d82fbc688fd64a18b228512acec139aef987).

  Caliber: lengths in units of the unit-disk radius; V and T are lengths, E_alpha and
  T^2 are lengths squared.  y is a probability vector (y >= 0, sum y = 1).
  Norming: sum_f beta_f = 1 with beta_f >= 0; sum_ell g_ell = 1 per pair.

  WHAT THIS FILE PROVES
    Part A: the derivation step.  If lambda >= 0, A y <= b, y >= 0, sum y = 1 and
            m <= c_q + sum_j lambda_j A j q for every q, then
                f0 - (sum_j lambda_j b_j) + m  <=  f0 + sum_q c_q y_q .
            This is exactly the weak-duality step that turns the recorded multipliers
            into a lower bound for the leaf's affine function F(y) = f0 + sum c_q y_q.
            NOTE: it does NOT require min_q (c_q + (A^T lambda)_q) >= 0; a negative
            minimum is harmless because y is a probability vector.
    Part B: concrete rational facts about one leaf's data:
              - its 90 recorded multipliers are all >= 0;
              - one Schur-eliminated weight (511-digit numerator) is > 0;
              - the recorded lower bound exceeds T^2, and T^2 = T * T;
              - for the tightest leaf the recorded bound is BELOW (19/50)^2, i.e.
                the threshold T (not 19/50) is what this leaf needs.

  WHAT THIS FILE DOES NOT PROVE (deferred, see evidence/g3-recon/FIRST-SLICE-PROBE.md)
    * the identity  stored = f0 - sum_j lambda_j b_j + min_q (...)  -- it involves
      L = 2*arcsin(19/50) and D = 9L - 2*pi and therefore needs outward rational
      brackets for L and pi;
    * the one-variable cosine minorant  1 - cos mu >= s*mu + v  on a cell interval,
      which needs the project's high-order rational cos bounds widened from [-1,1] to
      |x| <= 1.5592 (derived bound: max distance of any cell interval to pi*Z);
    * E_alpha <= V^2 and the definition of V, which live in the (unformalized) C923
      reduction.
  No axiom beyond the standard three is introduced here (see the companion
  G3-SLICE-L0-PRINT-AXIOMS.lean).
-/
import Mathlib

namespace N11Formalization.G3SliceL0

/-! ## Part A -- the derivation (general, no data, no trigonometry) -/

/-- Weak-duality minimum step: for a probability vector `y` and any real function `r`
with `m ≤ r i` pointwise, `m ≤ ∑ i, r i * y i`. -/
theorem minStep {ι : Type*} [Fintype ι] (r y : ι → ℚ) (m : ℚ)
    (hm : ∀ i, m ≤ r i) (hy : ∀ i, 0 ≤ y i) (hsum : ∑ i, y i = 1) :
    m ≤ ∑ i, r i * y i := by
  calc m = m * (∑ i, y i) := by rw [hsum, mul_one]
    _ = ∑ i, m * y i := by rw [Finset.mul_sum]
    _ ≤ ∑ i, r i * y i :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hm i) (hy i)

/-- Monotonicity step for the multipliers: `λ ≥ 0` and `u ≤ b` pointwise give
`∑ j, λ j * u j ≤ ∑ j, λ j * b j`. -/
theorem dualStep {κ : Type*} [Fintype κ] (lam u b : κ → ℚ)
    (hlam : ∀ j, 0 ≤ lam j) (hub : ∀ j, u j ≤ b j) :
    ∑ j, lam j * u j ≤ ∑ j, lam j * b j :=
  Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hub j) (hlam j)

/-- The algebraic decomposition used by the derivation:
`∑ c q * y q  =  ∑ (c q + ∑ j, λ j * A j q) * y q  -  ∑ j, λ j * (∑ q, A j q * y q)`. -/
theorem decomp {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c y : ι → ℚ) (A : κ → ι → ℚ) (lam : κ → ℚ) :
    ∑ q, c q * y q
      = ∑ q, (c q + ∑ j, lam j * A j q) * y q - ∑ j, lam j * (∑ q, A j q * y q) := by
  have hS : ∑ q, (∑ j, lam j * A j q) * y q = ∑ j, lam j * (∑ q, A j q * y q) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  have hsplit : ∑ q, (c q + ∑ j, lam j * A j q) * y q
      = (∑ q, c q * y q) + ∑ q, (∑ j, lam j * A j q) * y q := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun q _ => add_mul _ _ _
  rw [hsplit, hS]
  abel

/-- **The leaf-obligation derivation.**  Given nonnegative multipliers `lam`, a feasible
point `y` of the leaf's DBM cell (`A y ≤ b`, `y ≥ 0`, `∑ y = 1`) and `m` below every
`c q + ∑ j, lam j * A j q`, the recorded bound `f0 - ∑ lam j * b j + m` is a lower bound
for the leaf's affine function `f0 + ∑ c q * y q`. -/
theorem lowerBound {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f0 m : ℚ) (c y : ι → ℚ) (A : κ → ι → ℚ) (b lam : κ → ℚ)
    (hlam : ∀ j, 0 ≤ lam j)
    (hAy : ∀ j, ∑ q, A j q * y q ≤ b j)
    (hy : ∀ q, 0 ≤ y q) (hsum : ∑ q, y q = 1)
    (hm : ∀ q, m ≤ c q + ∑ j, lam j * A j q) :
    f0 - (∑ j, lam j * b j) + m ≤ f0 + ∑ q, c q * y q := by
  have hdecomp := decomp c y A lam
  have hmin : m ≤ ∑ q, (c q + ∑ j, lam j * A j q) * y q :=
    minStep (fun q => c q + ∑ j, lam j * A j q) y m hm hy hsum
  have hdual : ∑ j, lam j * (∑ q, A j q * y q) ≤ ∑ j, lam j * b j :=
    dualStep lam (fun j => ∑ q, A j q * y q) b hlam hAy
  linarith [hdecomp, hmin, hdual]

/-- Composed form: if in addition the recorded threshold inequality holds, then the
leaf's function exceeds `T2` at every feasible point of the cell. -/
theorem lowerBound_gt_of_threshold {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f0 m T2 : ℚ) (c y : ι → ℚ) (A : κ → ι → ℚ) (b lam : κ → ℚ)
    (hlam : ∀ j, 0 ≤ lam j)
    (hAy : ∀ j, ∑ q, A j q * y q ≤ b j)
    (hy : ∀ q, 0 ≤ y q) (hsum : ∑ q, y q = 1)
    (hm : ∀ q, m ≤ c q + ∑ j, lam j * A j q)
    (hthr : f0 - (∑ j, lam j * b j) + m > T2) :
    f0 + ∑ q, c q * y q > T2 := by
  linarith [lowerBound f0 m c y A b lam hlam hAy hy hsum hm]

/-! ## Part B -- concrete data of one energy leaf (`leaf 3` of the C921 tree) -/

/-- The 90 recorded DBM multipliers of leaf 3, as exact numerator/denominator pairs.
(Order = the 90 rows of `cosine_polytope.py::domain_rows`: for 0 ≤ i < j ≤ 9, first the
row `∑_{i ≤ k < j} y_k ≤ db[i][j]`, then the row `-∑_{k} y_k ≤ db[j][i]`.) -/
def lam3 : List (ℤ × ℤ) := [
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (24098721173, 1000000000000),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
  (0, 1),
]

/-- The multiplier list has exactly one nonzero entry, at index 56. -/
theorem lam3_length : lam3.length = 90 := by unfold lam3; decide

/-- **Every recorded multiplier of leaf 3 is nonnegative.** -/
theorem lam3_num_nonneg : ∀ p ∈ lam3, (0 : ℤ) ≤ p.1 := by unfold lam3; decide
theorem lam3_den_pos : ∀ p ∈ lam3, (0 : ℤ) < p.2 := by unfold lam3; decide

theorem lam3_nonneg : ∀ p ∈ lam3, (0 : ℚ) ≤ (p.1 : ℚ) / (p.2 : ℚ) := by
  intro p hp
  have h1 : (0 : ℚ) ≤ (p.1 : ℚ) := by exact_mod_cast lam3_num_nonneg p hp
  have h2 : (0 : ℚ) < (p.2 : ℚ) := by exact_mod_cast lam3_den_pos p hp
  exact div_nonneg h1 (le_of_lt h2)

/-- The Schur-eliminated weight of pair (0,1) for leaf 3 (511-digit numerator),
assembled from the five nonzero norming weights listed below. -/
def leaf3W0Num : ℤ := 3578988580592856051431337261536724250777188008305223531833072640204938504796050596460097661252744617326718917601127372886310543821898614186445902466736998570393814733696502234111234474622390942903778407480512652884052343307485156390206184123769571623782263564195895528052486700429305143239482466727695214084213693131859394851809404364865691233012209509550688674909995525475816240166822797028477521206875395997144486348869017036311097703772843616601384896721427937477150403271838134126151835612866125767631540181
def leaf3W0Den : ℤ := 338707979988363738202435007278727335689362406459473069990843850170574036484195265297768087013365254825502943028859056202147500946509729724614099869690327229694678228468087401809150394441437629951444305664382227054822306926171844785244698035012312258688273748135809378035637036154973958843702940781076558084655973165655523684261806140341793607737739437378139057956671876566863415875555896415866102223615029155868153928391181798747071985186672209328131442300867573146529938866215573834748559868015336400000000000000

theorem leaf3W0_pos : (0 : ℚ) < (leaf3W0Num : ℚ) / (leaf3W0Den : ℚ) := by
  unfold leaf3W0Num leaf3W0Den
  norm_num

theorem leaf3W0_num_pos : (0 : ℤ) < leaf3W0Num := by unfold leaf3W0Num; norm_num

/-- The nonnegativity of the norming weights: `Σ_f β_f = 1` with `β_f ≥ 0` and only five
nonzero entries (source stress-table indices 14, 17, 24, 27, 45). -/
theorem beta3_nonneg : ∀ p ∈ ([(14, 1000000000000), (17, 200000000000), (24, 1000000000000), (27, 1000000000000), (45, 500000000000)] : List (ℕ × ℤ)),
    (0 : ℤ) < p.2 := by decide

theorem beta3_num_nonneg : ∀ p ∈ ([(13314647773, 1000000000000), (5155649261, 200000000000), (698706419623, 1000000000000), (149937198853, 1000000000000), (56131743723, 500000000000)] : List (ℤ × ℤ)),
    (0 : ℤ) ≤ p.1 := by decide

/-- Sum of the five nonzero norming weights is 1 (exactly). -/
theorem beta3_sum_eq_one :
    ((13314647773 : ℚ) / (1000000000000 : ℚ) + (5155649261 : ℚ) / (200000000000 : ℚ) + (698706419623 : ℚ) / (1000000000000 : ℚ) + (149937198853 : ℚ) / (1000000000000 : ℚ) + (56131743723 : ℚ) / (500000000000 : ℚ) : ℚ) = 1 := by norm_num

/-! ## Part C -- the threshold facts -/

/-- The exact root threshold `T` and its square `T^2` (as recorded in every certificate) -/
def T : ℚ := (1899919265599193545242591 : ℚ) / (5000000000000000000000000 : ℚ)
def T2 : ℚ := (3609693215794978945499128383491614947609040393281 : ℚ) / (25000000000000000000000000000000000000000000000000 : ℚ)
def R0sq : ℚ := (19 / 50 : ℚ) * (19 / 50 : ℚ)

theorem T_sq : T * T = T2 := by unfold T T2; norm_num

/-- The recorded lower bound of leaf 3. -/
def stored3 : ℚ := (7220845141644027253801595759707211622989518349348455455922882925019801556635909 : ℚ) / (50000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)
/-- The recorded lower bound of the tightest energy leaf (leaf 4348, depth 62). -/
def stored4348 : ℚ := (14438773027413103364747526082504086048756863066479200760509283185397963923981387 : ℚ) / (100000000000000000000000000000000000000000000000000000000000000000000000000000000 : ℚ)

theorem stored3_gt_T2 : stored3 > T2 := by unfold stored3 T2; norm_num
theorem stored4348_gt_T2 : stored4348 > T2 := by unfold stored4348 T2; norm_num

/-- **The boundary fact**: the tightest leaf's recorded bound is *below* `(19/50)^2`,
so this leaf genuinely needs the threshold `T` rather than the cruder `19/50`. -/
theorem stored4348_lt_R0sq : stored4348 < R0sq := by unfold stored4348 R0sq; norm_num

/-- For leaf 3 the cruder threshold `(19/50)^2` is also met (both hold there). -/
theorem stored3_gt_R0sq : stored3 > R0sq := by unfold stored3 R0sq; norm_num

end N11Formalization.G3SliceL0

/-! ## Part D -- axiom profile (only readable when this file has 0 errors) -/

#print axioms N11Formalization.G3SliceL0.minStep
#print axioms N11Formalization.G3SliceL0.dualStep
#print axioms N11Formalization.G3SliceL0.decomp
#print axioms N11Formalization.G3SliceL0.lowerBound
#print axioms N11Formalization.G3SliceL0.lowerBound_gt_of_threshold
#print axioms N11Formalization.G3SliceL0.lam3_length
#print axioms N11Formalization.G3SliceL0.lam3_num_nonneg
#print axioms N11Formalization.G3SliceL0.lam3_den_pos
#print axioms N11Formalization.G3SliceL0.lam3_nonneg
#print axioms N11Formalization.G3SliceL0.leaf3W0_pos
#print axioms N11Formalization.G3SliceL0.leaf3W0_num_pos
#print axioms N11Formalization.G3SliceL0.beta3_nonneg
#print axioms N11Formalization.G3SliceL0.beta3_num_nonneg
#print axioms N11Formalization.G3SliceL0.beta3_sum_eq_one
#print axioms N11Formalization.G3SliceL0.T_sq
#print axioms N11Formalization.G3SliceL0.stored3_gt_T2
#print axioms N11Formalization.G3SliceL0.stored4348_gt_T2
#print axioms N11Formalization.G3SliceL0.stored4348_lt_R0sq
#print axioms N11Formalization.G3SliceL0.stored3_gt_R0sq
