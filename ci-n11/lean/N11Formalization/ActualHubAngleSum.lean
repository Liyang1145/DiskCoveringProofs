import N11Formalization.ActualSiteAngleChain
import N11Formalization.ActualHubLinkCycles
import N11Formalization.ActualFiniteNearestRefinement
import N11Formalization.ActualIncidentFanInteriors

/-! Exact consequences of the actual hub winding certificate.

The site-angle chain already proves that a genuine hub site has a positive
integer number of turns.  This file pays the purely ordered/measure-theoretic
part of the lift: an independently produced upper bound by one turn forces
the exact value `2 * pi`.  It also records a reusable interval-packing lemma
which is the target interface for the still-missing radial-star producer.

No radial-star or angular-interval producer is postulated here.  In
particular, `hub_sum_eq_two_pi_of_upper` consumes an upper bound and does not
rename it as a geometric theorem.
-/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.ActualHubAngleSum

open MeasureTheory
open ActualCoverStructuralReduction
open ActualFiniteNearestRefinement ActualSiteAngleChain
open ActualHubLinkCycles ActualIncidentFanInteriors
open ActualHubTriangleCensus

theorem hub_sum_eq_two_pi_of_upper {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (i : Fin 11) (hi : 9 ≤ i.val)
    (hupper : siteFaceSum R i ≤ 2*Real.pi) :
    siteFaceSum R i = 2*Real.pi := by
  obtain ⟨n, hn, he⟩ := actual_hub_positive_integer_turns h hr R i hi
  have hpi : 0 < Real.pi := Real.pi_pos
  have hnle : (n : ℝ) ≤ 1 := by
    rw [he] at hupper
    nlinarith
  have hnI : n ≤ 1 := by exact_mod_cast hnle
  have hn1 : n = 1 := by omega
  simpa [hn1] using he

theorem hub_sum_eq_two_pi_of_strict_upper {c : Fin 11 → Point} {r : ℝ}
    (h : Representative c r) (hr : r < 19/50) (R : Refinement c r)
    (i : Fin 11) (hi : 9 ≤ i.val)
    (hupper : siteFaceSum R i < 2*Real.pi) : False := by
  obtain ⟨n, hn, he⟩ := actual_hub_positive_integer_turns h hr R i hi
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [he] at hupper
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  nlinarith

/-! Finite interval packing on the real angular lift.

The hypotheses are deliberately explicit.  A future geometric producer can
instantiate `a` and `b` with compatible lifts of the directed rays of the
selected triangles; `hdisj` is the radial-star non-overlap statement and
`hsub` puts all lifts in one period.  The proof itself uses only exact
Lebesgue measure, so no angle estimate or graph premise is hidden here.
-/
theorem sum_interval_lengths_le_period {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (hab : ∀ i, a i ≤ b i)
    (hdisj : Pairwise (fun i j =>
      Disjoint (Set.Ioc (a i) (b i)) (Set.Ioc (a j) (b j))))
    (hsub : ∀ i, Set.Ioc (a i) (b i) ⊆ Set.Ioc (0 : ℝ) (2*Real.pi)) :
    ∑ i, (b i-a i) ≤ 2*Real.pi := by
  let I : ι → Set ℝ := fun i => Set.Ioc (a i) (b i)
  have hmeas : ∀ i, MeasurableSet (I i) := by
    intro i
    exact measurableSet_Ioc
  have hfinite : ∀ i, volume (I i) ≠ (⊤ : ENNReal) := by
    intro i
    change volume (Set.Ioc (a i) (b i)) ≠ (⊤ : ENNReal)
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have heq : volume.real (⋃ i, I i) = ∑ i, volume.real (I i) := by
    apply measureReal_iUnion_fintype
    · exact hdisj
    · exact hmeas
    · exact hfinite
  have hperiod : volume.real (Set.Ioc (0 : ℝ) (2*Real.pi)) = 2*Real.pi := by
    rw [Real.volume_real_Ioc_of_le]
    · ring
    · positivity
  have hmono : volume.real (⋃ i, I i) ≤
      volume.real (Set.Ioc (0 : ℝ) (2*Real.pi)) := by
    apply measureReal_mono
    · exact Set.iUnion_subset hsub
    · rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top
  rw [heq, hperiod] at hmono
  have hvol : ∀ i, volume.real (I i) = b i-a i := by
    intro i
    change volume.real (Set.Ioc (a i) (b i)) = b i-a i
    exact Real.volume_real_Ioc_of_le (hab i)
  calc
    ∑ i, (b i-a i) = ∑ i, volume.real (I i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (hvol i).symm
    _ ≤ 2*Real.pi := hmono

end N11Formalization.ActualHubAngleSum

#check @N11Formalization.ActualHubAngleSum.hub_sum_eq_two_pi_of_upper
#check @N11Formalization.ActualHubAngleSum.sum_interval_lengths_le_period
#print axioms N11Formalization.ActualHubAngleSum.hub_sum_eq_two_pi_of_upper
#print axioms N11Formalization.ActualHubAngleSum.sum_interval_lengths_le_period
