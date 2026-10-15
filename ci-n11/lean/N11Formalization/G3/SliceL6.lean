/-
  G3 first slice, level L6 -- the two correct general endpoint lemmas.

  THE DIRECTION MATTERS.  The per-line obligation is an UPPER bound on
        phi(z) = S s v z = s*z + v - (1 - cos z)  <=  0    on [a,b],
  with phi' = s - sin z and phi'' = -cos z.  Whether the two ENDPOINT conditions
  suffice depends on where phi's MAXIMUM sits:

    (a) cos <= 0 on [a,b]  =>  phi'' >= 0  =>  phi CONVEX
        =>  phi(z) <= max(phi a, phi b)      (ConvexOn.le_on_segment)
        =>  endpoints suffice.                [k ODD class]
    (b) phi' = s - sin z of constant sign  =>  phi MONOTONE
        =>  max at an endpoint  =>  endpoints suffice.  [k EVEN, residual]

  (Concavity would control the MINIMUM and is therefore the wrong tool here; an
  earlier report phrased it that way and was retracted -- claim C1204.)

  MEASURED COVERAGE (evidence/g3-recon/final_split.py; the direction was validated
  empirically on 4000 recorded lines by validate_split.py, 0 exceptions: argmax of phi
  at an endpoint 2355/2355 for class (a), 469/469 for class (b), interior 1176/1176
  for the class left over):
        (a) k odd                      64864  52.3%
        (b) k even, phi' constant sign 13275  10.7%
        (c) k even, phi' changes sign  45991  37.1%  <- bracket slice needed
  => these two lemmas cover 78139 lines = 62.9%.

  REUSED, NOT RESTATED: L3's `S`, `deriv_S`, `hasDerivAt_S`, `continuous_S` (root).
  Discipline: no sorry, no custom axiom, no native_decide, no #eval.
-/
import Mathlib
import N11Formalization.G3.SliceL3

namespace N11Formalization.G3SliceL6

open N11Formalization.G3SliceL3 (S deriv_S hasDerivAt_S continuous_S)

/-! ## 1. The second derivative of the slack function -/

/-- `S'' = -cos`, the key sign that decides convexity. -/
theorem deriv2_S (s v z : ℝ) : deriv^[2] (S s v) z = -Real.cos z := by
  have hd1 : deriv (S s v) = fun w : ℝ => s - Real.sin w := funext (fun w => deriv_S s v w)
  have hd2 : deriv (fun w : ℝ => s - Real.sin w) z = -Real.cos z := by
    have h := ((hasDerivAt_const (x := z) (c := s)).sub (Real.hasDerivAt_sin z)).deriv
    rw [zero_sub] at h
    exact h
  show deriv (deriv (S s v)) z = -Real.cos z
  rw [hd1]
  exact hd2

theorem differentiableAt_deriv_S (s v z : ℝ) : DifferentiableAt ℝ (deriv (S s v)) z := by
  have hd1 : deriv (S s v) = fun w : ℝ => s - Real.sin w := funext (fun w => deriv_S s v w)
  rw [hd1]
  exact ((hasDerivAt_const (x := z) (c := s)).sub (Real.hasDerivAt_sin z)).differentiableAt

/-! ## 2. Convexity where `cos <= 0`, and the first general lemma -/

/-- Where `cos <= 0` on the interval, `S` is convex. -/
theorem convexOn_S_of_cos_nonpos {a b s v : ℝ}
    (hcos : ∀ z ∈ Set.Icc a b, Real.cos z ≤ 0) :
    ConvexOn ℝ (Set.Icc a b) (S s v) := by
  refine convexOn_of_deriv2_nonneg (convex_Icc a b) ?_ ?_ ?_ ?_
  · exact (continuous_S s v).continuousOn
  · intro x hx
    exact (hasDerivAt_S s v x).differentiableAt.differentiableWithinAt
  · intro x hx
    exact (differentiableAt_deriv_S s v x).differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Set.Icc a b := interior_subset hx
    rw [deriv2_S]
    linarith [hcos x hx']

/-- **General lemma (a): where `cos <= 0` on `[a,b]`, the two endpoint conditions
imply the whole per-line obligation.**  (`k` odd class: 64864 lines, 52.3%.) -/
theorem minorant_of_cos_nonpos {a b s v : ℝ} (hab : a ≤ b)
    (hcos : ∀ z ∈ Set.Icc a b, Real.cos z ≤ 0)
    (ha : s * a + v ≤ 1 - Real.cos a) (hb : s * b + v ≤ 1 - Real.cos b) :
    ∀ z ∈ Set.Icc a b, s * z + v ≤ 1 - Real.cos z := by
  have hconv := convexOn_S_of_cos_nonpos (s := s) (v := v) hcos
  intro z hz
  have hseg : z ∈ segment ℝ a b := by
    rw [segment_eq_Icc hab]
    exact hz
  have hmax := hconv.le_on_segment ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hseg
  have ha' : S s v a ≤ 0 := by unfold N11Formalization.G3SliceL3.S; linarith
  have hb' : S s v b ≤ 0 := by unfold N11Formalization.G3SliceL3.S; linarith
  have hz' : S s v z ≤ 0 := le_trans hmax (max_le ha' hb')
  unfold N11Formalization.G3SliceL3.S at hz'
  linarith

/-! ## 3. The monotone case, and the second general lemma -/

/-- **General lemma (b1): if `S' = s - sin z >= 0` on `[a,b]` then `S` is monotone**,
so the right endpoint decides. -/
theorem minorant_of_deriv_nonneg {a b s v : ℝ} (hab : a ≤ b)
    (hm : ∀ z ∈ Set.Icc a b, 0 ≤ s - Real.sin z)
    (hb : s * b + v ≤ 1 - Real.cos b) :
    ∀ z ∈ Set.Icc a b, s * z + v ≤ 1 - Real.cos z := by
  have hmono : MonotoneOn (S s v) (Set.Icc a b) :=
    monotoneOn_of_deriv_nonneg (convex_Icc a b) (continuous_S s v).continuousOn
      (fun x hx => (hasDerivAt_S s v x).differentiableAt.differentiableWithinAt)
      (fun x hx => by rw [deriv_S]; exact hm x (interior_subset hx))
  intro z hz
  have hbz : S s v z ≤ S s v b := hmono hz ⟨hab, le_rfl⟩ hz.2
  have hb' : S s v b ≤ 0 := by unfold N11Formalization.G3SliceL3.S; linarith
  have hz' : S s v z ≤ 0 := le_trans hbz hb'
  unfold N11Formalization.G3SliceL3.S at hz'
  linarith

/-- **General lemma (b2): the mirror case `S' <= 0`**, decided by the left endpoint. -/
theorem minorant_of_deriv_nonpos {a b s v : ℝ} (hab : a ≤ b)
    (hm : ∀ z ∈ Set.Icc a b, s - Real.sin z ≤ 0)
    (ha : s * a + v ≤ 1 - Real.cos a) :
    ∀ z ∈ Set.Icc a b, s * z + v ≤ 1 - Real.cos z := by
  have hanti : AntitoneOn (S s v) (Set.Icc a b) :=
    antitoneOn_of_deriv_nonpos (convex_Icc a b) (continuous_S s v).continuousOn
      (fun x hx => (hasDerivAt_S s v x).differentiableAt.differentiableWithinAt)
      (fun x hx => by rw [deriv_S]; exact hm x (interior_subset hx))
  intro z hz
  have haz : S s v z ≤ S s v a := hanti ⟨le_rfl, hab⟩ hz hz.1
  have ha' : S s v a ≤ 0 := by unfold N11Formalization.G3SliceL3.S; linarith
  have hz' : S s v z ≤ 0 := le_trans haz ha'
  unfold N11Formalization.G3SliceL3.S at hz'
  linarith

end N11Formalization.G3SliceL6

/-! ## 4. Axiom profile (read only when this file has 0 errors) -/

#print axioms N11Formalization.G3SliceL6.deriv2_S
#print axioms N11Formalization.G3SliceL6.convexOn_S_of_cos_nonpos
#print axioms N11Formalization.G3SliceL6.minorant_of_cos_nonpos
#print axioms N11Formalization.G3SliceL6.minorant_of_deriv_nonneg
#print axioms N11Formalization.G3SliceL6.minorant_of_deriv_nonpos
