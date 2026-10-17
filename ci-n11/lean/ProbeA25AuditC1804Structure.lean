/-
  ProbeA25AuditC1804Structure.lean   (owner: lead)

  ============================ CREDIT SCOPE ============================
  Completes the KERNEL-CHECKED structural layer of the C1804 face-P obstruction.
  Companion to `ProbeA25AuditC1804FaceP.lean`, which proved the ALGEBRAIC core:
  the six equations `-mu_i - kap_e = target` are jointly contradictory because a
  signed sum cancels every mu and kap and leaves `0 = tP1 - tP0` ≠ 0.

  This probe proves the STRUCTURAL layer: at the three faces {0,1,9}, {0,9,10},
  {1,9,10} of `q0Faces 1` and the stated slots, `canonicalFaceP D kap` produces
  exactly those six equations.  Together the two probes give a fully
  kernel-checked refutation of
      ∃ D kap, ∀ f : q0Faces 1, canonicalFaceP D kap f = start0_face1_p
  already at these six slots (three faces of the eleven).

  This is a STRUCTURAL OBSTRUCTION, not a class payment and not a disproof of any
  existing theorem.  It does not show the A25 route is dead: a consistent data
  set could still be generated.  It pays no class credit.

  Technique note: `Finset.orderIsoOfFin` does NOT reduce definitionally, so
  `decide`/`rfl` cannot evaluate `canonicalLabel`.  `audLabel_zero/one/two`
  instead use monotonicity + surjectivity + injectivity of the order iso, which
  is why they are stated generally over any 3-element finset.

  Axioms: propext, Classical.choice, Quot.sound only.
-/
import N11Formalization.CanonicalSharedMomentFiniteCertificate
import N11Formalization.SharedMomentConcreteFace1Data

set_option autoImplicit false
noncomputable section
namespace N11Formalization.ProbeA25AuditC1804Structure

open ActualCanonicalMomentTransport ActualOrderedMetricGraphs
open ActualCanonicalFaceCoordinates
open SharedMomentConcreteFace1

/-! ## The three label positions on a 3-element face -/

/-- On a 3-element face, slot 0 carries the LEAST element. -/
theorem audLabel_zero (f : Finset (Fin 11)) (h : f.card = 3) {i : Fin 11} (hi : i ∈ f)
    (hmin : ∀ j ∈ f, i ≤ j) : canonicalLabel f h 0 = i := by
  unfold canonicalLabel
  have hmem : ((f.orderIsoOfFin h) 0).val ∈ f := ((f.orderIsoOfFin h) 0).property
  have hle : i ≤ ((f.orderIsoOfFin h) 0).val := hmin _ hmem
  by_contra hne
  have hlt : i < ((f.orderIsoOfFin h) 0).val := lt_of_le_of_ne hle (Ne.symm hne)
  obtain ⟨s, hs⟩ := (f.orderIsoOfFin h).surjective ⟨i, hi⟩
  have hs0 : (0 : Fin 3) ≤ s := Fin.zero_le s
  have hge : ((f.orderIsoOfFin h) 0).val ≤ i := by
    have hm := (f.orderIsoOfFin h).monotone hs0
    rw [hs] at hm
    exact hm
  exact absurd (lt_of_le_of_lt hge hlt) (lt_irrefl _)

/-- On a 3-element face, slot 2 carries the GREATEST element. -/
theorem audLabel_two (f : Finset (Fin 11)) (h : f.card = 3) {i : Fin 11} (hi : i ∈ f)
    (hmax : ∀ j ∈ f, j ≤ i) : canonicalLabel f h 2 = i := by
  unfold canonicalLabel
  have hmem : ((f.orderIsoOfFin h) 2).val ∈ f := ((f.orderIsoOfFin h) 2).property
  have hle : ((f.orderIsoOfFin h) 2).val ≤ i := hmax _ hmem
  by_contra hne
  have hlt : ((f.orderIsoOfFin h) 2).val < i := lt_of_le_of_ne hle hne
  obtain ⟨s, hs⟩ := (f.orderIsoOfFin h).surjective ⟨i, hi⟩
  have hs2 : s ≤ (2 : Fin 3) := Fin.le_last s
  have hge : i ≤ ((f.orderIsoOfFin h) 2).val := by
    have hm := (f.orderIsoOfFin h).monotone hs2
    rw [hs] at hm
    exact hm
  exact absurd (lt_of_lt_of_le hlt hge) (lt_irrefl _)

/-- Slot 1 is what remains: if slots 0 and 2 carry `a` and `c`, slot 1 carries the
third element `b`, by injectivity/surjectivity of the order iso. -/
theorem audLabel_one (f : Finset (Fin 11)) (h : f.card = 3) {a b c : Fin 11}
    (ha : canonicalLabel f h 0 = a) (hc : canonicalLabel f h 2 = c) (hb : b ∈ f)
    (hne_a : b ≠ a) (hne_c : b ≠ c) : canonicalLabel f h 1 = b := by
  unfold canonicalLabel at ha hc ⊢
  by_contra hne
  obtain ⟨s, hs⟩ := (f.orderIsoOfFin h).surjective ⟨b, hb⟩
  have hs' : ((f.orderIsoOfFin h) s).val = b := congrArg Subtype.val hs
  fin_cases s
  · simp only [Fin.mk_zero] at hs'
    rw [ha] at hs'
    exact hne_a hs'.symm
  · simp only [Fin.mk_one] at hs'
    exact hne hs'
  · simp only [Fin.reduceFinMk] at hs'
    rw [hc] at hs'
    exact hne_c hs'.symm

/-! ## The three faces used by the obstruction -/

def f019 : q0Faces 1 := ⟨({0, 1, 9} : Finset (Fin 11)), by decide +kernel⟩
def f0910 : q0Faces 1 := ⟨({0, 9, 10} : Finset (Fin 11)), by decide +kernel⟩
def f1910 : q0Faces 1 := ⟨({1, 9, 10} : Finset (Fin 11)), by decide +kernel⟩

/-- **The obstruction, kernel-checked.**  No `D` and `kap` can make
`canonicalFaceP D kap f = start0_face1_p` hold at the six slots
`(f019,0) (f019,1) (f0910,0) (f0910,2) (f1910,0) (f1910,2)`.  The six required
equations are exactly the algebraic core refuted in `ProbeA25AuditC1804FaceP`,
and the label/flagEdge values are the ones computed here. -/
theorem audFaceP_obstruction (D : CanonicalCoeffQ (q0Faces 1))
    (kap : Finset (Fin 11) → ℚ)
    (h0 : canonicalFaceP D kap f019 0 = start0_face1_p 0)
    (h1 : canonicalFaceP D kap f019 1 = start0_face1_p 1)
    (h2 : canonicalFaceP D kap f0910 0 = start0_face1_p 0)
    (h3 : canonicalFaceP D kap f0910 2 = start0_face1_p 2)
    (h4 : canonicalFaceP D kap f1910 0 = start0_face1_p 0)
    (h5 : canonicalFaceP D kap f1910 2 = start0_face1_p 2) : False := by
  -- unfold canonicalFaceP and the three labels/flagEdges
  simp only [canonicalFaceP, f019, f0910, f1910, start0_face1_p] at h0 h1 h2 h3 h4 h5
  -- the label values, stated at the unfolded faces
  have l019_0 : D.label ⟨({0,1,9} : Finset (Fin 11)), f019._proof_1⟩ 0 = 0 :=
    audLabel_zero _ _ (by decide) (by decide)
  have l019_2 : D.label ⟨({0,1,9} : Finset (Fin 11)), f019._proof_1⟩ 2 = 9 :=
    audLabel_two _ _ (by decide) (by decide)
  have l019_1 : D.label ⟨({0,1,9} : Finset (Fin 11)), f019._proof_1⟩ 1 = 1 :=
    audLabel_one _ _
      (by show canonicalLabel ({0,1,9} : Finset (Fin 11)) _ 0 = 0
          simpa only [CanonicalCoeffQ.label] using l019_0)
      (by show canonicalLabel ({0,1,9} : Finset (Fin 11)) _ 2 = 9
          simpa only [CanonicalCoeffQ.label] using l019_2)
      (by decide) (by decide) (by decide)
  have l0910_0 : D.label ⟨({0,9,10} : Finset (Fin 11)), f0910._proof_1⟩ 0 = 0 :=
    audLabel_zero _ _ (by decide) (by decide)
  have l0910_2 : D.label ⟨({0,9,10} : Finset (Fin 11)), f0910._proof_1⟩ 2 = 10 :=
    audLabel_two _ _ (by decide) (by decide)
  have l1910_0 : D.label ⟨({1,9,10} : Finset (Fin 11)), f1910._proof_1⟩ 0 = 1 :=
    audLabel_zero _ _ (by decide) (by decide)
  have l1910_2 : D.label ⟨({1,9,10} : Finset (Fin 11)), f1910._proof_1⟩ 2 = 10 :=
    audLabel_two _ _ (by decide) (by decide)
  simp only [l019_0, l019_1, l0910_0, l0910_2, l1910_0, l1910_2] at h0 h1 h2 h3 h4 h5
  -- the flagEdge values
  have e019_0 : D.flagEdge ⟨({0,1,9} : Finset (Fin 11)), f019._proof_1⟩ 0 = {1, 9} := by
    simp only [CanonicalCoeffQ.flagEdge, l019_0]; decide +kernel
  have e019_1 : D.flagEdge ⟨({0,1,9} : Finset (Fin 11)), f019._proof_1⟩ 1 = {0, 9} := by
    simp only [CanonicalCoeffQ.flagEdge, l019_1]; decide +kernel
  have e0910_0 : D.flagEdge ⟨({0,9,10} : Finset (Fin 11)), f0910._proof_1⟩ 0 = {9, 10} := by
    simp only [CanonicalCoeffQ.flagEdge, l0910_0]; decide +kernel
  have e0910_2 : D.flagEdge ⟨({0,9,10} : Finset (Fin 11)), f0910._proof_1⟩ 2 = {0, 9} := by
    simp only [CanonicalCoeffQ.flagEdge, l0910_2]; decide +kernel
  have e1910_0 : D.flagEdge ⟨({1,9,10} : Finset (Fin 11)), f1910._proof_1⟩ 0 = {9, 10} := by
    simp only [CanonicalCoeffQ.flagEdge, l1910_0]; decide +kernel
  have e1910_2 : D.flagEdge ⟨({1,9,10} : Finset (Fin 11)), f1910._proof_1⟩ 2 = {1, 9} := by
    simp only [CanonicalCoeffQ.flagEdge, l1910_2]; decide +kernel
  simp only [e019_0, e019_1, e0910_0, e0910_2, e1910_0, e1910_2] at h0 h1 h2 h3 h4 h5
  -- reduce the matrix literals to their component values
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val_fin_one] at h0 h1 h2 h3 h4 h5
  -- now the algebraic core: the signed combination cancels mu and kap
  have hcomb : (0 : ℚ) = (-30939859 / 1000000000) - (14313377 / 250000000) := by
    linarith only [h0, h1, h2, h3, h4, h5]
  norm_num at hcomb

end N11Formalization.ProbeA25AuditC1804Structure

#print axioms N11Formalization.ProbeA25AuditC1804Structure.audLabel_zero
#print axioms N11Formalization.ProbeA25AuditC1804Structure.audLabel_two
#print axioms N11Formalization.ProbeA25AuditC1804Structure.audLabel_one
#print axioms N11Formalization.ProbeA25AuditC1804Structure.audFaceP_obstruction
