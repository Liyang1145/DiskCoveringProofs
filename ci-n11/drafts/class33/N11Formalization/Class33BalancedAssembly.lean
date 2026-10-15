import N11Formalization.Class33SwitchBridge
import N11Formalization.CanonicalBalancedFiniteClassCertificate
import N11Formalization.SharedMomentConcreteFace1Certificate
import N11Formalization.Class33Labels

/-! Class33 DRAFT (uncompiled). What remains for the q1-balanced class, made exact:
* `balanced_exclusion_of_two_canonical` = `balanced_exclusion_of_two_finite` but consuming
  `CanonicalCertificate`s (semantic bounds), so face bounds may come from ANY sound theorem, e.g. a
  slot-permuted tree (`face_upper_of_permuted_coefficients`).
* `rep7_certificate`: for cut 7, given the 11 face bounds and 9 sector bounds and the strict total,
  produce the `CanonicalCertificate`; balance, kap/eta signs, the sharp bracket and ALL NINE SWITCH
  bounds are supplied (switches from the A25 SwitchBatch via Class33SwitchBridge).
* `rep7_face189_upper`: the A25 Face1 tree (`start0_face1_full_domain_upper`, proved) IS the face
  {1,8,9} bound of rep7 after reversing slots (canonical slot s = data slot 2-s).
No class credit until the remaining 10+9 (rep7) and 11+9+9 (rep1) factor bounds are proved. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.Class33BalancedAssembly
open CanonicalSharedMomentFiniteCertificate CanonicalSharedMomentOrbitTransport CanonicalBalancedFiniteClassCertificate
open ActualCanonicalSharedMomentConsumer ActualCanonicalMomentTransport ActualOrderedMetricGraphs
open ActualMetricClassReduction ActualBoundaryNineTies SharedMomentFactorGridCertificate
open SharedMomentFiniteFactorCertificate Class33RepData Class33SwitchBridge Class33Labels

theorem balanced_exclusion_of_two_canonical
    (H7 : ∃ D : CanonicalCoeffQ (q1Faces 7 4), ∃ kap : Finset (Fin 11) → ℚ, ∃ eta : ℚ,
      Nonempty (CanonicalCertificate D kap 0 eta sharpAlpha))
    (H1 : ∃ D : CanonicalCoeffQ (q1Faces 1 4), ∃ kap : Finset (Fin 11) → ℚ, ∃ eta : ℚ,
      Nonempty (CanonicalCertificate D kap 0 eta sharpAlpha)) : Q1RunExclusion 4 := by
  have Hall := balanced_certificates_of_two sharpAlpha H7 H1
  intro c r h hr R O hm
  obtain ⟨v⟩ := nineTies_of_cover h.cover hr h.labels h.midpoint_order
  have he : O.run_length=(4 : Fin 8) := Fin.ext hm
  have hcut := Hall O.cut
  rw [← he] at hcut
  obtain ⟨D,kap,eta,⟨K⟩⟩ := hcut
  exact exclude_q1_ordered h hr R v O D kap eta sharpAlpha K

/-- rep7 certificate from the remaining face/sector bounds. -/
def rep7_certificate (faceMax : q1Faces 7 4 → ℚ) (sectorMax : Fin 9 → ℚ)
    (hface : ∀ (f : q1Faces 7 4) (a : Fin 3 → ℝ),
      (∀ s, a s ∈ Set.Icc (0 : ℝ) Real.pi) → (∑ s : Fin 3, a s)=Real.pi →
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
        faceObjective (fun s => (canonicalFaceP rep7D rep7Kap f s : ℝ))
          (fun s => (canonicalFaceQ rep7D f s : ℝ)) (fun s => (canonicalFaceB rep7D f s : ℝ)) a y ≤ faceMax f)
    (hsector : ∀ i : Fin 9, EfficientSectorCertificate (canonicalSectorC rep7D 0 rep7Eta i)
      (rep7D.mu (nextSite i)) (rep7D.leftSecond i) (rep7D.rightSecond i)
      (rep7D.leftFirst i) (rep7D.rightFirst i) (sectorMax i))
    (hstrict : canonicalTotalUpperQ rep7D rep7Kap rep7Eta sharpAlpha faceMax rep7SwitchMax sectorMax <
      RatInterval.piLo) :
    CanonicalCertificate rep7D rep7Kap 0 rep7Eta sharpAlpha where
  faceMax := faceMax
  switchMax := rep7SwitchMax
  sectorMax := sectorMax
  balance := rep7_balance
  edge_nonnegative := rep7_kap_nonneg
  eta_nonnegative := rep7_eta_nonneg
  bracket := sharpAlpha_bracket
  bounds := ⟨hface,fun i => (rep7Switches i).sound,fun i => (hsector i).sound⟩
  strict := hstrict

/-- The face {1,8,9} of rep7 is bounded by the proved A25 Face1 tree, slots reversed
(canonical slot s carries label (1,8,9)_s; Face1 data slots carry (9,8,1)). -/
theorem rep7_face189_upper (hmem : ({1,8,9} : Finset (Fin 11)) ∈ q1Faces 7 4) :
    ∀ a : Fin 3 → ℝ, (∀ s, a s ∈ Set.Icc (0 : ℝ) Real.pi) → (∑ s : Fin 3, a s)=Real.pi →
      ∀ y ∈ Set.Icc (0 : ℝ) 1,
        faceObjective (fun s => (canonicalFaceP rep7D rep7Kap ⟨_,hmem⟩ s : ℝ))
          (fun s => (canonicalFaceQ rep7D ⟨_,hmem⟩ s : ℝ)) (fun s => (canonicalFaceB rep7D ⟨_,hmem⟩ s : ℝ)) a y ≤
          (SharedMomentConcreteFace1.start0_face1_bound : ℝ) := by
  have h3 := q1FaceCard 7 4 ⟨({1,8,9} : Finset (Fin 11)), hmem⟩
  have l0 : canonicalLabel ({1,8,9} : Finset (Fin 11)) h3 0 = 1 := lab_zero _ _ (by decide) (by decide)
  have l2 : canonicalLabel ({1,8,9} : Finset (Fin 11)) h3 2 = 9 := lab_two _ _ (by decide) (by decide)
  have l1 : canonicalLabel ({1,8,9} : Finset (Fin 11)) h3 1 = 8 :=
    lab_one _ _ l0 l2 (by decide) (by decide) (by decide)
  have e0 : edgeCode (({1,8,9} : Finset (Fin 11)).erase 1) = 768 := by decide
  have e1 : edgeCode (({1,8,9} : Finset (Fin 11)).erase 8) = 514 := by decide
  have e2 : edgeCode (({1,8,9} : Finset (Fin 11)).erase 9) = 258 := by decide
  have c3 : edgeCode ({1,8,9} : Finset (Fin 11)) = 770 := by decide
  have r0 : Fin.rev (0 : Fin 3) = 2 := by decide
  have r1 : Fin.rev (1 : Fin 3) = 1 := by decide
  have r2 : Fin.rev (2 : Fin 3) = 0 := by decide
  have hp : ∀ s : Fin 3, canonicalFaceP rep7D rep7Kap ⟨_,hmem⟩ s =
      SharedMomentConcreteFace1.start0_face1_p (Fin.rev s) := by
    intro s
    fin_cases s <;>
      simp only [canonicalFaceP,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,rep7Kap,
        l0,l1,l2,e0,e1,e2,r0,r1,r2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MuN,rep7KapCode,SharedMomentConcreteFace1.start0_face1_p]
  have hq : ∀ s : Fin 3, canonicalFaceQ rep7D ⟨_,hmem⟩ s =
      SharedMomentConcreteFace1.start0_face1_q (Fin.rev s) := by
    intro s
    fin_cases s <;>
      simp only [canonicalFaceQ,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,
        l0,l1,l2,e0,e1,e2,c3,r0,r1,r2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MaskCode,rep7MinusPairs,rep7SideSecondCode,SharedMomentConcreteFace1.start0_face1_q]
  have hb : ∀ s : Fin 3, canonicalFaceB rep7D ⟨_,hmem⟩ s =
      SharedMomentConcreteFace1.start0_face1_b (Fin.rev s) := by
    intro s
    fin_cases s <;>
      simp only [canonicalFaceB,CanonicalCoeffQ.label,CanonicalCoeffQ.flagEdge,rep7D,
        l0,l1,l2,e0,e1,e2,c3,r0,r1,r2,Fin.zero_eta,Fin.mk_one,Fin.reduceFinMk,Fin.isValue] <;>
      norm_num [rep7MaskCode,rep7MinusPairs,rep7SideFirstCode,SharedMomentConcreteFace1.start0_face1_b]
  have H := SharedMomentFactorPermutation.face_upper_of_permuted_coefficients
    (fun s => (SharedMomentConcreteFace1.start0_face1_p s : ℝ))
    (fun s => (SharedMomentConcreteFace1.start0_face1_q s : ℝ))
    (fun s => (SharedMomentConcreteFace1.start0_face1_b s : ℝ)) _ Fin.revPerm
    SharedMomentConcreteFace1.start0_face1_full_domain_upper
  intro a ha hsum y hy
  have hh := H a ha hsum y hy
  simp only [Fin.revPerm_apply] at hh
  simpa only [hp,hq,hb] using hh

end N11Formalization.Class33BalancedAssembly
#print axioms N11Formalization.Class33BalancedAssembly.balanced_exclusion_of_two_canonical
#print axioms N11Formalization.Class33BalancedAssembly.rep7_certificate
#print axioms N11Formalization.Class33BalancedAssembly.rep7_face189_upper
