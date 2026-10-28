import N11Formalization.SourceNEnclosure
import N11Formalization.SourceAdaptiveBalanceInputs
import N11Formalization.SourceActiveMatrixIntervals

/-! Exact 9/10 scaling of a dyadic metric PROPOSAL. No whitening/eigenvalue
property is assumed. The original N/actual stress/root remain unchanged.
Exact source/canonical transforms, mass/force balance and entry-box semantics
are proved below; numeric row norms and coercivity are separate consumers. -/
set_option autoImplicit false
namespace N11Formalization.SourceRelativeMetric
open N11Formalization RatInterval ResumeNetwork ResumeDirichlet ResumeLocalIncidence
open SourceNormalizedKernel SourceNormalizedCanonical SourceNEnclosure
open SourceActiveMatrixIntervals SourceAdaptiveBalanceInputs
noncomputable section

def RM : Fin 4 → Fin 4 → ℤ :=
 ![![5977389212899689600,3084234978919466880,2008156729907682720,-1388190849679244160],
   ![3084234978919466880,9498906412506436608,81357739426959030,2604409099499393280],
   ![2008156729907683008,81357739426959498,10429456537443393792,267363491656565880],
   ![-1388190849679243872,2604409099499393280,267363491656566096,9886849369067412864]]

def R : Fin 4 → Fin 4 → ℚ := fun i a => (RM i a : ℚ)/1475739525896764129280

def columnSlot : Fin 45 → (Fin 41 ⊕ Fin 4) :=
 ![Sum.inl (38 : Fin 41),
   Sum.inl (33 : Fin 41),
   Sum.inl (23 : Fin 41),
   Sum.inl (36 : Fin 41),
   Sum.inl (32 : Fin 41),
   Sum.inr (3 : Fin 4),
   Sum.inl (31 : Fin 41),
   Sum.inr (2 : Fin 4),
   Sum.inl (35 : Fin 41),
   Sum.inl (28 : Fin 41),
   Sum.inr (1 : Fin 4),
   Sum.inl (29 : Fin 41),
   Sum.inl (30 : Fin 41),
   Sum.inl (24 : Fin 41),
   Sum.inl (34 : Fin 41),
   Sum.inl (37 : Fin 41),
   Sum.inl (26 : Fin 41),
   Sum.inl (25 : Fin 41),
   Sum.inr (0 : Fin 4),
   Sum.inl (5 : Fin 41),
   Sum.inl (21 : Fin 41),
   Sum.inl (2 : Fin 41),
   Sum.inl (1 : Fin 41),
   Sum.inl (20 : Fin 41),
   Sum.inl (14 : Fin 41),
   Sum.inl (17 : Fin 41),
   Sum.inl (7 : Fin 41),
   Sum.inl (8 : Fin 41),
   Sum.inl (15 : Fin 41),
   Sum.inl (27 : Fin 41),
   Sum.inl (3 : Fin 41),
   Sum.inl (4 : Fin 41),
   Sum.inl (0 : Fin 41),
   Sum.inl (11 : Fin 41),
   Sum.inl (16 : Fin 41),
   Sum.inl (22 : Fin 41),
   Sum.inl (10 : Fin 41),
   Sum.inl (18 : Fin 41),
   Sum.inl (39 : Fin 41),
   Sum.inl (19 : Fin 41),
   Sum.inl (9 : Fin 41),
   Sum.inl (40 : Fin 41),
   Sum.inl (12 : Fin 41),
   Sum.inl (13 : Fin 41),
   Sum.inl (6 : Fin 41)]

theorem columnSlot_forward : ∀ e : Fin 45, columnEquiv (columnSlot e) = e := by decide

theorem columnSlot_inverse (e : Fin 45) : columnEquiv.symm e = columnSlot e := by
  have h := congrArg columnEquiv.symm (columnSlot_forward e)
  simpa only [Equiv.symm_apply_apply] using h.symm

def rawBox (e : Fin 45) (a : Fin 4) : RatInterval :=
  match columnSlot e with
  | .inl i => dependentBox i a
  | .inr b => ofRat (if b=a then 1 else 0)

theorem rawBox_mem (e : Fin 45) (a : Fin 4) : (rawBox e a).Mem (N e a) := by
  have h := NBox_mem e a
  simp only [NBox,columnSlot_inverse] at h
  exact h

def sourceN (e : Fin 45) (a : Fin 4) : ℝ := ∑ b : Fin 4, N e b*(R b a : ℝ)
def canonicalN (e : Edge) (a : Fin 4) : ℝ :=
  ∑ b : Fin 4, Ncanon e b*(R b a : ℝ)

def metricBox (e : Fin 45) (a : Fin 4) : RatInterval :=
  sumI (fun b : Fin 4 => mul (rawBox e b) (ofRat (R b a)))

theorem metricBox_mem (e : Fin 45) (a : Fin 4) :
    (metricBox e a).Mem (sourceN e a) :=
  sumI_mem (fun b => mul_mem (rawBox_mem e b) (ofRat_mem (R b a)))

theorem canonical_source (s : SourceEdge) (a : Fin 4) :
    canonicalN (edgeMap s) a = sourceN (HarmonicSourceTransport.srcFlat s) a := by
  simp only [canonicalN,sourceN,Ncanon_edgeMap,Nsource]

theorem canonical_zero_off (e : Edge)
    (he : ¬ ∃ s : SourceEdge, edgeMap s = e) (a : Fin 4) : canonicalN e a = 0 := by
  simp [canonicalN,Ncanon,he]

theorem canonical_slack_zero (q : Fin 3) (a : Fin 4) :
    canonicalN (.inr (5,q)) a = 0 ∧ canonicalN (.inr (7,q)) a = 0 := by
  have h5 (b : Fin 4) := (Ncanon_zero_slack q b).1
  have h7 (b : Fin 4) := (Ncanon_zero_slack q b).2
  simp only [canonicalN,h5,h7,zero_mul,Finset.sum_const_zero,and_self]

theorem canonical_mass_zero (a : Fin 4) : ∑ e : Edge, canonicalN e a = 0 := by
  have hcol (b : Fin 4) : ∑ e : Edge, Ncanon e b = 0 := adaptive_hNcol b
  simp only [canonicalN]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul,hcol,zero_mul]
  exact Finset.sum_const_zero

theorem canonical_force_zero (a : Fin 4) (v : Free) :
    ∑ e : Edge, (canonicalN e a*incidence e v) •
      edgeVector (FlashRootNetwork.canonAnchors SourceExactRoot.sourceRoot)
        (FlashRootNetwork.canonCenters SourceExactRoot.sourceRoot)
        (LocalSharpAuxZ.canonFaceZ SourceExactRoot.sourceRoot) e = 0 := by
  have ht (e : Edge) :
      (canonicalN e a*incidence e v) •
        edgeVector (FlashRootNetwork.canonAnchors SourceExactRoot.sourceRoot)
          (FlashRootNetwork.canonCenters SourceExactRoot.sourceRoot)
          (LocalSharpAuxZ.canonFaceZ SourceExactRoot.sourceRoot) e =
      ∑ b : Fin 4, (R b a : ℝ) •
        ((NcanonCol b e*incidence e v) •
          edgeVector (FlashRootNetwork.canonAnchors SourceExactRoot.sourceRoot)
            (FlashRootNetwork.canonCenters SourceExactRoot.sourceRoot)
            (LocalSharpAuxZ.canonFaceZ SourceExactRoot.sourceRoot) e) := by
    simp only [canonicalN,Finset.sum_mul,Finset.sum_smul,smul_smul,NcanonCol]
    apply Finset.sum_congr rfl
    intro b _
    congr 1
    ring
  simp_rw [ht]
  rw [Finset.sum_comm]
  simp_rw [← Finset.smul_sum,adaptive_hNbal,smul_zero]
  exact Finset.sum_const_zero

end
end N11Formalization.SourceRelativeMetric
#check @N11Formalization.SourceRelativeMetric.metricBox_mem
#check @N11Formalization.SourceRelativeMetric.canonical_mass_zero
#check @N11Formalization.SourceRelativeMetric.canonical_force_zero
#print axioms N11Formalization.SourceRelativeMetric.metricBox_mem
#print axioms N11Formalization.SourceRelativeMetric.canonical_force_zero
