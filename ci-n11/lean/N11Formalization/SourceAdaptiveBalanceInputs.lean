import N11Formalization.SourceNormalizedCanonical

/-! Exact adaptive-balance inputs for the canonical51 network. The four
canonical N columns are the actual M-inverse columns, zero on slack faces.
This pays hNcol and hNbal for later adaptive/local consumers; no quantitative
N/G/flux norm or mixed-coercivity claim is made. -/
set_option autoImplicit false
namespace N11Formalization.SourceAdaptiveBalanceInputs
open N11Formalization
open ResumeNetwork ResumeDirichlet ResumeLocalIncidence HarmonicSourceTransport
open SourceNormalizedCanonical SourceNormalizedKernel
noncomputable section

theorem Ncanon_zero_off_image (a : Fin 4) :
    ∀ e : Edge, e ∉ Finset.univ.image edgeMap → NcanonCol a e = 0 := by
  intro e he
  have hnot : ¬ ∃ s : SourceEdge, edgeMap s = e := by
    intro h
    obtain ⟨s, hs⟩ := h
    exact he (Finset.mem_image.mpr ⟨s, Finset.mem_univ _, hs⟩)
  simp [NcanonCol,Ncanon,hnot]

theorem Ncanon_sum_reindex (a : Fin 4) :
    (∑ e : Edge, NcanonCol a e) =
      ∑ s : SourceEdge, NcanonCol a (edgeMap s) := by
  have h := sum_edge_eq_sum_sourceEdge
    (α := NcanonCol a) (F := fun _ : Edge => (1 : ℝ))
    (Ncanon_zero_off_image a)
  simpa using h

theorem Ncanon_sum_zero (a : Fin 4) : ∑ e : Edge, NcanonCol a e = 0 := by
  rw [Ncanon_sum_reindex]
  have hs := sourceEdgeEquiv.symm.sum_comp
    (fun s : SourceEdge => N (HarmonicSourceTransport.srcFlat s) a)
  calc
    (∑ s : SourceEdge, NcanonCol a (edgeMap s)) =
        ∑ s : SourceEdge, N (HarmonicSourceTransport.srcFlat s) a := by
          apply Finset.sum_congr rfl
          intro s _
          simp [NcanonCol,Ncanon_edgeMap,Nsource]
    _ = ∑ e : Fin 45, N e a := by
      have hEq (e : Fin 45) :
          HarmonicSourceTransport.srcFlat (sourceEdgeEquiv.symm e) = e :=
        sourceEdgeEquiv.apply_symm_apply e
      simpa only [hEq] using hs.symm
    _ = 0 := by
      exact SourceNormalizedKernel.column_sum_zero a

theorem Ncanon_balance (a : Fin 4) (v : Free) :
    ∑ e : Edge,
      (NcanonCol a e * incidence e v) •
        edgeVector (FlashRootNetwork.canonAnchors SourceExactRoot.sourceRoot)
          (FlashRootNetwork.canonCenters SourceExactRoot.sourceRoot)
          (LocalSharpAuxZ.canonFaceZ SourceExactRoot.sourceRoot) e = 0 :=
  canonical_free_balance a v

theorem adaptive_hNcol :
    ∀ a : Fin 4, ∑ e : Edge, NcanonCol a e = 0 :=
  Ncanon_sum_zero

theorem adaptive_hNbal :
    ∀ a : Fin 4, ∀ v : Free,
      ∑ e : Edge,
        (NcanonCol a e * incidence e v) •
          edgeVector (FlashRootNetwork.canonAnchors SourceExactRoot.sourceRoot)
            (FlashRootNetwork.canonCenters SourceExactRoot.sourceRoot)
            (LocalSharpAuxZ.canonFaceZ SourceExactRoot.sourceRoot) e = 0 :=
  Ncanon_balance

end
end N11Formalization.SourceAdaptiveBalanceInputs
#check @N11Formalization.SourceAdaptiveBalanceInputs.adaptive_hNcol
#check @N11Formalization.SourceAdaptiveBalanceInputs.adaptive_hNbal
#print axioms N11Formalization.SourceAdaptiveBalanceInputs.adaptive_hNcol
#print axioms N11Formalization.SourceAdaptiveBalanceInputs.adaptive_hNbal
