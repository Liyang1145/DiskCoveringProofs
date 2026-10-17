import N11Formalization.HarmonicSourceGeometry
import N11Formalization.HarmonicSourceGeomConsumer
import N11Formalization.SourceNormalizedKernel

/-! Exact transport of the four actual source-kernel columns from the
corrected45-edge SourceN2 indexing to the canonical51-edge network. Slack
faces5/7 are zero by construction; no approximate reindexing or graph
surrogate is used. This pays canonical free-force balance for each exact N
column, but not quantitative N/G/flux bounds or mixed coercivity. -/
set_option autoImplicit false
namespace N11Formalization.SourceNormalizedCanonical
open N11Formalization
open ResumeNetwork ResumeDirichlet ResumeLocalIncidence
open HarmonicSourceTransport SourceN2 HarmonicSourceGeometryV2
open SourceNormalizedKernel
noncomputable section

noncomputable def sourceEdgeEquiv : SourceEdge ≃ Fin 45 :=
  Equiv.ofBijective HarmonicSourceTransport.srcFlat (by decide)

def Nsource (s : SourceEdge) (a : Fin 4) : ℝ :=
  N (HarmonicSourceTransport.srcFlat s) a

noncomputable def Ncanon (e : Edge) (a : Fin 4) : ℝ :=
  if h : ∃ s : SourceEdge, edgeMap s = e then
    Nsource (Classical.choose h) a
  else 0

theorem Ncanon_edgeMap (s : SourceEdge) (a : Fin 4) :
    Ncanon (edgeMap s) a = Nsource s a := by
  unfold Ncanon
  split_ifs with h
  · have heq : Classical.choose h = s :=
      edgeMap_injective (Classical.choose_spec h)
    simp only [heq]
  · exact False.elim (h ⟨s,rfl⟩)

theorem Ncanon_zero_slack (k : Fin 3) (a : Fin 4) :
    Ncanon (.inr (5,k)) a = 0 ∧ Ncanon (.inr (7,k)) a = 0 := by
  have h5 : ¬ ∃ s : SourceEdge, edgeMap s = (.inr (5,k) : Edge) := by
    intro h
    have hh := (edgeMap_image (.inr (5,k))).1 h
    omega
  have h7 : ¬ ∃ s : SourceEdge, edgeMap s = (.inr (7,k) : Edge) := by
    intro h
    have hh := (edgeMap_image (.inr (7,k))).1 h
    omega
  simp [Ncanon,h5,h7]

def NcanonCol (a : Fin 4) : Edge → ℝ := fun e => Ncanon e a

theorem source_B2_rows (a : Fin 4) (w : SrcFree) (c : Fin 2) :
    ∑ s : SourceEdge,
      srcB2 SourceExactRoot.sourceRoot (rowIdx w c)
        (HarmonicSourceTransport.srcFlat s) *
        Ncanon (edgeMap s) a = 0 := by
  have hfin := SourceNormalizedKernel.all_B_rows
    (HarmonicSourceGeometryV2.rowIdx w c) a
  have hsum := sourceEdgeEquiv.symm.sum_comp
    (fun s : SourceEdge =>
      srcB2 SourceExactRoot.sourceRoot (rowIdx w c)
          (HarmonicSourceTransport.srcFlat s) *
        N (HarmonicSourceTransport.srcFlat s) a)
  calc
    _ = ∑ s : SourceEdge,
      srcB2 SourceExactRoot.sourceRoot (rowIdx w c)
          (HarmonicSourceTransport.srcFlat s) *
        N (HarmonicSourceTransport.srcFlat s) a := by
      simp [Ncanon_edgeMap,Nsource]
    _ = ∑ e : Fin 45,
      srcB2 SourceExactRoot.sourceRoot (rowIdx w c) e * N e a := by
      have hEq (e : Fin 45) :
          HarmonicSourceTransport.srcFlat (sourceEdgeEquiv.symm e) = e :=
        sourceEdgeEquiv.apply_symm_apply e
      simpa only [hEq] using hsum.symm
    _ = 0 := hfin

theorem source_vector_balance (a : Fin 4) :
    ∀ w : SrcFree, srcRowSum (NcanonCol a) SourceExactRoot.sourceRoot w = 0 := by
  intro w
  apply (geom_balance_iff_b2_rows (α := NcanonCol a)
    (u := SourceExactRoot.sourceRoot)).mp
  intro w' c
  exact source_B2_rows a w' c

theorem canonical_free_balance (a : Fin 4) :
    ∀ v : Free,
      ∑ e : Edge,
        (NcanonCol a e * incidence e v) •
          edgeVector (FlashRootNetwork.canonAnchors SourceExactRoot.sourceRoot)
            (FlashRootNetwork.canonCenters SourceExactRoot.sourceRoot)
            (LocalSharpAuxZ.canonFaceZ SourceExactRoot.sourceRoot) e = 0 := by
  apply canonical_free_balance_of_source_geom
    (α := NcanonCol a) (u := SourceExactRoot.sourceRoot)
  · intro k
    exact Ncanon_zero_slack k a
  · intro s
    exact HarmonicSourceGeomConsumer.hEV_discharged
      SourceExactRoot.sourceRoot s
  · exact source_vector_balance a

end
end N11Formalization.SourceNormalizedCanonical
#check @N11Formalization.SourceNormalizedCanonical.Ncanon_edgeMap
#check @N11Formalization.SourceNormalizedCanonical.source_vector_balance
#check @N11Formalization.SourceNormalizedCanonical.canonical_free_balance
#print axioms N11Formalization.SourceNormalizedCanonical.canonical_free_balance
