import N11Formalization.SourceTotalCentreForce
import N11Formalization.HarmonicSourceGeomConsumer
import N11Formalization.SourceAlphaOf

/-! Reading the22 actual source centre B2 rows from the actual signed45 force
functional. No centre-force, graph balance or positivity assumption is supplied.
Combined with18 auxiliary rows this pays all40 B2 rows for the same coefficient
function. Nonnegativity/positive stress/radial flux are still separate. -/
set_option autoImplicit false
namespace N11Formalization.SourceCentreB2Readout
open N11Formalization CartesianReflectionSpace SourceFaceReflection ResumeLocalIncidence
open SourceTieForceTransport
noncomputable section

def siteOf : SourceEdge → Fin 11
  | .inl (k,s) => spokeSite k s
  | .inr (f,t) => sourceFaces f t
def otherPoint : SourceEdge → Point
  | .inl (k,_) => arcEnd SourceExactRoot.sourceRoot k
  | .inr (f,_) => SourceN2.srcZ2 SourceExactRoot.sourceRoot f
def edgeVector (e : SourceEdge) : Point :=
  centersOfRoot SourceExactRoot.sourceRoot (siteOf e)-otherPoint e
def forceFunctional (v : Full) : ℝ :=
  ∑ e : SourceEdge,SourceSignedStressAssembly.stress e*inner ℝ (edgeVector e) (siteFull v (siteOf e))

theorem forceFunctional_zero (v : Full) : forceFunctional v=0 := by
  have hf := SourceFaceForceTransport.totalFaceForce_actual v
  have ht : totalTieForce v =
      ∑ k : Fin 9,∑ s : Fin 2,SourceSignedStressAssembly.spokeCoefficient k s*
        inner ℝ (centersOfRoot SourceExactRoot.sourceRoot (spokeSite k s)-arcEnd SourceExactRoot.sourceRoot k)
          (siteFull v (spokeSite k s)) := by
    simp only [totalTieForce,tieForce,SourceSignedStressAssembly.spokeCoefficient,
      Finset.mul_sum,mul_assoc]
  have he : forceFunctional v=SourceFaceForceTransport.totalFaceForce v+totalTieForce v := by
    rw [hf,ht]
    simp only [forceFunctional,Fintype.sum_sum_type,Fintype.sum_prod_type,
      SourceSignedStressAssembly.stress,edgeVector,siteOf,otherPoint]
    ring
  simp only [he]
  exact SourceTotalCentreForce.totalCentreForce_zero v

def centreIndex (i : Fin 11) (c : Fin 2) : Fin 23 := ⟨2*i.val+c.val,by omega⟩

private theorem centreIndex_eq (i j : Fin 11) (c d : Fin 2) :
    centreIndex j d=centreIndex i c ↔ j=i ∧ d=c := by
  simp only [centreIndex,Fin.ext_iff]
  constructor <;> intro h <;> omega

theorem siteFull_coordinates (v : Full) (j : Fin 11) :
    siteFull v j = !₂[v (centreIndex j 0),v (centreIndex j 1)] := by
  ext c
  fin_cases j <;> fin_cases c <;> rfl

theorem coordinate_velocity_inner (p : Point) (i j : Fin 11) (c : Fin 2) :
    inner ℝ p (siteFull (Pi.single (centreIndex i c) 1 : Full) j)=
      if j=i then p c else 0 := by
  rw [siteFull_coordinates,PinTangentGeometry.inner_coords]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Pi.single_apply,centreIndex_eq]
  fin_cases c
  · by_cases hji : j=i <;> simp [hji,Fin.ext_iff]
  · by_cases hji : j=i <;> simp [hji,Fin.ext_iff]

theorem spokeSite_formula :
    ∀ k : Fin 9, ∀ s : Fin 2, spokeSite k s =
      (⟨(k.val+s.val)%9,by omega⟩ : Fin 11) := by decide

private theorem source_vertex_index (e : SourceEdge) :
    (SourceN2.srcEdgeV2 (HarmonicSourceTransport.srcFlat e)).val=9+(siteOf e).val := by
  rcases e with ⟨k,s⟩ | ⟨f,t⟩
  · simp only [HarmonicSourceTransport.srcFlat,SourceN2GeomEdge.srcEdgeV2_spoke,
      siteOf,spokeSite_formula,Fin.val_mk]
  · simp only [HarmonicSourceTransport.srcFlat,SourceN2.srcEdgeV2_face,siteOf,Fin.val_mk]

private theorem source_other_ne_centre (e : SourceEdge) (i : Fin 11) :
    (SourceN2.srcEdgeW2 (HarmonicSourceTransport.srcFlat e)).val≠9+i.val := by
  rcases e with ⟨k,s⟩ | ⟨f,t⟩
  · simp only [HarmonicSourceTransport.srcFlat,SourceN2GeomEdge.srcEdgeW2_spoke,Fin.val_mk]
    omega
  · simp only [HarmonicSourceTransport.srcFlat,SourceN2Geom.srcEdgeW2_face,Fin.val_mk]
    omega

private theorem actual_edge_coordinate (e : SourceEdge) (c : Fin 2) :
    SourceN2.srcD2 SourceExactRoot.sourceRoot (HarmonicSourceTransport.srcFlat e) c=edgeVector e c := by
  rcases e with ⟨k,s⟩ | ⟨f,t⟩
  · simp only [HarmonicSourceTransport.srcFlat,SourceN2.srcD2_spoke,edgeVector,siteOf,otherPoint,
      spokeSite_formula,PiLp.sub_apply]
  · simp only [HarmonicSourceTransport.srcFlat,SourceN2.srcD2_face,edgeVector,siteOf,otherPoint,
      PiLp.sub_apply]

/-- Actual B2 incidence and source edge vector, at an independent centre row. -/
theorem centre_B2_entry (i : Fin 11) (c : Fin 2) (e : SourceEdge) :
    SourceN2.srcB2 SourceExactRoot.sourceRoot (⟨2*i.val+c.val,by omega⟩ : Fin 41)
      (HarmonicSourceTransport.srcFlat e)=if siteOf e=i then edgeVector e c else 0 := by
  have hmass : 2*i.val+c.val≠40 := by omega
  have hdiv : (2*i.val+c.val)/2=i.val := by omega
  have hmod : (⟨(2*i.val+c.val)%2,by omega⟩ : Fin 2)=c := by
    apply Fin.ext
    simp only [Fin.val_mk]
    omega
  simp only [SourceN2.srcB2,Fin.val_mk,hmass,if_false,hdiv,hmod,
    source_vertex_index,source_other_ne_centre,add_zero,actual_edge_coordinate]
  have he : (9+(siteOf e).val=9+i.val) ↔ siteOf e=i := by simp [Fin.ext_iff]
  by_cases hi : siteOf e=i
  · have hn := he.mpr hi
    simp only [hi,hn,ite_true]
  · have hn : ¬(9+(siteOf e).val=9+i.val) := fun h => hi (he.mp h)
    simp only [hi,hn,ite_false]

/-- All22 centre-coordinate B2 sums from the actual physical stationary objective,
for the SAME assembled45-edge signed stress. No graph force hypothesis. -/
theorem full_centre_B2_rows (i : Fin 11) (c : Fin 2) :
    ∑ e : SourceEdge,SourceN2.srcB2 SourceExactRoot.sourceRoot
      (⟨2*i.val+c.val,by omega⟩ : Fin 41) (HarmonicSourceTransport.srcFlat e)*
      SourceSignedStressAssembly.stress e=0 := by
  have h := forceFunctional_zero (Pi.single (centreIndex i c) 1 : Full)
  simp only [forceFunctional,coordinate_velocity_inner] at h
  rw [Finset.sum_congr rfl (fun e (_ : e ∈ (Finset.univ : Finset SourceEdge)) =>
    congrArg (fun a : ℝ => a*SourceSignedStressAssembly.stress e) (centre_B2_entry i c e))]
  convert h using 1
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- Complete actual40-row B2 certificate, retaining signed-weight status.
Positivity remains the five actual tie-weight sign obligation. -/
theorem all_B2_rows (w : HarmonicSourceTransport.SrcFree) (c : Fin 2) :
    ∑ e : SourceEdge,SourceN2.srcB2 SourceExactRoot.sourceRoot
      (HarmonicSourceGeometryV2.rowIdx w c) (HarmonicSourceTransport.srcFlat e)*
      SourceSignedStressAssembly.stress e=0 := by
  rcases w with i | f
  · have h := full_centre_B2_rows i c
    convert h using 1
    apply Finset.sum_congr rfl
    intro e _
    congr 2
    apply Fin.ext
    simp [HarmonicSourceGeometryV2.rowIdx,HarmonicSourceTransport.srcNode29]
  · have h := SourceSignedStressAssembly.full_auxiliary_B2_rows f c
    convert h using 1
    apply Finset.sum_congr rfl
    intro e _
    congr 2
    apply Fin.ext
    simp [HarmonicSourceGeometryV2.rowIdx,HarmonicSourceTransport.srcNode29]
    omega

def canonicalStress : ResumeNetwork.Edge → ℝ :=
  SourceAlphaOf.alphaEdge SourceSignedStressAssembly.stress

theorem canonical_slack_zero (q : Fin 3) :
    canonicalStress (.inr (5,q))=0 ∧ canonicalStress (.inr (7,q))=0 :=
  ⟨SourceAlphaOf.alphaEdge_slack_five _ q,SourceAlphaOf.alphaEdge_slack_seven _ q⟩

theorem canonical_source_rows (w : HarmonicSourceTransport.SrcFree) (c : Fin 2) :
    ∑ e : SourceEdge,SourceN2.srcB2 SourceExactRoot.sourceRoot
      (HarmonicSourceGeometryV2.rowIdx w c) (HarmonicSourceTransport.srcFlat e)*
      canonicalStress (ResumeLocalIncidence.edgeMap e)=0 := by
  simp only [canonicalStress,SourceAlphaOf.alphaEdge_edgeMap]
  exact all_B2_rows w c

theorem canonical_mass_one : ∑ e : ResumeNetwork.Edge,canonicalStress e=1 := by
  rw [ResumeLocalIncidence.sum_reindex canonicalStress (fun f q hf => by
    rcases hf with rfl | rfl
    · exact (canonical_slack_zero q).1
    · exact (canonical_slack_zero q).2)]
  simp only [canonicalStress,SourceAlphaOf.alphaEdge_edgeMap]
  exact SourceSignedStressAssembly.stress_mass_one

/-- Actual canonical51-edge signed force balance, directly consuming all40
source rows and the existing correct geometry/reindex consumer. Six slack
edges vanish, not their primal geometric constraints. No positivity inferred. -/
theorem canonical_free_balance (v : ResumeDirichlet.Free) :
    ∑ e : ResumeNetwork.Edge,
      (canonicalStress e*ResumeDirichlet.incidence e v) •
        ResumeDirichlet.edgeVector (FlashRootNetwork.canonAnchors SourceExactRoot.sourceRoot)
          (FlashRootNetwork.canonCenters SourceExactRoot.sourceRoot)
          (LocalSharpAuxZ.canonFaceZ SourceExactRoot.sourceRoot) e=0 := by
  apply HarmonicSourceGeometryV2.canonical_free_balance_of_source_geom canonical_slack_zero
    (HarmonicSourceGeomConsumer.hEV_discharged SourceExactRoot.sourceRoot)
  exact (HarmonicSourceGeometryV2.geom_balance_iff_b2_rows).mp canonical_source_rows

end
end N11Formalization.SourceCentreB2Readout
#check @N11Formalization.SourceCentreB2Readout.full_centre_B2_rows
#check @N11Formalization.SourceCentreB2Readout.all_B2_rows
#check @N11Formalization.SourceCentreB2Readout.canonical_free_balance
#check @N11Formalization.SourceCentreB2Readout.canonical_mass_one
#print axioms N11Formalization.SourceCentreB2Readout.all_B2_rows
#print axioms N11Formalization.SourceCentreB2Readout.canonical_free_balance
