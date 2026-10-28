import N11Formalization.SourceFaceReflection
import N11Formalization.HarmonicSourceTransport

/-!
All nine CORRECT source active face blocks, including reflected faces.
Positive representative physical weights are split by the actual orbit sizes.
All27 face-edge coefficients, exact face-mass preservation and the FULL
45-edge sums for18 auxiliary B2 coordinate rows are supplied. Centre B2 rows,
boundary multipliers/spoke weights and positive normalized total stress remain.
-/
set_option autoImplicit false
namespace N11Formalization.SourceAllFaceBalance
open N11Formalization ResumeLocalIncidence SourceFaceReflection
open CircumcenterGeometry
noncomputable section

def repIndex (f : Fin 9) : Fin 5 := ![4,4,0,1,2,2,1,0,3] f
def mirrored (f : Fin 9) : Bool := ![true,false,false,false,false,true,true,true,false] f
def vertexPerm (f : Fin 9) (t : Fin 3) : Fin 3 :=
  ![t,t,t,t,t,swapVertex t,swapVertex t,swapVertex t,t] f
def beta (f : Fin 9) (t : Fin 3) : ℝ := SourceRepresentativeFaceBalance.beta (repIndex f) (vertexPerm f t)
def center (f : Fin 9) : Point :=
  if mirrored f then flip (SourceRepresentativeFaceBalance.center (repIndex f))
  else SourceRepresentativeFaceBalance.center (repIndex f)

theorem source_face_indices :
    ∀ f : Fin 9, ∀ t : Fin 3,
      sourceFaces f t =
        if mirrored f then
          siteMirror (sourceFaces (SourceRepresentativeFaceBalance.faceIndex (repIndex f)) (vertexPerm f t))
        else sourceFaces (SourceRepresentativeFaceBalance.faceIndex (repIndex f)) (vertexPerm f t) := by
  decide

def vertex (f : Fin 9) (t : Fin 3) : Point :=
  if mirrored f then flip (SourceRepresentativeFaceBalance.vertices (repIndex f) (vertexPerm f t))
  else SourceRepresentativeFaceBalance.vertices (repIndex f) (vertexPerm f t)

theorem actual_vertex (f : Fin 9) (t : Fin 3) :
    centersOfRoot SourceExactRoot.sourceRoot (sourceFaces f t)=vertex f t := by
  rw [source_face_indices]
  unfold vertex
  split_ifs
  · rw [actual_site_reflection,SourceRepresentativeFaceBalance.source_vertex]
  · rw [SourceRepresentativeFaceBalance.source_vertex]

theorem beta_pos (f : Fin 9) (t : Fin 3) : 0<beta f t :=
  SourceRepresentativeFaceBalance.beta_pos _ _

private theorem sum_swap_real (g : Fin 3 → ℝ) :
    ∑ t : Fin 3, g (swapVertex t)=∑ t : Fin 3,g t := by
  simp [swapVertex,Fin.sum_univ_succ]
  ring
private theorem sum_swap_point (g : Fin 3 → Point) :
    ∑ t : Fin 3, g (swapVertex t)=∑ t : Fin 3,g t := by
  simp [swapVertex,Fin.sum_univ_succ]
  abel

theorem beta_sum (f : Fin 9) : ∑ t : Fin 3,beta f t=1 := by
  have hs (j : Fin 5) := SourceRepresentativeFaceBalance.beta_sum j
  fin_cases f <;> simp only [beta,repIndex,vertexPerm,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val,Fin.reduceFinMk]
  all_goals first
    | exact hs _
    | (rw [sum_swap_real]; exact hs _)

theorem center_affine (f : Fin 9) : center f=∑ t : Fin 3,beta f t • vertex f t := by
  have hs (j : Fin 5) := SourceRepresentativeFaceBalance.center_affine j
  have hm (j : Fin 5) : flip (SourceRepresentativeFaceBalance.center j) =
      ∑ t : Fin 3, SourceRepresentativeFaceBalance.beta j t •
        flip (SourceRepresentativeFaceBalance.vertices j t) := by
    have h := congrArg flipLinear (hs j)
    simpa only [map_sum,map_smul,flipLinear_apply] using h
  have hms (j : Fin 5) : flip (SourceRepresentativeFaceBalance.center j) =
      ∑ t : Fin 3,SourceRepresentativeFaceBalance.beta j (swapVertex t) •
        flip (SourceRepresentativeFaceBalance.vertices j (swapVertex t)) :=
    (hm j).trans (sum_swap_point (fun t : Fin 3 =>
      SourceRepresentativeFaceBalance.beta j t •
        flip (SourceRepresentativeFaceBalance.vertices j t))).symm
  fin_cases f <;> simp only [center,beta,vertex,repIndex,vertexPerm,mirrored,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,Fin.reduceFinMk,ite_true]
  · exact hm 4
  · exact hs 4
  · exact hs 0
  · exact hs 1
  · exact hs 2
  · exact hms 2
  · exact hms 1
  · exact hms 0
  · exact hs 3

private theorem representative_det (j : Fin 5) :
    triangleDet (SourceRepresentativeFaceBalance.vertices j 0)
      (SourceRepresentativeFaceBalance.vertices j 1)
      (SourceRepresentativeFaceBalance.vertices j 2)≠0 := by
  simpa only [SourceRepresentativeFaceBalance.source_vertex] using representative_source_det j

theorem actual_triangle_det (f : Fin 9) :
    triangleDet (vertex f 0) (vertex f 1) (vertex f 2)≠0 := by
  have hs (j : Fin 5) := representative_det j
  fin_cases f <;> simp only [vertex,repIndex,vertexPerm,mirrored,
    swapVertex,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val,Fin.reduceFinMk,ite_true]
  · rw [triangleDet_flip]; exact neg_ne_zero.mpr (hs 4)
  · exact hs 4
  · exact hs 0
  · exact hs 1
  · exact hs 2
  · rw [triangleDet_flip,triangleDet_swap,neg_neg]; exact hs 2
  · rw [triangleDet_flip,triangleDet_swap,neg_neg]; exact hs 1
  · rw [triangleDet_flip,triangleDet_swap,neg_neg]; exact hs 0
  · exact hs 3

private theorem representative_circumcenter (j : Fin 5) :
    circumcenter (SourceRepresentativeFaceBalance.vertices j 0)
      (SourceRepresentativeFaceBalance.vertices j 1)
      (SourceRepresentativeFaceBalance.vertices j 2)=SourceRepresentativeFaceBalance.center j := by
  have h := SourceRepresentativeFaceBalance.source_aux j
  rw [SourceN2.srcZ2_eq,SourceRepresentativeFaceBalance.source_vertex,
    SourceRepresentativeFaceBalance.source_vertex,SourceRepresentativeFaceBalance.source_vertex] at h
  exact h

private theorem circumcenter_swap (A B C : Point) (hdet : triangleDet A B C≠0) :
    circumcenter B A C=circumcenter A B C := by
  obtain ⟨hAB,hAC⟩ := circumcenter_equidistant A B C hdet
  apply circumcenter_eq_of_equidistant
  · rw [triangleDet_swap]
    exact neg_ne_zero.mpr hdet
  · exact hAB.symm
  · exact hAB.symm.trans hAC

/-- Exact actual SourceN2 auxiliary identity for ALL9 faces, not merely a
reindexed formal point or a root value supplied as a hypothesis. -/
theorem actual_aux (f : Fin 9) : SourceN2.srcZ2 SourceExactRoot.sourceRoot f=center f := by
  rw [SourceN2.srcZ2_eq,actual_vertex,actual_vertex,actual_vertex]
  have hs (j : Fin 5) := representative_circumcenter j
  have hmf (j : Fin 5) :
      circumcenter (flip (SourceRepresentativeFaceBalance.vertices j 0))
        (flip (SourceRepresentativeFaceBalance.vertices j 1))
        (flip (SourceRepresentativeFaceBalance.vertices j 2))=
        flip (SourceRepresentativeFaceBalance.center j) := by
    rw [circumcenter_flip _ _ _ (representative_det j),hs]
  have hswap (j : Fin 5) :
      circumcenter (flip (SourceRepresentativeFaceBalance.vertices j 1))
        (flip (SourceRepresentativeFaceBalance.vertices j 0))
        (flip (SourceRepresentativeFaceBalance.vertices j 2))=
        flip (SourceRepresentativeFaceBalance.center j) := by
    have hd : triangleDet (SourceRepresentativeFaceBalance.vertices j 1)
        (SourceRepresentativeFaceBalance.vertices j 0)
        (SourceRepresentativeFaceBalance.vertices j 2)≠0 := by
      rw [triangleDet_swap]
      exact neg_ne_zero.mpr (representative_det j)
    rw [circumcenter_flip _ _ _ hd,
      circumcenter_swap _ _ _ (representative_det j),hs]
  fin_cases f <;> simp only [vertex,center,repIndex,vertexPerm,mirrored,
    swapVertex,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val,Fin.reduceFinMk,ite_true]
  · exact hmf 4
  · exact hs 4
  · exact hs 0
  · exact hs 1
  · exact hs 2
  · exact hswap 2
  · exact hswap 1
  · exact hswap 0
  · exact hs 3

def orbitSize (j : Fin 5) : ℝ := ![2,2,2,1,2] j
def faceWeight (f : Fin 9) : ℝ := PhysicalInteriorObjective.weight (repIndex f)/orbitSize (repIndex f)
def coefficient (f : Fin 9) (t : Fin 3) : ℝ := faceWeight f*beta f t

theorem orbitSize_pos (j : Fin 5) : 0<orbitSize j := by fin_cases j <;> norm_num [orbitSize]
theorem faceWeight_pos (f : Fin 9) : 0<faceWeight f :=
  div_pos (PhysicalInteriorObjective.weight_pos _) (orbitSize_pos _)
theorem coefficient_pos (f : Fin 9) (t : Fin 3) : 0<coefficient f t :=
  mul_pos (faceWeight_pos f) (beta_pos f t)

theorem faceWeight_mass :
    ∑ f : Fin 9,faceWeight f=∑ j : Fin 5,PhysicalInteriorObjective.weight j := by
  simp [faceWeight,repIndex,orbitSize,Fin.sum_univ_succ]
  ring

theorem coefficient_mass :
    ∑ f : Fin 9,∑ t : Fin 3,coefficient f t=∑ j : Fin 5,PhysicalInteriorObjective.weight j := by
  simp only [coefficient,← Finset.mul_sum,beta_sum,mul_one]
  exact faceWeight_mass

theorem actual_auxiliary_balance (f : Fin 9) :
    ∑ t : Fin 3, coefficient f t •
      (SourceN2.srcZ2 SourceExactRoot.sourceRoot f-
        centersOfRoot SourceExactRoot.sourceRoot (sourceFaces f t))=0 := by
  simp only [coefficient,actual_aux,actual_vertex,mul_smul]
  rw [← Finset.smul_sum]
  have hz : ∑ t : Fin 3,beta f t • (center f-vertex f t)=0 := by
    simp only [smul_sub,Finset.sum_sub_distrib]
    rw [← Finset.sum_smul,beta_sum,one_smul,← center_affine,sub_self]
  rw [hz,smul_zero]

theorem actual_auxiliary_B2_rows (f : Fin 9) (c : Fin 2) :
    ∑ t : Fin 3,
      SourceN2.srcB2 SourceExactRoot.sourceRoot
        (⟨22+2*f.val+c.val,by omega⟩ : Fin 41) (SourceN2.faceFlatEdge f t)*coefficient f t=0 := by
  simp only [SourceN2Geom.srcB2_face_aux_row,SourceN2.srcD2_face]
  have hc := congrArg (fun p : Point => p c) (actual_auxiliary_balance f)
  simp only [WithLp.ofLp_sum,Finset.sum_apply,WithLp.ofLp_smul,Pi.smul_apply,
    PiLp.sub_apply,PiLp.zero_apply,smul_eq_mul] at hc
  convert hc using 1
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- Face-only coefficients; spoke weights are ZERO here, not the final stress. -/
def faceOnlyStress : SourceEdge → ℝ
  | .inl _ => 0
  | .inr (f,t) => coefficient f t

/-- Full45-edge sums for ALL18 auxiliary source B2 rows. Centre-force rows and
the physical tie/spoke assembly are NOT claimed by this face-only consumer. -/
theorem full_auxiliary_B2_rows (f : Fin 9) (c : Fin 2) :
    ∑ s : SourceEdge, SourceN2.srcB2 SourceExactRoot.sourceRoot
      (⟨22+2*f.val+c.val,by omega⟩ : Fin 41) (HarmonicSourceTransport.srcFlat s)*
      faceOnlyStress s=0 := by
  simp only [Fintype.sum_sum_type,faceOnlyStress,mul_zero,Finset.sum_const_zero,zero_add,
    Fintype.sum_prod_type,HarmonicSourceTransport.srcFlat]
  have hz (g : Fin 9) (hgf : g≠f) (t : Fin 3) :
      SourceN2.srcB2 SourceExactRoot.sourceRoot
        (⟨22+2*f.val+c.val,by omega⟩ : Fin 41) (SourceN2.faceFlatEdge g t)=0 := by
    apply SourceN2Geom.srcB2_face_zero_row
    · change 22+2*f.val+c.val≠40
      omega
    · have hg : (sourceFaces g t).val<11 := (sourceFaces g t).isLt
      change (22+2*f.val+c.val)/2≠(sourceFaces g t).val
      omega
    · have hne : g.val≠f.val := fun h => hgf (Fin.ext h)
      change (22+2*f.val+c.val)/2≠11+g.val
      omega
  calc
    _ = ∑ g : Fin 9, if g=f then
        (∑ t : Fin 3,SourceN2.srcB2 SourceExactRoot.sourceRoot
          (⟨22+2*f.val+c.val,by omega⟩ : Fin 41) (SourceN2.faceFlatEdge f t)*coefficient f t)
        else 0 := by
      apply Finset.sum_congr rfl
      intro g _
      by_cases hgf : g=f
      · subst g
        simp
      · simp [hgf,hz g hgf]
    _ = 0 := by simp [actual_auxiliary_B2_rows]

end
end N11Formalization.SourceAllFaceBalance
#check @N11Formalization.SourceAllFaceBalance.actual_aux
#check @N11Formalization.SourceAllFaceBalance.coefficient_pos
#check @N11Formalization.SourceAllFaceBalance.coefficient_mass
#check @N11Formalization.SourceAllFaceBalance.full_auxiliary_B2_rows
#print axioms N11Formalization.SourceAllFaceBalance.full_auxiliary_B2_rows
