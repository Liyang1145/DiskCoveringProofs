import N11Formalization.SevenClassQ0Deg3TableCertificate
import N11Formalization.ActualCanonicalMomentTransport
import N11Formalization.ActualHubDegreeClasses
import N11Formalization.ActualQ0RunDegrees
import N11Formalization.ActualBoundaryNineTies

/-! Lane A: transport the canonical degree-three table bounds through the
canonical relabelling supplied by `degree_three_table_graph`.

The graph theorem gives an unknown rotation `k` and reflection `b`.  The
definitions below pull the dual vector, edge maxima and sector maxima back by
that permutation.  The resulting certificate therefore has no explicit
canonical-edge hypothesis; the strict finite total remains a separate named
premise. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3RelabelledTableCertificate

open ActualCanonicalFaceCoordinates ActualCanonicalSitePermutation
open ActualCanonicalMomentTransport
open MetricAreaRationalCertificate
open SevenClassQ0Deg3
open SevenClassQ0Deg3TableBounds
open SevenClassQ0Deg3UpperTables

def renameMu (p : Equiv.Perm (Fin 11)) (mu : Fin 11 → ℚ) : Fin 11 → ℚ :=
  fun i => mu (p.symm i)

def renameEdgeMax (p : Equiv.Perm (Fin 11))
    (edgeMax : Finset (Fin 11) → ℚ) : Finset (Fin 11) → ℚ :=
  fun e => edgeMax (labelMap p.symm e)

def renameSectorMax (cut : Fin 9) (sectorMax : Fin 9 → ℚ) : Fin 9 → ℚ :=
  fun i => sectorMax (i-cut)

theorem edge_bound_relabel {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (T : TableBounds) (p : Equiv.Perm (Fin 11))
    (hedges : edges R = (Finset.univ.image tableEdges).image (labelMap p)) :
    ∀ e ∈ edges R, ∀ k : Fin 2049,
      edgeUpper (∑ j ∈ e, renameMu p mu j) (nodeQ RatInterval.piHi 2048 k) ≤
        renameEdgeMax p edgeMax e := by
  intro e he k
  have he' : e ∈ (Finset.univ.image tableEdges).image (labelMap p) := by
    simpa only [hedges] using he
  rcases Finset.mem_image.mp he' with ⟨t, ht, rfl⟩
  rcases Finset.mem_image.mp ht with ⟨i, _, rfl⟩
  have hsum : (∑ j ∈ labelMap p (tableEdges i), renameMu p mu j)=
      ∑ j ∈ tableEdges i, mu j := by
    simpa only [renameMu] using sum_labelMap_pullback p mu (tableEdges i)
  have hmax : renameEdgeMax p edgeMax (labelMap p (tableEdges i))=edgeMaxAt i := by
    simp only [renameEdgeMax,labelMap_symm_apply,edgeMax_tableEdges]
  simpa only [hsum,hmax] using T.edge i k

theorem sector_bound_relabel {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (T : TableBounds) (cut : Fin 9) (b : Bool) :
    ∀ (i : Fin 9) (k : Fin 2049),
      sectorUpper (renameMu (canonicalPerm cut b) mu (nextSite i)) lam
          (nodeQ RatInterval.piHi 2048 k) (nodeBin k) ≤
        renameSectorMax cut sectorMax i := by
  intro i k
  have hnext : canonicalPerm cut b (nextSite (i-cut))=nextSite i := by
    rw [canonicalPerm_nextSite]
    exact sub_add_cancel i cut
  have hmu : renameMu (canonicalPerm cut b) mu (nextSite i)=mu (nextSite (i-cut)) := by
    simp only [renameMu,← hnext,Equiv.symm_apply_apply]
  simpa only [hmu,renameSectorMax] using T.sector (i-cut) k

/-- Relabelling the dual vector and both tables leaves the exact finite total
unchanged, provided the actual edge set is the relabelled canonical table. -/
theorem totalUpper_relabel_eq {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (cut : Fin 9) (b : Bool) (U : ℚ) (N : ℕ)
    (hedges : edges R =
      (Finset.univ.image tableEdges).image (labelMap (canonicalPerm cut b))) :
    totalUpper R (renameMu (canonicalPerm cut b) mu) lam U N
        (renameEdgeMax (canonicalPerm cut b) edgeMax) (renameSectorMax cut sectorMax) =
      totalUpper R mu lam U N edgeMax sectorMax := by
  have htotal : (∑ j : Fin 11, renameMu (canonicalPerm cut b) mu j) =
      ∑ j : Fin 11, mu j := by
    simpa only [renameMu] using Equiv.sum_comp (canonicalPerm cut b).symm mu
  have hedge :
      (∑ e ∈ edges R,
        (renameEdgeMax (canonicalPerm cut b) edgeMax e +
          ((19/50 : ℚ)^2 + |∑ j ∈ e,
            renameMu (canonicalPerm cut b) mu j|) * U / N)) =
      (∑ i : Fin 21,
        (edgeMaxAt i +
          ((19/50 : ℚ)^2 + |∑ j ∈ tableEdges i, mu j|) * U / N)) := by
    rw [hedges, Finset.image_image,
      Finset.sum_image (fun i _ j _ hij =>
        tableEdges_injective (labelMap_injective (canonicalPerm cut b) hij))]
    apply Finset.sum_congr rfl
    intro i _
    have hsum : (∑ j ∈ labelMap (canonicalPerm cut b) (tableEdges i),
        renameMu (canonicalPerm cut b) mu j) =
        ∑ j ∈ tableEdges i, mu j := by
      simpa only [renameMu] using
        sum_labelMap_pullback (canonicalPerm cut b) mu (tableEdges i)
    have hmax : renameEdgeMax (canonicalPerm cut b) edgeMax
        (labelMap (canonicalPerm cut b) (tableEdges i)) = edgeMaxAt i := by
      simp only [renameEdgeMax,labelMap_symm_apply,edgeMax_tableEdges]
    simp only [hsum,hmax]
  have hsector :
      (∑ i : Fin 9,
        (renameSectorMax cut sectorMax i +
          (1 + lam + |renameMu (canonicalPerm cut b) mu (nextSite i)|) * U / N)) =
      (∑ i : Fin 9,
        (sectorMax i + (1 + lam + |mu (nextSite i)|) * U / N)) := by
    have hnext (i : Fin 9) :
        renameMu (canonicalPerm cut b) mu (nextSite i) = mu (nextSite (i-cut)) := by
      have hsite : canonicalPerm cut b (nextSite (i-cut)) = nextSite i := by
        rw [canonicalPerm_nextSite]
        exact sub_add_cancel i cut
      simp only [renameMu,← hsite,Equiv.symm_apply_apply]
    simpa only [renameSectorMax,hnext] using
      cyclicSum_pullback cut
        (fun i : Fin 9 => sectorMax i + (1 + lam + |mu (nextSite i)|) * U / N)
  unfold totalUpper
  rw [htotal,hedge,hsector]

/-- The relocated strict finite total is equivalent to the canonical strict
finite total on a relabelled canonical table. -/
theorem strict_relabel_iff {c : Fin 11 → Point} {r : ℝ} {R : Refinement c r}
    (cut : Fin 9) (b : Bool) (U : ℚ) (N : ℕ)
    (hedges : edges R =
      (Finset.univ.image tableEdges).image (labelMap (canonicalPerm cut b))) :
    totalUpper R (renameMu (canonicalPerm cut b) mu) lam U N
        (renameEdgeMax (canonicalPerm cut b) edgeMax)
        (renameSectorMax cut sectorMax) < RatInterval.piLo ↔
      totalUpper R mu lam U N edgeMax sectorMax < RatInterval.piLo := by
  rw [totalUpper_relabel_eq cut b U N hedges]

/-- The degree-three graph theorem plus the canonical strict total constructs
the area certificate.  The canonical-edge premise is discharged existentially
from the actual cover, and the strict inequality is transported to the chosen
relabelling by `strict_relabel_iff`. -/
theorem certificate_of_degreeThreeGraph {c : Fin 11 → Point} {r : ℝ}
    {h : Representative c r} {hr : r < 19/50} {R : Refinement c r}
    (v : NineTies c r) (T : TableBounds)
    (hq : (ringOnlyTriangles R).card = 0)
    (hd : (neighbors R 9).card = 3 ∨ (neighbors R 10).card = 3)
    (hstrict : totalUpper R mu lam RatInterval.piHi 2048 edgeMax sectorMax <
      RatInterval.piLo) :
    Degree3AreaCertificate h hr R := by
  rcases degree_three_table_graph h hr R hq hd with ⟨cut, b, hedges⟩
  refine
    { v := v
      mu := renameMu (canonicalPerm cut b) mu
      lam := lam
      lam_nonnegative := by norm_num [lam]
      U := RatInterval.piHi
      grid_covers_pi := le_rfl
      N := 2048
      grid_positive := by norm_num
      node := nodeBin
      node_valid := T.node
      edgeMax := renameEdgeMax (canonicalPerm cut b) edgeMax
      sectorMax := renameSectorMax cut sectorMax
      edge_bound := edge_bound_relabel T (canonicalPerm cut b) hedges
      sector_bound := sector_bound_relabel T cut b
      strict := (strict_relabel_iff cut b RatInterval.piHi 2048 hedges).mpr hstrict }

theorem false_of_degreeThreeGraph {c : Fin 11 → Point} {r : ℝ}
    {h : Representative c r} {hr : r < 19/50} {R : Refinement c r}
    (v : NineTies c r) (T : TableBounds)
    (hq : (ringOnlyTriangles R).card = 0)
    (hd : (neighbors R 9).card = 3 ∨ (neighbors R 10).card = 3)
    (hstrict : totalUpper R mu lam RatInterval.piHi 2048 edgeMax sectorMax <
      RatInterval.piLo) : False :=
  false_of_areaCertificate (certificate_of_degreeThreeGraph v T hq hd hstrict)

/-- A single canonical strict-total estimate for every degree-three q0 run
constructs the previously named `Q0Degree3AreaInput`.  The q0/degree-three
hypotheses are derived from run length one and the actual hub census; they are
not assumed. -/
theorem q0Degree3AreaInput_of_strictTotal
    (hstrict : ∀ {c : Fin 11 → Point} {r : ℝ} {h : Representative c r}
      {hr : r < 19/50} {R : Refinement c r} (O : OrderedData R),
      O.run_length.val = 1 →
        totalUpper R mu lam RatInterval.piHi 2048 edgeMax sectorMax <
          RatInterval.piLo) :
    Q0Degree3AreaInput := by
  refine ⟨fun c r h hr R O hrun => ?_⟩
  have hdeg := ActualQ0RunDegrees.actual_q0_run_degrees h hr O
  have hmin : min (neighbors R 9).card (neighbors R 10).card = 3 := by
    have hs := hdeg
    cases hc : O.fans.colors O.cut <;>
      simp only [hc, ActualQ0BoundaryFans.hubSite, Bool.not_false,
        Bool.not_true, Bool.false_eq_true, if_false, if_true] at hs ⊢ <;>
      omega
  have hmax : max (neighbors R 9).card (neighbors R 10).card = 10 := by
    have hs := hdeg
    cases hc : O.fans.colors O.cut <;>
      simp only [hc, ActualQ0BoundaryFans.hubSite, Bool.not_false,
        Bool.not_true, Bool.false_eq_true, if_false, if_true] at hs ⊢ <;>
      omega
  have hq : (ringOnlyTriangles R).card = 0 := by
    rcases ActualHubDegreeClasses.actual_q0_q1_degree_classes h hr R with
      ⟨hq, _⟩ | ⟨_, hq1⟩
    · exact hq
    · exfalso
      unfold ActualHubDegreeClasses.Q1Classes at hq1
      omega
  have hd : (neighbors R 9).card = 3 ∨ (neighbors R 10).card = 3 := by
    by_cases hle : (neighbors R 9).card ≤ (neighbors R 10).card
    · left
      rw [min_eq_left hle] at hmin
      exact hmin
    · right
      have hle' : (neighbors R 10).card ≤ (neighbors R 9).card := by omega
      rw [min_eq_right hle'] at hmin
      exact hmin
  obtain ⟨v⟩ := ActualBoundaryNineTies.nineTies_of_cover
    h.cover hr h.labels h.midpoint_order
  exact ⟨certificate_of_degreeThreeGraph v tableBounds hq hd
    (hstrict O hrun)⟩

end N11Formalization.SevenClassQ0Deg3RelabelledTableCertificate
#check @N11Formalization.SevenClassQ0Deg3RelabelledTableCertificate.edge_bound_relabel
#check @N11Formalization.SevenClassQ0Deg3RelabelledTableCertificate.sector_bound_relabel
#check @N11Formalization.SevenClassQ0Deg3RelabelledTableCertificate.certificate_of_degreeThreeGraph
#check @N11Formalization.SevenClassQ0Deg3RelabelledTableCertificate.false_of_degreeThreeGraph
#check @N11Formalization.SevenClassQ0Deg3RelabelledTableCertificate.q0Degree3AreaInput_of_strictTotal
#print axioms N11Formalization.SevenClassQ0Deg3RelabelledTableCertificate.edge_bound_relabel
#print axioms N11Formalization.SevenClassQ0Deg3RelabelledTableCertificate.sector_bound_relabel
#print axioms N11Formalization.SevenClassQ0Deg3RelabelledTableCertificate.totalUpper_relabel_eq
#print axioms N11Formalization.SevenClassQ0Deg3RelabelledTableCertificate.strict_relabel_iff
#print axioms N11Formalization.SevenClassQ0Deg3RelabelledTableCertificate.certificate_of_degreeThreeGraph
#print axioms N11Formalization.SevenClassQ0Deg3RelabelledTableCertificate.false_of_degreeThreeGraph
#print axioms N11Formalization.SevenClassQ0Deg3RelabelledTableCertificate.q0Degree3AreaInput_of_strictTotal
