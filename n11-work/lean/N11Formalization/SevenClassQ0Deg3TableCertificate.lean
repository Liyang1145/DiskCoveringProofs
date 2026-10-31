import N11Formalization.SevenClassQ0Deg3
import N11Formalization.SevenClassQ0Deg3TableBounds

/-! Lane A: assemble the proved q0 degree-three tables into the existing
rational area certificate interface.

The only graph input kept explicit here is that the refinement edge set is the
canonical 21-edge table.  The source degree-three theorem supplies the same
table after a canonical relabelling; transporting the dual vector and sector
table through that relabelling remains a separate geometric obligation. -/
set_option autoImplicit false
noncomputable section
namespace N11Formalization.SevenClassQ0Deg3TableCertificate

open MetricAreaRationalCertificate
open SevenClassQ0Deg3
open SevenClassQ0Deg3TableBounds
open SevenClassQ0Deg3UpperTables

/-- The proved edge, sector, and node tables give a `Degree3AreaCertificate`
once the actual edge set is the canonical table and the strict finite total is
checked.  No bound or strict inequality is postulated. -/
theorem certificate_of_canonicalTable {c : Fin 11 → Point} {r : ℝ}
    {h : Representative c r} {hr : r < 19/50} {R : Refinement c r}
    (v : NineTies c r) (T : TableBounds)
    (hedges : edges R = Finset.univ.image tableEdges)
    (hstrict :
      totalUpper R mu lam RatInterval.piHi 2048 edgeMax sectorMax <
        RatInterval.piLo) :
    Degree3AreaCertificate h hr R := by
  refine
    { v := v
      mu := mu
      lam := lam
      lam_nonnegative := by norm_num [lam]
      U := RatInterval.piHi
      grid_covers_pi := le_rfl
      N := 2048
      grid_positive := by norm_num
      node := nodeBin
      node_valid := T.node
      edgeMax := edgeMax
      sectorMax := sectorMax
      edge_bound := ?_
      sector_bound := T.sector
      strict := hstrict }
  intro e he k
  have he' : e ∈ Finset.univ.image tableEdges := by simpa only [hedges]
  rcases Finset.mem_image.mp he' with ⟨i, _, rfl⟩
  have hi : edgeUpper (∑ j ∈ tableEdges i, mu j)
      (nodeQ RatInterval.piHi 2048 k) ≤ edgeMaxAt i := T.edge i k
  simpa only [edgeMax_tableEdges] using hi

/-- Contradiction form of the canonical-table bridge, directly consumable by
the degree-three exclusion once the relabelling transport is proved. -/
theorem false_of_canonicalTable {c : Fin 11 → Point} {r : ℝ}
    {h : Representative c r} {hr : r < 19/50} {R : Refinement c r}
    (v : NineTies c r) (T : TableBounds)
    (hedges : edges R = Finset.univ.image tableEdges)
    (hstrict :
      totalUpper R mu lam RatInterval.piHi 2048 edgeMax sectorMax <
        RatInterval.piLo) :
    False :=
  false_of_areaCertificate
    (certificate_of_canonicalTable v T hedges hstrict)

end N11Formalization.SevenClassQ0Deg3TableCertificate
#check @N11Formalization.SevenClassQ0Deg3TableCertificate.certificate_of_canonicalTable
#check @N11Formalization.SevenClassQ0Deg3TableCertificate.false_of_canonicalTable
#print axioms N11Formalization.SevenClassQ0Deg3TableCertificate.certificate_of_canonicalTable
#print axioms N11Formalization.SevenClassQ0Deg3TableCertificate.false_of_canonicalTable
