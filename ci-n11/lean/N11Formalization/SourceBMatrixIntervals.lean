import N11Formalization.SourceAllFaceBalance
import N11Formalization.NondegProof
import N11Formalization.TCChartStationarityRoot

/-! Unconditional interval input for the ACTUAL corrected source B41x45.
The nine real circumcentres are bound by actual_aux to true source Uvec/wPoint
and reflection. No interval circumcentre division or supplied geometry premise
is used. Hub sites stay Fin11 9/10. This pays input membership, not selected
submatrix invertibility, a stress kernel, numeric width adequacy or global
optimality. -/
set_option autoImplicit false
namespace N11Formalization.SourceBMatrixIntervals
open N11Formalization RatInterval SourceN2
noncomputable section

private theorem root_mem (i : Fin 12) : (ndBox i).Mem (SourceExactRoot.sourceRoot i) :=
  ndBox_mem TCChartStationarityRoot.sourceRoot_mem_ball i

def siteBox (i : Fin 11) (q : Fin 2) : RatInterval :=
  if h : i.val < 9 then ndRingBox ndBox ⟨i.val,h⟩ q
  else if i.val = 9 then ndHub0Box ndBox q
  else ndHub1Box ndBox q

theorem siteBox_mem (i : Fin 11) (q : Fin 2) :
    (siteBox i q).Mem ((centersOfRoot SourceExactRoot.sourceRoot i).ofLp q) := by
  unfold siteBox centersOfRoot
  split_ifs
  · exact ndRingBox_mem root_mem _ q
  · exact ndHub0Box_mem root_mem q
  · exact ndHub1Box_mem root_mem q

def representativeBox (j : Fin 5) (q : Fin 2) : RatInterval :=
  ![ndUvecBox ndBox 1 q,ndUvecBox ndBox 2 q,ndUvecBox ndBox 3 q,
    ndUvecBox ndBox 8 q,ndWPointBox ndBox q] j

theorem representativeBox_mem (j : Fin 5) (q : Fin 2) :
    (representativeBox j q).Mem ((SourceRepresentativeFaceBalance.center j).ofLp q) := by
  fin_cases j
  · exact ndUvecBox_mem root_mem 1 q
  · exact ndUvecBox_mem root_mem 2 q
  · exact ndUvecBox_mem root_mem 3 q
  · exact ndUvecBox_mem root_mem 8 q
  · exact ndWPointBox_mem root_mem q

/-- Reflection preserves x and negates y, with both coordinate cases checked. -/
def flipBox (I : Fin 2 → RatInterval) (q : Fin 2) : RatInterval :=
  if q = 0 then I 0 else neg (I 1)

theorem flipBox_mem (I : Fin 2 → RatInterval) (p : Point)
    (hI : ∀ q, (I q).Mem (p.ofLp q)) (q : Fin 2) :
    (flipBox I q).Mem ((SourceFaceReflection.flip p).ofLp q) := by
  fin_cases q
  · change (I 0).Mem (p.ofLp 0)
    exact hI 0
  · change (neg (I 1)).Mem (-p.ofLp 1)
    exact neg_mem (hI 1)

def auxBox (f : Fin 9) (q : Fin 2) : RatInterval :=
  if SourceAllFaceBalance.mirrored f then
    flipBox (representativeBox (SourceAllFaceBalance.repIndex f)) q
  else representativeBox (SourceAllFaceBalance.repIndex f) q

/-- ALL9 true source circumcentres, using the paid actual_aux identity. -/
theorem auxBox_mem (f : Fin 9) (q : Fin 2) :
    (auxBox f q).Mem ((srcZ2 SourceExactRoot.sourceRoot f).ofLp q) := by
  rw [SourceAllFaceBalance.actual_aux]
  unfold auxBox SourceAllFaceBalance.center
  split_ifs
  · exact flipBox_mem _ _ (representativeBox_mem _) q
  · exact representativeBox_mem _ q

def nodeBox (i : Fin 29) (q : Fin 2) : RatInterval :=
  if h : i.val < 9 then ndArcBox ndBox ⟨i.val,h⟩ q
  else if h2 : i.val < 20 then siteBox ⟨i.val-9,by omega⟩ q
  else auxBox ⟨i.val-20,by omega⟩ q

theorem nodeBox_mem (i : Fin 29) (q : Fin 2) :
    (nodeBox i q).Mem ((srcX2 SourceExactRoot.sourceRoot i).ofLp q) := by
  unfold nodeBox srcX2
  split_ifs
  · exact ndArcBox_mem root_mem _ q
  · exact siteBox_mem _ q
  · exact auxBox_mem _ q

def edgeBox (e : Fin 45) (q : Fin 2) : RatInterval :=
  sub (nodeBox (srcEdgeV2 e) q) (nodeBox (srcEdgeW2 e) q)

theorem edgeBox_mem (e : Fin 45) (q : Fin 2) :
    (edgeBox e q).Mem (srcD2 SourceExactRoot.sourceRoot e q) :=
  sub_mem (nodeBox_mem (srcEdgeV2 e) q) (nodeBox_mem (srcEdgeW2 e) q)

def BBox (i : Fin 41) (e : Fin 45) : RatInterval :=
  if i.val = 40 then ofRat 1
  else
    let node : ℕ := 9+i.val/2
    let q : Fin 2 := ⟨i.val%2,by omega⟩
    add (if (srcEdgeV2 e).val = node then edgeBox e q else ofRat 0)
      (if (srcEdgeW2 e).val = node then neg (edgeBox e q) else ofRat 0)

private theorem ite_mem (p : Prop) [Decidable p] (I J : RatInterval) (x y : ℝ)
    (hI : I.Mem x) (hJ : J.Mem y) :
    (if p then I else J).Mem (if p then x else y) := by
  by_cases hp : p
  · simp only [if_pos hp]
    exact hI
  · simp only [if_neg hp]
    exact hJ

/-- ALL1845 actual correct B entries: no membership or source-geometry premise. -/
theorem BBox_mem (i : Fin 41) (e : Fin 45) :
    (BBox i e).Mem (srcB2 SourceExactRoot.sourceRoot i e) := by
  by_cases hi : i.val = 40
  · simp only [BBox,srcB2,if_pos hi]
    simpa only [Rat.cast_one] using ofRat_mem (1 : ℚ)
  · simp only [BBox,srcB2,if_neg hi]
    exact add_mem
      (ite_mem _ _ _ _ _ (edgeBox_mem _ _)
        (by simpa only [Rat.cast_zero] using ofRat_mem (0 : ℚ)))
      (ite_mem _ _ _ _ _ (neg_mem (edgeBox_mem _ _))
        (by simpa only [Rat.cast_zero] using ofRat_mem (0 : ℚ)))

theorem BBox_mass (e : Fin 45) : BBox 40 e = ofRat 1 := rfl

theorem actual_mass_row (e : Fin 45) :
    srcB2 SourceExactRoot.sourceRoot 40 e = 1 := rfl

end
end N11Formalization.SourceBMatrixIntervals
#check @N11Formalization.SourceBMatrixIntervals.auxBox_mem
#check @N11Formalization.SourceBMatrixIntervals.BBox_mem
#print axioms N11Formalization.SourceBMatrixIntervals.auxBox_mem
#print axioms N11Formalization.SourceBMatrixIntervals.BBox_mem
