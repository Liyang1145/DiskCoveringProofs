import N11Formalization
set_option autoImplicit false
open N11Formalization SourceChartIsometry
abbrev Case := Fin 7
def nodeID : Case → Fin 5011 := ![3591,3601,3619,3852,3874,3950,4266]
set_option maxRecDepth 10000
namespace CuttingPlaneDomains
-- Exact potentials read from each ACTUAL node, not numerical angle samples.
def Y (ci : Case) (q : Fin 9) : ℚ :=
  DBMMinorantDual.db (nodeID ci) 0 q.succ-DBMMinorantDual.db (nodeID ci) 0 q.castSucc
def y (ci : Case) (q : Fin 9) : ℝ := (Y ci q : ℝ)
private theorem rows0 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 0 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 0 q)≤
        DBMMinorantDual.db (nodeID 0) i j := by decide +kernel
private theorem rows1 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 1 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 1 q)≤
        DBMMinorantDual.db (nodeID 1) i j := by decide +kernel
private theorem rows2 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 2 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 2 q)≤
        DBMMinorantDual.db (nodeID 2) i j := by decide +kernel
private theorem rows3 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 3 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 3 q)≤
        DBMMinorantDual.db (nodeID 3) i j := by decide +kernel
private theorem rows4 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 4 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 4 q)≤
        DBMMinorantDual.db (nodeID 4) i j := by decide +kernel
private theorem rows5 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 5 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 5 q)≤
        DBMMinorantDual.db (nodeID 5) i j := by decide +kernel
private theorem rows6 : ∀ i j : Fin 10,
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y 6 q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y 6 q)≤
        DBMMinorantDual.db (nodeID 6) i j := by decide +kernel
private theorem rational_rows (ci : Case) (i j : Fin 10) :
    (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < j.val),Y ci q)-
      (∑ q ∈ Finset.univ.filter (fun q : Fin 9 => q.val < i.val),Y ci q)≤
        DBMMinorantDual.db (nodeID ci) i j := by
  fin_cases ci
  · exact rows0 i j
  · exact rows1 i j
  · exact rows2 i j
  · exact rows3 i j
  · exact rows4 i j
  · exact rows5 i j
  · exact rows6 i j
theorem real_cell (ci : Case) :
    FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 (nodeID ci))
      (FlashLeafSplit.tlift (y ci)) := by
  intro i j
  have h := (Rat.cast_le (K := ℝ)).mpr (rational_rows ci i j)
  simpa only [DBMMinorantDual.db,DBMTreeKernel.matrix,Rat.cast_sub,Rat.cast_sum,
    Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat,Int.cast_ofNat,
    FlashLeafSplit.tlift,y] using h
theorem simplex (ci : Case) : (∀ q,0 ≤ y ci q) ∧ ∑ q : Fin 9,y ci q=1 := by
  have h0 : ∀ ci : Case,∀ q : Fin 9,(0 : ℚ)≤Y ci q := by decide +kernel
  have h1 : ∀ ci : Case,(∑ q : Fin 9,Y ci q)=1 := by decide +kernel
  constructor
  · intro q; change (0 : ℝ)≤(Y ci q : ℝ); exact_mod_cast h0 ci q
  · change (∑ q : Fin 9,(Y ci q : ℝ))=1
    have h := congrArg (fun t : ℚ => (t : ℝ)) (h1 ci)
    simpa only [Rat.cast_sum,Rat.cast_one] using h
end CuttingPlaneDomains
#print axioms CuttingPlaneDomains.real_cell
#print axioms CuttingPlaneDomains.simplex
