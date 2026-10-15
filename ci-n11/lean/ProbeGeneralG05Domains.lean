import N11Formalization
set_option autoImplicit false
open N11Formalization SourceChartIsometry Finset
set_option maxRecDepth 10000
namespace GeneralG05Nonempty
abbrev Case := Fin 21
def nodeID : Case → Fin 5011 := ![456,457,460,465,466,483,485,488,490,491,492,493,499,502,504,510,512,519,521,544,546]
def Y (ci : Case) (q : Fin 9) : ℚ :=
  DBMMinorantDual.db (nodeID ci) 0 q.succ - DBMMinorantDual.db (nodeID ci) 0 q.castSucc
def y (ci : Case) (q : Fin 9) : ℝ := (Y ci q : ℝ)
private theorem rows0 : ∀ i j : Fin 10,
    (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < j.val), Y 0 q) -
      (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < i.val), Y 0 q) ≤
        DBMMinorantDual.db (nodeID 0) i j := by decide +kernel
private theorem rows1 : ∀ i j : Fin 10,
    (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < j.val), Y 1 q) -
      (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < i.val), Y 1 q) ≤
        DBMMinorantDual.db (nodeID 1) i j := by decide +kernel
private theorem rows2 : ∀ i j : Fin 10,
    (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < j.val), Y 2 q) -
      (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < i.val), Y 2 q) ≤
        DBMMinorantDual.db (nodeID 2) i j := by decide +kernel
private theorem rows3 : ∀ i j : Fin 10,
    (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < j.val), Y 3 q) -
      (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < i.val), Y 3 q) ≤
        DBMMinorantDual.db (nodeID 3) i j := by decide +kernel
private theorem rows4 : ∀ i j : Fin 10,
    (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < j.val), Y 4 q) -
      (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < i.val), Y 4 q) ≤
        DBMMinorantDual.db (nodeID 4) i j := by decide +kernel
private theorem rows5 : ∀ i j : Fin 10,
    (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < j.val), Y 5 q) -
      (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < i.val), Y 5 q) ≤
        DBMMinorantDual.db (nodeID 5) i j := by decide +kernel
private theorem rows6 : ∀ i j : Fin 10,
    (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < j.val), Y 6 q) -
      (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < i.val), Y 6 q) ≤
        DBMMinorantDual.db (nodeID 6) i j := by decide +kernel
private theorem rows7 : ∀ i j : Fin 10,
    (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < j.val), Y 7 q) -
      (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < i.val), Y 7 q) ≤
        DBMMinorantDual.db (nodeID 7) i j := by decide +kernel
private theorem rows8 : ∀ i j : Fin 10,
    (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < j.val), Y 8 q) -
      (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < i.val), Y 8 q) ≤
        DBMMinorantDual.db (nodeID 8) i j := by decide +kernel
private theorem rows9 : ∀ i j : Fin 10,
    (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < j.val), Y 9 q) -
      (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < i.val), Y 9 q) ≤
        DBMMinorantDual.db (nodeID 9) i j := by decide +kernel
private theorem rows10 : ∀ i j : Fin 10,
    (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < j.val), Y 10 q) -
      (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < i.val), Y 10 q) ≤
        DBMMinorantDual.db (nodeID 10) i j := by decide +kernel
private theorem rows11 : ∀ i j : Fin 10,
    (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < j.val), Y 11 q) -
      (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < i.val), Y 11 q) ≤
        DBMMinorantDual.db (nodeID 11) i j := by decide +kernel
private theorem rows12 : ∀ i j : Fin 10,
    (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < j.val), Y 12 q) -
      (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < i.val), Y 12 q) ≤
        DBMMinorantDual.db (nodeID 12) i j := by decide +kernel
private theorem rows13 : ∀ i j : Fin 10,
    (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < j.val), Y 13 q) -
      (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < i.val), Y 13 q) ≤
        DBMMinorantDual.db (nodeID 13) i j := by decide +kernel
private theorem rows14 : ∀ i j : Fin 10,
    (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < j.val), Y 14 q) -
      (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < i.val), Y 14 q) ≤
        DBMMinorantDual.db (nodeID 14) i j := by decide +kernel
private theorem rows15 : ∀ i j : Fin 10,
    (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < j.val), Y 15 q) -
      (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < i.val), Y 15 q) ≤
        DBMMinorantDual.db (nodeID 15) i j := by decide +kernel
private theorem rows16 : ∀ i j : Fin 10,
    (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < j.val), Y 16 q) -
      (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < i.val), Y 16 q) ≤
        DBMMinorantDual.db (nodeID 16) i j := by decide +kernel
private theorem rows17 : ∀ i j : Fin 10,
    (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < j.val), Y 17 q) -
      (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < i.val), Y 17 q) ≤
        DBMMinorantDual.db (nodeID 17) i j := by decide +kernel
private theorem rows18 : ∀ i j : Fin 10,
    (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < j.val), Y 18 q) -
      (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < i.val), Y 18 q) ≤
        DBMMinorantDual.db (nodeID 18) i j := by decide +kernel
private theorem rows19 : ∀ i j : Fin 10,
    (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < j.val), Y 19 q) -
      (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < i.val), Y 19 q) ≤
        DBMMinorantDual.db (nodeID 19) i j := by decide +kernel
private theorem rows20 : ∀ i j : Fin 10,
    (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < j.val), Y 20 q) -
      (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < i.val), Y 20 q) ≤
        DBMMinorantDual.db (nodeID 20) i j := by decide +kernel
theorem rational_rows (ci : Case) (i j : Fin 10) :
    (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < j.val), Y ci q) -
      (∑ q ∈ univ.filter (fun q : Fin 9 => q.val < i.val), Y ci q) ≤
        DBMMinorantDual.db (nodeID ci) i j := by
  fin_cases ci
  · exact rows0 i j
  · exact rows1 i j
  · exact rows2 i j
  · exact rows3 i j
  · exact rows4 i j
  · exact rows5 i j
  · exact rows6 i j
  · exact rows7 i j
  · exact rows8 i j
  · exact rows9 i j
  · exact rows10 i j
  · exact rows11 i j
  · exact rows12 i j
  · exact rows13 i j
  · exact rows14 i j
  · exact rows15 i j
  · exact rows16 i j
  · exact rows17 i j
  · exact rows18 i j
  · exact rows19 i j
  · exact rows20 i j
theorem real_cell (ci : Case) :
    FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 (nodeID ci))
      (FlashLeafSplit.tlift (y ci)) := by
  intro i j
  have h := (Rat.cast_le (K := ℝ)).mpr (rational_rows ci i j)
  simpa only [DBMMinorantDual.db, DBMTreeKernel.matrix, Rat.cast_sub, Rat.cast_sum,
    Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat, Int.cast_ofNat,
    FlashLeafSplit.tlift, y] using h
theorem simplex (ci : Case) : (∀ q, 0 ≤ y ci q) ∧ ∑ q : Fin 9, y ci q = 1 := by
  have h0 : ∀ ci : Case, ∀ q : Fin 9, (0 : ℚ) ≤ Y ci q := by decide +kernel
  have h1 : ∀ ci : Case, (∑ q : Fin 9, Y ci q) = 1 := by decide +kernel
  constructor
  · intro q
    change (0 : ℝ) ≤ (Y ci q : ℝ)
    exact_mod_cast h0 ci q
  · change (∑ q : Fin 9, (Y ci q : ℝ)) = 1
    have h := congrArg (fun t : ℚ => (t : ℝ)) (h1 ci)
    simpa only [Rat.cast_sum, Rat.cast_one] using h
end GeneralG05Nonempty
#print axioms GeneralG05Nonempty.real_cell
#print axioms GeneralG05Nonempty.simplex
