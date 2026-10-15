/-
  DSHTopologyHubFan — DSH-TOPO-C3: two-hub / two-fan on the ACTUAL frozen `Fin 11` face table.

  Teammate `topo-hub-fan`, task-3 (handoff §2C item 3).
  Write scope: `lean/N11Formalization/DSHTopologyHubFan*.lean`, `evidence/dsh/topology/hub-fan/`.

  ## Object (frozen, referenced — never re-declared here)

  * `ResumeNetwork.face : Fin 11 → Fin 3 → Fin 11` — paid canonical face table
    (9 fan faces + 2 central faces), `edge_card = 51`.
  * `ResumeNetwork.Edge = (Fin 9 × Fin 2) ⊕ (Fin 11 × Fin 3)` — 18 boundary rows
    (`anchorIndex`) + 33 face rows (`face`).
  * `ResumeLocalIncidence.sourceFaces : Fin 9 → Fin 3 → Fin 11`, `faceMap : Fin 9 → Fin 11`,
    `rawToCanon : Fin 11 → Fin 11`, with the paid `faceMap_exact`.

  ## Representation (measured, not assumed — evidence/dsh/topology/hub-fan/probe*.log)

  Two Mathlib facilities do **not** kernel-reduce on this object and are therefore unused:

  1. `Sym2 (Fin 11)`: its `DecidableEq` is `Quot`-based and does not reduce — `decide` *proved
     false* the true statement `s(1,9) = s(9,1)` (probe7.log).
  2. `Finset.image` / `Finset.filter` enumerations: their `Decidable` instances get stuck
     (`Quot.lift`, `decidable_of_iff`), so every `decide` goal over them failed
     (probe2/9/10.log).  (`#eval` prints a value in those cases, which is why a "guessed"
     number must never be written into a `decide` goal without measuring it first.)

  All enumerations here use `List` (`filter`, `map`, `eraseDups`, `mergeSort`, `all`), which
  kernel-reduces; unordered vertex pairs are the normalised ordered pair `ep a b` (smaller
  index first).  Every numeric assertion was first *measured* by `#eval` (probe17/18/19 logs).

  ## Scope

  `local[graph]`, `standalone`.  Statements about the frozen tables only.  This file does NOT
  assert that an arbitrary `Covers c r` realizes these faces (C1/C2 + C5, other lanes), and it
  is not the lead's global `∀ r c, 0 ≤ r → Covers c r → sourceRadius ≤ r` target.
  No `sorry`, no custom axiom, no `native_decide`, no heartbeat bump.
-/
import Mathlib
import N11Formalization.ResumeNetwork
import N11Formalization.ResumeGlobalIncidence
import N11Formalization.ResumeLocalIncidence

set_option maxRecDepth 8000
set_option autoImplicit false
set_option linter.unusedVariables false

namespace N11Formalization.DSHTopologyHubFan
open N11Formalization.ResumeNetwork
open N11Formalization.ResumeLocalIncidence
open N11Formalization.ResumeGlobal

/-- Vertices of the canonical table: raw sites `0..8` (ring) and `9`,`10` (hubs). -/
abbrev V : Type := Fin 11

/-- All 11 vertices, in index order (the enumeration used by every list comprehension). -/
def allV : List V := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- The nine canonical fan faces, in index order. -/
def fanFaces : List (Fin 11) := [0, 1, 2, 3, 4, 5, 6, 7, 8]

/-- The three face slots, in order. -/
def all3 : List (Fin 3) := [0, 1, 2]

/-- Successor slot in `Fin 3` (face vertices are read cyclically). -/
def nxt (t : Fin 3) : Fin 3 := ⟨((t : ℕ) + 1) % 3, by omega⟩

/-- Normalised ordered representative of the unordered pair `{a,b}` (smaller index first). -/
def ep (a b : V) : V × V :=
  if ((a : ℕ) : Nat) ≤ ((b : ℕ) : Nat) then (a, b) else (b, a)

theorem ep_comm (a b : V) : ep a b = ep b a := by
  unfold ep
  by_cases h : ((a : ℕ) : Nat) ≤ ((b : ℕ) : Nat)
  · by_cases h2 : ((b : ℕ) : Nat) ≤ ((a : ℕ) : Nat)
    · rw [if_pos h, if_pos h2, Prod.ext_iff]
      exact ⟨Fin.ext (le_antisymm h h2), Fin.ext (le_antisymm h2 h)⟩
    · rw [if_pos h, if_neg h2]
  · rw [if_neg h, if_pos (Nat.le_of_lt (Nat.lt_of_not_le h))]

theorem ep_self (a : V) : ep a a = (a, a) := by
  unfold ep
  rw [if_pos (Nat.le_refl ((a : ℕ) : Nat))]

/-- Cyclic successor on the nine ring sites. -/
def cycSucc (v : V) : V := ⟨((v : ℕ) + 1) % 9, by omega⟩

/-- Ring-vertex predicate, Bool-valued so every comprehension reduces. -/
def isRing (v : V) : Bool := decide ((v : ℕ) < 9)

/-! ## 1. The frozen tables, verbatim (evaluated by the kernel) -/

/-- `ResumeNetwork.face`, evaluated. -/
theorem face_table :
    face 0 = ![0, 1, 9] ∧ face 1 = ![1, 2, 9] ∧ face 2 = ![2, 3, 9] ∧
    face 3 = ![3, 4, 9] ∧ face 4 = ![4, 5, 10] ∧ face 5 = ![5, 6, 10] ∧
    face 6 = ![6, 7, 10] ∧ face 7 = ![7, 8, 10] ∧ face 8 = ![8, 0, 10] ∧
    face 9 = ![0, 9, 10] ∧ face 10 = ![4, 9, 10] := by decide

/-- `ResumeLocalIncidence.sourceFaces`, evaluated (the frozen paid source table). -/
theorem sourceFaces_table :
    sourceFaces 0 = ![2, 9, 10] ∧ sourceFaces 1 = ![6, 9, 10] ∧ sourceFaces 2 = ![1, 2, 10] ∧
    sourceFaces 3 = ![2, 3, 9] ∧ sourceFaces 4 = ![3, 4, 9] ∧ sourceFaces 5 = ![4, 5, 9] ∧
    sourceFaces 6 = ![5, 6, 9] ∧ sourceFaces 7 = ![6, 7, 10] ∧ sourceFaces 8 = ![8, 0, 10] := by
  decide

/-- `faceMap`, evaluated. -/
theorem faceMap_table : faceMap = ![9, 10, 8, 0, 1, 2, 3, 4, 6] := by decide

/-- Every source face carries a hub in its third slot, and it is `9` or `10`. -/
theorem sourceFaces_hub_slot : ∀ f : Fin 9,
    (sourceFaces f 2).val = 9 ∨ (sourceFaces f 2).val = 10 := by decide

/-! ## 2. Row decomposition of the frozen 33 face rows -/

/-- Face vertex list of `f`. -/
def faceVerts (f : Fin 11) : List V := [face f 0, face f 1, face f 2]

/-- Face pairs contributed by a face list, in `(f,t)` order (duplicates kept). -/
def rowsOf (fs : List (Fin 11)) : List (V × V) :=
  (fs.map (fun f => all3.map (fun t => ep (face f t) (face f (nxt t))))).flatten

/-- The 33 canonical face rows as vertex pairs. -/
def faceRows : List (V × V) := rowsOf allV

/-- The 9 ring rows among the face rows. -/
def ringRows : List (V × V) := faceRows.filter (fun p => isRing p.1 && isRing p.2)

/-- The 24 hub rows among the face rows (at least one end a hub). -/
def hubRows : List (V × V) := faceRows.filter (fun p => !(isRing p.1 && isRing p.2))

/-- The 22 spoke rows (exactly one end a hub). -/
def spokeRows : List (V × V) := faceRows.filter (fun p => isRing p.1 != isRing p.2)

/-- Occurrence count of a pair. -/
def multi (l : List (V × V)) (p : V × V) : ℕ := (l.filter (fun q => q == p)).length

/-- The far end of a hub row from hub `h`. -/
def other (h : V) (p : V × V) : V := if p.1 == h then p.2 else p.1

/-- Vertices touched by a row list. -/
def vertsOf (l : List (V × V)) : List V := (l.map (fun p => [p.1, p.2])).flatten.eraseDups

theorem faceRows_length : faceRows.length = 33 := by decide
theorem faceRows_distinct : faceRows.eraseDups.length = 21 := by decide

/-- 9 ring rows + 24 hub rows = 33 face rows. -/
theorem row_split : ringRows.length = 9 ∧ hubRows.length = 24 ∧ spokeRows.length = 22 ∧
    ringRows.length + hubRows.length = faceRows.length := by decide

/-- **The 9 ring rows are exactly the nine consecutive edges of the 9-cycle, each exactly once.** -/
theorem ring_cycle_exact :
    ringRows = [ep 0 1, ep 1 2, ep 2 3, ep 3 4, ep 4 5, ep 5 6, ep 6 7, ep 7 8, ep 0 8] := by
  decide

/-- Every ring row is a pair of cyclically consecutive ring sites (and there are 9 of them). -/
theorem ring_cycle_consecutive :
    ringRows.all (fun p : V × V => cycSucc p.1 == p.2 || cycSucc p.2 == p.1) = true ∧
    ringRows.length = 9 := by decide

/-- **Hub rows are exactly 12 distinct pairs, each occurring exactly twice** (once in each of
the two faces sharing that spoke). -/
theorem hub_rows_multiplicity :
    hubRows.eraseDups.length = 12 ∧
    hubRows.eraseDups.all (fun p => multi hubRows p == 2) = true := by decide

/-- The 12 distinct hub-row pairs, in first-occurrence order of the frozen table. -/
theorem hub_pairs_exact :
    hubRows.eraseDups = [ep 1 9, ep 0 9, ep 2 9, ep 3 9, ep 4 9, ep 5 10, ep 4 10, ep 6 10,
      ep 7 10, ep 8 10, ep 0 10, ep 9 10] := by decide

/-- The hub-hub pair `{9,10}` is a face row. -/
theorem hub_pair_is_row : (ep 9 10) ∈ faceRows := by decide

/-! ## 3. (a) Hub identification: `9` and `10` are exactly the two hub vertices -/

/-- Faces whose vertex list contains `v`. -/
def facesWith (v : V) : List (Fin 11) := allV.filter (fun f => (faceVerts f).contains v)

/-- Neighbours of `v` in the canonical face graph (duplicates kept). -/
def neighborList (v : V) : List V :=
  ((facesWith v).map faceVerts).flatten.filter (fun w => (w == v) == false)

/-- Neighbour set of `v`, in first-occurrence order. -/
def nbrs (v : V) : List V := (neighborList v).eraseDups

/-- Face-incidence degree of `v`. -/
def degree (v : V) : Nat := (nbrs v).length

theorem degree_hub9 : degree 9 = 6 := by decide
theorem degree_hub10 : degree 10 = 7 := by decide

/-- The hub-degree pair is exactly `(6,7)`. -/
theorem hub_degrees : (degree 9, degree 10) = (6, 7) := by decide

/-- Every ring vertex has face-degree 3 or 4 (4 exactly at the two switch sites `0`,`4`). -/
theorem ring_degrees : ∀ v : V, (v : ℕ) < 9 → degree v = 3 ∨ degree v = 4 := by decide

/-- Ring vertices have face-degree at most 4. -/
theorem ring_degree_le_four : ∀ v : V, (v : ℕ) < 9 → degree v ≤ 4 := by decide

/-- The two switch ring vertices `0` and `4` have degree 4; the other seven ring vertices have
degree 3. -/
theorem ring_degree_split :
    (allV.filter (fun v => decide (degree v = 4))).length = 2 ∧
    (allV.filter (fun v => decide (degree v = 3))).length = 7 := by decide

/-- **(a) main.** A vertex is a hub (`degree ≥ 5`) **iff** it is `9` or `10`. -/
theorem hub_iff : ∀ v : V, 5 ≤ degree v ↔ v = 9 ∨ v = 10 := by decide

/-- Exactly two hub vertices. -/
theorem hub_count_two : (allV.filter (fun v => decide (5 ≤ degree v))).length = 2 := by decide

/-- The hub set is `{9,10}`. -/
theorem hub_set : allV.filter (fun v => decide (5 ≤ degree v)) = [9, 10] := by decide

/-- Ring sites and hubs partition the vertex set. -/
theorem vertex_partition :
    (allV.filter (fun v => isRing v)).length = 9 ∧
    (allV.filter (fun v => isRing v)).append ([9, 10] : List V) = allV := by decide

/-- **Negative control on the hub threshold.**  Degree `≥ 4` does *not* isolate the hubs
(it also catches the two switch sites `0`,`4`), so "exactly two hubs" genuinely uses the
degree gap `4 < 5 ≤ 6`. -/
theorem hub_threshold_control :
    (allV.filter (fun v => decide (4 ≤ degree v))).length = 4 ∧
    (allV.filter (fun v => decide (6 ≤ degree v))).length = 2 ∧
    (allV.filter (fun v => decide (5 ≤ degree v))).length = 2 := by decide

/-- The two hubs are adjacent. -/
theorem hubs_adjacent : (ep 9 10) ∈ faceRows := by decide

/-- The two hubs have exactly two common neighbours, the ring switch vertices `0` and `4`. -/
theorem hub_common_neighbors : (nbrs 9).filter (fun v => (nbrs 10).contains v) = [0, 4] := by
  decide

/-- The hub pair `{9,10}` appears only in the two central faces: it is *not* a row of either
fan. -/
theorem hub_pair_only_central :
    (ep 9 10) ∉ rowsOf [0, 1, 2, 3] ∧ (ep 9 10) ∉ rowsOf [4, 5, 6, 7, 8] ∧
    (ep 9 10) ∈ rowsOf [9, 10] := by decide

/-! ### 3.1 Independent second criterion: face-incidence counts (not neighbour counts)

`facesWith v` (faces containing `v`) is a different function from `nbrs v` (distinct
neighbours), and its count obeys the incidence identity `Σ_v |facesWith v| = 33`.  The hub
identification reproduces under this independent criterion, which is a genuine cross-check
rather than a restatement. -/

/-- Incidence identity: the 33 slots of the 11 faces are distributed over the vertices. -/
theorem incidence_sum : (allV.map (fun v => (facesWith v).length)).sum = 33 := by decide

/-- Handshake identity for the face graph: `Σ_v degree v = 2 · (number of face rows that are
distinct pairs) − (hub-pair double count)`; the measured value is 42. -/
theorem degree_sum : (allV.map degree).sum = 42 := by decide

/-- **Second, independent hub criterion**: `v` is a hub iff it lies in at least 5 faces. -/
theorem hub_iff_incidence : ∀ v : V, 5 ≤ (facesWith v).length ↔ v = 9 ∨ v = 10 := by decide

/-! ## 4. (b) Adjacency / incidence lists of the two hubs -/

/-- Hub 9's neighbours: ring `0,1,2,3,4` then hub `10`. -/
theorem neighbors_hub9 : nbrs 9 = [0, 1, 2, 3, 4, 10] := by decide

/-- Hub 10's neighbours: ring `4,5,6,7,8,0` then hub `9`. -/
theorem neighbors_hub10 : nbrs 10 = [4, 5, 6, 7, 8, 0, 9] := by decide

/-- Hub 9's face-incidence list. -/
theorem hub9_faces : facesWith 9 = [0, 1, 2, 3, 9, 10] := by decide

/-- Hub 10's face-incidence list. -/
theorem hub10_faces : facesWith 10 = [4, 5, 6, 7, 8, 9, 10] := by decide

/-- Hub 9's ring neighbours (spokes), in cyclic order. -/
theorem hub9_ring_spokes : (nbrs 9).filter isRing = [0, 1, 2, 3, 4] := by decide

/-- Hub 10's ring neighbours (spokes), in cyclic order. -/
theorem hub10_ring_spokes : (nbrs 10).filter isRing = [4, 5, 6, 7, 8, 0] := by decide

/-- The hub-9 spoke rows (5, in first-occurrence order). -/
theorem hub9_spoke_pairs :
    spokeRows.eraseDups.filter (fun p => (p.1 == 9) || (p.2 == 9)) =
      [ep 1 9, ep 0 9, ep 2 9, ep 3 9, ep 4 9] := by decide

/-- The hub-10 spoke rows (6). -/
theorem hub10_spoke_pairs :
    spokeRows.eraseDups.filter (fun p => (p.1 == 10) || (p.2 == 10)) =
      [ep 5 10, ep 4 10, ep 6 10, ep 7 10, ep 8 10, ep 0 10] := by decide

/-- The two spoke sets are disjoint. -/
theorem hub_spokes_disjoint :
    ((spokeRows.eraseDups.filter (fun p => (p.1 == 9) || (p.2 == 9))).filter
      (fun p => (spokeRows.eraseDups.filter (fun q => (q.1 == 10) || (q.2 == 10))).contains p)) =
      [] := by decide

/-- The 5 + 6 spokes cover all nine ring vertices exactly once (first-occurrence order). -/
theorem hub_spokes_cover_ring :
    (((spokeRows.eraseDups.filter (fun p => (p.1 == 9) || (p.2 == 9))).map (other 9)) ++
      ((spokeRows.eraseDups.filter (fun p => (p.1 == 10) || (p.2 == 10))).map (other 10))).eraseDups =
        [1, 0, 2, 3, 4, 5, 6, 7, 8] := by decide

/-- **Hub incidence in the boundary (18-row) block.**  `anchorIndex : Fin 9 → Fin 2 → Fin 9` is
ring-typed, so no boundary row carries a hub index: the two hubs are interior-only vertices. -/
theorem boundary_rows_are_ring : ∀ i : Fin 9, ∀ s : Fin 2, (anchorIndex i s).val < 9 := by decide

/-- The two boundary rows owned by site `i` are `(i, i-1)` (side 0) and `(i, i)` (side 1):
site `i` owns the switches `U_(i-1)` and `U_i`. -/
theorem anchorIndex_table : ∀ i : Fin 9, (anchorIndex i 0) + 1 = i ∧ anchorIndex i 1 = i := by
  decide

/-! ## 5. (c) Cyclic order of the ring neighbours around each hub -/

/-- **Hub 9's ring neighbours form the consecutive arc `0→1→2→3→4`** (no gap). -/
theorem hub9_ring_arc_consecutive :
    (((nbrs 9).filter isRing).zip (((nbrs 9).filter isRing).tail)).all
      (fun c : V × V => cycSucc c.1 == c.2) = true := by decide

/-- **Hub 10's ring neighbours form the consecutive arc `4→5→6→7→8→0`** (wrap at `8→0`). -/
theorem hub10_ring_arc_consecutive :
    (((nbrs 10).filter isRing).zip (((nbrs 10).filter isRing).tail)).all
      (fun c : V × V => cycSucc c.1 == c.2) = true := by decide

/-- The two arcs' union is the whole ring. -/
theorem hub_arcs_cover :
    (((nbrs 9).filter isRing) ++ ((nbrs 10).filter isRing)).eraseDups =
      [0, 1, 2, 3, 4, 5, 6, 7, 8] := by decide

/-- The two arcs meet exactly at the two switch ring vertices `0` and `4`. -/
theorem hub_arcs_meet :
    ((nbrs 9).filter isRing).filter (fun v => ((nbrs 10).filter isRing).contains v) = [0, 4] := by
  decide

/-- The two arcs' **interior** parts (endpoints `0`,`4` removed) partition the remaining seven
ring sites. -/
theorem hub_arcs_interior_partition :
    (((((nbrs 9).filter isRing).filter (fun v => v != 0 && v != (4 : V))) ++
      (((nbrs 10).filter isRing).filter (fun v => v != 0 && v != (4 : V)))).eraseDups) =
        [1, 2, 3, 5, 6, 7, 8] := by decide

/-- The arcs are strictly increasing along the cyclic order: no ring neighbour of hub 9 lies
between `4` and `0` going the other way, and none of hub 10's lies between `0` and `4`. -/
theorem hub_arcs_are_the_two_cyclic_arcs :
    (nbrs 9).filter isRing = [0, 1, 2, 3, 4] ∧ (nbrs 10).filter isRing = [4, 5, 6, 7, 8, 0] ∧
    ((nbrs 9).filter isRing).length + ((nbrs 10).filter isRing).length = 11 := by decide

/-! ## 6. (d) Two-sided fan structure -/

/-- Fan A face list (hub-9 side). -/
def fanAFaces : List (Fin 11) := [0, 1, 2, 3]

/-- Fan B face list (hub-10 side). -/
def fanBFaces : List (Fin 11) := [4, 5, 6, 7, 8]

/-- Fan A rows. -/
def fanARows : List (V × V) := rowsOf fanAFaces

/-- Fan B rows. -/
def fanBRows : List (V × V) := rowsOf fanBFaces

/-- Central rows (the two hub-hub faces). -/
def centralRows : List (V × V) := rowsOf [9, 10]

/-- The nine canonical fan faces split into the two fans. -/
theorem fan_face_partition : fanAFaces ++ fanBFaces = fanFaces := by decide

/-- Hub 9 is incident with exactly fan A plus the two central faces. -/
theorem hub9_faces_decomp : facesWith 9 = fanAFaces ++ [9, 10] := by decide

/-- Hub 10 is incident with exactly fan B plus the two central faces. -/
theorem hub10_faces_decomp : facesWith 10 = fanBFaces ++ [9, 10] := by decide

/-- **The two fans' row sets are disjoint.** -/
theorem fan_rows_disjoint :
    (fanARows.eraseDups.filter (fun p => (fanBRows.eraseDups).contains p)) = [] := by decide

theorem fanA_row_card : fanARows.eraseDups.length = 9 := by decide
theorem fanB_row_card : fanBRows.eraseDups.length = 11 := by decide

/-- Fan A's ring rows are the path `0-1-2-3-4` (4 consecutive edges). -/
theorem fanA_ring_rows :
    fanARows.eraseDups.filter (fun p => isRing p.1 && isRing p.2) =
      [ep 0 1, ep 1 2, ep 2 3, ep 3 4] := by decide

/-- Fan B's ring rows are the path `4-5-6-7-8-0` (5 consecutive edges). -/
theorem fanB_ring_rows :
    fanBRows.eraseDups.filter (fun p => isRing p.1 && isRing p.2) =
      [ep 4 5, ep 5 6, ep 6 7, ep 7 8, ep 0 8] := by decide

/-- Fan A's spoke rows are the five hub-9 spokes; fan B's are the six hub-10 spokes. -/
theorem fan_spokes :
    fanARows.eraseDups.filter (fun p => isRing p.1 != isRing p.2) =
      [ep 1 9, ep 0 9, ep 2 9, ep 3 9, ep 4 9] ∧
    fanBRows.eraseDups.filter (fun p => isRing p.1 != isRing p.2) =
      [ep 5 10, ep 4 10, ep 6 10, ep 7 10, ep 8 10, ep 0 10] := by decide

/-- The two fans' ring rows together are exactly the nine ring rows of the cycle. -/
theorem fan_ring_rows_union :
    (fanARows.eraseDups.filter (fun p => isRing p.1 && isRing p.2)) ++
      (fanBRows.eraseDups.filter (fun p => isRing p.1 && isRing p.2)) = ringRows := by decide

/-- **Where the two fans meet (I).**  The vertex sets of the two fan row families intersect in
exactly the two ring switch vertices `0` and `4`. -/
theorem fan_vertex_meet :
    (vertsOf fanARows).filter (fun v => (vertsOf fanBRows).contains v) = [0, 4] := by decide

/-- **Where the two fans meet (II).**  The fans together cover every vertex (first-occurrence
order); the only face rows they do *not* produce are the central pairs. -/
theorem fan_vertex_cover :
    ((vertsOf fanARows) ++ (vertsOf fanBRows)).eraseDups = [0, 1, 9, 2, 3, 4, 5, 10, 6, 7, 8] := by
  decide

/-- The central rows (first-occurrence order): the only pair with both ends hubs is `{9,10}`. -/
theorem central_rows_exact :
    centralRows.eraseDups = [ep 0 9, ep 9 10, ep 0 10, ep 4 9, ep 4 10] := by decide

/-- **The rows shared by the two hubs' full incidence sets are exactly the five central pairs.** -/
theorem hub_incidence_meet :
    ((rowsOf (facesWith 9)).eraseDups).filter
      (fun p => ((rowsOf (facesWith 10)).eraseDups).contains p) =
        [ep 0 9, ep 4 9, ep 9 10, ep 0 10, ep 4 10] := by decide

/-- The unique hub-hub row among them is `{9,10}`. -/
theorem hub_incidence_meet_unique_hub_pair :
    (((rowsOf (facesWith 9)).eraseDups).filter
      (fun p => ((rowsOf (facesWith 10)).eraseDups).contains p)).filter
        (fun p => !(isRing p.1) && !(isRing p.2)) = [ep 9 10] := by decide

/-- **The complete 33-row pair decomposition.**  The three families are the two fans and the
central pair block; their union is all 21 face pairs, their sizes sum to 25, and the only pair
outside the two fans is `{9,10}`. -/
theorem face_rows_decomposition :
    (fanARows.eraseDups ++ fanBRows.eraseDups ++ centralRows.eraseDups).eraseDups.length = 21 ∧
    fanARows.eraseDups.length + fanBRows.eraseDups.length + centralRows.eraseDups.length = 25 ∧
    faceRows.eraseDups.filter
      (fun p => ¬ ((fanARows.eraseDups ++ fanBRows.eraseDups).contains p)) = [ep 9 10] := by
  decide

/-- **(d) main, discrete form of "the two fans meet exactly at the hubs".**  The two fan row
families are disjoint; their only common vertices are the two ring switches `0`,`4`; each hub is
incident with exactly its own fan plus the two central faces; and the two central faces are
exactly the faces containing both hubs.  Hence the two fans communicate only through the
hub-hub central faces. -/
theorem two_fan_structure :
    (fanARows.eraseDups.filter (fun p => (fanBRows.eraseDups).contains p) = []) ∧
    ((vertsOf fanARows).filter (fun v => (vertsOf fanBRows).contains v) = [0, 4]) ∧
    (facesWith 9 = fanAFaces ++ [9, 10]) ∧ (facesWith 10 = fanBFaces ++ [9, 10]) ∧
    (allV.filter (fun f => (faceVerts f).contains (9 : V) && (faceVerts f).contains (10 : V)) =
      [9, 10]) := by decide

/-- **No face row crosses between the two fans' interiors.**  Vertex `1,2,3` lie in fan A only
and `5,6,7,8` in fan B only; no canonical face row joins one to the other.  Together with
`fan_vertex_meet` this says the two fans meet only at the hubs and the two shared ring switches
`0`,`4` — i.e. the "two-sided fan meeting exactly at hub 9 / hub 10" of the assembly. -/
theorem fan_rows_no_crossing :
    (fanARows.eraseDups ++ fanBRows.eraseDups).filter
      (fun p => (((p.1 == 1 || p.1 == 2 || p.1 == 3) && (p.2 == 5 || p.2 == 6 || p.2 == 7 || p.2 == 8)) ||
        ((p.2 == 1 || p.2 == 2 || p.2 == 3) && (p.1 == 5 || p.1 == 6 || p.1 == 7 || p.1 == 8)))) =
      [] := by decide

/-! ## 7. Tie to the frozen paid source face table -/

/-- Source faces whose hub slot is `9`. -/
def srcHub9Faces : List (Fin 9) := (List.finRange 9).filter (fun f => (sourceFaces f 2).val = 9)

/-- Source faces whose hub slot is `10`. -/
def srcHub10Faces : List (Fin 9) := (List.finRange 9).filter (fun f => (sourceFaces f 2).val = 10)

theorem srcHub9Faces_exact : srcHub9Faces = [3, 4, 5, 6] := by decide
theorem srcHub10Faces_exact : srcHub10Faces = [0, 1, 2, 7, 8] := by decide

/-- **Source hub-9 faces map to exactly canonical fan A.** -/
theorem source_hub9_map : srcHub9Faces.map faceMap = fanAFaces := by decide

/-- **Source hub-10 faces map into fan B ∪ the central faces**; the two canonical fan-B faces the
source table omits are exactly `5` and `7`. -/
theorem source_hub10_map :
    (srcHub10Faces.map faceMap).eraseDups = [9, 10, 8, 4, 6] ∧
    (fanBFaces.filter (fun f => ((srcHub10Faces.map faceMap).contains f) == false)) = [5, 7] := by
  decide

/-- The two omitted canonical fan faces are the two slack faces `[5,6,10]` and `[7,8,10]`
(consistent with the independent C4 finding that the six non-source face rows are exactly
`face 5`, `face 7`). -/
theorem omitted_faces_are_slack :
    face 5 = ![5, 6, 10] ∧ face 7 = ![7, 8, 10] ∧
    (srcHub10Faces.map faceMap).contains (5 : Fin 11) = false ∧
    (srcHub10Faces.map faceMap).contains (7 : Fin 11) = false := by decide

/-- Every source face row is a canonical row of its mapped face: the source table is a genuine
sub-table of the canonical two-fan table. -/
theorem source_rows_are_canonical_rows :
    (List.finRange 9).all (fun f : Fin 9 => all3.all (fun t : Fin 3 =>
      (faceVerts (faceMap f)).contains (rawToCanon (sourceFaces f t)))) = true := by
  decide

end N11Formalization.DSHTopologyHubFan

/-! ## 8. Verbatim type printouts and axiom audit -/

#print axioms N11Formalization.DSHTopologyHubFan.face_table
#print axioms N11Formalization.DSHTopologyHubFan.sourceFaces_table
#print axioms N11Formalization.DSHTopologyHubFan.faceMap_table
#print axioms N11Formalization.DSHTopologyHubFan.faceRows_length
#print axioms N11Formalization.DSHTopologyHubFan.faceRows_distinct
#print axioms N11Formalization.DSHTopologyHubFan.row_split
#print axioms N11Formalization.DSHTopologyHubFan.ring_cycle_exact
#print axioms N11Formalization.DSHTopologyHubFan.ring_cycle_consecutive
#print axioms N11Formalization.DSHTopologyHubFan.hub_rows_multiplicity
#print axioms N11Formalization.DSHTopologyHubFan.hub_pairs_exact
#print axioms N11Formalization.DSHTopologyHubFan.hub_iff
#print axioms N11Formalization.DSHTopologyHubFan.hub_count_two
#print axioms N11Formalization.DSHTopologyHubFan.hub_set
#print axioms N11Formalization.DSHTopologyHubFan.hub_degrees
#print axioms N11Formalization.DSHTopologyHubFan.ring_degrees
#print axioms N11Formalization.DSHTopologyHubFan.hub_threshold_control
#print axioms N11Formalization.DSHTopologyHubFan.hub_common_neighbors
#print axioms N11Formalization.DSHTopologyHubFan.neighbors_hub9
#print axioms N11Formalization.DSHTopologyHubFan.neighbors_hub10
#print axioms N11Formalization.DSHTopologyHubFan.hub9_faces
#print axioms N11Formalization.DSHTopologyHubFan.hub10_faces
#print axioms N11Formalization.DSHTopologyHubFan.hub9_ring_spokes
#print axioms N11Formalization.DSHTopologyHubFan.hub10_ring_spokes
#print axioms N11Formalization.DSHTopologyHubFan.hub9_spoke_pairs
#print axioms N11Formalization.DSHTopologyHubFan.hub10_spoke_pairs
#print axioms N11Formalization.DSHTopologyHubFan.hub_spokes_cover_ring
#print axioms N11Formalization.DSHTopologyHubFan.boundary_rows_are_ring
#print axioms N11Formalization.DSHTopologyHubFan.hub9_ring_arc_consecutive
#print axioms N11Formalization.DSHTopologyHubFan.hub10_ring_arc_consecutive
#print axioms N11Formalization.DSHTopologyHubFan.hub_arcs_cover
#print axioms N11Formalization.DSHTopologyHubFan.hub_arcs_meet
#print axioms N11Formalization.DSHTopologyHubFan.fan_face_partition
#print axioms N11Formalization.DSHTopologyHubFan.hub9_faces_decomp
#print axioms N11Formalization.DSHTopologyHubFan.hub10_faces_decomp
#print axioms N11Formalization.DSHTopologyHubFan.fan_rows_disjoint
#print axioms N11Formalization.DSHTopologyHubFan.fanA_ring_rows
#print axioms N11Formalization.DSHTopologyHubFan.fanB_ring_rows
#print axioms N11Formalization.DSHTopologyHubFan.fan_spokes
#print axioms N11Formalization.DSHTopologyHubFan.fan_ring_rows_union
#print axioms N11Formalization.DSHTopologyHubFan.fan_vertex_meet
#print axioms N11Formalization.DSHTopologyHubFan.central_rows_exact
#print axioms N11Formalization.DSHTopologyHubFan.hub_incidence_meet
#print axioms N11Formalization.DSHTopologyHubFan.face_rows_decomposition
#print axioms N11Formalization.DSHTopologyHubFan.two_fan_structure
#print axioms N11Formalization.DSHTopologyHubFan.fan_rows_no_crossing
#print axioms N11Formalization.DSHTopologyHubFan.source_hub9_map
#print axioms N11Formalization.DSHTopologyHubFan.source_hub10_map
#print axioms N11Formalization.DSHTopologyHubFan.omitted_faces_are_slack
#print axioms N11Formalization.DSHTopologyHubFan.incidence_sum
#print axioms N11Formalization.DSHTopologyHubFan.degree_sum
#print axioms N11Formalization.DSHTopologyHubFan.hub_iff_incidence

#check @N11Formalization.DSHTopologyHubFan.hub_iff
#check @N11Formalization.DSHTopologyHubFan.hub_count_two
#check @N11Formalization.DSHTopologyHubFan.hub_set
#check @N11Formalization.DSHTopologyHubFan.hub_degrees
#check @N11Formalization.DSHTopologyHubFan.ring_degrees
#check @N11Formalization.DSHTopologyHubFan.neighbors_hub9
#check @N11Formalization.DSHTopologyHubFan.neighbors_hub10
#check @N11Formalization.DSHTopologyHubFan.hub9_faces
#check @N11Formalization.DSHTopologyHubFan.hub10_faces
#check @N11Formalization.DSHTopologyHubFan.hub9_spoke_pairs
#check @N11Formalization.DSHTopologyHubFan.hub10_spoke_pairs
#check @N11Formalization.DSHTopologyHubFan.hub9_ring_spokes
#check @N11Formalization.DSHTopologyHubFan.hub10_ring_spokes
#check @N11Formalization.DSHTopologyHubFan.hub9_ring_arc_consecutive
#check @N11Formalization.DSHTopologyHubFan.hub10_ring_arc_consecutive
#check @N11Formalization.DSHTopologyHubFan.hub_arcs_meet
#check @N11Formalization.DSHTopologyHubFan.ring_cycle_exact
#check @N11Formalization.DSHTopologyHubFan.fan_face_partition
#check @N11Formalization.DSHTopologyHubFan.fan_rows_disjoint
#check @N11Formalization.DSHTopologyHubFan.fanA_ring_rows
#check @N11Formalization.DSHTopologyHubFan.fanB_ring_rows
#check @N11Formalization.DSHTopologyHubFan.fan_vertex_meet
#check @N11Formalization.DSHTopologyHubFan.central_rows_exact
#check @N11Formalization.DSHTopologyHubFan.hub_incidence_meet
#check @N11Formalization.DSHTopologyHubFan.two_fan_structure
#check @N11Formalization.DSHTopologyHubFan.fan_rows_no_crossing
#check @N11Formalization.DSHTopologyHubFan.hub_iff_incidence
#check @N11Formalization.DSHTopologyHubFan.source_hub9_map
#check @N11Formalization.DSHTopologyHubFan.source_hub10_map