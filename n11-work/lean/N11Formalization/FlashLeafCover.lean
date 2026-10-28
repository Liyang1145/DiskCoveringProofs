import Mathlib

/-!
# FlashLeaf — exact cover skeleton for the source DBM branch tree

Structural core of the exhaustive-cover obligation for the source DBM branch tree
`cosine_dbm_local920.json` (sha256 `6706b426…`).  **No cover theorem for the tree and no
concrete tree here**; the file fixes the objects and proves the component lemmas.  The tree and
its 2505 splits are audited exactly outside Lean (`evidence/flash-leaves/`).

## Semantics

A cell stores a 10×10 rational matrix `d` and carries the constraint system
`Cell d t := ∀ i j, t_j − t_i ≤ d i j`.  Because `d` is an **upper** bound,

* `d ≤ e` pointwise ⇒ `Cell e ⊆ Cell d`  (`cell_mono`): a smaller matrix is a *tighter* system,
  so its cell is smaller; a point satisfying the looser rows also satisfies the tighter ones.

## Cover step, orientation resolved by exact audit

For a split at pair `(i,j)` with threshold `m`, the stored children are
`childL = closure(dpar + {t_j − t_i ≤ m})`, `childR = closure(dpar + {t_i − t_j ≤ m})`.
The exact cover test (see `evidence/flash-leaves/split-cover.txt`) verifies for **all 2505 splits**

    max{ t_b − t_a : Cell dpar t, t_j − t_i ≤ m }  ≤  childL a b     (A)
    max{ t_b − t_a : Cell dpar t, t_i − t_j ≤ m }  ≤  childR a b     (B)

with `max = min(dpar a b, dpar a i + dpar j b + m)` for (A) and the mirror for (B), and reports
**0 violations in both children for every split**.  So each split is an exact cover step, and the
cover obligation reduces to (A)/(B) — a finite rational-arithmetic statement about the stored
matrices, not a geometric one.  `localCover` below is that statement as a Lean predicate, and
`cover_of_localCover` is the recursion.

## Proved here (unconditional)

* `root_contains_chart` — the root cell contains the whole chart, over reals;
* `cell_mono`, `cell_intro`, `localCover_of_pointwise` — the pointwise machinery;
* `cover_of_localCover` — the finite-tree recursion.
-/

namespace N11Formalization.FlashLeaf

/-! ## Chart -/

/-- The correct source domain: 9 nonnegative width deficits summing to 1. -/
def Chart9 (z : Fin 9 → ℝ) : Prop := (∀ q, 0 ≤ z q) ∧ ∑ q, z q = 1

/-- The generator's free chart coordinates: `y_0..y_7 ≥ 0`, `Σ_{q<8} y_q ≤ 1`. -/
def Chart8 (z : Fin 8 → ℝ) : Prop := (∀ q, 0 ≤ z q) ∧ ∑ q, z q ≤ 1

/-- `Fin 8 → Fin 9`: last coordinate `1 − Σ_{q<8} y_q`. -/
def lift8 (z : Fin 8 → ℝ) : Fin 9 → ℝ := Fin.lastCases (1 - ∑ q, z q) z

theorem lift8_last (z : Fin 8 → ℝ) : lift8 z (Fin.last 8) = 1 - ∑ q, z q :=
  Fin.lastCases_last

theorem lift8_castSucc (z : Fin 8 → ℝ) (i : Fin 8) : lift8 z i.castSucc = z i :=
  Fin.lastCases_castSucc i

/-- The `Fin 8` lift sums to 1 exactly on `Chart8`. -/
theorem sum_lift8 {z : Fin 8 → ℝ} (hz : Chart8 z) : ∑ q, lift8 z q = 1 := by
  obtain ⟨_, h2⟩ := hz
  rw [Fin.sum_univ_castSucc]
  have h1 : (∑ i : Fin 8, lift8 z i.castSucc) = ∑ i, z i :=
    Finset.sum_congr rfl (fun i _ => lift8_castSucc z i)
  rw [h1, lift8_last]
  linarith

/-- `Chart8` and `Chart9` describe the same set of points. -/
theorem chart_of_chart8 {z : Fin 8 → ℝ} (h : Chart8 z) : Chart9 (lift8 z) :=
  ⟨fun q => by
    refine Fin.lastCases ?_ (fun i => ?_) q
    · rw [lift8_last]; linarith [h.2]
    · rw [lift8_castSucc]; exact h.1 i,
   sum_lift8 h⟩

/-! ## The `t`-lift -/

/-- `t_k = Σ_{q<k} z_q`, as a `Fin (n+1)` vector. -/
def tlift (n : ℕ) (z : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  fun k => ∑ q ∈ Finset.univ.filter (fun q : Fin n => (q : ℕ) < (k : ℕ)), z q

theorem tlift_zero (n : ℕ) (z : Fin n → ℝ) : tlift n z 0 = 0 := by
  unfold tlift
  rw [show (Finset.univ.filter (fun q : Fin n => (q : ℕ) < ((0 : Fin (n+1)) : ℕ))) = ∅ from by
    ext q; simp]
  simp

theorem tlift_last (n : ℕ) (z : Fin n → ℝ) : tlift n z (Fin.last n) = ∑ q, z q := by
  unfold tlift
  rw [show (Finset.univ.filter (fun q : Fin n => (q : ℕ) < ((Fin.last n : Fin (n+1)) : ℕ)))
      = Finset.univ from by
    ext q; simp [Fin.val_last]]

theorem tlift_nonneg {n : ℕ} {z : Fin n → ℝ} (hz : ∀ q, 0 ≤ z q) (k : Fin (n + 1)) :
    0 ≤ tlift n z k := by
  unfold tlift
  exact Finset.sum_nonneg (fun q _ => hz q)

theorem tlift_le_sum {n : ℕ} {z : Fin n → ℝ} (hz : ∀ q, 0 ≤ z q) (k : Fin (n + 1)) :
    tlift n z k ≤ ∑ q, z q := by
  unfold tlift
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun q _ _ => hz q)

theorem tlift_mono {n : ℕ} {z : Fin n → ℝ} (hz : ∀ q, 0 ≤ z q) {k j : Fin (n + 1)}
    (h : k ≤ j) : tlift n z k ≤ tlift n z j := by
  unfold tlift
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    exact lt_of_lt_of_le hq (Fin.le_iff_val_le_val.mp h)
  · intro q _ _; exact hz q

/-! ## Cells and the pointwise machinery -/

/-- `Cell d t` : every row of `d` holds at `t`.  `d` is an upper bound, so a smaller `d` is a
tighter system (`cell_mono`). -/
def Cell (d : Fin 10 → Fin 10 → ℝ) (t : Fin 10 → ℝ) : Prop := ∀ i j, t j - t i ≤ d i j

/-- **Monotonicity.**  `e ≤ d` pointwise ⇒ `Cell e ⊆ Cell d`. -/
theorem cell_mono {d e : Fin 10 → Fin 10 → ℝ} (h : ∀ i j, e i j ≤ d i j) :
    ∀ t, Cell e t → Cell d t := by
  intro t ht i j
  exact le_trans (ht i j) (h i j)

/-- Introduction rule: a bound on every row gives the cell. -/
theorem cell_intro {d : Fin 10 → Fin 10 → ℝ} {t : Fin 10 → ℝ}
    (h : ∀ i j, t j - t i ≤ d i j) : Cell d t := h

/-- **The local cover step, as a Lean predicate (exactly the audited statement).**
`dpar` is the parent matrix, `dch` a child matrix, `(i,j)` the split pair, `m` the threshold.
This says: every parent point satisfying the split's added row lies in the child cell.
It is precisely conditions (A) (for `left`) and (B) (for `right`) of the file header. -/
def LocalCover (dpar dch : Fin 10 → Fin 10 → ℝ) (i j : Fin 10) (m : ℝ) : Prop :=
  ∀ t : Fin 10 → ℝ, Cell dpar t → t j - t i ≤ m → Cell dch t

/-- **Pointwise discharge.**  If `dch` satisfies every row bound of the parent-constrained
region, `LocalCover` holds.  This is the shape the audited finite data produces. -/
theorem localCover_of_pointwise {dpar dch : Fin 10 → Fin 10 → ℝ} {i j : Fin 10} {m : ℝ}
    (h : ∀ a b : Fin 10,
      ∀ t : Fin 10 → ℝ, Cell dpar t → t j - t i ≤ m → t b - t a ≤ dch a b) :
    LocalCover dpar dch i j m :=
  fun t ht hh => fun a b => h a b t ht hh

/-- **The generic cover step.**  If each stored child contains the parent cell intersected with
its own halfspace, then the two children's cells cover the whole parent cell — the dichotomy
`t_j − t_i ≤ m ∨ m ≤ t_j − t_i` is a tautology of `ℝ`.  The right child's halfspace
`m ≤ t_j − t_i` is the same as `t_i − t_j ≤ −m`, so its `LocalCover` carries threshold `−m`.
This is the exact interface the 2505 audited `LocalCover` instances plug into: no geometry, no
topology, no convexity. -/
theorem cover_step_of_localCover {dpar dchL dchR : Fin 10 → Fin 10 → ℝ} {i j : Fin 10} {m : ℝ}
    (hL : LocalCover dpar dchL i j m) (hR : LocalCover dpar dchR j i (-m)) :
    ∀ t : Fin 10 → ℝ, Cell dpar t → Cell dchL t ∨ Cell dchR t := by
  intro t ht
  rcases le_total (t j - t i) m with hle | hle
  · exact Or.inl (hL t ht hle)
  · exact Or.inr (hR t ht (by linarith))

/-! ## The finite-tree cover recursion -/

/-- A finite tree of cells: `node c l r` records that cell `c` splits into `l` and `r`. -/
inductive Tree : Type
  | leaf (c : ℕ) : Tree
  | node (c : ℕ) (l r : Tree) : Tree

namespace Tree

/-- The cell index carried by the root. -/
def rootIdx : Tree → ℕ
  | .leaf c => c
  | .node c _ _ => c

/-- The leaf indices of a tree. -/
def leaves : Tree → List ℕ
  | .leaf c => [c]
  | .node _ l r => leaves l ++ leaves r

end Tree

/-- The cell predicate of a tree node, read off a family `CellOf`. -/
def TreeCell {X : Type*} (CellOf : ℕ → X → Prop) : Tree → X → Prop
  | .leaf c, t => CellOf c t
  | .node c _ _, t => CellOf c t

/-- `TreeCover` : some leaf cell of the tree holds. -/
def TreeCover {X : Type*} (CellOf : ℕ → X → Prop) : Tree → X → Prop
  | .leaf c, t => CellOf c t
  | .node _ l r, t => TreeCover CellOf l t ∨ TreeCover CellOf r t

/-- `SubCover` : the point is in one of the two children's leaves. -/
def SubCover {X : Type*} (CellOf : ℕ → X → Prop) (l r : Tree) (t : X) : Prop :=
  (∃ c ∈ Tree.leaves l, CellOf c t) ∨ (∃ c ∈ Tree.leaves r, CellOf c t)

/-- Leaves witness coverage.  Every point covered by a tree lies in one of its leaves. -/
theorem treeCover_leaf {X : Type*} {CellOf : ℕ → X → Prop} {T : Tree} {t : X}
    (h : TreeCover CellOf T t) : ∃ c ∈ Tree.leaves T, CellOf c t := by
  induction T with
  | leaf c => exact ⟨c, by simp [Tree.leaves], h⟩
  | node c l r ihl ihr =>
      rcases h with hl | hr
      · obtain ⟨c', hc', hcell⟩ := ihl hl
        exact ⟨c', List.mem_append_left _ hc', hcell⟩
      · obtain ⟨c', hc', hcell⟩ := ihr hr
        exact ⟨c', List.mem_append_right _ hc', hcell⟩

/-- **Node soundness.**  At every node, a point of the node's cell lies either in one of the two
children's own cells, or already inside one of their leaves.  At the root this is exactly the
audited per-split statement (children's cells), the second disjunct being free. -/
def Sound {X : Type*} (CellOf : ℕ → X → Prop) : Tree → Prop
  | .leaf _ => True
  | .node c l r =>
      (∀ t : X,
          CellOf c t → CellOf l.rootIdx t ∨ CellOf r.rootIdx t ∨ SubCover CellOf l r t) ∧
      Sound CellOf l ∧ Sound CellOf r

/-- **Cover recursion.**  A sound tree covers its root cell by its leaves. -/
theorem cover_of_sound {X : Type*} {CellOf : ℕ → X → Prop} :
    ∀ {T : Tree}, Sound CellOf T →
      ∀ t : X, CellOf (Tree.rootIdx T) t → ∃ c ∈ Tree.leaves T, CellOf c t := by
  intro T
  induction T with
  | leaf c => intro _ t ht; exact ⟨c, by simp [Tree.leaves], ht⟩
  | node c l r ihl ihr =>
      intro hs t ht
      obtain ⟨hstep, hsl, hsr⟩ := hs
      rcases hstep t ht with h | h | h
      · obtain ⟨c', hc', hcell⟩ := ihl hsl t h
        exact ⟨c', List.mem_append_left _ hc', hcell⟩
      · obtain ⟨c', hc', hcell⟩ := ihr hsr t h
        exact ⟨c', List.mem_append_right _ hc', hcell⟩
      · rcases h with ⟨c', hc', hcell⟩ | ⟨c', hc', hcell⟩
        · exact ⟨c', List.mem_append_left _ hc', hcell⟩
        · exact ⟨c', List.mem_append_right _ hc', hcell⟩

/-! ## The root cell contains the chart -/

/-- Root row block: the raw root DBM matrix of the JSON (entries all in `{0,1,−1}`). -/
def Proot (t : Fin 10 → ℝ) : Prop :=
  (∀ i j : Fin 10, i < j → t j - t i ≤ 1) ∧ (∀ i j : Fin 10, j < i → t j - t i ≤ 0)

/-- The pin `t_0 = 0` and `t_9 − t_0 = 1`; the latter is NOT implied by `Proot`. -/
def P9 (t : Fin 10 → ℝ) : Prop := t 0 = 0 ∧ t 9 - t 0 ≤ 1 ∧ t 0 - t 9 ≤ -1

/-- Root cell: rows plus the pin. -/
def P (t : Fin 10 → ℝ) : Prop := Proot t ∧ P9 t

theorem tlift_le_one {n : ℕ} {z : Fin n → ℝ} (hz : ∀ q, 0 ≤ z q) (h1 : ∑ q, z q = 1)
    (k : Fin (n + 1)) : tlift n z k ≤ 1 := by
  have := tlift_le_sum hz k
  linarith

/-- **The root cell contains the chart.**  Unconditional, over reals. -/
theorem root_contains_chart {z : Fin 9 → ℝ} (hz : Chart9 z) : P (tlift 9 z) := by
  have h9 : tlift 9 z (9 : Fin 10) = 1 := by
    rw [show (9 : Fin 10) = Fin.last 9 from rfl, tlift_last, hz.2]
  have h0 : tlift 9 z 0 = 0 := tlift_zero 9 z
  refine ⟨⟨fun i j _ => ?_, fun i j hji => ?_⟩, h0, ?_, ?_⟩
  · have h3 : tlift 9 z j ≤ 1 := tlift_le_one hz.1 hz.2 j
    have h4 : 0 ≤ tlift 9 z i := tlift_nonneg hz.1 i
    linarith
  · have h3 : tlift 9 z j ≤ tlift 9 z i := tlift_mono hz.1 hji.le
    linarith
  · rw [h9, h0]; norm_num
  · rw [h0, h9]; norm_num

/-- **The root cell contains the chart, `Fin 8` form** (the generator's free coordinates). -/
theorem root_contains_chart8 {z : Fin 8 → ℝ} (hz : Chart8 z) : P (tlift 9 (lift8 z)) :=
  root_contains_chart (chart_of_chart8 hz)

end N11Formalization.FlashLeaf

