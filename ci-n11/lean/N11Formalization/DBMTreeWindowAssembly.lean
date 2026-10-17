import N11Formalization.DBMTreeKernel
import N11Formalization.DBMTreeWindow00
import N11Formalization.DBMTreeWindow01
import N11Formalization.DBMTreeWindow02
import N11Formalization.DBMTreeWindow03
import N11Formalization.DBMTreeWindow04
import N11Formalization.DBMTreeWindow05
import N11Formalization.DBMTreeWindow06
import N11Formalization.DBMTreeWindow07
import N11Formalization.DBMTreeWindow08
import N11Formalization.DBMTreeWindow09
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000

/-
# DBMTreeWindowAssembler — generic window/grid assembly for the DBM source tree

Object: any `data : Fin N → DBMTreeKernel.Node N`.  The emitted source instance
(`N11Formalization.DBMSourceTree.data`, N = 5011, width 64, B = 79 = 78×64+19) is one instance;
nothing in this file refers to it.

## Proved here (and only this)

* `grid_block` — pure `Nat` cover: with `b = n/M`, `k = n%M` one has `b < B`, `k < min M (N - M*b)`
  and `M*b + k = n`, for any `M > 0`, any `B` with `N ≤ B*M`.  Blocks past `N` have 0 slots, so
  overshooting `B` is legal; the last source block carries exactly 19 slots (no padding, no illegal
  `Fin`).
* `all_valid_of_value_windows` — the assembled interface `∀ n : Fin N, Valid data n` from one window
  certificate per block.
* `terminal_cover_of_value_windows` — that interface is exactly the `hv` argument of
  `DBMTreeKernel.terminal_cover`; the consumer chain is closed here.

## NOT proved here

Any window certificate.  They are the explicit hypothesis `hw`; for the source instance they are the
79 frozen declarations `DBMSourceTree.ValidWindows.window000 … window078`, of which only the
4-window edge calibration and pack 0 have been kernel-checked so far.  No axiom, no sorry, no
native_decide in this file.

## Interface rule (engineering choice; no mathematical claim, no claim of necessity)

The frozen source windows are literal-closed terms

  `windowBBB : ∀ k : Fin (count), Valid data (⟨off + k.val, by omega⟩ : Fin 5011)`

Lean's kernel definitional equality includes proof irrelevance for `Prop` (proofs of one proposition
are definitionally equal), so `Fin` values with the same value and different proof fields are
definitionally interchangeable; the frozen windows are therefore already convertible to any other
indexing of the same slots.  The value-level certificate used here is a *convenience* that keeps
this file independent of the frozen proof terms:

  `ValidAt data n := ∃ h : n < N, Valid data ⟨n, h⟩`

Each bridge is then the literal one-liner `fun k => ⟨_, windowBBB k⟩` (the existential witness is a
metavariable that unification assigns to the emitter's own proof term), and this file's own
definitional-equality work is pure `Nat` reduction (`64*1 + ↑k` vs `64 + ↑k`,
`min 64 (5011 - 64*1)` vs `64`, …).

The `Fin`-typed shape `blockIndex`/`WindowValid` is an equivalent second representation of the same
predicate (mutual transports `validAtWindow_of_value_windows`, `value_windows_of_windowValid`).
Neither representation is a necessary repair and neither is new mathematics; `ValidAt` is not
claimed to be required for consuming the frozen windows.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace N11Formalization.DBMTreeWindowAssembler

open N11Formalization.DBMTreeKernel

/-! ## 1. Value-level validity and the window predicate -/

/-- Value-level validity: the `Fin N` bound proof is existentially quantified, so no statement here
depends on which proof term an emitter wrote. -/
abbrev ValidAt {N : ℕ} (data : Fin N → Node N) (n : ℕ) : Prop := ∃ h : n < N, Valid data ⟨n, h⟩

/-- Number of slots of block `b` in the width-`M` grid: `min M (N - M*b)` (`0` for blocks past `N`). -/
abbrev count (N M b : ℕ) : ℕ := Nat.min M (N - M * b)

/-- Block `b` of the width-`M` grid: every slot is valid. -/
abbrev ValidAtWindow {N : ℕ} (data : Fin N → Node N) (M b : ℕ) : Prop :=
  ∀ k : Fin (count N M b), ValidAt data (M * b + k.val)

/-- Forget the bound proof: `Valid` at a value gives value-level validity. -/
theorem validAt_of_valid {N : ℕ} (data : Fin N → Node N) {n : ℕ} (h : n < N)
    (hv : Valid data ⟨n, h⟩) : ValidAt data n := ⟨h, hv⟩

/-! ## 2. Grid cover (pure `Nat` arithmetic, core lemmas only) -/

/-- Every index lies in exactly one grid slot: `b = n/M`, `k = n%M` satisfy `b < B`,
`k < min M (N - M*b)` and `M*b + k = n`. -/
theorem grid_block {N M B : ℕ} (hM : 0 < M) (hN : N ≤ B * M) (n : Fin N) :
    ∃ (b : Fin B) (k : Fin (count N M b.val)), M * b.val + k.val = n.val := by
  have hn : n.val < B * M := lt_of_lt_of_le n.isLt hN
  have hb : n.val / M < B := by
    have h1 : n.val / M * M ≤ n.val := Nat.div_mul_le_self n.val M
    exact Nat.lt_of_mul_lt_mul_right (a := M) (b := n.val / M) (c := B) (lt_of_le_of_lt h1 hn)
  have hmod : n.val % M < M := Nat.mod_lt n.val hM
  have hdiv : M * (n.val / M) + n.val % M = n.val := Nat.div_add_mod n.val M
  have hsub : n.val % M < N - M * (n.val / M) := by
    have hsum : n.val % M + M * (n.val / M) < N := by
      rw [Nat.add_comm, hdiv]
      exact n.isLt
    exact Nat.lt_sub_of_add_lt (a := n.val % M) (b := M * (n.val / M)) (c := N) hsum
  refine ⟨⟨n.val / M, hb⟩, ⟨n.val % M, ?_⟩, ?_⟩
  · have hcount : count N M (n.val / M) = Nat.min M (N - M * (n.val / M)) := rfl
    rw [hcount]
    exact Nat.lt_min.mpr ⟨hmod, hsub⟩
  · show M * (n.val / M) + n.val % M = n.val
    exact hdiv

/-! ## 3. Assembly -/

/-- **Main assembler.**  One block certificate per grid block assembles into the full pointwise
interface `∀ n, Valid data n`. -/
theorem all_valid_of_value_windows {N : ℕ} (data : Fin N → Node N) (M B : ℕ)
    (hM : 0 < M) (hN : N ≤ B * M) (hw : ∀ b : Fin B, ValidAtWindow data M b.val) :
    ∀ n : Fin N, Valid data n := by
  intro n
  obtain ⟨b, k, hk⟩ := grid_block (N := N) (M := M) (B := B) hM hN n
  obtain ⟨hn, hval⟩ := hw b k
  have he : (⟨M * b.val + k.val, hn⟩ : Fin N) = n := Fin.ext hk
  rw [← he]
  exact hval

/-- Escape hatch for non-grid covers (arbitrary index type surjecting onto `Fin N`). -/
theorem all_valid_of_surjective {N : ℕ} (data : Fin N → Node N) {ι : Type*} (f : ι → Fin N)
    (hsurj : ∀ n : Fin N, ∃ i : ι, f i = n) (h : ∀ i : ι, Valid data (f i)) :
    ∀ n : Fin N, Valid data n := by
  intro n
  obtain ⟨i, hi⟩ := hsurj n
  rw [← hi]
  exact h i

/-- **Consumer bridge.**  `DBMTreeKernel.terminal_cover` with its `hv` argument discharged by the
block certificates. -/
theorem terminal_cover_of_value_windows {N : ℕ} (data : Fin N → Node N) (scale : ℤ) (hs : 0 < scale)
    (M B : ℕ) (hM : 0 < M) (hN : N ≤ B * M)
    (hw : ∀ b : Fin B, ValidAtWindow data M b.val)
    (t : Fin 10 → ℝ) (n : Fin N) (ht : FlashLeafSplit.Cell (matrix data scale n) t) :
    ∃ l : Fin N, (data l).terminal = true ∧ FlashLeafSplit.Cell (matrix data scale l) t :=
  terminal_cover data scale hs (all_valid_of_value_windows data M B hM hN hw) t n ht

/-! ## 4. Second representation: `Fin`-typed index (`blockIndex` / `WindowValid`) -/

/-- Slot `k` of block `b` as a `Fin N`, with the bound from the slot count. -/
abbrev blockIndex {N M b : ℕ} (k : Fin (count N M b)) : Fin N :=
  ⟨M * b + k.val, by
    have hk : k.val < N - M * b := lt_of_lt_of_le k.isLt (Nat.min_le_right M (N - M * b))
    rw [Nat.add_comm (M * b) k.val]
    exact Nat.add_lt_of_lt_sub hk⟩

/-- Block `b` of the width-`M` grid, `Fin`-indexed form. -/
abbrev WindowValid {N : ℕ} (data : Fin N → Node N) (M b : ℕ) : Prop :=
  ∀ k : Fin (count N M b), Valid data (blockIndex (N := N) (M := M) (b := b) k)

/-- Value-level windows give `Fin`-indexed windows (transport by `Fin.ext rfl`: values only). -/
theorem validAtWindow_of_value_windows {N : ℕ} (data : Fin N → Node N) (M b : ℕ)
    (h : ValidAtWindow data M b) : WindowValid data M b := by
  intro k
  obtain ⟨hn, hv⟩ := h k
  have he : (⟨M * b + k.val, hn⟩ : Fin N) = blockIndex (N := N) (M := M) (b := b) k :=
    Fin.ext rfl
  rw [← he]
  exact hv

/-- `Fin`-indexed windows give value-level windows (witness assigned by unification). -/
theorem value_windows_of_windowValid {N : ℕ} (data : Fin N → Node N) (M b : ℕ)
    (h : WindowValid data M b) : ValidAtWindow data M b := fun k => ⟨_, h k⟩

/-- Assembly in the `Fin`-indexed representation. -/
theorem all_valid_of_window_grid {N : ℕ} (data : Fin N → Node N) (M B : ℕ)
    (hM : 0 < M) (hN : N ≤ B * M) (hblk : ∀ b : Fin B, WindowValid data M b.val) :
    ∀ n : Fin N, Valid data n :=
  all_valid_of_value_windows data M B hM hN
    (fun b => value_windows_of_windowValid data M b.val (hblk b))

end N11Formalization.DBMTreeWindowAssembler

set_option pp.universes true in
#check @N11Formalization.DBMTreeWindowAssembler.ValidAt
#check @N11Formalization.DBMTreeWindowAssembler.count
#check @N11Formalization.DBMTreeWindowAssembler.ValidAtWindow
#check @N11Formalization.DBMTreeWindowAssembler.validAt_of_valid
#check @N11Formalization.DBMTreeWindowAssembler.grid_block
#check @N11Formalization.DBMTreeWindowAssembler.all_valid_of_value_windows
#check @N11Formalization.DBMTreeWindowAssembler.all_valid_of_surjective
#check @N11Formalization.DBMTreeWindowAssembler.terminal_cover_of_value_windows
#check @N11Formalization.DBMTreeWindowAssembler.blockIndex
#check @N11Formalization.DBMTreeWindowAssembler.WindowValid
#check @N11Formalization.DBMTreeWindowAssembler.validAtWindow_of_value_windows
#check @N11Formalization.DBMTreeWindowAssembler.value_windows_of_windowValid
#check @N11Formalization.DBMTreeWindowAssembler.all_valid_of_window_grid
#print axioms N11Formalization.DBMTreeWindowAssembler.grid_block
#print axioms N11Formalization.DBMTreeWindowAssembler.all_valid_of_value_windows
#print axioms N11Formalization.DBMTreeWindowAssembler.all_valid_of_surjective
#print axioms N11Formalization.DBMTreeWindowAssembler.terminal_cover_of_value_windows
#print axioms N11Formalization.DBMTreeWindowAssembler.validAtWindow_of_value_windows
#print axioms N11Formalization.DBMTreeWindowAssembler.value_windows_of_windowValid
#print axioms N11Formalization.DBMTreeWindowAssembler.all_valid_of_window_grid

namespace N11Formalization.DBMTreeWindowAssembly
open N11Formalization.DBMTreeWindowAssembler
open N11Formalization.DBMSourceTree
open N11Formalization.DBMSourceTree.ValidWindows
open N11Formalization.DBMTreeKernel
/-- ids 0..63; bridge from the frozen literal window `window000`. -/
theorem vw000 : ∀ k : Fin 64, ValidAt data (0 + k.val) :=
  fun k => ⟨_, window000 k⟩

/-- ids 64..127; bridge from the frozen literal window `window001`. -/
theorem vw001 : ∀ k : Fin 64, ValidAt data (64 + k.val) :=
  fun k => ⟨_, window001 k⟩

/-- ids 128..191; bridge from the frozen literal window `window002`. -/
theorem vw002 : ∀ k : Fin 64, ValidAt data (128 + k.val) :=
  fun k => ⟨_, window002 k⟩

/-- ids 192..255; bridge from the frozen literal window `window003`. -/
theorem vw003 : ∀ k : Fin 64, ValidAt data (192 + k.val) :=
  fun k => ⟨_, window003 k⟩

/-- ids 256..319; bridge from the frozen literal window `window004`. -/
theorem vw004 : ∀ k : Fin 64, ValidAt data (256 + k.val) :=
  fun k => ⟨_, window004 k⟩

/-- ids 320..383; bridge from the frozen literal window `window005`. -/
theorem vw005 : ∀ k : Fin 64, ValidAt data (320 + k.val) :=
  fun k => ⟨_, window005 k⟩

/-- ids 384..447; bridge from the frozen literal window `window006`. -/
theorem vw006 : ∀ k : Fin 64, ValidAt data (384 + k.val) :=
  fun k => ⟨_, window006 k⟩

/-- ids 448..511; bridge from the frozen literal window `window007`. -/
theorem vw007 : ∀ k : Fin 64, ValidAt data (448 + k.val) :=
  fun k => ⟨_, window007 k⟩

/-- ids 512..575; bridge from the frozen literal window `window008`. -/
theorem vw008 : ∀ k : Fin 64, ValidAt data (512 + k.val) :=
  fun k => ⟨_, window008 k⟩

/-- ids 576..639; bridge from the frozen literal window `window009`. -/
theorem vw009 : ∀ k : Fin 64, ValidAt data (576 + k.val) :=
  fun k => ⟨_, window009 k⟩

/-- ids 640..703; bridge from the frozen literal window `window010`. -/
theorem vw010 : ∀ k : Fin 64, ValidAt data (640 + k.val) :=
  fun k => ⟨_, window010 k⟩

/-- ids 704..767; bridge from the frozen literal window `window011`. -/
theorem vw011 : ∀ k : Fin 64, ValidAt data (704 + k.val) :=
  fun k => ⟨_, window011 k⟩

/-- ids 768..831; bridge from the frozen literal window `window012`. -/
theorem vw012 : ∀ k : Fin 64, ValidAt data (768 + k.val) :=
  fun k => ⟨_, window012 k⟩

/-- ids 832..895; bridge from the frozen literal window `window013`. -/
theorem vw013 : ∀ k : Fin 64, ValidAt data (832 + k.val) :=
  fun k => ⟨_, window013 k⟩

/-- ids 896..959; bridge from the frozen literal window `window014`. -/
theorem vw014 : ∀ k : Fin 64, ValidAt data (896 + k.val) :=
  fun k => ⟨_, window014 k⟩

/-- ids 960..1023; bridge from the frozen literal window `window015`. -/
theorem vw015 : ∀ k : Fin 64, ValidAt data (960 + k.val) :=
  fun k => ⟨_, window015 k⟩

/-- ids 1024..1087; bridge from the frozen literal window `window016`. -/
theorem vw016 : ∀ k : Fin 64, ValidAt data (1024 + k.val) :=
  fun k => ⟨_, window016 k⟩

/-- ids 1088..1151; bridge from the frozen literal window `window017`. -/
theorem vw017 : ∀ k : Fin 64, ValidAt data (1088 + k.val) :=
  fun k => ⟨_, window017 k⟩

/-- ids 1152..1215; bridge from the frozen literal window `window018`. -/
theorem vw018 : ∀ k : Fin 64, ValidAt data (1152 + k.val) :=
  fun k => ⟨_, window018 k⟩

/-- ids 1216..1279; bridge from the frozen literal window `window019`. -/
theorem vw019 : ∀ k : Fin 64, ValidAt data (1216 + k.val) :=
  fun k => ⟨_, window019 k⟩

/-- ids 1280..1343; bridge from the frozen literal window `window020`. -/
theorem vw020 : ∀ k : Fin 64, ValidAt data (1280 + k.val) :=
  fun k => ⟨_, window020 k⟩

/-- ids 1344..1407; bridge from the frozen literal window `window021`. -/
theorem vw021 : ∀ k : Fin 64, ValidAt data (1344 + k.val) :=
  fun k => ⟨_, window021 k⟩

/-- ids 1408..1471; bridge from the frozen literal window `window022`. -/
theorem vw022 : ∀ k : Fin 64, ValidAt data (1408 + k.val) :=
  fun k => ⟨_, window022 k⟩

/-- ids 1472..1535; bridge from the frozen literal window `window023`. -/
theorem vw023 : ∀ k : Fin 64, ValidAt data (1472 + k.val) :=
  fun k => ⟨_, window023 k⟩

/-- ids 1536..1599; bridge from the frozen literal window `window024`. -/
theorem vw024 : ∀ k : Fin 64, ValidAt data (1536 + k.val) :=
  fun k => ⟨_, window024 k⟩

/-- ids 1600..1663; bridge from the frozen literal window `window025`. -/
theorem vw025 : ∀ k : Fin 64, ValidAt data (1600 + k.val) :=
  fun k => ⟨_, window025 k⟩

/-- ids 1664..1727; bridge from the frozen literal window `window026`. -/
theorem vw026 : ∀ k : Fin 64, ValidAt data (1664 + k.val) :=
  fun k => ⟨_, window026 k⟩

/-- ids 1728..1791; bridge from the frozen literal window `window027`. -/
theorem vw027 : ∀ k : Fin 64, ValidAt data (1728 + k.val) :=
  fun k => ⟨_, window027 k⟩

/-- ids 1792..1855; bridge from the frozen literal window `window028`. -/
theorem vw028 : ∀ k : Fin 64, ValidAt data (1792 + k.val) :=
  fun k => ⟨_, window028 k⟩

/-- ids 1856..1919; bridge from the frozen literal window `window029`. -/
theorem vw029 : ∀ k : Fin 64, ValidAt data (1856 + k.val) :=
  fun k => ⟨_, window029 k⟩

/-- ids 1920..1983; bridge from the frozen literal window `window030`. -/
theorem vw030 : ∀ k : Fin 64, ValidAt data (1920 + k.val) :=
  fun k => ⟨_, window030 k⟩

/-- ids 1984..2047; bridge from the frozen literal window `window031`. -/
theorem vw031 : ∀ k : Fin 64, ValidAt data (1984 + k.val) :=
  fun k => ⟨_, window031 k⟩

/-- ids 2048..2111; bridge from the frozen literal window `window032`. -/
theorem vw032 : ∀ k : Fin 64, ValidAt data (2048 + k.val) :=
  fun k => ⟨_, window032 k⟩

/-- ids 2112..2175; bridge from the frozen literal window `window033`. -/
theorem vw033 : ∀ k : Fin 64, ValidAt data (2112 + k.val) :=
  fun k => ⟨_, window033 k⟩

/-- ids 2176..2239; bridge from the frozen literal window `window034`. -/
theorem vw034 : ∀ k : Fin 64, ValidAt data (2176 + k.val) :=
  fun k => ⟨_, window034 k⟩

/-- ids 2240..2303; bridge from the frozen literal window `window035`. -/
theorem vw035 : ∀ k : Fin 64, ValidAt data (2240 + k.val) :=
  fun k => ⟨_, window035 k⟩

/-- ids 2304..2367; bridge from the frozen literal window `window036`. -/
theorem vw036 : ∀ k : Fin 64, ValidAt data (2304 + k.val) :=
  fun k => ⟨_, window036 k⟩

/-- ids 2368..2431; bridge from the frozen literal window `window037`. -/
theorem vw037 : ∀ k : Fin 64, ValidAt data (2368 + k.val) :=
  fun k => ⟨_, window037 k⟩

/-- ids 2432..2495; bridge from the frozen literal window `window038`. -/
theorem vw038 : ∀ k : Fin 64, ValidAt data (2432 + k.val) :=
  fun k => ⟨_, window038 k⟩

/-- ids 2496..2559; bridge from the frozen literal window `window039`. -/
theorem vw039 : ∀ k : Fin 64, ValidAt data (2496 + k.val) :=
  fun k => ⟨_, window039 k⟩

/-- ids 2560..2623; bridge from the frozen literal window `window040`. -/
theorem vw040 : ∀ k : Fin 64, ValidAt data (2560 + k.val) :=
  fun k => ⟨_, window040 k⟩

/-- ids 2624..2687; bridge from the frozen literal window `window041`. -/
theorem vw041 : ∀ k : Fin 64, ValidAt data (2624 + k.val) :=
  fun k => ⟨_, window041 k⟩

/-- ids 2688..2751; bridge from the frozen literal window `window042`. -/
theorem vw042 : ∀ k : Fin 64, ValidAt data (2688 + k.val) :=
  fun k => ⟨_, window042 k⟩

/-- ids 2752..2815; bridge from the frozen literal window `window043`. -/
theorem vw043 : ∀ k : Fin 64, ValidAt data (2752 + k.val) :=
  fun k => ⟨_, window043 k⟩

/-- ids 2816..2879; bridge from the frozen literal window `window044`. -/
theorem vw044 : ∀ k : Fin 64, ValidAt data (2816 + k.val) :=
  fun k => ⟨_, window044 k⟩

/-- ids 2880..2943; bridge from the frozen literal window `window045`. -/
theorem vw045 : ∀ k : Fin 64, ValidAt data (2880 + k.val) :=
  fun k => ⟨_, window045 k⟩

/-- ids 2944..3007; bridge from the frozen literal window `window046`. -/
theorem vw046 : ∀ k : Fin 64, ValidAt data (2944 + k.val) :=
  fun k => ⟨_, window046 k⟩

/-- ids 3008..3071; bridge from the frozen literal window `window047`. -/
theorem vw047 : ∀ k : Fin 64, ValidAt data (3008 + k.val) :=
  fun k => ⟨_, window047 k⟩

/-- ids 3072..3135; bridge from the frozen literal window `window048`. -/
theorem vw048 : ∀ k : Fin 64, ValidAt data (3072 + k.val) :=
  fun k => ⟨_, window048 k⟩

/-- ids 3136..3199; bridge from the frozen literal window `window049`. -/
theorem vw049 : ∀ k : Fin 64, ValidAt data (3136 + k.val) :=
  fun k => ⟨_, window049 k⟩

/-- ids 3200..3263; bridge from the frozen literal window `window050`. -/
theorem vw050 : ∀ k : Fin 64, ValidAt data (3200 + k.val) :=
  fun k => ⟨_, window050 k⟩

/-- ids 3264..3327; bridge from the frozen literal window `window051`. -/
theorem vw051 : ∀ k : Fin 64, ValidAt data (3264 + k.val) :=
  fun k => ⟨_, window051 k⟩

/-- ids 3328..3391; bridge from the frozen literal window `window052`. -/
theorem vw052 : ∀ k : Fin 64, ValidAt data (3328 + k.val) :=
  fun k => ⟨_, window052 k⟩

/-- ids 3392..3455; bridge from the frozen literal window `window053`. -/
theorem vw053 : ∀ k : Fin 64, ValidAt data (3392 + k.val) :=
  fun k => ⟨_, window053 k⟩

/-- ids 3456..3519; bridge from the frozen literal window `window054`. -/
theorem vw054 : ∀ k : Fin 64, ValidAt data (3456 + k.val) :=
  fun k => ⟨_, window054 k⟩

/-- ids 3520..3583; bridge from the frozen literal window `window055`. -/
theorem vw055 : ∀ k : Fin 64, ValidAt data (3520 + k.val) :=
  fun k => ⟨_, window055 k⟩

/-- ids 3584..3647; bridge from the frozen literal window `window056`. -/
theorem vw056 : ∀ k : Fin 64, ValidAt data (3584 + k.val) :=
  fun k => ⟨_, window056 k⟩

/-- ids 3648..3711; bridge from the frozen literal window `window057`. -/
theorem vw057 : ∀ k : Fin 64, ValidAt data (3648 + k.val) :=
  fun k => ⟨_, window057 k⟩

/-- ids 3712..3775; bridge from the frozen literal window `window058`. -/
theorem vw058 : ∀ k : Fin 64, ValidAt data (3712 + k.val) :=
  fun k => ⟨_, window058 k⟩

/-- ids 3776..3839; bridge from the frozen literal window `window059`. -/
theorem vw059 : ∀ k : Fin 64, ValidAt data (3776 + k.val) :=
  fun k => ⟨_, window059 k⟩

/-- ids 3840..3903; bridge from the frozen literal window `window060`. -/
theorem vw060 : ∀ k : Fin 64, ValidAt data (3840 + k.val) :=
  fun k => ⟨_, window060 k⟩

/-- ids 3904..3967; bridge from the frozen literal window `window061`. -/
theorem vw061 : ∀ k : Fin 64, ValidAt data (3904 + k.val) :=
  fun k => ⟨_, window061 k⟩

/-- ids 3968..4031; bridge from the frozen literal window `window062`. -/
theorem vw062 : ∀ k : Fin 64, ValidAt data (3968 + k.val) :=
  fun k => ⟨_, window062 k⟩

/-- ids 4032..4095; bridge from the frozen literal window `window063`. -/
theorem vw063 : ∀ k : Fin 64, ValidAt data (4032 + k.val) :=
  fun k => ⟨_, window063 k⟩

/-- ids 4096..4159; bridge from the frozen literal window `window064`. -/
theorem vw064 : ∀ k : Fin 64, ValidAt data (4096 + k.val) :=
  fun k => ⟨_, window064 k⟩

/-- ids 4160..4223; bridge from the frozen literal window `window065`. -/
theorem vw065 : ∀ k : Fin 64, ValidAt data (4160 + k.val) :=
  fun k => ⟨_, window065 k⟩

/-- ids 4224..4287; bridge from the frozen literal window `window066`. -/
theorem vw066 : ∀ k : Fin 64, ValidAt data (4224 + k.val) :=
  fun k => ⟨_, window066 k⟩

/-- ids 4288..4351; bridge from the frozen literal window `window067`. -/
theorem vw067 : ∀ k : Fin 64, ValidAt data (4288 + k.val) :=
  fun k => ⟨_, window067 k⟩

/-- ids 4352..4415; bridge from the frozen literal window `window068`. -/
theorem vw068 : ∀ k : Fin 64, ValidAt data (4352 + k.val) :=
  fun k => ⟨_, window068 k⟩

/-- ids 4416..4479; bridge from the frozen literal window `window069`. -/
theorem vw069 : ∀ k : Fin 64, ValidAt data (4416 + k.val) :=
  fun k => ⟨_, window069 k⟩

/-- ids 4480..4543; bridge from the frozen literal window `window070`. -/
theorem vw070 : ∀ k : Fin 64, ValidAt data (4480 + k.val) :=
  fun k => ⟨_, window070 k⟩

/-- ids 4544..4607; bridge from the frozen literal window `window071`. -/
theorem vw071 : ∀ k : Fin 64, ValidAt data (4544 + k.val) :=
  fun k => ⟨_, window071 k⟩

/-- ids 4608..4671; bridge from the frozen literal window `window072`. -/
theorem vw072 : ∀ k : Fin 64, ValidAt data (4608 + k.val) :=
  fun k => ⟨_, window072 k⟩

/-- ids 4672..4735; bridge from the frozen literal window `window073`. -/
theorem vw073 : ∀ k : Fin 64, ValidAt data (4672 + k.val) :=
  fun k => ⟨_, window073 k⟩

/-- ids 4736..4799; bridge from the frozen literal window `window074`. -/
theorem vw074 : ∀ k : Fin 64, ValidAt data (4736 + k.val) :=
  fun k => ⟨_, window074 k⟩

/-- ids 4800..4863; bridge from the frozen literal window `window075`. -/
theorem vw075 : ∀ k : Fin 64, ValidAt data (4800 + k.val) :=
  fun k => ⟨_, window075 k⟩

/-- ids 4864..4927; bridge from the frozen literal window `window076`. -/
theorem vw076 : ∀ k : Fin 64, ValidAt data (4864 + k.val) :=
  fun k => ⟨_, window076 k⟩

/-- ids 4928..4991; bridge from the frozen literal window `window077`. -/
theorem vw077 : ∀ k : Fin 64, ValidAt data (4928 + k.val) :=
  fun k => ⟨_, window077 k⟩

/-- ids 4992..5010; bridge from the frozen literal window `window078`. -/
theorem vw078 : ∀ k : Fin 19, ValidAt data (4992 + k.val) :=
  fun k => ⟨_, window078 k⟩
/-- Interface check for block 0: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨0,_⟩ : Fin 79)` accepts the literal bridge `vw000`. -/
example : ValidAtWindow data 64 (0 : Fin 79).val := vw000

/-- Interface check for block 1: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨1,_⟩ : Fin 79)` accepts the literal bridge `vw001`. -/
example : ValidAtWindow data 64 (1 : Fin 79).val := vw001

/-- Interface check for block 2: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨2,_⟩ : Fin 79)` accepts the literal bridge `vw002`. -/
example : ValidAtWindow data 64 (2 : Fin 79).val := vw002

/-- Interface check for block 3: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨3,_⟩ : Fin 79)` accepts the literal bridge `vw003`. -/
example : ValidAtWindow data 64 (3 : Fin 79).val := vw003

/-- Interface check for block 4: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨4,_⟩ : Fin 79)` accepts the literal bridge `vw004`. -/
example : ValidAtWindow data 64 (4 : Fin 79).val := vw004

/-- Interface check for block 5: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨5,_⟩ : Fin 79)` accepts the literal bridge `vw005`. -/
example : ValidAtWindow data 64 (5 : Fin 79).val := vw005

/-- Interface check for block 6: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨6,_⟩ : Fin 79)` accepts the literal bridge `vw006`. -/
example : ValidAtWindow data 64 (6 : Fin 79).val := vw006

/-- Interface check for block 7: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨7,_⟩ : Fin 79)` accepts the literal bridge `vw007`. -/
example : ValidAtWindow data 64 (7 : Fin 79).val := vw007

/-- Interface check for block 8: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨8,_⟩ : Fin 79)` accepts the literal bridge `vw008`. -/
example : ValidAtWindow data 64 (8 : Fin 79).val := vw008

/-- Interface check for block 9: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨9,_⟩ : Fin 79)` accepts the literal bridge `vw009`. -/
example : ValidAtWindow data 64 (9 : Fin 79).val := vw009

/-- Interface check for block 10: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨10,_⟩ : Fin 79)` accepts the literal bridge `vw010`. -/
example : ValidAtWindow data 64 (10 : Fin 79).val := vw010

/-- Interface check for block 11: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨11,_⟩ : Fin 79)` accepts the literal bridge `vw011`. -/
example : ValidAtWindow data 64 (11 : Fin 79).val := vw011

/-- Interface check for block 12: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨12,_⟩ : Fin 79)` accepts the literal bridge `vw012`. -/
example : ValidAtWindow data 64 (12 : Fin 79).val := vw012

/-- Interface check for block 13: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨13,_⟩ : Fin 79)` accepts the literal bridge `vw013`. -/
example : ValidAtWindow data 64 (13 : Fin 79).val := vw013

/-- Interface check for block 14: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨14,_⟩ : Fin 79)` accepts the literal bridge `vw014`. -/
example : ValidAtWindow data 64 (14 : Fin 79).val := vw014

/-- Interface check for block 15: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨15,_⟩ : Fin 79)` accepts the literal bridge `vw015`. -/
example : ValidAtWindow data 64 (15 : Fin 79).val := vw015

/-- Interface check for block 16: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨16,_⟩ : Fin 79)` accepts the literal bridge `vw016`. -/
example : ValidAtWindow data 64 (16 : Fin 79).val := vw016

/-- Interface check for block 17: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨17,_⟩ : Fin 79)` accepts the literal bridge `vw017`. -/
example : ValidAtWindow data 64 (17 : Fin 79).val := vw017

/-- Interface check for block 18: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨18,_⟩ : Fin 79)` accepts the literal bridge `vw018`. -/
example : ValidAtWindow data 64 (18 : Fin 79).val := vw018

/-- Interface check for block 19: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨19,_⟩ : Fin 79)` accepts the literal bridge `vw019`. -/
example : ValidAtWindow data 64 (19 : Fin 79).val := vw019

/-- Interface check for block 20: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨20,_⟩ : Fin 79)` accepts the literal bridge `vw020`. -/
example : ValidAtWindow data 64 (20 : Fin 79).val := vw020

/-- Interface check for block 21: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨21,_⟩ : Fin 79)` accepts the literal bridge `vw021`. -/
example : ValidAtWindow data 64 (21 : Fin 79).val := vw021

/-- Interface check for block 22: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨22,_⟩ : Fin 79)` accepts the literal bridge `vw022`. -/
example : ValidAtWindow data 64 (22 : Fin 79).val := vw022

/-- Interface check for block 23: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨23,_⟩ : Fin 79)` accepts the literal bridge `vw023`. -/
example : ValidAtWindow data 64 (23 : Fin 79).val := vw023

/-- Interface check for block 24: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨24,_⟩ : Fin 79)` accepts the literal bridge `vw024`. -/
example : ValidAtWindow data 64 (24 : Fin 79).val := vw024

/-- Interface check for block 25: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨25,_⟩ : Fin 79)` accepts the literal bridge `vw025`. -/
example : ValidAtWindow data 64 (25 : Fin 79).val := vw025

/-- Interface check for block 26: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨26,_⟩ : Fin 79)` accepts the literal bridge `vw026`. -/
example : ValidAtWindow data 64 (26 : Fin 79).val := vw026

/-- Interface check for block 27: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨27,_⟩ : Fin 79)` accepts the literal bridge `vw027`. -/
example : ValidAtWindow data 64 (27 : Fin 79).val := vw027

/-- Interface check for block 28: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨28,_⟩ : Fin 79)` accepts the literal bridge `vw028`. -/
example : ValidAtWindow data 64 (28 : Fin 79).val := vw028

/-- Interface check for block 29: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨29,_⟩ : Fin 79)` accepts the literal bridge `vw029`. -/
example : ValidAtWindow data 64 (29 : Fin 79).val := vw029

/-- Interface check for block 30: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨30,_⟩ : Fin 79)` accepts the literal bridge `vw030`. -/
example : ValidAtWindow data 64 (30 : Fin 79).val := vw030

/-- Interface check for block 31: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨31,_⟩ : Fin 79)` accepts the literal bridge `vw031`. -/
example : ValidAtWindow data 64 (31 : Fin 79).val := vw031

/-- Interface check for block 32: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨32,_⟩ : Fin 79)` accepts the literal bridge `vw032`. -/
example : ValidAtWindow data 64 (32 : Fin 79).val := vw032

/-- Interface check for block 33: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨33,_⟩ : Fin 79)` accepts the literal bridge `vw033`. -/
example : ValidAtWindow data 64 (33 : Fin 79).val := vw033

/-- Interface check for block 34: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨34,_⟩ : Fin 79)` accepts the literal bridge `vw034`. -/
example : ValidAtWindow data 64 (34 : Fin 79).val := vw034

/-- Interface check for block 35: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨35,_⟩ : Fin 79)` accepts the literal bridge `vw035`. -/
example : ValidAtWindow data 64 (35 : Fin 79).val := vw035

/-- Interface check for block 36: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨36,_⟩ : Fin 79)` accepts the literal bridge `vw036`. -/
example : ValidAtWindow data 64 (36 : Fin 79).val := vw036

/-- Interface check for block 37: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨37,_⟩ : Fin 79)` accepts the literal bridge `vw037`. -/
example : ValidAtWindow data 64 (37 : Fin 79).val := vw037

/-- Interface check for block 38: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨38,_⟩ : Fin 79)` accepts the literal bridge `vw038`. -/
example : ValidAtWindow data 64 (38 : Fin 79).val := vw038

/-- Interface check for block 39: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨39,_⟩ : Fin 79)` accepts the literal bridge `vw039`. -/
example : ValidAtWindow data 64 (39 : Fin 79).val := vw039

/-- Interface check for block 40: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨40,_⟩ : Fin 79)` accepts the literal bridge `vw040`. -/
example : ValidAtWindow data 64 (40 : Fin 79).val := vw040

/-- Interface check for block 41: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨41,_⟩ : Fin 79)` accepts the literal bridge `vw041`. -/
example : ValidAtWindow data 64 (41 : Fin 79).val := vw041

/-- Interface check for block 42: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨42,_⟩ : Fin 79)` accepts the literal bridge `vw042`. -/
example : ValidAtWindow data 64 (42 : Fin 79).val := vw042

/-- Interface check for block 43: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨43,_⟩ : Fin 79)` accepts the literal bridge `vw043`. -/
example : ValidAtWindow data 64 (43 : Fin 79).val := vw043

/-- Interface check for block 44: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨44,_⟩ : Fin 79)` accepts the literal bridge `vw044`. -/
example : ValidAtWindow data 64 (44 : Fin 79).val := vw044

/-- Interface check for block 45: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨45,_⟩ : Fin 79)` accepts the literal bridge `vw045`. -/
example : ValidAtWindow data 64 (45 : Fin 79).val := vw045

/-- Interface check for block 46: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨46,_⟩ : Fin 79)` accepts the literal bridge `vw046`. -/
example : ValidAtWindow data 64 (46 : Fin 79).val := vw046

/-- Interface check for block 47: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨47,_⟩ : Fin 79)` accepts the literal bridge `vw047`. -/
example : ValidAtWindow data 64 (47 : Fin 79).val := vw047

/-- Interface check for block 48: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨48,_⟩ : Fin 79)` accepts the literal bridge `vw048`. -/
example : ValidAtWindow data 64 (48 : Fin 79).val := vw048

/-- Interface check for block 49: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨49,_⟩ : Fin 79)` accepts the literal bridge `vw049`. -/
example : ValidAtWindow data 64 (49 : Fin 79).val := vw049

/-- Interface check for block 50: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨50,_⟩ : Fin 79)` accepts the literal bridge `vw050`. -/
example : ValidAtWindow data 64 (50 : Fin 79).val := vw050

/-- Interface check for block 51: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨51,_⟩ : Fin 79)` accepts the literal bridge `vw051`. -/
example : ValidAtWindow data 64 (51 : Fin 79).val := vw051

/-- Interface check for block 52: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨52,_⟩ : Fin 79)` accepts the literal bridge `vw052`. -/
example : ValidAtWindow data 64 (52 : Fin 79).val := vw052

/-- Interface check for block 53: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨53,_⟩ : Fin 79)` accepts the literal bridge `vw053`. -/
example : ValidAtWindow data 64 (53 : Fin 79).val := vw053

/-- Interface check for block 54: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨54,_⟩ : Fin 79)` accepts the literal bridge `vw054`. -/
example : ValidAtWindow data 64 (54 : Fin 79).val := vw054

/-- Interface check for block 55: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨55,_⟩ : Fin 79)` accepts the literal bridge `vw055`. -/
example : ValidAtWindow data 64 (55 : Fin 79).val := vw055

/-- Interface check for block 56: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨56,_⟩ : Fin 79)` accepts the literal bridge `vw056`. -/
example : ValidAtWindow data 64 (56 : Fin 79).val := vw056

/-- Interface check for block 57: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨57,_⟩ : Fin 79)` accepts the literal bridge `vw057`. -/
example : ValidAtWindow data 64 (57 : Fin 79).val := vw057

/-- Interface check for block 58: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨58,_⟩ : Fin 79)` accepts the literal bridge `vw058`. -/
example : ValidAtWindow data 64 (58 : Fin 79).val := vw058

/-- Interface check for block 59: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨59,_⟩ : Fin 79)` accepts the literal bridge `vw059`. -/
example : ValidAtWindow data 64 (59 : Fin 79).val := vw059

/-- Interface check for block 60: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨60,_⟩ : Fin 79)` accepts the literal bridge `vw060`. -/
example : ValidAtWindow data 64 (60 : Fin 79).val := vw060

/-- Interface check for block 61: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨61,_⟩ : Fin 79)` accepts the literal bridge `vw061`. -/
example : ValidAtWindow data 64 (61 : Fin 79).val := vw061

/-- Interface check for block 62: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨62,_⟩ : Fin 79)` accepts the literal bridge `vw062`. -/
example : ValidAtWindow data 64 (62 : Fin 79).val := vw062

/-- Interface check for block 63: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨63,_⟩ : Fin 79)` accepts the literal bridge `vw063`. -/
example : ValidAtWindow data 64 (63 : Fin 79).val := vw063

/-- Interface check for block 64: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨64,_⟩ : Fin 79)` accepts the literal bridge `vw064`. -/
example : ValidAtWindow data 64 (64 : Fin 79).val := vw064

/-- Interface check for block 65: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨65,_⟩ : Fin 79)` accepts the literal bridge `vw065`. -/
example : ValidAtWindow data 64 (65 : Fin 79).val := vw065

/-- Interface check for block 66: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨66,_⟩ : Fin 79)` accepts the literal bridge `vw066`. -/
example : ValidAtWindow data 64 (66 : Fin 79).val := vw066

/-- Interface check for block 67: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨67,_⟩ : Fin 79)` accepts the literal bridge `vw067`. -/
example : ValidAtWindow data 64 (67 : Fin 79).val := vw067

/-- Interface check for block 68: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨68,_⟩ : Fin 79)` accepts the literal bridge `vw068`. -/
example : ValidAtWindow data 64 (68 : Fin 79).val := vw068

/-- Interface check for block 69: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨69,_⟩ : Fin 79)` accepts the literal bridge `vw069`. -/
example : ValidAtWindow data 64 (69 : Fin 79).val := vw069

/-- Interface check for block 70: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨70,_⟩ : Fin 79)` accepts the literal bridge `vw070`. -/
example : ValidAtWindow data 64 (70 : Fin 79).val := vw070

/-- Interface check for block 71: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨71,_⟩ : Fin 79)` accepts the literal bridge `vw071`. -/
example : ValidAtWindow data 64 (71 : Fin 79).val := vw071

/-- Interface check for block 72: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨72,_⟩ : Fin 79)` accepts the literal bridge `vw072`. -/
example : ValidAtWindow data 64 (72 : Fin 79).val := vw072

/-- Interface check for block 73: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨73,_⟩ : Fin 79)` accepts the literal bridge `vw073`. -/
example : ValidAtWindow data 64 (73 : Fin 79).val := vw073

/-- Interface check for block 74: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨74,_⟩ : Fin 79)` accepts the literal bridge `vw074`. -/
example : ValidAtWindow data 64 (74 : Fin 79).val := vw074

/-- Interface check for block 75: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨75,_⟩ : Fin 79)` accepts the literal bridge `vw075`. -/
example : ValidAtWindow data 64 (75 : Fin 79).val := vw075

/-- Interface check for block 76: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨76,_⟩ : Fin 79)` accepts the literal bridge `vw076`. -/
example : ValidAtWindow data 64 (76 : Fin 79).val := vw076

/-- Interface check for block 77: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨77,_⟩ : Fin 79)` accepts the literal bridge `vw077`. -/
example : ValidAtWindow data 64 (77 : Fin 79).val := vw077

/-- Interface check for block 78: the dispatcher goal shape `ValidAtWindow data 64 (↑⟨78,_⟩ : Fin 79)` accepts the literal bridge `vw078`. -/
example : ValidAtWindow data 64 (78 : Fin 79).val := vw078
/-- Dispatcher over the 79 frozen blocks (one `exact` per block; no kernel reduction here). -/
theorem all_vw : ∀ b : Fin 79, ValidAtWindow data 64 b.val := by
  intro b
  fin_cases b
  · exact vw000
  · exact vw001
  · exact vw002
  · exact vw003
  · exact vw004
  · exact vw005
  · exact vw006
  · exact vw007
  · exact vw008
  · exact vw009
  · exact vw010
  · exact vw011
  · exact vw012
  · exact vw013
  · exact vw014
  · exact vw015
  · exact vw016
  · exact vw017
  · exact vw018
  · exact vw019
  · exact vw020
  · exact vw021
  · exact vw022
  · exact vw023
  · exact vw024
  · exact vw025
  · exact vw026
  · exact vw027
  · exact vw028
  · exact vw029
  · exact vw030
  · exact vw031
  · exact vw032
  · exact vw033
  · exact vw034
  · exact vw035
  · exact vw036
  · exact vw037
  · exact vw038
  · exact vw039
  · exact vw040
  · exact vw041
  · exact vw042
  · exact vw043
  · exact vw044
  · exact vw045
  · exact vw046
  · exact vw047
  · exact vw048
  · exact vw049
  · exact vw050
  · exact vw051
  · exact vw052
  · exact vw053
  · exact vw054
  · exact vw055
  · exact vw056
  · exact vw057
  · exact vw058
  · exact vw059
  · exact vw060
  · exact vw061
  · exact vw062
  · exact vw063
  · exact vw064
  · exact vw065
  · exact vw066
  · exact vw067
  · exact vw068
  · exact vw069
  · exact vw070
  · exact vw071
  · exact vw072
  · exact vw073
  · exact vw074
  · exact vw075
  · exact vw076
  · exact vw077
  · exact vw078

/-- The 79 frozen window certificates assemble into the full pointwise interface. -/
theorem all_valid : ∀ n : Fin 5011, Valid data n :=
  all_valid_of_value_windows data 64 79 (by norm_num) (by norm_num) all_vw

/-- Consumer: `terminal_cover` at the source root with `hv` discharged by `all_valid`.
Compose with the accepted `root_cell_chart9` (tree-consumer/DBMTreeConsumer.lean) by
`t := FlashLeafSplit.tlift y` to get the unconditional chart statement. -/
theorem terminal_cover_root (t : Fin 10 → ℝ)
    (ht : FlashLeafSplit.Cell (matrix data 4096 (0 : Fin 5011)) t) :
    ∃ l : Fin 5011, (data l).terminal = true ∧ FlashLeafSplit.Cell (matrix data 4096 l) t :=
  terminal_cover_of_value_windows data 4096 (by norm_num) 64 79 (by norm_num) (by norm_num)
    all_vw t 0 ht

end N11Formalization.DBMTreeWindowAssembly

#check @N11Formalization.DBMTreeWindowAssembly.all_vw
#check @N11Formalization.DBMTreeWindowAssembly.all_valid
#check @N11Formalization.DBMTreeWindowAssembly.terminal_cover_root
#print axioms N11Formalization.DBMTreeWindowAssembly.all_vw
#print axioms N11Formalization.DBMTreeWindowAssembly.all_valid
#print axioms N11Formalization.DBMTreeWindowAssembly.terminal_cover_root
#check @N11Formalization.DBMTreeWindowAssembly.vw000
#print axioms N11Formalization.DBMTreeWindowAssembly.vw000
#check @N11Formalization.DBMTreeWindowAssembly.vw001
#print axioms N11Formalization.DBMTreeWindowAssembly.vw001
#check @N11Formalization.DBMTreeWindowAssembly.vw002
#print axioms N11Formalization.DBMTreeWindowAssembly.vw002
#check @N11Formalization.DBMTreeWindowAssembly.vw003
#print axioms N11Formalization.DBMTreeWindowAssembly.vw003
#check @N11Formalization.DBMTreeWindowAssembly.vw004
#print axioms N11Formalization.DBMTreeWindowAssembly.vw004
#check @N11Formalization.DBMTreeWindowAssembly.vw005
#print axioms N11Formalization.DBMTreeWindowAssembly.vw005
#check @N11Formalization.DBMTreeWindowAssembly.vw006
#print axioms N11Formalization.DBMTreeWindowAssembly.vw006
#check @N11Formalization.DBMTreeWindowAssembly.vw007
#print axioms N11Formalization.DBMTreeWindowAssembly.vw007
#check @N11Formalization.DBMTreeWindowAssembly.vw008
#print axioms N11Formalization.DBMTreeWindowAssembly.vw008
#check @N11Formalization.DBMTreeWindowAssembly.vw009
#print axioms N11Formalization.DBMTreeWindowAssembly.vw009
#check @N11Formalization.DBMTreeWindowAssembly.vw010
#print axioms N11Formalization.DBMTreeWindowAssembly.vw010
#check @N11Formalization.DBMTreeWindowAssembly.vw011
#print axioms N11Formalization.DBMTreeWindowAssembly.vw011
#check @N11Formalization.DBMTreeWindowAssembly.vw012
#print axioms N11Formalization.DBMTreeWindowAssembly.vw012
#check @N11Formalization.DBMTreeWindowAssembly.vw013
#print axioms N11Formalization.DBMTreeWindowAssembly.vw013
#check @N11Formalization.DBMTreeWindowAssembly.vw014
#print axioms N11Formalization.DBMTreeWindowAssembly.vw014
#check @N11Formalization.DBMTreeWindowAssembly.vw015
#print axioms N11Formalization.DBMTreeWindowAssembly.vw015
#check @N11Formalization.DBMTreeWindowAssembly.vw016
#print axioms N11Formalization.DBMTreeWindowAssembly.vw016
#check @N11Formalization.DBMTreeWindowAssembly.vw017
#print axioms N11Formalization.DBMTreeWindowAssembly.vw017
#check @N11Formalization.DBMTreeWindowAssembly.vw018
#print axioms N11Formalization.DBMTreeWindowAssembly.vw018
#check @N11Formalization.DBMTreeWindowAssembly.vw019
#print axioms N11Formalization.DBMTreeWindowAssembly.vw019
#check @N11Formalization.DBMTreeWindowAssembly.vw020
#print axioms N11Formalization.DBMTreeWindowAssembly.vw020
#check @N11Formalization.DBMTreeWindowAssembly.vw021
#print axioms N11Formalization.DBMTreeWindowAssembly.vw021
#check @N11Formalization.DBMTreeWindowAssembly.vw022
#print axioms N11Formalization.DBMTreeWindowAssembly.vw022
#check @N11Formalization.DBMTreeWindowAssembly.vw023
#print axioms N11Formalization.DBMTreeWindowAssembly.vw023
#check @N11Formalization.DBMTreeWindowAssembly.vw024
#print axioms N11Formalization.DBMTreeWindowAssembly.vw024
#check @N11Formalization.DBMTreeWindowAssembly.vw025
#print axioms N11Formalization.DBMTreeWindowAssembly.vw025
#check @N11Formalization.DBMTreeWindowAssembly.vw026
#print axioms N11Formalization.DBMTreeWindowAssembly.vw026
#check @N11Formalization.DBMTreeWindowAssembly.vw027
#print axioms N11Formalization.DBMTreeWindowAssembly.vw027
#check @N11Formalization.DBMTreeWindowAssembly.vw028
#print axioms N11Formalization.DBMTreeWindowAssembly.vw028
#check @N11Formalization.DBMTreeWindowAssembly.vw029
#print axioms N11Formalization.DBMTreeWindowAssembly.vw029
#check @N11Formalization.DBMTreeWindowAssembly.vw030
#print axioms N11Formalization.DBMTreeWindowAssembly.vw030
#check @N11Formalization.DBMTreeWindowAssembly.vw031
#print axioms N11Formalization.DBMTreeWindowAssembly.vw031
#check @N11Formalization.DBMTreeWindowAssembly.vw032
#print axioms N11Formalization.DBMTreeWindowAssembly.vw032
#check @N11Formalization.DBMTreeWindowAssembly.vw033
#print axioms N11Formalization.DBMTreeWindowAssembly.vw033
#check @N11Formalization.DBMTreeWindowAssembly.vw034
#print axioms N11Formalization.DBMTreeWindowAssembly.vw034
#check @N11Formalization.DBMTreeWindowAssembly.vw035
#print axioms N11Formalization.DBMTreeWindowAssembly.vw035
#check @N11Formalization.DBMTreeWindowAssembly.vw036
#print axioms N11Formalization.DBMTreeWindowAssembly.vw036
#check @N11Formalization.DBMTreeWindowAssembly.vw037
#print axioms N11Formalization.DBMTreeWindowAssembly.vw037
#check @N11Formalization.DBMTreeWindowAssembly.vw038
#print axioms N11Formalization.DBMTreeWindowAssembly.vw038
#check @N11Formalization.DBMTreeWindowAssembly.vw039
#print axioms N11Formalization.DBMTreeWindowAssembly.vw039
#check @N11Formalization.DBMTreeWindowAssembly.vw040
#print axioms N11Formalization.DBMTreeWindowAssembly.vw040
#check @N11Formalization.DBMTreeWindowAssembly.vw041
#print axioms N11Formalization.DBMTreeWindowAssembly.vw041
#check @N11Formalization.DBMTreeWindowAssembly.vw042
#print axioms N11Formalization.DBMTreeWindowAssembly.vw042
#check @N11Formalization.DBMTreeWindowAssembly.vw043
#print axioms N11Formalization.DBMTreeWindowAssembly.vw043
#check @N11Formalization.DBMTreeWindowAssembly.vw044
#print axioms N11Formalization.DBMTreeWindowAssembly.vw044
#check @N11Formalization.DBMTreeWindowAssembly.vw045
#print axioms N11Formalization.DBMTreeWindowAssembly.vw045
#check @N11Formalization.DBMTreeWindowAssembly.vw046
#print axioms N11Formalization.DBMTreeWindowAssembly.vw046
#check @N11Formalization.DBMTreeWindowAssembly.vw047
#print axioms N11Formalization.DBMTreeWindowAssembly.vw047
#check @N11Formalization.DBMTreeWindowAssembly.vw048
#print axioms N11Formalization.DBMTreeWindowAssembly.vw048
#check @N11Formalization.DBMTreeWindowAssembly.vw049
#print axioms N11Formalization.DBMTreeWindowAssembly.vw049
#check @N11Formalization.DBMTreeWindowAssembly.vw050
#print axioms N11Formalization.DBMTreeWindowAssembly.vw050
#check @N11Formalization.DBMTreeWindowAssembly.vw051
#print axioms N11Formalization.DBMTreeWindowAssembly.vw051
#check @N11Formalization.DBMTreeWindowAssembly.vw052
#print axioms N11Formalization.DBMTreeWindowAssembly.vw052
#check @N11Formalization.DBMTreeWindowAssembly.vw053
#print axioms N11Formalization.DBMTreeWindowAssembly.vw053
#check @N11Formalization.DBMTreeWindowAssembly.vw054
#print axioms N11Formalization.DBMTreeWindowAssembly.vw054
#check @N11Formalization.DBMTreeWindowAssembly.vw055
#print axioms N11Formalization.DBMTreeWindowAssembly.vw055
#check @N11Formalization.DBMTreeWindowAssembly.vw056
#print axioms N11Formalization.DBMTreeWindowAssembly.vw056
#check @N11Formalization.DBMTreeWindowAssembly.vw057
#print axioms N11Formalization.DBMTreeWindowAssembly.vw057
#check @N11Formalization.DBMTreeWindowAssembly.vw058
#print axioms N11Formalization.DBMTreeWindowAssembly.vw058
#check @N11Formalization.DBMTreeWindowAssembly.vw059
#print axioms N11Formalization.DBMTreeWindowAssembly.vw059
#check @N11Formalization.DBMTreeWindowAssembly.vw060
#print axioms N11Formalization.DBMTreeWindowAssembly.vw060
#check @N11Formalization.DBMTreeWindowAssembly.vw061
#print axioms N11Formalization.DBMTreeWindowAssembly.vw061
#check @N11Formalization.DBMTreeWindowAssembly.vw062
#print axioms N11Formalization.DBMTreeWindowAssembly.vw062
#check @N11Formalization.DBMTreeWindowAssembly.vw063
#print axioms N11Formalization.DBMTreeWindowAssembly.vw063
#check @N11Formalization.DBMTreeWindowAssembly.vw064
#print axioms N11Formalization.DBMTreeWindowAssembly.vw064
#check @N11Formalization.DBMTreeWindowAssembly.vw065
#print axioms N11Formalization.DBMTreeWindowAssembly.vw065
#check @N11Formalization.DBMTreeWindowAssembly.vw066
#print axioms N11Formalization.DBMTreeWindowAssembly.vw066
#check @N11Formalization.DBMTreeWindowAssembly.vw067
#print axioms N11Formalization.DBMTreeWindowAssembly.vw067
#check @N11Formalization.DBMTreeWindowAssembly.vw068
#print axioms N11Formalization.DBMTreeWindowAssembly.vw068
#check @N11Formalization.DBMTreeWindowAssembly.vw069
#print axioms N11Formalization.DBMTreeWindowAssembly.vw069
#check @N11Formalization.DBMTreeWindowAssembly.vw070
#print axioms N11Formalization.DBMTreeWindowAssembly.vw070
#check @N11Formalization.DBMTreeWindowAssembly.vw071
#print axioms N11Formalization.DBMTreeWindowAssembly.vw071
#check @N11Formalization.DBMTreeWindowAssembly.vw072
#print axioms N11Formalization.DBMTreeWindowAssembly.vw072
#check @N11Formalization.DBMTreeWindowAssembly.vw073
#print axioms N11Formalization.DBMTreeWindowAssembly.vw073
#check @N11Formalization.DBMTreeWindowAssembly.vw074
#print axioms N11Formalization.DBMTreeWindowAssembly.vw074
#check @N11Formalization.DBMTreeWindowAssembly.vw075
#print axioms N11Formalization.DBMTreeWindowAssembly.vw075
#check @N11Formalization.DBMTreeWindowAssembly.vw076
#print axioms N11Formalization.DBMTreeWindowAssembly.vw076
#check @N11Formalization.DBMTreeWindowAssembly.vw077
#print axioms N11Formalization.DBMTreeWindowAssembly.vw077
#check @N11Formalization.DBMTreeWindowAssembly.vw078
#print axioms N11Formalization.DBMTreeWindowAssembly.vw078
