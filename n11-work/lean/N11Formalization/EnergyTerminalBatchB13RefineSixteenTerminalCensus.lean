import N11Formalization.DBMSourceTreeData

/-! Lane-B terminal census in bounded kernel blocks.

Each chunk covers at most 256 source indices.  The per-chunk membership
equivalence and cardinality are checked with `decide +kernel`; the top
cardinality follows from `Finset.card_biUnion`.  This pays no radius. -/
set_option autoImplicit false
namespace N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual
open Finset
noncomputable section

def terminalIDs : Finset (Fin 5011) :=
  Finset.univ.filter fun n => (DBMSourceTree.data n).terminal = true

def embed0 (n : Fin 256) : Fin 5011 := ⟨n.val + 0, by omega⟩
def census0 : Finset (Fin 256) :=
  Finset.univ.filter fun n => (DBMSourceTree.data (embed0 n)).terminal = true

theorem census0_spec (n : Fin 256) :
    (DBMSourceTree.data (embed0 n)).terminal = true ↔ n ∈ census0 := by
  simp only [census0, Finset.mem_filter, Finset.mem_univ, true_and]

theorem census0_card : census0.card = 61 := by
  decide +kernel

def blockIDs0 : Finset (Fin 5011) := census0.image embed0

theorem blockIDs0_card : blockIDs0.card = 61 := by
  rw [blockIDs0, Finset.card_image_of_injective _ ?_, census0_card]
  intro x y h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [embed0] at this ⊢
  omega

theorem blockIDs0_upper : blockIDs0 ⊆
    Finset.univ.filter (fun n : Fin 5011 => n.val < 256) := by
  intro n hn
  rw [blockIDs0, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed0]; all_goals omega
theorem blockIDs0_lower : blockIDs0 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 0 ≤ n.val) := by
  intro n hn
  rw [blockIDs0, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed0]; all_goals omega

theorem block_mem0 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 0 ≤ n.val) (hhi : n.val < 256) : n ∈ blockIDs0 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 0, by omega⟩, ?_, ?_⟩
  · exact (census0_spec _).mp (by
      have he : embed0 ⟨n.val - 0, by omega⟩ = n := by ext; simp [embed0]; all_goals omega
      simpa [he] using ht)
  · ext; simp [embed0]; all_goals omega

theorem block_terminal0 {n : Fin 5011} (hn : n ∈ blockIDs0) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census0_spec m).mpr hm

theorem blockIDs0_interval : blockIDs0 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 0 ≤ n.val ∧ n.val < 256) := by
  intro n hn
  have hu := blockIDs0_upper hn
  have hl := blockIDs0_lower hn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hl ⊢
  exact ⟨hl, hu⟩

def embed1 (n : Fin 256) : Fin 5011 := ⟨n.val + 256, by omega⟩
def census1 : Finset (Fin 256) :=
  Finset.univ.filter fun n => (DBMSourceTree.data (embed1 n)).terminal = true

theorem census1_spec (n : Fin 256) :
    (DBMSourceTree.data (embed1 n)).terminal = true ↔ n ∈ census1 := by
  simp only [census1, Finset.mem_filter, Finset.mem_univ, true_and]

theorem census1_card : census1.card = 75 := by
  decide +kernel

def blockIDs1 : Finset (Fin 5011) := census1.image embed1

theorem blockIDs1_card : blockIDs1.card = 75 := by
  rw [blockIDs1, Finset.card_image_of_injective _ ?_, census1_card]
  intro x y h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [embed1] at this ⊢
  omega

theorem blockIDs1_upper : blockIDs1 ⊆
    Finset.univ.filter (fun n : Fin 5011 => n.val < 512) := by
  intro n hn
  rw [blockIDs1, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed1]; all_goals omega
theorem blockIDs1_lower : blockIDs1 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 256 ≤ n.val) := by
  intro n hn
  rw [blockIDs1, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed1]; all_goals omega

theorem block_mem1 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 256 ≤ n.val) (hhi : n.val < 512) : n ∈ blockIDs1 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 256, by omega⟩, ?_, ?_⟩
  · exact (census1_spec _).mp (by
      have he : embed1 ⟨n.val - 256, by omega⟩ = n := by ext; simp [embed1]; all_goals omega
      simpa [he] using ht)
  · ext; simp [embed1]; all_goals omega

theorem block_terminal1 {n : Fin 5011} (hn : n ∈ blockIDs1) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census1_spec m).mpr hm

theorem blockIDs1_interval : blockIDs1 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 256 ≤ n.val ∧ n.val < 512) := by
  intro n hn
  have hu := blockIDs1_upper hn
  have hl := blockIDs1_lower hn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hl ⊢
  exact ⟨hl, hu⟩

def embed2 (n : Fin 256) : Fin 5011 := ⟨n.val + 512, by omega⟩
def census2 : Finset (Fin 256) :=
  Finset.univ.filter fun n => (DBMSourceTree.data (embed2 n)).terminal = true

theorem census2_spec (n : Fin 256) :
    (DBMSourceTree.data (embed2 n)).terminal = true ↔ n ∈ census2 := by
  simp only [census2, Finset.mem_filter, Finset.mem_univ, true_and]

theorem census2_card : census2.card = 69 := by
  decide +kernel

def blockIDs2 : Finset (Fin 5011) := census2.image embed2

theorem blockIDs2_card : blockIDs2.card = 69 := by
  rw [blockIDs2, Finset.card_image_of_injective _ ?_, census2_card]
  intro x y h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [embed2] at this ⊢
  omega

theorem blockIDs2_upper : blockIDs2 ⊆
    Finset.univ.filter (fun n : Fin 5011 => n.val < 768) := by
  intro n hn
  rw [blockIDs2, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed2]; all_goals omega
theorem blockIDs2_lower : blockIDs2 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 512 ≤ n.val) := by
  intro n hn
  rw [blockIDs2, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed2]; all_goals omega

theorem block_mem2 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 512 ≤ n.val) (hhi : n.val < 768) : n ∈ blockIDs2 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 512, by omega⟩, ?_, ?_⟩
  · exact (census2_spec _).mp (by
      have he : embed2 ⟨n.val - 512, by omega⟩ = n := by ext; simp [embed2]; all_goals omega
      simpa [he] using ht)
  · ext; simp [embed2]; all_goals omega

theorem block_terminal2 {n : Fin 5011} (hn : n ∈ blockIDs2) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census2_spec m).mpr hm

theorem blockIDs2_interval : blockIDs2 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 512 ≤ n.val ∧ n.val < 768) := by
  intro n hn
  have hu := blockIDs2_upper hn
  have hl := blockIDs2_lower hn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hl ⊢
  exact ⟨hl, hu⟩

def embed3 (n : Fin 256) : Fin 5011 := ⟨n.val + 768, by omega⟩
def census3 : Finset (Fin 256) :=
  Finset.univ.filter fun n => (DBMSourceTree.data (embed3 n)).terminal = true

theorem census3_spec (n : Fin 256) :
    (DBMSourceTree.data (embed3 n)).terminal = true ↔ n ∈ census3 := by
  simp only [census3, Finset.mem_filter, Finset.mem_univ, true_and]

theorem census3_card : census3.card = 62 := by
  decide +kernel

def blockIDs3 : Finset (Fin 5011) := census3.image embed3

theorem blockIDs3_card : blockIDs3.card = 62 := by
  rw [blockIDs3, Finset.card_image_of_injective _ ?_, census3_card]
  intro x y h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [embed3] at this ⊢
  omega

theorem blockIDs3_upper : blockIDs3 ⊆
    Finset.univ.filter (fun n : Fin 5011 => n.val < 1024) := by
  intro n hn
  rw [blockIDs3, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed3]; all_goals omega
theorem blockIDs3_lower : blockIDs3 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 768 ≤ n.val) := by
  intro n hn
  rw [blockIDs3, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed3]; all_goals omega

theorem block_mem3 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 768 ≤ n.val) (hhi : n.val < 1024) : n ∈ blockIDs3 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 768, by omega⟩, ?_, ?_⟩
  · exact (census3_spec _).mp (by
      have he : embed3 ⟨n.val - 768, by omega⟩ = n := by ext; simp [embed3]; all_goals omega
      simpa [he] using ht)
  · ext; simp [embed3]; all_goals omega

theorem block_terminal3 {n : Fin 5011} (hn : n ∈ blockIDs3) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census3_spec m).mpr hm

theorem blockIDs3_interval : blockIDs3 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 768 ≤ n.val ∧ n.val < 1024) := by
  intro n hn
  have hu := blockIDs3_upper hn
  have hl := blockIDs3_lower hn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hl ⊢
  exact ⟨hl, hu⟩

def embed4 (n : Fin 256) : Fin 5011 := ⟨n.val + 1024, by omega⟩
def census4 : Finset (Fin 256) :=
  Finset.univ.filter fun n => (DBMSourceTree.data (embed4 n)).terminal = true

theorem census4_spec (n : Fin 256) :
    (DBMSourceTree.data (embed4 n)).terminal = true ↔ n ∈ census4 := by
  simp only [census4, Finset.mem_filter, Finset.mem_univ, true_and]

theorem census4_card : census4.card = 62 := by
  decide +kernel

def blockIDs4 : Finset (Fin 5011) := census4.image embed4

theorem blockIDs4_card : blockIDs4.card = 62 := by
  rw [blockIDs4, Finset.card_image_of_injective _ ?_, census4_card]
  intro x y h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [embed4] at this ⊢
  omega

theorem blockIDs4_upper : blockIDs4 ⊆
    Finset.univ.filter (fun n : Fin 5011 => n.val < 1280) := by
  intro n hn
  rw [blockIDs4, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed4]; all_goals omega
theorem blockIDs4_lower : blockIDs4 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 1024 ≤ n.val) := by
  intro n hn
  rw [blockIDs4, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed4]; all_goals omega

theorem block_mem4 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 1024 ≤ n.val) (hhi : n.val < 1280) : n ∈ blockIDs4 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 1024, by omega⟩, ?_, ?_⟩
  · exact (census4_spec _).mp (by
      have he : embed4 ⟨n.val - 1024, by omega⟩ = n := by ext; simp [embed4]; all_goals omega
      simpa [he] using ht)
  · ext; simp [embed4]; all_goals omega

theorem block_terminal4 {n : Fin 5011} (hn : n ∈ blockIDs4) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census4_spec m).mpr hm

theorem blockIDs4_interval : blockIDs4 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 1024 ≤ n.val ∧ n.val < 1280) := by
  intro n hn
  have hu := blockIDs4_upper hn
  have hl := blockIDs4_lower hn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hl ⊢
  exact ⟨hl, hu⟩

def embed5 (n : Fin 256) : Fin 5011 := ⟨n.val + 1280, by omega⟩
def census5 : Finset (Fin 256) :=
  Finset.univ.filter fun n => (DBMSourceTree.data (embed5 n)).terminal = true

theorem census5_spec (n : Fin 256) :
    (DBMSourceTree.data (embed5 n)).terminal = true ↔ n ∈ census5 := by
  simp only [census5, Finset.mem_filter, Finset.mem_univ, true_and]

theorem census5_card : census5.card = 61 := by
  decide +kernel

def blockIDs5 : Finset (Fin 5011) := census5.image embed5

theorem blockIDs5_card : blockIDs5.card = 61 := by
  rw [blockIDs5, Finset.card_image_of_injective _ ?_, census5_card]
  intro x y h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [embed5] at this ⊢
  omega

theorem blockIDs5_upper : blockIDs5 ⊆
    Finset.univ.filter (fun n : Fin 5011 => n.val < 1536) := by
  intro n hn
  rw [blockIDs5, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed5]; all_goals omega
theorem blockIDs5_lower : blockIDs5 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 1280 ≤ n.val) := by
  intro n hn
  rw [blockIDs5, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed5]; all_goals omega

theorem block_mem5 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 1280 ≤ n.val) (hhi : n.val < 1536) : n ∈ blockIDs5 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 1280, by omega⟩, ?_, ?_⟩
  · exact (census5_spec _).mp (by
      have he : embed5 ⟨n.val - 1280, by omega⟩ = n := by ext; simp [embed5]; all_goals omega
      simpa [he] using ht)
  · ext; simp [embed5]; all_goals omega

theorem block_terminal5 {n : Fin 5011} (hn : n ∈ blockIDs5) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census5_spec m).mpr hm

theorem blockIDs5_interval : blockIDs5 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 1280 ≤ n.val ∧ n.val < 1536) := by
  intro n hn
  have hu := blockIDs5_upper hn
  have hl := blockIDs5_lower hn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hl ⊢
  exact ⟨hl, hu⟩

def embed6 (n : Fin 256) : Fin 5011 := ⟨n.val + 1536, by omega⟩
def census6 : Finset (Fin 256) :=
  Finset.univ.filter fun n => (DBMSourceTree.data (embed6 n)).terminal = true

theorem census6_spec (n : Fin 256) :
    (DBMSourceTree.data (embed6 n)).terminal = true ↔ n ∈ census6 := by
  simp only [census6, Finset.mem_filter, Finset.mem_univ, true_and]

theorem census6_card : census6.card = 55 := by
  decide +kernel

def blockIDs6 : Finset (Fin 5011) := census6.image embed6

theorem blockIDs6_card : blockIDs6.card = 55 := by
  rw [blockIDs6, Finset.card_image_of_injective _ ?_, census6_card]
  intro x y h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [embed6] at this ⊢
  omega

theorem blockIDs6_upper : blockIDs6 ⊆
    Finset.univ.filter (fun n : Fin 5011 => n.val < 1792) := by
  intro n hn
  rw [blockIDs6, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed6]; all_goals omega
theorem blockIDs6_lower : blockIDs6 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 1536 ≤ n.val) := by
  intro n hn
  rw [blockIDs6, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed6]; all_goals omega

theorem block_mem6 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 1536 ≤ n.val) (hhi : n.val < 1792) : n ∈ blockIDs6 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 1536, by omega⟩, ?_, ?_⟩
  · exact (census6_spec _).mp (by
      have he : embed6 ⟨n.val - 1536, by omega⟩ = n := by ext; simp [embed6]; all_goals omega
      simpa [he] using ht)
  · ext; simp [embed6]; all_goals omega

theorem block_terminal6 {n : Fin 5011} (hn : n ∈ blockIDs6) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census6_spec m).mpr hm

theorem blockIDs6_interval : blockIDs6 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 1536 ≤ n.val ∧ n.val < 1792) := by
  intro n hn
  have hu := blockIDs6_upper hn
  have hl := blockIDs6_lower hn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hl ⊢
  exact ⟨hl, hu⟩

def embed7 (n : Fin 256) : Fin 5011 := ⟨n.val + 1792, by omega⟩
def census7 : Finset (Fin 256) :=
  Finset.univ.filter fun n => (DBMSourceTree.data (embed7 n)).terminal = true

theorem census7_spec (n : Fin 256) :
    (DBMSourceTree.data (embed7 n)).terminal = true ↔ n ∈ census7 := by
  simp only [census7, Finset.mem_filter, Finset.mem_univ, true_and]

theorem census7_card : census7.card = 56 := by
  decide +kernel

def blockIDs7 : Finset (Fin 5011) := census7.image embed7

theorem blockIDs7_card : blockIDs7.card = 56 := by
  rw [blockIDs7, Finset.card_image_of_injective _ ?_, census7_card]
  intro x y h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [embed7] at this ⊢
  omega

theorem blockIDs7_upper : blockIDs7 ⊆
    Finset.univ.filter (fun n : Fin 5011 => n.val < 2048) := by
  intro n hn
  rw [blockIDs7, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed7]; all_goals omega
theorem blockIDs7_lower : blockIDs7 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 1792 ≤ n.val) := by
  intro n hn
  rw [blockIDs7, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed7]; all_goals omega

theorem block_mem7 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 1792 ≤ n.val) (hhi : n.val < 2048) : n ∈ blockIDs7 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 1792, by omega⟩, ?_, ?_⟩
  · exact (census7_spec _).mp (by
      have he : embed7 ⟨n.val - 1792, by omega⟩ = n := by ext; simp [embed7]; all_goals omega
      simpa [he] using ht)
  · ext; simp [embed7]; all_goals omega

theorem block_terminal7 {n : Fin 5011} (hn : n ∈ blockIDs7) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census7_spec m).mpr hm

theorem blockIDs7_interval : blockIDs7 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 1792 ≤ n.val ∧ n.val < 2048) := by
  intro n hn
  have hu := blockIDs7_upper hn
  have hl := blockIDs7_lower hn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hl ⊢
  exact ⟨hl, hu⟩

def embed8 (n : Fin 256) : Fin 5011 := ⟨n.val + 2048, by omega⟩
def census8 : Finset (Fin 256) :=
  Finset.univ.filter fun n => (DBMSourceTree.data (embed8 n)).terminal = true

theorem census8_spec (n : Fin 256) :
    (DBMSourceTree.data (embed8 n)).terminal = true ↔ n ∈ census8 := by
  simp only [census8, Finset.mem_filter, Finset.mem_univ, true_and]

theorem census8_card : census8.card = 66 := by
  decide +kernel

def blockIDs8 : Finset (Fin 5011) := census8.image embed8

theorem blockIDs8_card : blockIDs8.card = 66 := by
  rw [blockIDs8, Finset.card_image_of_injective _ ?_, census8_card]
  intro x y h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [embed8] at this ⊢
  omega

theorem blockIDs8_upper : blockIDs8 ⊆
    Finset.univ.filter (fun n : Fin 5011 => n.val < 2304) := by
  intro n hn
  rw [blockIDs8, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed8]; all_goals omega
theorem blockIDs8_lower : blockIDs8 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 2048 ≤ n.val) := by
  intro n hn
  rw [blockIDs8, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed8]; all_goals omega

theorem block_mem8 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 2048 ≤ n.val) (hhi : n.val < 2304) : n ∈ blockIDs8 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 2048, by omega⟩, ?_, ?_⟩
  · exact (census8_spec _).mp (by
      have he : embed8 ⟨n.val - 2048, by omega⟩ = n := by ext; simp [embed8]; all_goals omega
      simpa [he] using ht)
  · ext; simp [embed8]; all_goals omega

theorem block_terminal8 {n : Fin 5011} (hn : n ∈ blockIDs8) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census8_spec m).mpr hm

theorem blockIDs8_interval : blockIDs8 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 2048 ≤ n.val ∧ n.val < 2304) := by
  intro n hn
  have hu := blockIDs8_upper hn
  have hl := blockIDs8_lower hn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hl ⊢
  exact ⟨hl, hu⟩

def embed9 (n : Fin 256) : Fin 5011 := ⟨n.val + 2304, by omega⟩
def census9 : Finset (Fin 256) :=
  Finset.univ.filter fun n => (DBMSourceTree.data (embed9 n)).terminal = true

theorem census9_spec (n : Fin 256) :
    (DBMSourceTree.data (embed9 n)).terminal = true ↔ n ∈ census9 := by
  simp only [census9, Finset.mem_filter, Finset.mem_univ, true_and]

theorem census9_card : census9.card = 237 := by
  decide +kernel

def blockIDs9 : Finset (Fin 5011) := census9.image embed9

theorem blockIDs9_card : blockIDs9.card = 237 := by
  rw [blockIDs9, Finset.card_image_of_injective _ ?_, census9_card]
  intro x y h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [embed9] at this ⊢
  omega

theorem blockIDs9_upper : blockIDs9 ⊆
    Finset.univ.filter (fun n : Fin 5011 => n.val < 2560) := by
  intro n hn
  rw [blockIDs9, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed9]; all_goals omega
theorem blockIDs9_lower : blockIDs9 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 2304 ≤ n.val) := by
  intro n hn
  rw [blockIDs9, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed9]; all_goals omega

theorem block_mem9 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 2304 ≤ n.val) (hhi : n.val < 2560) : n ∈ blockIDs9 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 2304, by omega⟩, ?_, ?_⟩
  · exact (census9_spec _).mp (by
      have he : embed9 ⟨n.val - 2304, by omega⟩ = n := by ext; simp [embed9]; all_goals omega
      simpa [he] using ht)
  · ext; simp [embed9]; all_goals omega

theorem block_terminal9 {n : Fin 5011} (hn : n ∈ blockIDs9) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census9_spec m).mpr hm

theorem blockIDs9_interval : blockIDs9 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 2304 ≤ n.val ∧ n.val < 2560) := by
  intro n hn
  have hu := blockIDs9_upper hn
  have hl := blockIDs9_lower hn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hl ⊢
  exact ⟨hl, hu⟩

def embed10 (n : Fin 256) : Fin 5011 := ⟨n.val + 2560, by omega⟩
def census10 : Finset (Fin 256) :=
  Finset.univ.filter fun n => (DBMSourceTree.data (embed10 n)).terminal = true

theorem census10_spec (n : Fin 256) :
    (DBMSourceTree.data (embed10 n)).terminal = true ↔ n ∈ census10 := by
  simp only [census10, Finset.mem_filter, Finset.mem_univ, true_and]

theorem census10_card : census10.card = 254 := by
  decide +kernel

def blockIDs10 : Finset (Fin 5011) := census10.image embed10

theorem blockIDs10_card : blockIDs10.card = 254 := by
  rw [blockIDs10, Finset.card_image_of_injective _ ?_, census10_card]
  intro x y h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [embed10] at this ⊢
  omega

theorem blockIDs10_upper : blockIDs10 ⊆
    Finset.univ.filter (fun n : Fin 5011 => n.val < 2816) := by
  intro n hn
  rw [blockIDs10, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed10]; all_goals omega
theorem blockIDs10_lower : blockIDs10 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 2560 ≤ n.val) := by
  intro n hn
  rw [blockIDs10, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed10]; all_goals omega

theorem block_mem10 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 2560 ≤ n.val) (hhi : n.val < 2816) : n ∈ blockIDs10 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 2560, by omega⟩, ?_, ?_⟩
  · exact (census10_spec _).mp (by
      have he : embed10 ⟨n.val - 2560, by omega⟩ = n := by ext; simp [embed10]; all_goals omega
      simpa [he] using ht)
  · ext; simp [embed10]; all_goals omega

theorem block_terminal10 {n : Fin 5011} (hn : n ∈ blockIDs10) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census10_spec m).mpr hm

theorem blockIDs10_interval : blockIDs10 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 2560 ≤ n.val ∧ n.val < 2816) := by
  intro n hn
  have hu := blockIDs10_upper hn
  have hl := blockIDs10_lower hn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hl ⊢
  exact ⟨hl, hu⟩

def embed11 (n : Fin 256) : Fin 5011 := ⟨n.val + 2816, by omega⟩
def census11 : Finset (Fin 256) :=
  Finset.univ.filter fun n => (DBMSourceTree.data (embed11 n)).terminal = true

theorem census11_spec (n : Fin 256) :
    (DBMSourceTree.data (embed11 n)).terminal = true ↔ n ∈ census11 := by
  simp only [census11, Finset.mem_filter, Finset.mem_univ, true_and]

theorem census11_card : census11.card = 253 := by
  decide +kernel

def blockIDs11 : Finset (Fin 5011) := census11.image embed11

theorem blockIDs11_card : blockIDs11.card = 253 := by
  rw [blockIDs11, Finset.card_image_of_injective _ ?_, census11_card]
  intro x y h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [embed11] at this ⊢
  omega

theorem blockIDs11_upper : blockIDs11 ⊆
    Finset.univ.filter (fun n : Fin 5011 => n.val < 3072) := by
  intro n hn
  rw [blockIDs11, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed11]; all_goals omega
theorem blockIDs11_lower : blockIDs11 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 2816 ≤ n.val) := by
  intro n hn
  rw [blockIDs11, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed11]; all_goals omega

theorem block_mem11 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 2816 ≤ n.val) (hhi : n.val < 3072) : n ∈ blockIDs11 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 2816, by omega⟩, ?_, ?_⟩
  · exact (census11_spec _).mp (by
      have he : embed11 ⟨n.val - 2816, by omega⟩ = n := by ext; simp [embed11]; all_goals omega
      simpa [he] using ht)
  · ext; simp [embed11]; all_goals omega

theorem block_terminal11 {n : Fin 5011} (hn : n ∈ blockIDs11) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census11_spec m).mpr hm

theorem blockIDs11_interval : blockIDs11 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 2816 ≤ n.val ∧ n.val < 3072) := by
  intro n hn
  have hu := blockIDs11_upper hn
  have hl := blockIDs11_lower hn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hl ⊢
  exact ⟨hl, hu⟩

def embed12 (n : Fin 256) : Fin 5011 := ⟨n.val + 3072, by omega⟩
def census12 : Finset (Fin 256) :=
  Finset.univ.filter fun n => (DBMSourceTree.data (embed12 n)).terminal = true

theorem census12_spec (n : Fin 256) :
    (DBMSourceTree.data (embed12 n)).terminal = true ↔ n ∈ census12 := by
  simp only [census12, Finset.mem_filter, Finset.mem_univ, true_and]

theorem census12_card : census12.card = 255 := by
  decide +kernel

def blockIDs12 : Finset (Fin 5011) := census12.image embed12

theorem blockIDs12_card : blockIDs12.card = 255 := by
  rw [blockIDs12, Finset.card_image_of_injective _ ?_, census12_card]
  intro x y h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [embed12] at this ⊢
  omega

theorem blockIDs12_upper : blockIDs12 ⊆
    Finset.univ.filter (fun n : Fin 5011 => n.val < 3328) := by
  intro n hn
  rw [blockIDs12, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed12]; all_goals omega
theorem blockIDs12_lower : blockIDs12 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 3072 ≤ n.val) := by
  intro n hn
  rw [blockIDs12, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed12]; all_goals omega

theorem block_mem12 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 3072 ≤ n.val) (hhi : n.val < 3328) : n ∈ blockIDs12 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 3072, by omega⟩, ?_, ?_⟩
  · exact (census12_spec _).mp (by
      have he : embed12 ⟨n.val - 3072, by omega⟩ = n := by ext; simp [embed12]; all_goals omega
      simpa [he] using ht)
  · ext; simp [embed12]; all_goals omega

theorem block_terminal12 {n : Fin 5011} (hn : n ∈ blockIDs12) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census12_spec m).mpr hm

theorem blockIDs12_interval : blockIDs12 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 3072 ≤ n.val ∧ n.val < 3328) := by
  intro n hn
  have hu := blockIDs12_upper hn
  have hl := blockIDs12_lower hn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hl ⊢
  exact ⟨hl, hu⟩

def embed13 (n : Fin 256) : Fin 5011 := ⟨n.val + 3328, by omega⟩
def census13 : Finset (Fin 256) :=
  Finset.univ.filter fun n => (DBMSourceTree.data (embed13 n)).terminal = true

theorem census13_spec (n : Fin 256) :
    (DBMSourceTree.data (embed13 n)).terminal = true ↔ n ∈ census13 := by
  simp only [census13, Finset.mem_filter, Finset.mem_univ, true_and]

theorem census13_card : census13.card = 221 := by
  decide +kernel

def blockIDs13 : Finset (Fin 5011) := census13.image embed13

theorem blockIDs13_card : blockIDs13.card = 221 := by
  rw [blockIDs13, Finset.card_image_of_injective _ ?_, census13_card]
  intro x y h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [embed13] at this ⊢
  omega

theorem blockIDs13_upper : blockIDs13 ⊆
    Finset.univ.filter (fun n : Fin 5011 => n.val < 3584) := by
  intro n hn
  rw [blockIDs13, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed13]; all_goals omega
theorem blockIDs13_lower : blockIDs13 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 3328 ≤ n.val) := by
  intro n hn
  rw [blockIDs13, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed13]; all_goals omega

theorem block_mem13 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 3328 ≤ n.val) (hhi : n.val < 3584) : n ∈ blockIDs13 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 3328, by omega⟩, ?_, ?_⟩
  · exact (census13_spec _).mp (by
      have he : embed13 ⟨n.val - 3328, by omega⟩ = n := by ext; simp [embed13]; all_goals omega
      simpa [he] using ht)
  · ext; simp [embed13]; all_goals omega

theorem block_terminal13 {n : Fin 5011} (hn : n ∈ blockIDs13) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census13_spec m).mpr hm

theorem blockIDs13_interval : blockIDs13 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 3328 ≤ n.val ∧ n.val < 3584) := by
  intro n hn
  have hu := blockIDs13_upper hn
  have hl := blockIDs13_lower hn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hl ⊢
  exact ⟨hl, hu⟩

def embed14 (n : Fin 256) : Fin 5011 := ⟨n.val + 3584, by omega⟩
def census14 : Finset (Fin 256) :=
  Finset.univ.filter fun n => (DBMSourceTree.data (embed14 n)).terminal = true

theorem census14_spec (n : Fin 256) :
    (DBMSourceTree.data (embed14 n)).terminal = true ↔ n ∈ census14 := by
  simp only [census14, Finset.mem_filter, Finset.mem_univ, true_and]

theorem census14_card : census14.card = 115 := by
  decide +kernel

def blockIDs14 : Finset (Fin 5011) := census14.image embed14

theorem blockIDs14_card : blockIDs14.card = 115 := by
  rw [blockIDs14, Finset.card_image_of_injective _ ?_, census14_card]
  intro x y h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [embed14] at this ⊢
  omega

theorem blockIDs14_upper : blockIDs14 ⊆
    Finset.univ.filter (fun n : Fin 5011 => n.val < 3840) := by
  intro n hn
  rw [blockIDs14, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed14]; all_goals omega
theorem blockIDs14_lower : blockIDs14 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 3584 ≤ n.val) := by
  intro n hn
  rw [blockIDs14, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed14]; all_goals omega

theorem block_mem14 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 3584 ≤ n.val) (hhi : n.val < 3840) : n ∈ blockIDs14 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 3584, by omega⟩, ?_, ?_⟩
  · exact (census14_spec _).mp (by
      have he : embed14 ⟨n.val - 3584, by omega⟩ = n := by ext; simp [embed14]; all_goals omega
      simpa [he] using ht)
  · ext; simp [embed14]; all_goals omega

theorem block_terminal14 {n : Fin 5011} (hn : n ∈ blockIDs14) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census14_spec m).mpr hm

theorem blockIDs14_interval : blockIDs14 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 3584 ≤ n.val ∧ n.val < 3840) := by
  intro n hn
  have hu := blockIDs14_upper hn
  have hl := blockIDs14_lower hn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hl ⊢
  exact ⟨hl, hu⟩

def embed15 (n : Fin 256) : Fin 5011 := ⟨n.val + 3840, by omega⟩
def census15 : Finset (Fin 256) :=
  Finset.univ.filter fun n => (DBMSourceTree.data (embed15 n)).terminal = true

theorem census15_spec (n : Fin 256) :
    (DBMSourceTree.data (embed15 n)).terminal = true ↔ n ∈ census15 := by
  simp only [census15, Finset.mem_filter, Finset.mem_univ, true_and]

theorem census15_card : census15.card = 120 := by
  decide +kernel

def blockIDs15 : Finset (Fin 5011) := census15.image embed15

theorem blockIDs15_card : blockIDs15.card = 120 := by
  rw [blockIDs15, Finset.card_image_of_injective _ ?_, census15_card]
  intro x y h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [embed15] at this ⊢
  omega

theorem blockIDs15_upper : blockIDs15 ⊆
    Finset.univ.filter (fun n : Fin 5011 => n.val < 4096) := by
  intro n hn
  rw [blockIDs15, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed15]; all_goals omega
theorem blockIDs15_lower : blockIDs15 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 3840 ≤ n.val) := by
  intro n hn
  rw [blockIDs15, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed15]; all_goals omega

theorem block_mem15 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 3840 ≤ n.val) (hhi : n.val < 4096) : n ∈ blockIDs15 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 3840, by omega⟩, ?_, ?_⟩
  · exact (census15_spec _).mp (by
      have he : embed15 ⟨n.val - 3840, by omega⟩ = n := by ext; simp [embed15]; all_goals omega
      simpa [he] using ht)
  · ext; simp [embed15]; all_goals omega

theorem block_terminal15 {n : Fin 5011} (hn : n ∈ blockIDs15) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census15_spec m).mpr hm

theorem blockIDs15_interval : blockIDs15 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 3840 ≤ n.val ∧ n.val < 4096) := by
  intro n hn
  have hu := blockIDs15_upper hn
  have hl := blockIDs15_lower hn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hl ⊢
  exact ⟨hl, hu⟩

def embed16 (n : Fin 256) : Fin 5011 := ⟨n.val + 4096, by omega⟩
def census16 : Finset (Fin 256) :=
  Finset.univ.filter fun n => (DBMSourceTree.data (embed16 n)).terminal = true

theorem census16_spec (n : Fin 256) :
    (DBMSourceTree.data (embed16 n)).terminal = true ↔ n ∈ census16 := by
  simp only [census16, Finset.mem_filter, Finset.mem_univ, true_and]

theorem census16_card : census16.card = 108 := by
  decide +kernel

def blockIDs16 : Finset (Fin 5011) := census16.image embed16

theorem blockIDs16_card : blockIDs16.card = 108 := by
  rw [blockIDs16, Finset.card_image_of_injective _ ?_, census16_card]
  intro x y h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [embed16] at this ⊢
  omega

theorem blockIDs16_upper : blockIDs16 ⊆
    Finset.univ.filter (fun n : Fin 5011 => n.val < 4352) := by
  intro n hn
  rw [blockIDs16, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed16]; all_goals omega
theorem blockIDs16_lower : blockIDs16 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 4096 ≤ n.val) := by
  intro n hn
  rw [blockIDs16, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed16]; all_goals omega

theorem block_mem16 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 4096 ≤ n.val) (hhi : n.val < 4352) : n ∈ blockIDs16 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 4096, by omega⟩, ?_, ?_⟩
  · exact (census16_spec _).mp (by
      have he : embed16 ⟨n.val - 4096, by omega⟩ = n := by ext; simp [embed16]; all_goals omega
      simpa [he] using ht)
  · ext; simp [embed16]; all_goals omega

theorem block_terminal16 {n : Fin 5011} (hn : n ∈ blockIDs16) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census16_spec m).mpr hm

theorem blockIDs16_interval : blockIDs16 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 4096 ≤ n.val ∧ n.val < 4352) := by
  intro n hn
  have hu := blockIDs16_upper hn
  have hl := blockIDs16_lower hn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hl ⊢
  exact ⟨hl, hu⟩

def embed17 (n : Fin 256) : Fin 5011 := ⟨n.val + 4352, by omega⟩
def census17 : Finset (Fin 256) :=
  Finset.univ.filter fun n => (DBMSourceTree.data (embed17 n)).terminal = true

theorem census17_spec (n : Fin 256) :
    (DBMSourceTree.data (embed17 n)).terminal = true ↔ n ∈ census17 := by
  simp only [census17, Finset.mem_filter, Finset.mem_univ, true_and]

theorem census17_card : census17.card = 111 := by
  decide +kernel

def blockIDs17 : Finset (Fin 5011) := census17.image embed17

theorem blockIDs17_card : blockIDs17.card = 111 := by
  rw [blockIDs17, Finset.card_image_of_injective _ ?_, census17_card]
  intro x y h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [embed17] at this ⊢
  omega

theorem blockIDs17_upper : blockIDs17 ⊆
    Finset.univ.filter (fun n : Fin 5011 => n.val < 4608) := by
  intro n hn
  rw [blockIDs17, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed17]; all_goals omega
theorem blockIDs17_lower : blockIDs17 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 4352 ≤ n.val) := by
  intro n hn
  rw [blockIDs17, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed17]; all_goals omega

theorem block_mem17 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 4352 ≤ n.val) (hhi : n.val < 4608) : n ∈ blockIDs17 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 4352, by omega⟩, ?_, ?_⟩
  · exact (census17_spec _).mp (by
      have he : embed17 ⟨n.val - 4352, by omega⟩ = n := by ext; simp [embed17]; all_goals omega
      simpa [he] using ht)
  · ext; simp [embed17]; all_goals omega

theorem block_terminal17 {n : Fin 5011} (hn : n ∈ blockIDs17) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census17_spec m).mpr hm

theorem blockIDs17_interval : blockIDs17 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 4352 ≤ n.val ∧ n.val < 4608) := by
  intro n hn
  have hu := blockIDs17_upper hn
  have hl := blockIDs17_lower hn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hl ⊢
  exact ⟨hl, hu⟩

def embed18 (n : Fin 256) : Fin 5011 := ⟨n.val + 4608, by omega⟩
def census18 : Finset (Fin 256) :=
  Finset.univ.filter fun n => (DBMSourceTree.data (embed18 n)).terminal = true

theorem census18_spec (n : Fin 256) :
    (DBMSourceTree.data (embed18 n)).terminal = true ↔ n ∈ census18 := by
  simp only [census18, Finset.mem_filter, Finset.mem_univ, true_and]

theorem census18_card : census18.card = 150 := by
  decide +kernel

def blockIDs18 : Finset (Fin 5011) := census18.image embed18

theorem blockIDs18_card : blockIDs18.card = 150 := by
  rw [blockIDs18, Finset.card_image_of_injective _ ?_, census18_card]
  intro x y h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [embed18] at this ⊢
  omega

theorem blockIDs18_upper : blockIDs18 ⊆
    Finset.univ.filter (fun n : Fin 5011 => n.val < 4864) := by
  intro n hn
  rw [blockIDs18, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed18]; all_goals omega
theorem blockIDs18_lower : blockIDs18 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 4608 ≤ n.val) := by
  intro n hn
  rw [blockIDs18, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed18]; all_goals omega

theorem block_mem18 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 4608 ≤ n.val) (hhi : n.val < 4864) : n ∈ blockIDs18 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 4608, by omega⟩, ?_, ?_⟩
  · exact (census18_spec _).mp (by
      have he : embed18 ⟨n.val - 4608, by omega⟩ = n := by ext; simp [embed18]; all_goals omega
      simpa [he] using ht)
  · ext; simp [embed18]; all_goals omega

theorem block_terminal18 {n : Fin 5011} (hn : n ∈ blockIDs18) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census18_spec m).mpr hm

theorem blockIDs18_interval : blockIDs18 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 4608 ≤ n.val ∧ n.val < 4864) := by
  intro n hn
  have hu := blockIDs18_upper hn
  have hl := blockIDs18_lower hn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu hl ⊢
  exact ⟨hl, hu⟩

def embed19 (n : Fin 147) : Fin 5011 := ⟨n.val + 4864, by omega⟩
def census19 : Finset (Fin 147) :=
  Finset.univ.filter fun n => (DBMSourceTree.data (embed19 n)).terminal = true

theorem census19_spec (n : Fin 147) :
    (DBMSourceTree.data (embed19 n)).terminal = true ↔ n ∈ census19 := by
  simp only [census19, Finset.mem_filter, Finset.mem_univ, true_and]

theorem census19_card : census19.card = 115 := by
  decide +kernel

def blockIDs19 : Finset (Fin 5011) := census19.image embed19

theorem blockIDs19_card : blockIDs19.card = 115 := by
  rw [blockIDs19, Finset.card_image_of_injective _ ?_, census19_card]
  intro x y h
  apply Fin.ext
  have := congrArg Fin.val h
  simp [embed19] at this ⊢
  omega

theorem blockIDs19_lower : blockIDs19 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 4864 ≤ n.val) := by
  intro n hn
  rw [blockIDs19, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed19]; all_goals omega

theorem block_mem19 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 4864 ≤ n.val) (hhi : n.val < 5011) : n ∈ blockIDs19 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 4864, by omega⟩, ?_, ?_⟩
  · exact (census19_spec _).mp (by
      have he : embed19 ⟨n.val - 4864, by omega⟩ = n := by ext; simp [embed19]; all_goals omega
      simpa [he] using ht)
  · ext; simp [embed19]; all_goals omega

theorem block_terminal19 {n : Fin 5011} (hn : n ∈ blockIDs19) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census19_spec m).mpr hm

theorem blockIDs19_interval : blockIDs19 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 4864 ≤ n.val ∧ n.val < 5120) := by
  intro n hn
  have hl := blockIDs19_lower hn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
  exact ⟨hl, by omega⟩

def blockIDs : Fin 20 → Finset (Fin 5011) := ![blockIDs0,
    blockIDs1,
    blockIDs2,
    blockIDs3,
    blockIDs4,
    blockIDs5,
    blockIDs6,
    blockIDs7,
    blockIDs8,
    blockIDs9,
    blockIDs10,
    blockIDs11,
    blockIDs12,
    blockIDs13,
    blockIDs14,
    blockIDs15,
    blockIDs16,
    blockIDs17,
    blockIDs18,
    blockIDs19]

theorem blockIDs_interval (i : Fin 20) :
    blockIDs i ⊆ Finset.univ.filter
      (fun n : Fin 5011 => i.val * 256 ≤ n.val ∧ n.val < i.val * 256 + 256) := by
  fin_cases i
  · simpa [blockIDs] using blockIDs0_interval
  · simpa [blockIDs] using blockIDs1_interval
  · simpa [blockIDs] using blockIDs2_interval
  · simpa [blockIDs] using blockIDs3_interval
  · simpa [blockIDs] using blockIDs4_interval
  · simpa [blockIDs] using blockIDs5_interval
  · simpa [blockIDs] using blockIDs6_interval
  · simpa [blockIDs] using blockIDs7_interval
  · simpa [blockIDs] using blockIDs8_interval
  · simpa [blockIDs] using blockIDs9_interval
  · simpa [blockIDs] using blockIDs10_interval
  · simpa [blockIDs] using blockIDs11_interval
  · simpa [blockIDs] using blockIDs12_interval
  · simpa [blockIDs] using blockIDs13_interval
  · simpa [blockIDs] using blockIDs14_interval
  · simpa [blockIDs] using blockIDs15_interval
  · simpa [blockIDs] using blockIDs16_interval
  · simpa [blockIDs] using blockIDs17_interval
  · simpa [blockIDs] using blockIDs18_interval
  · simpa [blockIDs] using blockIDs19_interval

def censusIDs : Finset (Fin 5011) := Finset.univ.biUnion blockIDs

theorem terminalIDs_eq_censusIDs : terminalIDs = censusIDs := by
  ext n
  constructor
  · intro hn
    simp only [terminalIDs, Finset.mem_filter, Finset.mem_univ, true_and] at hn
    by_cases h0 : n.val < 256
    · rw [censusIDs, Finset.mem_biUnion]
      refine ⟨⟨0, by decide⟩, Finset.mem_univ _, ?_⟩
      simpa [blockIDs] using block_mem0 hn (by omega) h0
    by_cases h1 : n.val < 512
    · rw [censusIDs, Finset.mem_biUnion]
      refine ⟨⟨1, by decide⟩, Finset.mem_univ _, ?_⟩
      simpa [blockIDs] using block_mem1 hn (by omega) h1
    by_cases h2 : n.val < 768
    · rw [censusIDs, Finset.mem_biUnion]
      refine ⟨⟨2, by decide⟩, Finset.mem_univ _, ?_⟩
      simpa [blockIDs] using block_mem2 hn (by omega) h2
    by_cases h3 : n.val < 1024
    · rw [censusIDs, Finset.mem_biUnion]
      refine ⟨⟨3, by decide⟩, Finset.mem_univ _, ?_⟩
      simpa [blockIDs] using block_mem3 hn (by omega) h3
    by_cases h4 : n.val < 1280
    · rw [censusIDs, Finset.mem_biUnion]
      refine ⟨⟨4, by decide⟩, Finset.mem_univ _, ?_⟩
      simpa [blockIDs] using block_mem4 hn (by omega) h4
    by_cases h5 : n.val < 1536
    · rw [censusIDs, Finset.mem_biUnion]
      refine ⟨⟨5, by decide⟩, Finset.mem_univ _, ?_⟩
      simpa [blockIDs] using block_mem5 hn (by omega) h5
    by_cases h6 : n.val < 1792
    · rw [censusIDs, Finset.mem_biUnion]
      refine ⟨⟨6, by decide⟩, Finset.mem_univ _, ?_⟩
      simpa [blockIDs] using block_mem6 hn (by omega) h6
    by_cases h7 : n.val < 2048
    · rw [censusIDs, Finset.mem_biUnion]
      refine ⟨⟨7, by decide⟩, Finset.mem_univ _, ?_⟩
      simpa [blockIDs] using block_mem7 hn (by omega) h7
    by_cases h8 : n.val < 2304
    · rw [censusIDs, Finset.mem_biUnion]
      refine ⟨⟨8, by decide⟩, Finset.mem_univ _, ?_⟩
      simpa [blockIDs] using block_mem8 hn (by omega) h8
    by_cases h9 : n.val < 2560
    · rw [censusIDs, Finset.mem_biUnion]
      refine ⟨⟨9, by decide⟩, Finset.mem_univ _, ?_⟩
      simpa [blockIDs] using block_mem9 hn (by omega) h9
    by_cases h10 : n.val < 2816
    · rw [censusIDs, Finset.mem_biUnion]
      refine ⟨⟨10, by decide⟩, Finset.mem_univ _, ?_⟩
      simpa [blockIDs] using block_mem10 hn (by omega) h10
    by_cases h11 : n.val < 3072
    · rw [censusIDs, Finset.mem_biUnion]
      refine ⟨⟨11, by decide⟩, Finset.mem_univ _, ?_⟩
      simpa [blockIDs] using block_mem11 hn (by omega) h11
    by_cases h12 : n.val < 3328
    · rw [censusIDs, Finset.mem_biUnion]
      refine ⟨⟨12, by decide⟩, Finset.mem_univ _, ?_⟩
      simpa [blockIDs] using block_mem12 hn (by omega) h12
    by_cases h13 : n.val < 3584
    · rw [censusIDs, Finset.mem_biUnion]
      refine ⟨⟨13, by decide⟩, Finset.mem_univ _, ?_⟩
      simpa [blockIDs] using block_mem13 hn (by omega) h13
    by_cases h14 : n.val < 3840
    · rw [censusIDs, Finset.mem_biUnion]
      refine ⟨⟨14, by decide⟩, Finset.mem_univ _, ?_⟩
      simpa [blockIDs] using block_mem14 hn (by omega) h14
    by_cases h15 : n.val < 4096
    · rw [censusIDs, Finset.mem_biUnion]
      refine ⟨⟨15, by decide⟩, Finset.mem_univ _, ?_⟩
      simpa [blockIDs] using block_mem15 hn (by omega) h15
    by_cases h16 : n.val < 4352
    · rw [censusIDs, Finset.mem_biUnion]
      refine ⟨⟨16, by decide⟩, Finset.mem_univ _, ?_⟩
      simpa [blockIDs] using block_mem16 hn (by omega) h16
    by_cases h17 : n.val < 4608
    · rw [censusIDs, Finset.mem_biUnion]
      refine ⟨⟨17, by decide⟩, Finset.mem_univ _, ?_⟩
      simpa [blockIDs] using block_mem17 hn (by omega) h17
    by_cases h18 : n.val < 4864
    · rw [censusIDs, Finset.mem_biUnion]
      refine ⟨⟨18, by decide⟩, Finset.mem_univ _, ?_⟩
      simpa [blockIDs] using block_mem18 hn (by omega) h18
    by_cases h19 : n.val < 5011
    · rw [censusIDs, Finset.mem_biUnion]
      refine ⟨⟨19, by decide⟩, Finset.mem_univ _, ?_⟩
      simpa [blockIDs] using block_mem19 hn (by omega) h19
    · omega
  · intro hn
    rw [censusIDs, Finset.mem_biUnion] at hn
    rcases hn with ⟨i, _, hi⟩
    fin_cases i
    · exact block_terminal0 hi
    · exact block_terminal1 hi
    · exact block_terminal2 hi
    · exact block_terminal3 hi
    · exact block_terminal4 hi
    · exact block_terminal5 hi
    · exact block_terminal6 hi
    · exact block_terminal7 hi
    · exact block_terminal8 hi
    · exact block_terminal9 hi
    · exact block_terminal10 hi
    · exact block_terminal11 hi
    · exact block_terminal12 hi
    · exact block_terminal13 hi
    · exact block_terminal14 hi
    · exact block_terminal15 hi
    · exact block_terminal16 hi
    · exact block_terminal17 hi
    · exact block_terminal18 hi
    · exact block_terminal19 hi

theorem blockIDs_pairwiseDisjoint :
    ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, i ≠ j → Disjoint (blockIDs i) (blockIDs j) := by
  intro i _ j _ hij
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs_interval i hi
  have hj' := blockIDs_interval j hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  have hvals : i.val < j.val ∨ j.val < i.val := by
    have hne : i.val ≠ j.val := by
      intro h
      exact hij (Fin.ext h)
    exact Nat.lt_or_gt_of_ne hne
  omega

def blockSizes : Fin 20 → Nat := ![61, 75, 69, 62, 62, 61, 55, 56, 66, 237, 254, 253, 255, 221, 115, 120, 108, 111, 150, 115]

theorem blockIDs_card_eq (i : Fin 20) : (blockIDs i).card = blockSizes i := by
  fin_cases i
  · simpa [blockIDs, blockSizes] using blockIDs0_card
  · simpa [blockIDs, blockSizes] using blockIDs1_card
  · simpa [blockIDs, blockSizes] using blockIDs2_card
  · simpa [blockIDs, blockSizes] using blockIDs3_card
  · simpa [blockIDs, blockSizes] using blockIDs4_card
  · simpa [blockIDs, blockSizes] using blockIDs5_card
  · simpa [blockIDs, blockSizes] using blockIDs6_card
  · simpa [blockIDs, blockSizes] using blockIDs7_card
  · simpa [blockIDs, blockSizes] using blockIDs8_card
  · simpa [blockIDs, blockSizes] using blockIDs9_card
  · simpa [blockIDs, blockSizes] using blockIDs10_card
  · simpa [blockIDs, blockSizes] using blockIDs11_card
  · simpa [blockIDs, blockSizes] using blockIDs12_card
  · simpa [blockIDs, blockSizes] using blockIDs13_card
  · simpa [blockIDs, blockSizes] using blockIDs14_card
  · simpa [blockIDs, blockSizes] using blockIDs15_card
  · simpa [blockIDs, blockSizes] using blockIDs16_card
  · simpa [blockIDs, blockSizes] using blockIDs17_card
  · simpa [blockIDs, blockSizes] using blockIDs18_card
  · simpa [blockIDs, blockSizes] using blockIDs19_card

theorem blockSizes_sum : (∑ i : Fin 20, blockSizes i) = 2506 := by
  decide +kernel

theorem censusIDs_card_aux : (∑ i : Fin 20, (blockIDs i).card) = 2506 := by
  calc
    (∑ i : Fin 20, (blockIDs i).card) = ∑ i : Fin 20, blockSizes i := by
      apply Finset.sum_congr rfl
      intro i _
      exact blockIDs_card_eq i
    _ = 2506 := blockSizes_sum

theorem censusIDs_card : censusIDs.card = 2506 := by
  rw [censusIDs, Finset.card_biUnion blockIDs_pairwiseDisjoint]
  simpa using censusIDs_card_aux

theorem terminalIDs_card : terminalIDs.card = 2506 := by
  rw [terminalIDs_eq_censusIDs, censusIDs_card]

end
end N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual
