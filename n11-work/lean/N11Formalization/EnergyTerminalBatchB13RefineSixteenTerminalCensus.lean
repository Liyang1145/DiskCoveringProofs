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
def census0 : Finset (Fin 256) := {
  ⟨3, by decide⟩, ⟨5, by decide⟩, ⟨9, by decide⟩, ⟨23, by decide⟩, ⟨32, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨74, by decide⟩, ⟨79, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨85, by decide⟩, ⟨91, by decide⟩, ⟨101, by decide⟩, ⟨104, by decide⟩, ⟨106, by decide⟩, ⟨109, by decide⟩, ⟨111, by decide⟩, ⟨115, by decide⟩, ⟨126, by decide⟩, ⟨127, by decide⟩, ⟨142, by decide⟩, ⟨150, by decide⟩, ⟨152, by decide⟩, ⟨154, by decide⟩, ⟨155, by decide⟩, ⟨158, by decide⟩, ⟨160, by decide⟩, ⟨165, by decide⟩, ⟨167, by decide⟩, ⟨170, by decide⟩, ⟨182, by decide⟩, ⟨189, by decide⟩, ⟨191, by decide⟩, ⟨198, by decide⟩, ⟨213, by decide⟩, ⟨216, by decide⟩, ⟨217, by decide⟩, ⟨230, by decide⟩, ⟨231, by decide⟩, ⟨233, by decide⟩, ⟨236, by decide⟩, ⟨238, by decide⟩, ⟨240, by decide⟩, ⟨241, by decide⟩, ⟨246, by decide⟩, ⟨249, by decide⟩, ⟨252, by decide⟩
}

theorem census0_spec (n : Fin 256) :
    (DBMSourceTree.data (embed0 n)).terminal = true ↔ n ∈ census0 := by
  decide +kernel

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
  simp [embed0]
theorem blockIDs0_lower : blockIDs0 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 0 ≤ n.val) := by
  intro n hn
  rw [blockIDs0, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed0]

theorem block_mem0 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 0 ≤ n.val) (hhi : n.val < 256) : n ∈ blockIDs0 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 0, by omega⟩, ?_, ?_⟩
  · exact (census0_spec _).mp (by
      have he : embed0 ⟨n.val - 0, by omega⟩ = n := by ext; simp [embed0]; omega
      simpa [he] using ht)
  · ext; simp [embed0]; omega

theorem block_terminal0 {n : Fin 5011} (hn : n ∈ blockIDs0) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census0_spec m).mpr hm

def embed1 (n : Fin 256) : Fin 5011 := ⟨n.val + 256, by omega⟩
def census1 : Finset (Fin 256) := {
  ⟨1, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨17, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨50, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨66, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨80, by decide⟩, ⟨83, by decide⟩, ⟨85, by decide⟩, ⟨91, by decide⟩, ⟨100, by decide⟩, ⟨103, by decide⟩, ⟨105, by decide⟩, ⟨107, by decide⟩, ⟨109, by decide⟩, ⟨112, by decide⟩, ⟨115, by decide⟩, ⟨117, by decide⟩, ⟨119, by decide⟩, ⟨120, by decide⟩, ⟨123, by decide⟩, ⟨126, by decide⟩, ⟨127, by decide⟩, ⟨132, by decide⟩, ⟨136, by decide⟩, ⟨142, by decide⟩, ⟨143, by decide⟩, ⟨155, by decide⟩, ⟨160, by decide⟩, ⟨162, by decide⟩, ⟨164, by decide⟩, ⟨166, by decide⟩, ⟨168, by decide⟩, ⟨177, by decide⟩, ⟨181, by decide⟩, ⟨183, by decide⟩, ⟨188, by decide⟩, ⟨190, by decide⟩, ⟨191, by decide⟩, ⟨194, by decide⟩, ⟨196, by decide⟩, ⟨198, by decide⟩, ⟨200, by decide⟩, ⟨201, by decide⟩, ⟨204, by decide⟩, ⟨209, by decide⟩, ⟨210, by decide⟩, ⟨227, by decide⟩, ⟨229, by decide⟩, ⟨232, by decide⟩, ⟨234, by decide⟩, ⟨235, by decide⟩, ⟨236, by decide⟩, ⟨237, by decide⟩, ⟨243, by decide⟩, ⟨246, by decide⟩, ⟨248, by decide⟩, ⟨254, by decide⟩
}

theorem census1_spec (n : Fin 256) :
    (DBMSourceTree.data (embed1 n)).terminal = true ↔ n ∈ census1 := by
  decide +kernel

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
  simp [embed1]
theorem blockIDs1_lower : blockIDs1 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 256 ≤ n.val) := by
  intro n hn
  rw [blockIDs1, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed1]

theorem block_mem1 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 256 ≤ n.val) (hhi : n.val < 512) : n ∈ blockIDs1 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 256, by omega⟩, ?_, ?_⟩
  · exact (census1_spec _).mp (by
      have he : embed1 ⟨n.val - 256, by omega⟩ = n := by ext; simp [embed1]; omega
      simpa [he] using ht)
  · ext; simp [embed1]; omega

theorem block_terminal1 {n : Fin 5011} (hn : n ∈ blockIDs1) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census1_spec m).mpr hm

def embed2 (n : Fin 256) : Fin 5011 := ⟨n.val + 512, by omega⟩
def census2 : Finset (Fin 256) := {
  ⟨0, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨22, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨50, by decide⟩, ⟨53, by decide⟩, ⟨56, by decide⟩, ⟨60, by decide⟩, ⟨65, by decide⟩, ⟨75, by decide⟩, ⟨79, by decide⟩, ⟨94, by decide⟩, ⟨96, by decide⟩, ⟨103, by decide⟩, ⟨106, by decide⟩, ⟨110, by decide⟩, ⟨112, by decide⟩, ⟨113, by decide⟩, ⟨128, by decide⟩, ⟨129, by decide⟩, ⟨134, by decide⟩, ⟨135, by decide⟩, ⟨138, by decide⟩, ⟨139, by decide⟩, ⟨141, by decide⟩, ⟨144, by decide⟩, ⟨146, by decide⟩, ⟨148, by decide⟩, ⟨152, by decide⟩, ⟨154, by decide⟩, ⟨158, by decide⟩, ⟨159, by decide⟩, ⟨165, by decide⟩, ⟨167, by decide⟩, ⟨172, by decide⟩, ⟨174, by decide⟩, ⟨175, by decide⟩, ⟨181, by decide⟩, ⟨189, by decide⟩, ⟨192, by decide⟩, ⟨194, by decide⟩, ⟨196, by decide⟩, ⟨198, by decide⟩, ⟨200, by decide⟩, ⟨203, by decide⟩, ⟨204, by decide⟩, ⟨206, by decide⟩, ⟨208, by decide⟩, ⟨209, by decide⟩, ⟨213, by decide⟩, ⟨215, by decide⟩, ⟨217, by decide⟩, ⟨219, by decide⟩, ⟨221, by decide⟩, ⟨224, by decide⟩, ⟨225, by decide⟩, ⟨228, by decide⟩, ⟨229, by decide⟩, ⟨232, by decide⟩, ⟨234, by decide⟩, ⟨236, by decide⟩, ⟨238, by decide⟩, ⟨243, by decide⟩, ⟨249, by decide⟩, ⟨253, by decide⟩
}

theorem census2_spec (n : Fin 256) :
    (DBMSourceTree.data (embed2 n)).terminal = true ↔ n ∈ census2 := by
  decide +kernel

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
  simp [embed2]
theorem blockIDs2_lower : blockIDs2 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 512 ≤ n.val) := by
  intro n hn
  rw [blockIDs2, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed2]

theorem block_mem2 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 512 ≤ n.val) (hhi : n.val < 768) : n ∈ blockIDs2 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 512, by omega⟩, ?_, ?_⟩
  · exact (census2_spec _).mp (by
      have he : embed2 ⟨n.val - 512, by omega⟩ = n := by ext; simp [embed2]; omega
      simpa [he] using ht)
  · ext; simp [embed2]; omega

theorem block_terminal2 {n : Fin 5011} (hn : n ∈ blockIDs2) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census2_spec m).mpr hm

def embed3 (n : Fin 256) : Fin 5011 := ⟨n.val + 768, by omega⟩
def census3 : Finset (Fin 256) := {
  ⟨13, by decide⟩, ⟨16, by decide⟩, ⟨23, by decide⟩, ⟨37, by decide⟩, ⟨41, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨49, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨61, by decide⟩, ⟨71, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨79, by decide⟩, ⟨82, by decide⟩, ⟨87, by decide⟩, ⟨93, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨104, by decide⟩, ⟨107, by decide⟩, ⟨111, by decide⟩, ⟨114, by decide⟩, ⟨118, by decide⟩, ⟨120, by decide⟩, ⟨128, by decide⟩, ⟨133, by decide⟩, ⟨135, by decide⟩, ⟨142, by decide⟩, ⟨146, by decide⟩, ⟨159, by decide⟩, ⟨164, by decide⟩, ⟨166, by decide⟩, ⟨168, by decide⟩, ⟨171, by decide⟩, ⟨174, by decide⟩, ⟨178, by decide⟩, ⟨180, by decide⟩, ⟨182, by decide⟩, ⟨186, by decide⟩, ⟨190, by decide⟩, ⟨192, by decide⟩, ⟨194, by decide⟩, ⟨196, by decide⟩, ⟨198, by decide⟩, ⟨199, by decide⟩, ⟨201, by decide⟩, ⟨204, by decide⟩, ⟨205, by decide⟩, ⟨211, by decide⟩, ⟨216, by decide⟩, ⟨221, by decide⟩, ⟨232, by decide⟩, ⟨236, by decide⟩, ⟨239, by decide⟩, ⟨242, by decide⟩, ⟨247, by decide⟩, ⟨248, by decide⟩, ⟨250, by decide⟩, ⟨252, by decide⟩
}

theorem census3_spec (n : Fin 256) :
    (DBMSourceTree.data (embed3 n)).terminal = true ↔ n ∈ census3 := by
  decide +kernel

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
  simp [embed3]
theorem blockIDs3_lower : blockIDs3 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 768 ≤ n.val) := by
  intro n hn
  rw [blockIDs3, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed3]

theorem block_mem3 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 768 ≤ n.val) (hhi : n.val < 1024) : n ∈ blockIDs3 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 768, by omega⟩, ?_, ?_⟩
  · exact (census3_spec _).mp (by
      have he : embed3 ⟨n.val - 768, by omega⟩ = n := by ext; simp [embed3]; omega
      simpa [he] using ht)
  · ext; simp [embed3]; omega

theorem block_terminal3 {n : Fin 5011} (hn : n ∈ blockIDs3) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census3_spec m).mpr hm

def embed4 (n : Fin 256) : Fin 5011 := ⟨n.val + 1024, by omega⟩
def census4 : Finset (Fin 256) := {
  ⟨0, by decide⟩, ⟨9, by decide⟩, ⟨19, by decide⟩, ⟨30, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨55, by decide⟩, ⟨57, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨72, by decide⟩, ⟨88, by decide⟩, ⟨93, by decide⟩, ⟨95, by decide⟩, ⟨99, by decide⟩, ⟨104, by decide⟩, ⟨114, by decide⟩, ⟨115, by decide⟩, ⟨120, by decide⟩, ⟨136, by decide⟩, ⟨141, by decide⟩, ⟨144, by decide⟩, ⟨146, by decide⟩, ⟨147, by decide⟩, ⟨148, by decide⟩, ⟨153, by decide⟩, ⟨160, by decide⟩, ⟨164, by decide⟩, ⟨165, by decide⟩, ⟨167, by decide⟩, ⟨169, by decide⟩, ⟨171, by decide⟩, ⟨177, by decide⟩, ⟨181, by decide⟩, ⟨183, by decide⟩, ⟨185, by decide⟩, ⟨190, by decide⟩, ⟨191, by decide⟩, ⟨199, by decide⟩, ⟨203, by decide⟩, ⟨205, by decide⟩, ⟨208, by decide⟩, ⟨210, by decide⟩, ⟨211, by decide⟩, ⟨216, by decide⟩, ⟨217, by decide⟩, ⟨220, by decide⟩, ⟨228, by decide⟩, ⟨229, by decide⟩, ⟨233, by decide⟩, ⟨237, by decide⟩, ⟨242, by decide⟩, ⟨244, by decide⟩, ⟨253, by decide⟩, ⟨255, by decide⟩
}

theorem census4_spec (n : Fin 256) :
    (DBMSourceTree.data (embed4 n)).terminal = true ↔ n ∈ census4 := by
  decide +kernel

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
  simp [embed4]
theorem blockIDs4_lower : blockIDs4 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 1024 ≤ n.val) := by
  intro n hn
  rw [blockIDs4, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed4]

theorem block_mem4 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 1024 ≤ n.val) (hhi : n.val < 1280) : n ∈ blockIDs4 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 1024, by omega⟩, ?_, ?_⟩
  · exact (census4_spec _).mp (by
      have he : embed4 ⟨n.val - 1024, by omega⟩ = n := by ext; simp [embed4]; omega
      simpa [he] using ht)
  · ext; simp [embed4]; omega

theorem block_terminal4 {n : Fin 5011} (hn : n ∈ blockIDs4) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census4_spec m).mpr hm

def embed5 (n : Fin 256) : Fin 5011 := ⟨n.val + 1280, by omega⟩
def census5 : Finset (Fin 256) := {
  ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩, ⟨25, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨47, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨79, by decide⟩, ⟨92, by decide⟩, ⟨96, by decide⟩, ⟨98, by decide⟩, ⟨100, by decide⟩, ⟨102, by decide⟩, ⟨108, by decide⟩, ⟨112, by decide⟩, ⟨118, by decide⟩, ⟨119, by decide⟩, ⟨122, by decide⟩, ⟨124, by decide⟩, ⟨126, by decide⟩, ⟨128, by decide⟩, ⟨129, by decide⟩, ⟨138, by decide⟩, ⟨140, by decide⟩, ⟨142, by decide⟩, ⟨144, by decide⟩, ⟨146, by decide⟩, ⟨152, by decide⟩, ⟨154, by decide⟩, ⟨157, by decide⟩, ⟨159, by decide⟩, ⟨168, by decide⟩, ⟨170, by decide⟩, ⟨172, by decide⟩, ⟨175, by decide⟩, ⟨177, by decide⟩, ⟨179, by decide⟩, ⟨185, by decide⟩, ⟨188, by decide⟩, ⟨190, by decide⟩, ⟨193, by decide⟩, ⟨195, by decide⟩, ⟨210, by decide⟩, ⟨212, by decide⟩, ⟨213, by decide⟩, ⟨214, by decide⟩, ⟨215, by decide⟩, ⟨218, by decide⟩, ⟨226, by decide⟩, ⟨227, by decide⟩, ⟨230, by decide⟩, ⟨232, by decide⟩, ⟨234, by decide⟩, ⟨248, by decide⟩, ⟨252, by decide⟩
}

theorem census5_spec (n : Fin 256) :
    (DBMSourceTree.data (embed5 n)).terminal = true ↔ n ∈ census5 := by
  decide +kernel

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
  simp [embed5]
theorem blockIDs5_lower : blockIDs5 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 1280 ≤ n.val) := by
  intro n hn
  rw [blockIDs5, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed5]

theorem block_mem5 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 1280 ≤ n.val) (hhi : n.val < 1536) : n ∈ blockIDs5 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 1280, by omega⟩, ?_, ?_⟩
  · exact (census5_spec _).mp (by
      have he : embed5 ⟨n.val - 1280, by omega⟩ = n := by ext; simp [embed5]; omega
      simpa [he] using ht)
  · ext; simp [embed5]; omega

theorem block_terminal5 {n : Fin 5011} (hn : n ∈ blockIDs5) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census5_spec m).mpr hm

def embed6 (n : Fin 256) : Fin 5011 := ⟨n.val + 1536, by omega⟩
def census6 : Finset (Fin 256) := {
  ⟨4, by decide⟩, ⟨15, by decide⟩, ⟨17, by decide⟩, ⟨19, by decide⟩, ⟨22, by decide⟩, ⟨25, by decide⟩, ⟨44, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨70, by decide⟩, ⟨73, by decide⟩, ⟨80, by decide⟩, ⟨84, by decide⟩, ⟨86, by decide⟩, ⟨88, by decide⟩, ⟨90, by decide⟩, ⟨92, by decide⟩, ⟨112, by decide⟩, ⟨120, by decide⟩, ⟨122, by decide⟩, ⟨134, by decide⟩, ⟨135, by decide⟩, ⟨137, by decide⟩, ⟨139, by decide⟩, ⟨141, by decide⟩, ⟨156, by decide⟩, ⟨160, by decide⟩, ⟨162, by decide⟩, ⟨186, by decide⟩, ⟨188, by decide⟩, ⟨196, by decide⟩, ⟨198, by decide⟩, ⟨204, by decide⟩, ⟨206, by decide⟩, ⟨209, by decide⟩, ⟨212, by decide⟩, ⟨214, by decide⟩, ⟨216, by decide⟩, ⟨233, by decide⟩, ⟨236, by decide⟩, ⟨237, by decide⟩, ⟨240, by decide⟩, ⟨241, by decide⟩, ⟨243, by decide⟩, ⟨245, by decide⟩, ⟨247, by decide⟩, ⟨252, by decide⟩, ⟨253, by decide⟩
}

theorem census6_spec (n : Fin 256) :
    (DBMSourceTree.data (embed6 n)).terminal = true ↔ n ∈ census6 := by
  decide +kernel

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
  simp [embed6]
theorem blockIDs6_lower : blockIDs6 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 1536 ≤ n.val) := by
  intro n hn
  rw [blockIDs6, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed6]

theorem block_mem6 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 1536 ≤ n.val) (hhi : n.val < 1792) : n ∈ blockIDs6 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 1536, by omega⟩, ?_, ?_⟩
  · exact (census6_spec _).mp (by
      have he : embed6 ⟨n.val - 1536, by omega⟩ = n := by ext; simp [embed6]; omega
      simpa [he] using ht)
  · ext; simp [embed6]; omega

theorem block_terminal6 {n : Fin 5011} (hn : n ∈ blockIDs6) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census6_spec m).mpr hm

def embed7 (n : Fin 256) : Fin 5011 := ⟨n.val + 1792, by omega⟩
def census7 : Finset (Fin 256) := {
  ⟨0, by decide⟩, ⟨3, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩, ⟨20, by decide⟩, ⟨23, by decide⟩, ⟨28, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨37, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨46, by decide⟩, ⟨57, by decide⟩, ⟨59, by decide⟩, ⟨61, by decide⟩, ⟨69, by decide⟩, ⟨77, by decide⟩, ⟨83, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨105, by decide⟩, ⟨111, by decide⟩, ⟨113, by decide⟩, ⟨115, by decide⟩, ⟨117, by decide⟩, ⟨119, by decide⟩, ⟨121, by decide⟩, ⟨126, by decide⟩, ⟨127, by decide⟩, ⟨129, by decide⟩, ⟨133, by decide⟩, ⟨136, by decide⟩, ⟨140, by decide⟩, ⟨142, by decide⟩, ⟨151, by decide⟩, ⟨153, by decide⟩, ⟨155, by decide⟩, ⟨158, by decide⟩, ⟨162, by decide⟩, ⟨164, by decide⟩, ⟨166, by decide⟩, ⟨167, by decide⟩, ⟨170, by decide⟩, ⟨172, by decide⟩, ⟨176, by decide⟩, ⟨196, by decide⟩, ⟨198, by decide⟩, ⟨205, by decide⟩, ⟨224, by decide⟩, ⟨230, by decide⟩, ⟨232, by decide⟩, ⟨233, by decide⟩
}

theorem census7_spec (n : Fin 256) :
    (DBMSourceTree.data (embed7 n)).terminal = true ↔ n ∈ census7 := by
  decide +kernel

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
  simp [embed7]
theorem blockIDs7_lower : blockIDs7 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 1792 ≤ n.val) := by
  intro n hn
  rw [blockIDs7, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed7]

theorem block_mem7 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 1792 ≤ n.val) (hhi : n.val < 2048) : n ∈ blockIDs7 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 1792, by omega⟩, ?_, ?_⟩
  · exact (census7_spec _).mp (by
      have he : embed7 ⟨n.val - 1792, by omega⟩ = n := by ext; simp [embed7]; omega
      simpa [he] using ht)
  · ext; simp [embed7]; omega

theorem block_terminal7 {n : Fin 5011} (hn : n ∈ blockIDs7) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census7_spec m).mpr hm

def embed8 (n : Fin 256) : Fin 5011 := ⟨n.val + 2048, by omega⟩
def census8 : Finset (Fin 256) := {
  ⟨11, by decide⟩, ⟨17, by decide⟩, ⟨21, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨34, by decide⟩, ⟨36, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨41, by decide⟩, ⟨50, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨74, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨91, by decide⟩, ⟨93, by decide⟩, ⟨95, by decide⟩, ⟨97, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨105, by decide⟩, ⟨114, by decide⟩, ⟨115, by decide⟩, ⟨118, by decide⟩, ⟨120, by decide⟩, ⟨128, by decide⟩, ⟨129, by decide⟩, ⟨131, by decide⟩, ⟨135, by decide⟩, ⟨140, by decide⟩, ⟨148, by decide⟩, ⟨149, by decide⟩, ⟨158, by decide⟩, ⟨160, by decide⟩, ⟨166, by decide⟩, ⟨168, by decide⟩, ⟨170, by decide⟩, ⟨172, by decide⟩, ⟨173, by decide⟩, ⟨176, by decide⟩, ⟨186, by decide⟩, ⟨188, by decide⟩, ⟨190, by decide⟩, ⟨194, by decide⟩, ⟨196, by decide⟩, ⟨197, by decide⟩, ⟨201, by decide⟩, ⟨204, by decide⟩, ⟨205, by decide⟩, ⟨210, by decide⟩, ⟨214, by decide⟩, ⟨215, by decide⟩, ⟨219, by decide⟩, ⟨238, by decide⟩, ⟨240, by decide⟩, ⟨242, by decide⟩, ⟨244, by decide⟩, ⟨248, by decide⟩, ⟨254, by decide⟩, ⟨255, by decide⟩
}

theorem census8_spec (n : Fin 256) :
    (DBMSourceTree.data (embed8 n)).terminal = true ↔ n ∈ census8 := by
  decide +kernel

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
  simp [embed8]
theorem blockIDs8_lower : blockIDs8 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 2048 ≤ n.val) := by
  intro n hn
  rw [blockIDs8, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed8]

theorem block_mem8 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 2048 ≤ n.val) (hhi : n.val < 2304) : n ∈ blockIDs8 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 2048, by omega⟩, ?_, ?_⟩
  · exact (census8_spec _).mp (by
      have he : embed8 ⟨n.val - 2048, by omega⟩ = n := by ext; simp [embed8]; omega
      simpa [he] using ht)
  · ext; simp [embed8]; omega

theorem block_terminal8 {n : Fin 5011} (hn : n ∈ blockIDs8) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census8_spec m).mpr hm

def embed9 (n : Fin 256) : Fin 5011 := ⟨n.val + 2304, by omega⟩
def census9 : Finset (Fin 256) := {
  ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨14, by decide⟩, ⟨16, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩, ⟨110, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩, ⟨113, by decide⟩, ⟨114, by decide⟩, ⟨115, by decide⟩, ⟨116, by decide⟩, ⟨117, by decide⟩, ⟨118, by decide⟩, ⟨119, by decide⟩, ⟨120, by decide⟩, ⟨121, by decide⟩, ⟨122, by decide⟩, ⟨123, by decide⟩, ⟨124, by decide⟩, ⟨125, by decide⟩, ⟨126, by decide⟩, ⟨127, by decide⟩, ⟨128, by decide⟩, ⟨129, by decide⟩, ⟨130, by decide⟩, ⟨131, by decide⟩, ⟨132, by decide⟩, ⟨133, by decide⟩, ⟨134, by decide⟩, ⟨135, by decide⟩, ⟨136, by decide⟩, ⟨137, by decide⟩, ⟨138, by decide⟩, ⟨139, by decide⟩, ⟨140, by decide⟩, ⟨141, by decide⟩, ⟨142, by decide⟩, ⟨143, by decide⟩, ⟨144, by decide⟩, ⟨145, by decide⟩, ⟨146, by decide⟩, ⟨147, by decide⟩, ⟨148, by decide⟩, ⟨149, by decide⟩, ⟨150, by decide⟩, ⟨151, by decide⟩, ⟨152, by decide⟩, ⟨153, by decide⟩, ⟨154, by decide⟩, ⟨155, by decide⟩, ⟨156, by decide⟩, ⟨157, by decide⟩, ⟨158, by decide⟩, ⟨159, by decide⟩, ⟨160, by decide⟩, ⟨161, by decide⟩, ⟨162, by decide⟩, ⟨163, by decide⟩, ⟨164, by decide⟩, ⟨165, by decide⟩, ⟨166, by decide⟩, ⟨167, by decide⟩, ⟨168, by decide⟩, ⟨169, by decide⟩, ⟨170, by decide⟩, ⟨171, by decide⟩, ⟨172, by decide⟩, ⟨173, by decide⟩, ⟨174, by decide⟩, ⟨175, by decide⟩, ⟨176, by decide⟩, ⟨177, by decide⟩, ⟨178, by decide⟩, ⟨179, by decide⟩, ⟨180, by decide⟩, ⟨181, by decide⟩, ⟨182, by decide⟩, ⟨183, by decide⟩, ⟨184, by decide⟩, ⟨185, by decide⟩, ⟨186, by decide⟩, ⟨187, by decide⟩, ⟨188, by decide⟩, ⟨189, by decide⟩, ⟨190, by decide⟩, ⟨191, by decide⟩, ⟨192, by decide⟩, ⟨193, by decide⟩, ⟨194, by decide⟩, ⟨195, by decide⟩, ⟨196, by decide⟩, ⟨197, by decide⟩, ⟨198, by decide⟩, ⟨199, by decide⟩, ⟨200, by decide⟩, ⟨201, by decide⟩, ⟨202, by decide⟩, ⟨203, by decide⟩, ⟨204, by decide⟩, ⟨205, by decide⟩, ⟨206, by decide⟩, ⟨207, by decide⟩, ⟨208, by decide⟩, ⟨209, by decide⟩, ⟨210, by decide⟩, ⟨211, by decide⟩, ⟨212, by decide⟩, ⟨213, by decide⟩, ⟨214, by decide⟩, ⟨215, by decide⟩, ⟨216, by decide⟩, ⟨217, by decide⟩, ⟨218, by decide⟩, ⟨219, by decide⟩, ⟨220, by decide⟩, ⟨221, by decide⟩, ⟨222, by decide⟩, ⟨223, by decide⟩, ⟨224, by decide⟩, ⟨225, by decide⟩, ⟨226, by decide⟩, ⟨227, by decide⟩, ⟨228, by decide⟩, ⟨229, by decide⟩, ⟨230, by decide⟩, ⟨231, by decide⟩, ⟨232, by decide⟩, ⟨234, by decide⟩, ⟨235, by decide⟩, ⟨236, by decide⟩, ⟨237, by decide⟩, ⟨238, by decide⟩, ⟨239, by decide⟩, ⟨240, by decide⟩, ⟨241, by decide⟩, ⟨242, by decide⟩, ⟨243, by decide⟩, ⟨244, by decide⟩, ⟨245, by decide⟩, ⟨246, by decide⟩, ⟨247, by decide⟩, ⟨248, by decide⟩, ⟨249, by decide⟩, ⟨250, by decide⟩, ⟨252, by decide⟩, ⟨253, by decide⟩, ⟨254, by decide⟩, ⟨255, by decide⟩
}

theorem census9_spec (n : Fin 256) :
    (DBMSourceTree.data (embed9 n)).terminal = true ↔ n ∈ census9 := by
  decide +kernel

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
  simp [embed9]
theorem blockIDs9_lower : blockIDs9 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 2304 ≤ n.val) := by
  intro n hn
  rw [blockIDs9, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed9]

theorem block_mem9 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 2304 ≤ n.val) (hhi : n.val < 2560) : n ∈ blockIDs9 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 2304, by omega⟩, ?_, ?_⟩
  · exact (census9_spec _).mp (by
      have he : embed9 ⟨n.val - 2304, by omega⟩ = n := by ext; simp [embed9]; omega
      simpa [he] using ht)
  · ext; simp [embed9]; omega

theorem block_terminal9 {n : Fin 5011} (hn : n ∈ blockIDs9) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census9_spec m).mpr hm

def embed10 (n : Fin 256) : Fin 5011 := ⟨n.val + 2560, by omega⟩
def census10 : Finset (Fin 256) := {
  ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩, ⟨110, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩, ⟨113, by decide⟩, ⟨114, by decide⟩, ⟨115, by decide⟩, ⟨116, by decide⟩, ⟨117, by decide⟩, ⟨118, by decide⟩, ⟨119, by decide⟩, ⟨120, by decide⟩, ⟨121, by decide⟩, ⟨122, by decide⟩, ⟨123, by decide⟩, ⟨124, by decide⟩, ⟨125, by decide⟩, ⟨126, by decide⟩, ⟨127, by decide⟩, ⟨128, by decide⟩, ⟨129, by decide⟩, ⟨130, by decide⟩, ⟨131, by decide⟩, ⟨132, by decide⟩, ⟨133, by decide⟩, ⟨134, by decide⟩, ⟨135, by decide⟩, ⟨136, by decide⟩, ⟨137, by decide⟩, ⟨138, by decide⟩, ⟨139, by decide⟩, ⟨140, by decide⟩, ⟨141, by decide⟩, ⟨142, by decide⟩, ⟨143, by decide⟩, ⟨144, by decide⟩, ⟨145, by decide⟩, ⟨146, by decide⟩, ⟨147, by decide⟩, ⟨148, by decide⟩, ⟨149, by decide⟩, ⟨150, by decide⟩, ⟨151, by decide⟩, ⟨152, by decide⟩, ⟨153, by decide⟩, ⟨154, by decide⟩, ⟨155, by decide⟩, ⟨156, by decide⟩, ⟨157, by decide⟩, ⟨158, by decide⟩, ⟨159, by decide⟩, ⟨160, by decide⟩, ⟨161, by decide⟩, ⟨162, by decide⟩, ⟨163, by decide⟩, ⟨164, by decide⟩, ⟨165, by decide⟩, ⟨166, by decide⟩, ⟨167, by decide⟩, ⟨168, by decide⟩, ⟨169, by decide⟩, ⟨170, by decide⟩, ⟨171, by decide⟩, ⟨172, by decide⟩, ⟨173, by decide⟩, ⟨174, by decide⟩, ⟨175, by decide⟩, ⟨176, by decide⟩, ⟨177, by decide⟩, ⟨178, by decide⟩, ⟨179, by decide⟩, ⟨180, by decide⟩, ⟨181, by decide⟩, ⟨182, by decide⟩, ⟨183, by decide⟩, ⟨184, by decide⟩, ⟨185, by decide⟩, ⟨186, by decide⟩, ⟨187, by decide⟩, ⟨188, by decide⟩, ⟨189, by decide⟩, ⟨190, by decide⟩, ⟨191, by decide⟩, ⟨192, by decide⟩, ⟨193, by decide⟩, ⟨194, by decide⟩, ⟨195, by decide⟩, ⟨196, by decide⟩, ⟨197, by decide⟩, ⟨198, by decide⟩, ⟨199, by decide⟩, ⟨200, by decide⟩, ⟨201, by decide⟩, ⟨202, by decide⟩, ⟨203, by decide⟩, ⟨204, by decide⟩, ⟨205, by decide⟩, ⟨206, by decide⟩, ⟨207, by decide⟩, ⟨208, by decide⟩, ⟨209, by decide⟩, ⟨210, by decide⟩, ⟨211, by decide⟩, ⟨212, by decide⟩, ⟨213, by decide⟩, ⟨214, by decide⟩, ⟨215, by decide⟩, ⟨216, by decide⟩, ⟨217, by decide⟩, ⟨218, by decide⟩, ⟨219, by decide⟩, ⟨220, by decide⟩, ⟨221, by decide⟩, ⟨222, by decide⟩, ⟨223, by decide⟩, ⟨224, by decide⟩, ⟨225, by decide⟩, ⟨226, by decide⟩, ⟨227, by decide⟩, ⟨228, by decide⟩, ⟨229, by decide⟩, ⟨230, by decide⟩, ⟨231, by decide⟩, ⟨232, by decide⟩, ⟨233, by decide⟩, ⟨234, by decide⟩, ⟨235, by decide⟩, ⟨236, by decide⟩, ⟨237, by decide⟩, ⟨238, by decide⟩, ⟨239, by decide⟩, ⟨240, by decide⟩, ⟨241, by decide⟩, ⟨242, by decide⟩, ⟨243, by decide⟩, ⟨244, by decide⟩, ⟨245, by decide⟩, ⟨246, by decide⟩, ⟨247, by decide⟩, ⟨248, by decide⟩, ⟨249, by decide⟩, ⟨250, by decide⟩, ⟨251, by decide⟩, ⟨252, by decide⟩, ⟨253, by decide⟩, ⟨254, by decide⟩, ⟨255, by decide⟩
}

theorem census10_spec (n : Fin 256) :
    (DBMSourceTree.data (embed10 n)).terminal = true ↔ n ∈ census10 := by
  decide +kernel

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
  simp [embed10]
theorem blockIDs10_lower : blockIDs10 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 2560 ≤ n.val) := by
  intro n hn
  rw [blockIDs10, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed10]

theorem block_mem10 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 2560 ≤ n.val) (hhi : n.val < 2816) : n ∈ blockIDs10 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 2560, by omega⟩, ?_, ?_⟩
  · exact (census10_spec _).mp (by
      have he : embed10 ⟨n.val - 2560, by omega⟩ = n := by ext; simp [embed10]; omega
      simpa [he] using ht)
  · ext; simp [embed10]; omega

theorem block_terminal10 {n : Fin 5011} (hn : n ∈ blockIDs10) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census10_spec m).mpr hm

def embed11 (n : Fin 256) : Fin 5011 := ⟨n.val + 2816, by omega⟩
def census11 : Finset (Fin 256) := {
  ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩, ⟨110, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩, ⟨113, by decide⟩, ⟨114, by decide⟩, ⟨115, by decide⟩, ⟨116, by decide⟩, ⟨117, by decide⟩, ⟨118, by decide⟩, ⟨119, by decide⟩, ⟨120, by decide⟩, ⟨121, by decide⟩, ⟨122, by decide⟩, ⟨123, by decide⟩, ⟨124, by decide⟩, ⟨125, by decide⟩, ⟨126, by decide⟩, ⟨127, by decide⟩, ⟨128, by decide⟩, ⟨129, by decide⟩, ⟨130, by decide⟩, ⟨131, by decide⟩, ⟨132, by decide⟩, ⟨133, by decide⟩, ⟨134, by decide⟩, ⟨135, by decide⟩, ⟨136, by decide⟩, ⟨137, by decide⟩, ⟨138, by decide⟩, ⟨139, by decide⟩, ⟨140, by decide⟩, ⟨141, by decide⟩, ⟨142, by decide⟩, ⟨143, by decide⟩, ⟨144, by decide⟩, ⟨145, by decide⟩, ⟨146, by decide⟩, ⟨147, by decide⟩, ⟨148, by decide⟩, ⟨149, by decide⟩, ⟨151, by decide⟩, ⟨152, by decide⟩, ⟨153, by decide⟩, ⟨154, by decide⟩, ⟨155, by decide⟩, ⟨156, by decide⟩, ⟨157, by decide⟩, ⟨158, by decide⟩, ⟨159, by decide⟩, ⟨160, by decide⟩, ⟨161, by decide⟩, ⟨162, by decide⟩, ⟨163, by decide⟩, ⟨164, by decide⟩, ⟨165, by decide⟩, ⟨166, by decide⟩, ⟨169, by decide⟩, ⟨170, by decide⟩, ⟨171, by decide⟩, ⟨172, by decide⟩, ⟨173, by decide⟩, ⟨174, by decide⟩, ⟨175, by decide⟩, ⟨176, by decide⟩, ⟨177, by decide⟩, ⟨178, by decide⟩, ⟨179, by decide⟩, ⟨180, by decide⟩, ⟨181, by decide⟩, ⟨182, by decide⟩, ⟨183, by decide⟩, ⟨184, by decide⟩, ⟨185, by decide⟩, ⟨186, by decide⟩, ⟨187, by decide⟩, ⟨188, by decide⟩, ⟨189, by decide⟩, ⟨190, by decide⟩, ⟨191, by decide⟩, ⟨192, by decide⟩, ⟨193, by decide⟩, ⟨194, by decide⟩, ⟨195, by decide⟩, ⟨196, by decide⟩, ⟨197, by decide⟩, ⟨198, by decide⟩, ⟨199, by decide⟩, ⟨200, by decide⟩, ⟨201, by decide⟩, ⟨202, by decide⟩, ⟨203, by decide⟩, ⟨204, by decide⟩, ⟨205, by decide⟩, ⟨206, by decide⟩, ⟨207, by decide⟩, ⟨208, by decide⟩, ⟨209, by decide⟩, ⟨210, by decide⟩, ⟨211, by decide⟩, ⟨212, by decide⟩, ⟨213, by decide⟩, ⟨214, by decide⟩, ⟨215, by decide⟩, ⟨216, by decide⟩, ⟨217, by decide⟩, ⟨218, by decide⟩, ⟨219, by decide⟩, ⟨220, by decide⟩, ⟨221, by decide⟩, ⟨222, by decide⟩, ⟨223, by decide⟩, ⟨224, by decide⟩, ⟨225, by decide⟩, ⟨226, by decide⟩, ⟨227, by decide⟩, ⟨228, by decide⟩, ⟨229, by decide⟩, ⟨230, by decide⟩, ⟨231, by decide⟩, ⟨232, by decide⟩, ⟨233, by decide⟩, ⟨234, by decide⟩, ⟨235, by decide⟩, ⟨236, by decide⟩, ⟨237, by decide⟩, ⟨238, by decide⟩, ⟨239, by decide⟩, ⟨240, by decide⟩, ⟨241, by decide⟩, ⟨242, by decide⟩, ⟨243, by decide⟩, ⟨244, by decide⟩, ⟨245, by decide⟩, ⟨246, by decide⟩, ⟨247, by decide⟩, ⟨248, by decide⟩, ⟨249, by decide⟩, ⟨250, by decide⟩, ⟨251, by decide⟩, ⟨252, by decide⟩, ⟨253, by decide⟩, ⟨254, by decide⟩, ⟨255, by decide⟩
}

theorem census11_spec (n : Fin 256) :
    (DBMSourceTree.data (embed11 n)).terminal = true ↔ n ∈ census11 := by
  decide +kernel

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
  simp [embed11]
theorem blockIDs11_lower : blockIDs11 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 2816 ≤ n.val) := by
  intro n hn
  rw [blockIDs11, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed11]

theorem block_mem11 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 2816 ≤ n.val) (hhi : n.val < 3072) : n ∈ blockIDs11 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 2816, by omega⟩, ?_, ?_⟩
  · exact (census11_spec _).mp (by
      have he : embed11 ⟨n.val - 2816, by omega⟩ = n := by ext; simp [embed11]; omega
      simpa [he] using ht)
  · ext; simp [embed11]; omega

theorem block_terminal11 {n : Fin 5011} (hn : n ∈ blockIDs11) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census11_spec m).mpr hm

def embed12 (n : Fin 256) : Fin 5011 := ⟨n.val + 3072, by omega⟩
def census12 : Finset (Fin 256) := {
  ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩, ⟨110, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩, ⟨113, by decide⟩, ⟨114, by decide⟩, ⟨115, by decide⟩, ⟨116, by decide⟩, ⟨117, by decide⟩, ⟨118, by decide⟩, ⟨119, by decide⟩, ⟨120, by decide⟩, ⟨121, by decide⟩, ⟨122, by decide⟩, ⟨123, by decide⟩, ⟨124, by decide⟩, ⟨125, by decide⟩, ⟨126, by decide⟩, ⟨127, by decide⟩, ⟨128, by decide⟩, ⟨129, by decide⟩, ⟨130, by decide⟩, ⟨131, by decide⟩, ⟨132, by decide⟩, ⟨133, by decide⟩, ⟨134, by decide⟩, ⟨135, by decide⟩, ⟨136, by decide⟩, ⟨137, by decide⟩, ⟨138, by decide⟩, ⟨139, by decide⟩, ⟨140, by decide⟩, ⟨141, by decide⟩, ⟨142, by decide⟩, ⟨143, by decide⟩, ⟨144, by decide⟩, ⟨145, by decide⟩, ⟨146, by decide⟩, ⟨147, by decide⟩, ⟨148, by decide⟩, ⟨149, by decide⟩, ⟨150, by decide⟩, ⟨151, by decide⟩, ⟨152, by decide⟩, ⟨153, by decide⟩, ⟨154, by decide⟩, ⟨155, by decide⟩, ⟨156, by decide⟩, ⟨157, by decide⟩, ⟨158, by decide⟩, ⟨159, by decide⟩, ⟨160, by decide⟩, ⟨161, by decide⟩, ⟨162, by decide⟩, ⟨163, by decide⟩, ⟨164, by decide⟩, ⟨165, by decide⟩, ⟨166, by decide⟩, ⟨167, by decide⟩, ⟨168, by decide⟩, ⟨169, by decide⟩, ⟨170, by decide⟩, ⟨171, by decide⟩, ⟨172, by decide⟩, ⟨173, by decide⟩, ⟨174, by decide⟩, ⟨175, by decide⟩, ⟨176, by decide⟩, ⟨177, by decide⟩, ⟨178, by decide⟩, ⟨179, by decide⟩, ⟨180, by decide⟩, ⟨181, by decide⟩, ⟨182, by decide⟩, ⟨183, by decide⟩, ⟨184, by decide⟩, ⟨185, by decide⟩, ⟨186, by decide⟩, ⟨187, by decide⟩, ⟨188, by decide⟩, ⟨189, by decide⟩, ⟨190, by decide⟩, ⟨191, by decide⟩, ⟨192, by decide⟩, ⟨193, by decide⟩, ⟨194, by decide⟩, ⟨195, by decide⟩, ⟨196, by decide⟩, ⟨197, by decide⟩, ⟨198, by decide⟩, ⟨199, by decide⟩, ⟨200, by decide⟩, ⟨201, by decide⟩, ⟨202, by decide⟩, ⟨203, by decide⟩, ⟨204, by decide⟩, ⟨205, by decide⟩, ⟨206, by decide⟩, ⟨207, by decide⟩, ⟨208, by decide⟩, ⟨209, by decide⟩, ⟨210, by decide⟩, ⟨211, by decide⟩, ⟨212, by decide⟩, ⟨213, by decide⟩, ⟨214, by decide⟩, ⟨215, by decide⟩, ⟨216, by decide⟩, ⟨217, by decide⟩, ⟨218, by decide⟩, ⟨219, by decide⟩, ⟨220, by decide⟩, ⟨221, by decide⟩, ⟨222, by decide⟩, ⟨223, by decide⟩, ⟨224, by decide⟩, ⟨225, by decide⟩, ⟨226, by decide⟩, ⟨227, by decide⟩, ⟨228, by decide⟩, ⟨229, by decide⟩, ⟨230, by decide⟩, ⟨231, by decide⟩, ⟨232, by decide⟩, ⟨233, by decide⟩, ⟨234, by decide⟩, ⟨235, by decide⟩, ⟨236, by decide⟩, ⟨237, by decide⟩, ⟨238, by decide⟩, ⟨239, by decide⟩, ⟨240, by decide⟩, ⟨241, by decide⟩, ⟨242, by decide⟩, ⟨243, by decide⟩, ⟨244, by decide⟩, ⟨245, by decide⟩, ⟨246, by decide⟩, ⟨247, by decide⟩, ⟨248, by decide⟩, ⟨249, by decide⟩, ⟨250, by decide⟩, ⟨251, by decide⟩, ⟨252, by decide⟩, ⟨253, by decide⟩, ⟨254, by decide⟩, ⟨255, by decide⟩
}

theorem census12_spec (n : Fin 256) :
    (DBMSourceTree.data (embed12 n)).terminal = true ↔ n ∈ census12 := by
  decide +kernel

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
  simp [embed12]
theorem blockIDs12_lower : blockIDs12 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 3072 ≤ n.val) := by
  intro n hn
  rw [blockIDs12, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed12]

theorem block_mem12 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 3072 ≤ n.val) (hhi : n.val < 3328) : n ∈ blockIDs12 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 3072, by omega⟩, ?_, ?_⟩
  · exact (census12_spec _).mp (by
      have he : embed12 ⟨n.val - 3072, by omega⟩ = n := by ext; simp [embed12]; omega
      simpa [he] using ht)
  · ext; simp [embed12]; omega

theorem block_terminal12 {n : Fin 5011} (hn : n ∈ blockIDs12) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census12_spec m).mpr hm

def embed13 (n : Fin 256) : Fin 5011 := ⟨n.val + 3328, by omega⟩
def census13 : Finset (Fin 256) := {
  ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨39, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨78, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨85, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨88, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩, ⟨110, by decide⟩, ⟨111, by decide⟩, ⟨112, by decide⟩, ⟨113, by decide⟩, ⟨114, by decide⟩, ⟨117, by decide⟩, ⟨118, by decide⟩, ⟨119, by decide⟩, ⟨120, by decide⟩, ⟨121, by decide⟩, ⟨122, by decide⟩, ⟨123, by decide⟩, ⟨124, by decide⟩, ⟨125, by decide⟩, ⟨126, by decide⟩, ⟨127, by decide⟩, ⟨128, by decide⟩, ⟨129, by decide⟩, ⟨130, by decide⟩, ⟨131, by decide⟩, ⟨132, by decide⟩, ⟨133, by decide⟩, ⟨134, by decide⟩, ⟨135, by decide⟩, ⟨136, by decide⟩, ⟨137, by decide⟩, ⟨138, by decide⟩, ⟨139, by decide⟩, ⟨140, by decide⟩, ⟨141, by decide⟩, ⟨142, by decide⟩, ⟨143, by decide⟩, ⟨144, by decide⟩, ⟨145, by decide⟩, ⟨146, by decide⟩, ⟨147, by decide⟩, ⟨148, by decide⟩, ⟨149, by decide⟩, ⟨150, by decide⟩, ⟨151, by decide⟩, ⟨152, by decide⟩, ⟨153, by decide⟩, ⟨154, by decide⟩, ⟨155, by decide⟩, ⟨156, by decide⟩, ⟨157, by decide⟩, ⟨158, by decide⟩, ⟨159, by decide⟩, ⟨160, by decide⟩, ⟨161, by decide⟩, ⟨162, by decide⟩, ⟨163, by decide⟩, ⟨164, by decide⟩, ⟨165, by decide⟩, ⟨166, by decide⟩, ⟨167, by decide⟩, ⟨168, by decide⟩, ⟨169, by decide⟩, ⟨170, by decide⟩, ⟨171, by decide⟩, ⟨172, by decide⟩, ⟨173, by decide⟩, ⟨174, by decide⟩, ⟨175, by decide⟩, ⟨176, by decide⟩, ⟨177, by decide⟩, ⟨178, by decide⟩, ⟨179, by decide⟩, ⟨182, by decide⟩, ⟨183, by decide⟩, ⟨184, by decide⟩, ⟨185, by decide⟩, ⟨186, by decide⟩, ⟨187, by decide⟩, ⟨188, by decide⟩, ⟨189, by decide⟩, ⟨190, by decide⟩, ⟨191, by decide⟩, ⟨192, by decide⟩, ⟨193, by decide⟩, ⟨194, by decide⟩, ⟨195, by decide⟩, ⟨196, by decide⟩, ⟨198, by decide⟩, ⟨200, by decide⟩, ⟨201, by decide⟩, ⟨203, by decide⟩, ⟨205, by decide⟩, ⟨206, by decide⟩, ⟨207, by decide⟩, ⟨208, by decide⟩, ⟨210, by decide⟩, ⟨212, by decide⟩, ⟨214, by decide⟩, ⟨216, by decide⟩, ⟨217, by decide⟩, ⟨219, by decide⟩, ⟨221, by decide⟩, ⟨222, by decide⟩, ⟨223, by decide⟩, ⟨227, by decide⟩, ⟨229, by decide⟩, ⟨230, by decide⟩, ⟨235, by decide⟩, ⟨236, by decide⟩, ⟨237, by decide⟩, ⟨239, by decide⟩, ⟨241, by decide⟩, ⟨243, by decide⟩, ⟨245, by decide⟩, ⟨249, by decide⟩, ⟨250, by decide⟩, ⟨251, by decide⟩
}

theorem census13_spec (n : Fin 256) :
    (DBMSourceTree.data (embed13 n)).terminal = true ↔ n ∈ census13 := by
  decide +kernel

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
  simp [embed13]
theorem blockIDs13_lower : blockIDs13 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 3328 ≤ n.val) := by
  intro n hn
  rw [blockIDs13, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed13]

theorem block_mem13 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 3328 ≤ n.val) (hhi : n.val < 3584) : n ∈ blockIDs13 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 3328, by omega⟩, ?_, ?_⟩
  · exact (census13_spec _).mp (by
      have he : embed13 ⟨n.val - 3328, by omega⟩ = n := by ext; simp [embed13]; omega
      simpa [he] using ht)
  · ext; simp [embed13]; omega

theorem block_terminal13 {n : Fin 5011} (hn : n ∈ blockIDs13) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census13_spec m).mpr hm

def embed14 (n : Fin 256) : Fin 5011 := ⟨n.val + 3584, by omega⟩
def census14 : Finset (Fin 256) := {
  ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨9, by decide⟩, ⟨11, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩, ⟨17, by decide⟩, ⟨19, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨27, by decide⟩, ⟨29, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨45, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨53, by decide⟩, ⟨55, by decide⟩, ⟨59, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨73, by decide⟩, ⟨78, by decide⟩, ⟨80, by decide⟩, ⟨83, by decide⟩, ⟨85, by decide⟩, ⟨90, by decide⟩, ⟨92, by decide⟩, ⟨94, by decide⟩, ⟨96, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨112, by decide⟩, ⟨114, by decide⟩, ⟨116, by decide⟩, ⟨120, by decide⟩, ⟨124, by decide⟩, ⟨126, by decide⟩, ⟨128, by decide⟩, ⟨137, by decide⟩, ⟨139, by decide⟩, ⟨154, by decide⟩, ⟨155, by decide⟩, ⟨157, by decide⟩, ⟨163, by decide⟩, ⟨166, by decide⟩, ⟨168, by decide⟩, ⟨169, by decide⟩, ⟨172, by decide⟩, ⟨175, by decide⟩, ⟨178, by decide⟩, ⟨180, by decide⟩, ⟨181, by decide⟩, ⟨182, by decide⟩, ⟨186, by decide⟩, ⟨187, by decide⟩, ⟨189, by decide⟩, ⟨190, by decide⟩, ⟨193, by decide⟩, ⟨194, by decide⟩, ⟨196, by decide⟩, ⟨197, by decide⟩, ⟨198, by decide⟩, ⟨199, by decide⟩, ⟨201, by decide⟩, ⟨203, by decide⟩, ⟨205, by decide⟩, ⟨207, by decide⟩, ⟨208, by decide⟩, ⟨209, by decide⟩, ⟨210, by decide⟩, ⟨211, by decide⟩, ⟨212, by decide⟩, ⟨213, by decide⟩, ⟨215, by decide⟩, ⟨216, by decide⟩, ⟨217, by decide⟩, ⟨218, by decide⟩, ⟨219, by decide⟩, ⟨220, by decide⟩, ⟨221, by decide⟩, ⟨223, by decide⟩, ⟨224, by decide⟩, ⟨225, by decide⟩, ⟨226, by decide⟩, ⟨227, by decide⟩, ⟨228, by decide⟩, ⟨229, by decide⟩, ⟨230, by decide⟩, ⟨232, by decide⟩, ⟨233, by decide⟩, ⟨234, by decide⟩, ⟨236, by decide⟩, ⟨237, by decide⟩, ⟨238, by decide⟩, ⟨239, by decide⟩, ⟨240, by decide⟩, ⟨241, by decide⟩, ⟨243, by decide⟩, ⟨245, by decide⟩, ⟨246, by decide⟩, ⟨247, by decide⟩, ⟨248, by decide⟩, ⟨249, by decide⟩, ⟨250, by decide⟩, ⟨252, by decide⟩, ⟨253, by decide⟩, ⟨254, by decide⟩, ⟨255, by decide⟩
}

theorem census14_spec (n : Fin 256) :
    (DBMSourceTree.data (embed14 n)).terminal = true ↔ n ∈ census14 := by
  decide +kernel

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
  simp [embed14]
theorem blockIDs14_lower : blockIDs14 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 3584 ≤ n.val) := by
  intro n hn
  rw [blockIDs14, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed14]

theorem block_mem14 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 3584 ≤ n.val) (hhi : n.val < 3840) : n ∈ blockIDs14 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 3584, by omega⟩, ?_, ?_⟩
  · exact (census14_spec _).mp (by
      have he : embed14 ⟨n.val - 3584, by omega⟩ = n := by ext; simp [embed14]; omega
      simpa [he] using ht)
  · ext; simp [embed14]; omega

theorem block_terminal14 {n : Fin 5011} (hn : n ∈ blockIDs14) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census14_spec m).mpr hm

def embed15 (n : Fin 256) : Fin 5011 := ⟨n.val + 3840, by omega⟩
def census15 : Finset (Fin 256) := {
  ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨4, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨32, by decide⟩, ⟨33, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨39, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨74, by decide⟩, ⟨77, by decide⟩, ⟨79, by decide⟩, ⟨81, by decide⟩, ⟨83, by decide⟩, ⟨86, by decide⟩, ⟨87, by decide⟩, ⟨89, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨96, by decide⟩, ⟨97, by decide⟩, ⟨98, by decide⟩, ⟨100, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨108, by decide⟩, ⟨110, by decide⟩, ⟨112, by decide⟩, ⟨114, by decide⟩, ⟨115, by decide⟩, ⟨117, by decide⟩, ⟨119, by decide⟩, ⟨122, by decide⟩, ⟨123, by decide⟩, ⟨124, by decide⟩, ⟨125, by decide⟩, ⟨127, by decide⟩, ⟨139, by decide⟩, ⟨141, by decide⟩, ⟨154, by decide⟩, ⟨156, by decide⟩, ⟨158, by decide⟩, ⟨160, by decide⟩, ⟨162, by decide⟩, ⟨168, by decide⟩, ⟨171, by decide⟩, ⟨173, by decide⟩, ⟨175, by decide⟩, ⟨178, by decide⟩, ⟨180, by decide⟩, ⟨182, by decide⟩, ⟨184, by decide⟩, ⟨187, by decide⟩, ⟨196, by decide⟩, ⟨198, by decide⟩, ⟨200, by decide⟩, ⟨202, by decide⟩, ⟨203, by decide⟩, ⟨211, by decide⟩, ⟨212, by decide⟩, ⟨214, by decide⟩, ⟨216, by decide⟩, ⟨217, by decide⟩, ⟨218, by decide⟩, ⟨235, by decide⟩, ⟨236, by decide⟩, ⟨237, by decide⟩, ⟨239, by decide⟩, ⟨242, by decide⟩, ⟨244, by decide⟩, ⟨246, by decide⟩, ⟨248, by decide⟩, ⟨250, by decide⟩, ⟨252, by decide⟩, ⟨254, by decide⟩
}

theorem census15_spec (n : Fin 256) :
    (DBMSourceTree.data (embed15 n)).terminal = true ↔ n ∈ census15 := by
  decide +kernel

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
  simp [embed15]
theorem blockIDs15_lower : blockIDs15 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 3840 ≤ n.val) := by
  intro n hn
  rw [blockIDs15, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed15]

theorem block_mem15 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 3840 ≤ n.val) (hhi : n.val < 4096) : n ∈ blockIDs15 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 3840, by omega⟩, ?_, ?_⟩
  · exact (census15_spec _).mp (by
      have he : embed15 ⟨n.val - 3840, by omega⟩ = n := by ext; simp [embed15]; omega
      simpa [he] using ht)
  · ext; simp [embed15]; omega

theorem block_terminal15 {n : Fin 5011} (hn : n ∈ blockIDs15) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census15_spec m).mpr hm

def embed16 (n : Fin 256) : Fin 5011 := ⟨n.val + 4096, by omega⟩
def census16 : Finset (Fin 256) := {
  ⟨0, by decide⟩, ⟨4, by decide⟩, ⟨8, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨16, by decide⟩, ⟨35, by decide⟩, ⟨42, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨48, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨68, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨81, by decide⟩, ⟨82, by decide⟩, ⟨83, by decide⟩, ⟨98, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩, ⟨112, by decide⟩, ⟨114, by decide⟩, ⟨116, by decide⟩, ⟨118, by decide⟩, ⟨119, by decide⟩, ⟨120, by decide⟩, ⟨124, by decide⟩, ⟨131, by decide⟩, ⟨134, by decide⟩, ⟨136, by decide⟩, ⟨137, by decide⟩, ⟨140, by decide⟩, ⟨141, by decide⟩, ⟨142, by decide⟩, ⟨143, by decide⟩, ⟨146, by decide⟩, ⟨147, by decide⟩, ⟨148, by decide⟩, ⟨150, by decide⟩, ⟨155, by decide⟩, ⟨162, by decide⟩, ⟨167, by decide⟩, ⟨169, by decide⟩, ⟨170, by decide⟩, ⟨171, by decide⟩, ⟨172, by decide⟩, ⟨174, by decide⟩, ⟨176, by decide⟩, ⟨181, by decide⟩, ⟨190, by decide⟩, ⟨193, by decide⟩, ⟨194, by decide⟩, ⟨195, by decide⟩, ⟨196, by decide⟩, ⟨197, by decide⟩, ⟨198, by decide⟩, ⟨200, by decide⟩, ⟨201, by decide⟩, ⟨204, by decide⟩, ⟨208, by decide⟩, ⟨209, by decide⟩, ⟨210, by decide⟩, ⟨212, by decide⟩, ⟨213, by decide⟩, ⟨214, by decide⟩, ⟨215, by decide⟩, ⟨216, by decide⟩, ⟨217, by decide⟩, ⟨218, by decide⟩, ⟨221, by decide⟩, ⟨222, by decide⟩, ⟨223, by decide⟩, ⟨224, by decide⟩, ⟨225, by decide⟩, ⟨226, by decide⟩, ⟨227, by decide⟩, ⟨228, by decide⟩, ⟨229, by decide⟩, ⟨230, by decide⟩, ⟨231, by decide⟩, ⟨232, by decide⟩, ⟨233, by decide⟩, ⟨234, by decide⟩, ⟨235, by decide⟩, ⟨237, by decide⟩, ⟨239, by decide⟩, ⟨240, by decide⟩, ⟨241, by decide⟩, ⟨244, by decide⟩, ⟨245, by decide⟩, ⟨248, by decide⟩, ⟨249, by decide⟩, ⟨250, by decide⟩, ⟨251, by decide⟩, ⟨252, by decide⟩, ⟨255, by decide⟩
}

theorem census16_spec (n : Fin 256) :
    (DBMSourceTree.data (embed16 n)).terminal = true ↔ n ∈ census16 := by
  decide +kernel

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
  simp [embed16]
theorem blockIDs16_lower : blockIDs16 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 4096 ≤ n.val) := by
  intro n hn
  rw [blockIDs16, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed16]

theorem block_mem16 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 4096 ≤ n.val) (hhi : n.val < 4352) : n ∈ blockIDs16 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 4096, by omega⟩, ?_, ?_⟩
  · exact (census16_spec _).mp (by
      have he : embed16 ⟨n.val - 4096, by omega⟩ = n := by ext; simp [embed16]; omega
      simpa [he] using ht)
  · ext; simp [embed16]; omega

theorem block_terminal16 {n : Fin 5011} (hn : n ∈ blockIDs16) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census16_spec m).mpr hm

def embed17 (n : Fin 256) : Fin 5011 := ⟨n.val + 4352, by omega⟩
def census17 : Finset (Fin 256) := {
  ⟨5, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩, ⟨16, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨24, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨33, by decide⟩, ⟨39, by decide⟩, ⟨45, by decide⟩, ⟨47, by decide⟩, ⟨49, by decide⟩, ⟨51, by decide⟩, ⟨54, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨61, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨67, by decide⟩, ⟨69, by decide⟩, ⟨70, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨79, by decide⟩, ⟨80, by decide⟩, ⟨81, by decide⟩, ⟨83, by decide⟩, ⟨84, by decide⟩, ⟨95, by decide⟩, ⟨97, by decide⟩, ⟨99, by decide⟩, ⟨101, by decide⟩, ⟨105, by decide⟩, ⟨107, by decide⟩, ⟨109, by decide⟩, ⟨113, by decide⟩, ⟨115, by decide⟩, ⟨116, by decide⟩, ⟨121, by decide⟩, ⟨123, by decide⟩, ⟨125, by decide⟩, ⟨127, by decide⟩, ⟨131, by decide⟩, ⟨133, by decide⟩, ⟨135, by decide⟩, ⟨137, by decide⟩, ⟨139, by decide⟩, ⟨142, by decide⟩, ⟨144, by decide⟩, ⟨147, by decide⟩, ⟨149, by decide⟩, ⟨151, by decide⟩, ⟨153, by decide⟩, ⟨165, by decide⟩, ⟨166, by decide⟩, ⟨168, by decide⟩, ⟨170, by decide⟩, ⟨171, by decide⟩, ⟨172, by decide⟩, ⟨174, by decide⟩, ⟨175, by decide⟩, ⟨176, by decide⟩, ⟨177, by decide⟩, ⟨178, by decide⟩, ⟨191, by decide⟩, ⟨193, by decide⟩, ⟨195, by decide⟩, ⟨196, by decide⟩, ⟨198, by decide⟩, ⟨199, by decide⟩, ⟨204, by decide⟩, ⟨205, by decide⟩, ⟨208, by decide⟩, ⟨209, by decide⟩, ⟨210, by decide⟩, ⟨212, by decide⟩, ⟨214, by decide⟩, ⟨215, by decide⟩, ⟨216, by decide⟩, ⟨218, by decide⟩, ⟨223, by decide⟩, ⟨225, by decide⟩, ⟨227, by decide⟩, ⟨229, by decide⟩, ⟨235, by decide⟩, ⟨237, by decide⟩, ⟨238, by decide⟩, ⟨239, by decide⟩, ⟨244, by decide⟩, ⟨245, by decide⟩, ⟨247, by decide⟩, ⟨250, by decide⟩, ⟨253, by decide⟩
}

theorem census17_spec (n : Fin 256) :
    (DBMSourceTree.data (embed17 n)).terminal = true ↔ n ∈ census17 := by
  decide +kernel

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
  simp [embed17]
theorem blockIDs17_lower : blockIDs17 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 4352 ≤ n.val) := by
  intro n hn
  rw [blockIDs17, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed17]

theorem block_mem17 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 4352 ≤ n.val) (hhi : n.val < 4608) : n ∈ blockIDs17 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 4352, by omega⟩, ?_, ?_⟩
  · exact (census17_spec _).mp (by
      have he : embed17 ⟨n.val - 4352, by omega⟩ = n := by ext; simp [embed17]; omega
      simpa [he] using ht)
  · ext; simp [embed17]; omega

theorem block_terminal17 {n : Fin 5011} (hn : n ∈ blockIDs17) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census17_spec m).mpr hm

def embed18 (n : Fin 256) : Fin 5011 := ⟨n.val + 4608, by omega⟩
def census18 : Finset (Fin 256) := {
  ⟨0, by decide⟩, ⟨4, by decide⟩, ⟨10, by decide⟩, ⟨12, by decide⟩, ⟨14, by decide⟩, ⟨25, by decide⟩, ⟨26, by decide⟩, ⟨31, by decide⟩, ⟨33, by decide⟩, ⟨35, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨42, by decide⟩, ⟨44, by decide⟩, ⟨46, by decide⟩, ⟨48, by decide⟩, ⟨50, by decide⟩, ⟨52, by decide⟩, ⟨54, by decide⟩, ⟨55, by decide⟩, ⟨58, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨64, by decide⟩, ⟨65, by decide⟩, ⟨66, by decide⟩, ⟨67, by decide⟩, ⟨70, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨80, by decide⟩, ⟨82, by decide⟩, ⟨84, by decide⟩, ⟨86, by decide⟩, ⟨88, by decide⟩, ⟨90, by decide⟩, ⟨92, by decide⟩, ⟨94, by decide⟩, ⟨96, by decide⟩, ⟨98, by decide⟩, ⟨100, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨104, by decide⟩, ⟨105, by decide⟩, ⟨106, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩, ⟨113, by decide⟩, ⟨115, by decide⟩, ⟨118, by decide⟩, ⟨119, by decide⟩, ⟨122, by decide⟩, ⟨124, by decide⟩, ⟨125, by decide⟩, ⟨127, by decide⟩, ⟨129, by decide⟩, ⟨131, by decide⟩, ⟨133, by decide⟩, ⟨136, by decide⟩, ⟨137, by decide⟩, ⟨139, by decide⟩, ⟨142, by decide⟩, ⟨143, by decide⟩, ⟨145, by decide⟩, ⟨147, by decide⟩, ⟨149, by decide⟩, ⟨152, by decide⟩, ⟨153, by decide⟩, ⟨156, by decide⟩, ⟨157, by decide⟩, ⟨160, by decide⟩, ⟨162, by decide⟩, ⟨164, by decide⟩, ⟨165, by decide⟩, ⟨167, by decide⟩, ⟨170, by decide⟩, ⟨172, by decide⟩, ⟨174, by decide⟩, ⟨175, by decide⟩, ⟨176, by decide⟩, ⟨177, by decide⟩, ⟨178, by decide⟩, ⟨179, by decide⟩, ⟨180, by decide⟩, ⟨181, by decide⟩, ⟨184, by decide⟩, ⟨185, by decide⟩, ⟨186, by decide⟩, ⟨187, by decide⟩, ⟨188, by decide⟩, ⟨189, by decide⟩, ⟨191, by decide⟩, ⟨193, by decide⟩, ⟨196, by decide⟩, ⟨197, by decide⟩, ⟨198, by decide⟩, ⟨199, by decide⟩, ⟨201, by decide⟩, ⟨203, by decide⟩, ⟨205, by decide⟩, ⟨206, by decide⟩, ⟨207, by decide⟩, ⟨208, by decide⟩, ⟨209, by decide⟩, ⟨210, by decide⟩, ⟨211, by decide⟩, ⟨212, by decide⟩, ⟨213, by decide⟩, ⟨214, by decide⟩, ⟨215, by decide⟩, ⟨216, by decide⟩, ⟨217, by decide⟩, ⟨220, by decide⟩, ⟨221, by decide⟩, ⟨223, by decide⟩, ⟨225, by decide⟩, ⟨226, by decide⟩, ⟨227, by decide⟩, ⟨228, by decide⟩, ⟨229, by decide⟩, ⟨230, by decide⟩, ⟨231, by decide⟩, ⟨232, by decide⟩, ⟨233, by decide⟩, ⟨234, by decide⟩, ⟨235, by decide⟩, ⟨236, by decide⟩, ⟨237, by decide⟩, ⟨238, by decide⟩, ⟨239, by decide⟩, ⟨240, by decide⟩, ⟨241, by decide⟩, ⟨243, by decide⟩, ⟨244, by decide⟩, ⟨245, by decide⟩, ⟨246, by decide⟩, ⟨247, by decide⟩, ⟨248, by decide⟩, ⟨249, by decide⟩, ⟨250, by decide⟩, ⟨251, by decide⟩, ⟨252, by decide⟩, ⟨253, by decide⟩, ⟨254, by decide⟩, ⟨255, by decide⟩
}

theorem census18_spec (n : Fin 256) :
    (DBMSourceTree.data (embed18 n)).terminal = true ↔ n ∈ census18 := by
  decide +kernel

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
  simp [embed18]
theorem blockIDs18_lower : blockIDs18 ⊆
    Finset.univ.filter (fun n : Fin 5011 => 4608 ≤ n.val) := by
  intro n hn
  rw [blockIDs18, Finset.mem_image] at hn
  rcases hn with ⟨m, _, rfl⟩
  simp [embed18]

theorem block_mem18 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 4608 ≤ n.val) (hhi : n.val < 4864) : n ∈ blockIDs18 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 4608, by omega⟩, ?_, ?_⟩
  · exact (census18_spec _).mp (by
      have he : embed18 ⟨n.val - 4608, by omega⟩ = n := by ext; simp [embed18]; omega
      simpa [he] using ht)
  · ext; simp [embed18]; omega

theorem block_terminal18 {n : Fin 5011} (hn : n ∈ blockIDs18) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census18_spec m).mpr hm

def embed19 (n : Fin 147) : Fin 5011 := ⟨n.val + 4864, by omega⟩
def census19 : Finset (Fin 147) := {
  ⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨5, by decide⟩, ⟨6, by decide⟩, ⟨7, by decide⟩, ⟨8, by decide⟩, ⟨9, by decide⟩, ⟨10, by decide⟩, ⟨11, by decide⟩, ⟨12, by decide⟩, ⟨13, by decide⟩, ⟨15, by decide⟩, ⟨17, by decide⟩, ⟨18, by decide⟩, ⟨19, by decide⟩, ⟨20, by decide⟩, ⟨21, by decide⟩, ⟨22, by decide⟩, ⟨23, by decide⟩, ⟨24, by decide⟩, ⟨26, by decide⟩, ⟨27, by decide⟩, ⟨28, by decide⟩, ⟨29, by decide⟩, ⟨30, by decide⟩, ⟨31, by decide⟩, ⟨32, by decide⟩, ⟨34, by decide⟩, ⟨35, by decide⟩, ⟨36, by decide⟩, ⟨37, by decide⟩, ⟨38, by decide⟩, ⟨40, by decide⟩, ⟨41, by decide⟩, ⟨43, by decide⟩, ⟨44, by decide⟩, ⟨45, by decide⟩, ⟨46, by decide⟩, ⟨47, by decide⟩, ⟨48, by decide⟩, ⟨49, by decide⟩, ⟨50, by decide⟩, ⟨51, by decide⟩, ⟨52, by decide⟩, ⟨53, by decide⟩, ⟨54, by decide⟩, ⟨56, by decide⟩, ⟨57, by decide⟩, ⟨58, by decide⟩, ⟨59, by decide⟩, ⟨60, by decide⟩, ⟨62, by decide⟩, ⟨63, by decide⟩, ⟨65, by decide⟩, ⟨67, by decide⟩, ⟨68, by decide⟩, ⟨69, by decide⟩, ⟨71, by decide⟩, ⟨72, by decide⟩, ⟨73, by decide⟩, ⟨74, by decide⟩, ⟨75, by decide⟩, ⟨76, by decide⟩, ⟨77, by decide⟩, ⟨80, by decide⟩, ⟨83, by decide⟩, ⟨86, by decide⟩, ⟨88, by decide⟩, ⟨90, by decide⟩, ⟨91, by decide⟩, ⟨92, by decide⟩, ⟨93, by decide⟩, ⟨94, by decide⟩, ⟨95, by decide⟩, ⟨96, by decide⟩, ⟨98, by decide⟩, ⟨99, by decide⟩, ⟨100, by decide⟩, ⟨101, by decide⟩, ⟨102, by decide⟩, ⟨103, by decide⟩, ⟨106, by decide⟩, ⟨107, by decide⟩, ⟨108, by decide⟩, ⟨109, by decide⟩, ⟨110, by decide⟩, ⟨111, by decide⟩, ⟨113, by decide⟩, ⟨116, by decide⟩, ⟨117, by decide⟩, ⟨118, by decide⟩, ⟨119, by decide⟩, ⟨120, by decide⟩, ⟨121, by decide⟩, ⟨122, by decide⟩, ⟨124, by decide⟩, ⟨125, by decide⟩, ⟨126, by decide⟩, ⟨128, by decide⟩, ⟨129, by decide⟩, ⟨131, by decide⟩, ⟨132, by decide⟩, ⟨133, by decide⟩, ⟨135, by decide⟩, ⟨136, by decide⟩, ⟨137, by decide⟩, ⟨138, by decide⟩, ⟨139, by decide⟩, ⟨141, by decide⟩, ⟨142, by decide⟩, ⟨143, by decide⟩, ⟨144, by decide⟩, ⟨145, by decide⟩, ⟨146, by decide⟩
}

theorem census19_spec (n : Fin 147) :
    (DBMSourceTree.data (embed19 n)).terminal = true ↔ n ∈ census19 := by
  decide +kernel

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
  simp [embed19]

theorem block_mem19 {n : Fin 5011} (ht : (DBMSourceTree.data n).terminal = true)
    (hlo : 4864 ≤ n.val) (hhi : n.val < 5011) : n ∈ blockIDs19 := by
  refine Finset.mem_image.mpr ⟨⟨n.val - 4864, by omega⟩, ?_, ?_⟩
  · exact (census19_spec _).mp (by
      have he : embed19 ⟨n.val - 4864, by omega⟩ = n := by ext; simp [embed19]; omega
      simpa [he] using ht)
  · ext; simp [embed19]; omega

theorem block_terminal19 {n : Fin 5011} (hn : n ∈ blockIDs19) :
    (DBMSourceTree.data n).terminal = true := by
  rcases Finset.mem_image.mp hn with ⟨m, hm, rfl⟩
  exact (census19_spec m).mpr hm

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

def censusIDs : Finset (Fin 5011) := Finset.univ.biUnion blockIDs

theorem terminalIDs_eq_censusIDs : terminalIDs = censusIDs := by
  ext n
  constructor
  · intro hn
    simp only [terminalIDs, Finset.mem_filter, Finset.mem_univ, true_and] at hn
    by_cases h0 : n.val < 256
    · rw [censusIDs, Finset.mem_biUnion]
      exact ⟨⟨0, by decide⟩, Finset.mem_univ _, block_mem0 hn (by omega) h0⟩
    by_cases h1 : n.val < 512
    · rw [censusIDs, Finset.mem_biUnion]
      exact ⟨⟨1, by decide⟩, Finset.mem_univ _, block_mem1 hn (by omega) h1⟩
    by_cases h2 : n.val < 768
    · rw [censusIDs, Finset.mem_biUnion]
      exact ⟨⟨2, by decide⟩, Finset.mem_univ _, block_mem2 hn (by omega) h2⟩
    by_cases h3 : n.val < 1024
    · rw [censusIDs, Finset.mem_biUnion]
      exact ⟨⟨3, by decide⟩, Finset.mem_univ _, block_mem3 hn (by omega) h3⟩
    by_cases h4 : n.val < 1280
    · rw [censusIDs, Finset.mem_biUnion]
      exact ⟨⟨4, by decide⟩, Finset.mem_univ _, block_mem4 hn (by omega) h4⟩
    by_cases h5 : n.val < 1536
    · rw [censusIDs, Finset.mem_biUnion]
      exact ⟨⟨5, by decide⟩, Finset.mem_univ _, block_mem5 hn (by omega) h5⟩
    by_cases h6 : n.val < 1792
    · rw [censusIDs, Finset.mem_biUnion]
      exact ⟨⟨6, by decide⟩, Finset.mem_univ _, block_mem6 hn (by omega) h6⟩
    by_cases h7 : n.val < 2048
    · rw [censusIDs, Finset.mem_biUnion]
      exact ⟨⟨7, by decide⟩, Finset.mem_univ _, block_mem7 hn (by omega) h7⟩
    by_cases h8 : n.val < 2304
    · rw [censusIDs, Finset.mem_biUnion]
      exact ⟨⟨8, by decide⟩, Finset.mem_univ _, block_mem8 hn (by omega) h8⟩
    by_cases h9 : n.val < 2560
    · rw [censusIDs, Finset.mem_biUnion]
      exact ⟨⟨9, by decide⟩, Finset.mem_univ _, block_mem9 hn (by omega) h9⟩
    by_cases h10 : n.val < 2816
    · rw [censusIDs, Finset.mem_biUnion]
      exact ⟨⟨10, by decide⟩, Finset.mem_univ _, block_mem10 hn (by omega) h10⟩
    by_cases h11 : n.val < 3072
    · rw [censusIDs, Finset.mem_biUnion]
      exact ⟨⟨11, by decide⟩, Finset.mem_univ _, block_mem11 hn (by omega) h11⟩
    by_cases h12 : n.val < 3328
    · rw [censusIDs, Finset.mem_biUnion]
      exact ⟨⟨12, by decide⟩, Finset.mem_univ _, block_mem12 hn (by omega) h12⟩
    by_cases h13 : n.val < 3584
    · rw [censusIDs, Finset.mem_biUnion]
      exact ⟨⟨13, by decide⟩, Finset.mem_univ _, block_mem13 hn (by omega) h13⟩
    by_cases h14 : n.val < 3840
    · rw [censusIDs, Finset.mem_biUnion]
      exact ⟨⟨14, by decide⟩, Finset.mem_univ _, block_mem14 hn (by omega) h14⟩
    by_cases h15 : n.val < 4096
    · rw [censusIDs, Finset.mem_biUnion]
      exact ⟨⟨15, by decide⟩, Finset.mem_univ _, block_mem15 hn (by omega) h15⟩
    by_cases h16 : n.val < 4352
    · rw [censusIDs, Finset.mem_biUnion]
      exact ⟨⟨16, by decide⟩, Finset.mem_univ _, block_mem16 hn (by omega) h16⟩
    by_cases h17 : n.val < 4608
    · rw [censusIDs, Finset.mem_biUnion]
      exact ⟨⟨17, by decide⟩, Finset.mem_univ _, block_mem17 hn (by omega) h17⟩
    by_cases h18 : n.val < 4864
    · rw [censusIDs, Finset.mem_biUnion]
      exact ⟨⟨18, by decide⟩, Finset.mem_univ _, block_mem18 hn (by omega) h18⟩
    by_cases h19 : n.val < 5011
    · rw [censusIDs, Finset.mem_biUnion]
      exact ⟨⟨19, by decide⟩, Finset.mem_univ _, block_mem19 hn (by omega) h19⟩
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

theorem blockIDs_0_1_disjoint : Disjoint blockIDs0 blockIDs1 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs0_upper hi
  have hj' := blockIDs1_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_0_2_disjoint : Disjoint blockIDs0 blockIDs2 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs0_upper hi
  have hj' := blockIDs2_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_0_3_disjoint : Disjoint blockIDs0 blockIDs3 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs0_upper hi
  have hj' := blockIDs3_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_0_4_disjoint : Disjoint blockIDs0 blockIDs4 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs0_upper hi
  have hj' := blockIDs4_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_0_5_disjoint : Disjoint blockIDs0 blockIDs5 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs0_upper hi
  have hj' := blockIDs5_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_0_6_disjoint : Disjoint blockIDs0 blockIDs6 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs0_upper hi
  have hj' := blockIDs6_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_0_7_disjoint : Disjoint blockIDs0 blockIDs7 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs0_upper hi
  have hj' := blockIDs7_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_0_8_disjoint : Disjoint blockIDs0 blockIDs8 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs0_upper hi
  have hj' := blockIDs8_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_0_9_disjoint : Disjoint blockIDs0 blockIDs9 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs0_upper hi
  have hj' := blockIDs9_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_0_10_disjoint : Disjoint blockIDs0 blockIDs10 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs0_upper hi
  have hj' := blockIDs10_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_0_11_disjoint : Disjoint blockIDs0 blockIDs11 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs0_upper hi
  have hj' := blockIDs11_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_0_12_disjoint : Disjoint blockIDs0 blockIDs12 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs0_upper hi
  have hj' := blockIDs12_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_0_13_disjoint : Disjoint blockIDs0 blockIDs13 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs0_upper hi
  have hj' := blockIDs13_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_0_14_disjoint : Disjoint blockIDs0 blockIDs14 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs0_upper hi
  have hj' := blockIDs14_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_0_15_disjoint : Disjoint blockIDs0 blockIDs15 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs0_upper hi
  have hj' := blockIDs15_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_0_16_disjoint : Disjoint blockIDs0 blockIDs16 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs0_upper hi
  have hj' := blockIDs16_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_0_17_disjoint : Disjoint blockIDs0 blockIDs17 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs0_upper hi
  have hj' := blockIDs17_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_0_18_disjoint : Disjoint blockIDs0 blockIDs18 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs0_upper hi
  have hj' := blockIDs18_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_0_19_disjoint : Disjoint blockIDs0 blockIDs19 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs0_upper hi
  have hj' := blockIDs19_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_1_2_disjoint : Disjoint blockIDs1 blockIDs2 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs1_upper hi
  have hj' := blockIDs2_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_1_3_disjoint : Disjoint blockIDs1 blockIDs3 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs1_upper hi
  have hj' := blockIDs3_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_1_4_disjoint : Disjoint blockIDs1 blockIDs4 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs1_upper hi
  have hj' := blockIDs4_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_1_5_disjoint : Disjoint blockIDs1 blockIDs5 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs1_upper hi
  have hj' := blockIDs5_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_1_6_disjoint : Disjoint blockIDs1 blockIDs6 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs1_upper hi
  have hj' := blockIDs6_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_1_7_disjoint : Disjoint blockIDs1 blockIDs7 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs1_upper hi
  have hj' := blockIDs7_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_1_8_disjoint : Disjoint blockIDs1 blockIDs8 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs1_upper hi
  have hj' := blockIDs8_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_1_9_disjoint : Disjoint blockIDs1 blockIDs9 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs1_upper hi
  have hj' := blockIDs9_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_1_10_disjoint : Disjoint blockIDs1 blockIDs10 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs1_upper hi
  have hj' := blockIDs10_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_1_11_disjoint : Disjoint blockIDs1 blockIDs11 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs1_upper hi
  have hj' := blockIDs11_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_1_12_disjoint : Disjoint blockIDs1 blockIDs12 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs1_upper hi
  have hj' := blockIDs12_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_1_13_disjoint : Disjoint blockIDs1 blockIDs13 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs1_upper hi
  have hj' := blockIDs13_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_1_14_disjoint : Disjoint blockIDs1 blockIDs14 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs1_upper hi
  have hj' := blockIDs14_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_1_15_disjoint : Disjoint blockIDs1 blockIDs15 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs1_upper hi
  have hj' := blockIDs15_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_1_16_disjoint : Disjoint blockIDs1 blockIDs16 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs1_upper hi
  have hj' := blockIDs16_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_1_17_disjoint : Disjoint blockIDs1 blockIDs17 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs1_upper hi
  have hj' := blockIDs17_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_1_18_disjoint : Disjoint blockIDs1 blockIDs18 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs1_upper hi
  have hj' := blockIDs18_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_1_19_disjoint : Disjoint blockIDs1 blockIDs19 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs1_upper hi
  have hj' := blockIDs19_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_2_3_disjoint : Disjoint blockIDs2 blockIDs3 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs2_upper hi
  have hj' := blockIDs3_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_2_4_disjoint : Disjoint blockIDs2 blockIDs4 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs2_upper hi
  have hj' := blockIDs4_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_2_5_disjoint : Disjoint blockIDs2 blockIDs5 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs2_upper hi
  have hj' := blockIDs5_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_2_6_disjoint : Disjoint blockIDs2 blockIDs6 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs2_upper hi
  have hj' := blockIDs6_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_2_7_disjoint : Disjoint blockIDs2 blockIDs7 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs2_upper hi
  have hj' := blockIDs7_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_2_8_disjoint : Disjoint blockIDs2 blockIDs8 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs2_upper hi
  have hj' := blockIDs8_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_2_9_disjoint : Disjoint blockIDs2 blockIDs9 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs2_upper hi
  have hj' := blockIDs9_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_2_10_disjoint : Disjoint blockIDs2 blockIDs10 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs2_upper hi
  have hj' := blockIDs10_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_2_11_disjoint : Disjoint blockIDs2 blockIDs11 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs2_upper hi
  have hj' := blockIDs11_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_2_12_disjoint : Disjoint blockIDs2 blockIDs12 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs2_upper hi
  have hj' := blockIDs12_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_2_13_disjoint : Disjoint blockIDs2 blockIDs13 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs2_upper hi
  have hj' := blockIDs13_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_2_14_disjoint : Disjoint blockIDs2 blockIDs14 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs2_upper hi
  have hj' := blockIDs14_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_2_15_disjoint : Disjoint blockIDs2 blockIDs15 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs2_upper hi
  have hj' := blockIDs15_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_2_16_disjoint : Disjoint blockIDs2 blockIDs16 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs2_upper hi
  have hj' := blockIDs16_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_2_17_disjoint : Disjoint blockIDs2 blockIDs17 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs2_upper hi
  have hj' := blockIDs17_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_2_18_disjoint : Disjoint blockIDs2 blockIDs18 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs2_upper hi
  have hj' := blockIDs18_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_2_19_disjoint : Disjoint blockIDs2 blockIDs19 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs2_upper hi
  have hj' := blockIDs19_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_3_4_disjoint : Disjoint blockIDs3 blockIDs4 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs3_upper hi
  have hj' := blockIDs4_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_3_5_disjoint : Disjoint blockIDs3 blockIDs5 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs3_upper hi
  have hj' := blockIDs5_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_3_6_disjoint : Disjoint blockIDs3 blockIDs6 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs3_upper hi
  have hj' := blockIDs6_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_3_7_disjoint : Disjoint blockIDs3 blockIDs7 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs3_upper hi
  have hj' := blockIDs7_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_3_8_disjoint : Disjoint blockIDs3 blockIDs8 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs3_upper hi
  have hj' := blockIDs8_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_3_9_disjoint : Disjoint blockIDs3 blockIDs9 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs3_upper hi
  have hj' := blockIDs9_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_3_10_disjoint : Disjoint blockIDs3 blockIDs10 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs3_upper hi
  have hj' := blockIDs10_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_3_11_disjoint : Disjoint blockIDs3 blockIDs11 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs3_upper hi
  have hj' := blockIDs11_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_3_12_disjoint : Disjoint blockIDs3 blockIDs12 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs3_upper hi
  have hj' := blockIDs12_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_3_13_disjoint : Disjoint blockIDs3 blockIDs13 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs3_upper hi
  have hj' := blockIDs13_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_3_14_disjoint : Disjoint blockIDs3 blockIDs14 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs3_upper hi
  have hj' := blockIDs14_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_3_15_disjoint : Disjoint blockIDs3 blockIDs15 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs3_upper hi
  have hj' := blockIDs15_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_3_16_disjoint : Disjoint blockIDs3 blockIDs16 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs3_upper hi
  have hj' := blockIDs16_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_3_17_disjoint : Disjoint blockIDs3 blockIDs17 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs3_upper hi
  have hj' := blockIDs17_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_3_18_disjoint : Disjoint blockIDs3 blockIDs18 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs3_upper hi
  have hj' := blockIDs18_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_3_19_disjoint : Disjoint blockIDs3 blockIDs19 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs3_upper hi
  have hj' := blockIDs19_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_4_5_disjoint : Disjoint blockIDs4 blockIDs5 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs4_upper hi
  have hj' := blockIDs5_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_4_6_disjoint : Disjoint blockIDs4 blockIDs6 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs4_upper hi
  have hj' := blockIDs6_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_4_7_disjoint : Disjoint blockIDs4 blockIDs7 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs4_upper hi
  have hj' := blockIDs7_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_4_8_disjoint : Disjoint blockIDs4 blockIDs8 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs4_upper hi
  have hj' := blockIDs8_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_4_9_disjoint : Disjoint blockIDs4 blockIDs9 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs4_upper hi
  have hj' := blockIDs9_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_4_10_disjoint : Disjoint blockIDs4 blockIDs10 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs4_upper hi
  have hj' := blockIDs10_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_4_11_disjoint : Disjoint blockIDs4 blockIDs11 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs4_upper hi
  have hj' := blockIDs11_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_4_12_disjoint : Disjoint blockIDs4 blockIDs12 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs4_upper hi
  have hj' := blockIDs12_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_4_13_disjoint : Disjoint blockIDs4 blockIDs13 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs4_upper hi
  have hj' := blockIDs13_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_4_14_disjoint : Disjoint blockIDs4 blockIDs14 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs4_upper hi
  have hj' := blockIDs14_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_4_15_disjoint : Disjoint blockIDs4 blockIDs15 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs4_upper hi
  have hj' := blockIDs15_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_4_16_disjoint : Disjoint blockIDs4 blockIDs16 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs4_upper hi
  have hj' := blockIDs16_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_4_17_disjoint : Disjoint blockIDs4 blockIDs17 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs4_upper hi
  have hj' := blockIDs17_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_4_18_disjoint : Disjoint blockIDs4 blockIDs18 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs4_upper hi
  have hj' := blockIDs18_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_4_19_disjoint : Disjoint blockIDs4 blockIDs19 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs4_upper hi
  have hj' := blockIDs19_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_5_6_disjoint : Disjoint blockIDs5 blockIDs6 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs5_upper hi
  have hj' := blockIDs6_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_5_7_disjoint : Disjoint blockIDs5 blockIDs7 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs5_upper hi
  have hj' := blockIDs7_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_5_8_disjoint : Disjoint blockIDs5 blockIDs8 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs5_upper hi
  have hj' := blockIDs8_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_5_9_disjoint : Disjoint blockIDs5 blockIDs9 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs5_upper hi
  have hj' := blockIDs9_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_5_10_disjoint : Disjoint blockIDs5 blockIDs10 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs5_upper hi
  have hj' := blockIDs10_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_5_11_disjoint : Disjoint blockIDs5 blockIDs11 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs5_upper hi
  have hj' := blockIDs11_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_5_12_disjoint : Disjoint blockIDs5 blockIDs12 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs5_upper hi
  have hj' := blockIDs12_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_5_13_disjoint : Disjoint blockIDs5 blockIDs13 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs5_upper hi
  have hj' := blockIDs13_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_5_14_disjoint : Disjoint blockIDs5 blockIDs14 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs5_upper hi
  have hj' := blockIDs14_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_5_15_disjoint : Disjoint blockIDs5 blockIDs15 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs5_upper hi
  have hj' := blockIDs15_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_5_16_disjoint : Disjoint blockIDs5 blockIDs16 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs5_upper hi
  have hj' := blockIDs16_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_5_17_disjoint : Disjoint blockIDs5 blockIDs17 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs5_upper hi
  have hj' := blockIDs17_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_5_18_disjoint : Disjoint blockIDs5 blockIDs18 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs5_upper hi
  have hj' := blockIDs18_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_5_19_disjoint : Disjoint blockIDs5 blockIDs19 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs5_upper hi
  have hj' := blockIDs19_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_6_7_disjoint : Disjoint blockIDs6 blockIDs7 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs6_upper hi
  have hj' := blockIDs7_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_6_8_disjoint : Disjoint blockIDs6 blockIDs8 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs6_upper hi
  have hj' := blockIDs8_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_6_9_disjoint : Disjoint blockIDs6 blockIDs9 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs6_upper hi
  have hj' := blockIDs9_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_6_10_disjoint : Disjoint blockIDs6 blockIDs10 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs6_upper hi
  have hj' := blockIDs10_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_6_11_disjoint : Disjoint blockIDs6 blockIDs11 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs6_upper hi
  have hj' := blockIDs11_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_6_12_disjoint : Disjoint blockIDs6 blockIDs12 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs6_upper hi
  have hj' := blockIDs12_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_6_13_disjoint : Disjoint blockIDs6 blockIDs13 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs6_upper hi
  have hj' := blockIDs13_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_6_14_disjoint : Disjoint blockIDs6 blockIDs14 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs6_upper hi
  have hj' := blockIDs14_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_6_15_disjoint : Disjoint blockIDs6 blockIDs15 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs6_upper hi
  have hj' := blockIDs15_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_6_16_disjoint : Disjoint blockIDs6 blockIDs16 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs6_upper hi
  have hj' := blockIDs16_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_6_17_disjoint : Disjoint blockIDs6 blockIDs17 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs6_upper hi
  have hj' := blockIDs17_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_6_18_disjoint : Disjoint blockIDs6 blockIDs18 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs6_upper hi
  have hj' := blockIDs18_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_6_19_disjoint : Disjoint blockIDs6 blockIDs19 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs6_upper hi
  have hj' := blockIDs19_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_7_8_disjoint : Disjoint blockIDs7 blockIDs8 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs7_upper hi
  have hj' := blockIDs8_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_7_9_disjoint : Disjoint blockIDs7 blockIDs9 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs7_upper hi
  have hj' := blockIDs9_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_7_10_disjoint : Disjoint blockIDs7 blockIDs10 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs7_upper hi
  have hj' := blockIDs10_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_7_11_disjoint : Disjoint blockIDs7 blockIDs11 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs7_upper hi
  have hj' := blockIDs11_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_7_12_disjoint : Disjoint blockIDs7 blockIDs12 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs7_upper hi
  have hj' := blockIDs12_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_7_13_disjoint : Disjoint blockIDs7 blockIDs13 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs7_upper hi
  have hj' := blockIDs13_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_7_14_disjoint : Disjoint blockIDs7 blockIDs14 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs7_upper hi
  have hj' := blockIDs14_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_7_15_disjoint : Disjoint blockIDs7 blockIDs15 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs7_upper hi
  have hj' := blockIDs15_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_7_16_disjoint : Disjoint blockIDs7 blockIDs16 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs7_upper hi
  have hj' := blockIDs16_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_7_17_disjoint : Disjoint blockIDs7 blockIDs17 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs7_upper hi
  have hj' := blockIDs17_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_7_18_disjoint : Disjoint blockIDs7 blockIDs18 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs7_upper hi
  have hj' := blockIDs18_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_7_19_disjoint : Disjoint blockIDs7 blockIDs19 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs7_upper hi
  have hj' := blockIDs19_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_8_9_disjoint : Disjoint blockIDs8 blockIDs9 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs8_upper hi
  have hj' := blockIDs9_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_8_10_disjoint : Disjoint blockIDs8 blockIDs10 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs8_upper hi
  have hj' := blockIDs10_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_8_11_disjoint : Disjoint blockIDs8 blockIDs11 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs8_upper hi
  have hj' := blockIDs11_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_8_12_disjoint : Disjoint blockIDs8 blockIDs12 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs8_upper hi
  have hj' := blockIDs12_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_8_13_disjoint : Disjoint blockIDs8 blockIDs13 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs8_upper hi
  have hj' := blockIDs13_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_8_14_disjoint : Disjoint blockIDs8 blockIDs14 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs8_upper hi
  have hj' := blockIDs14_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_8_15_disjoint : Disjoint blockIDs8 blockIDs15 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs8_upper hi
  have hj' := blockIDs15_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_8_16_disjoint : Disjoint blockIDs8 blockIDs16 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs8_upper hi
  have hj' := blockIDs16_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_8_17_disjoint : Disjoint blockIDs8 blockIDs17 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs8_upper hi
  have hj' := blockIDs17_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_8_18_disjoint : Disjoint blockIDs8 blockIDs18 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs8_upper hi
  have hj' := blockIDs18_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_8_19_disjoint : Disjoint blockIDs8 blockIDs19 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs8_upper hi
  have hj' := blockIDs19_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_9_10_disjoint : Disjoint blockIDs9 blockIDs10 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs9_upper hi
  have hj' := blockIDs10_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_9_11_disjoint : Disjoint blockIDs9 blockIDs11 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs9_upper hi
  have hj' := blockIDs11_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_9_12_disjoint : Disjoint blockIDs9 blockIDs12 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs9_upper hi
  have hj' := blockIDs12_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_9_13_disjoint : Disjoint blockIDs9 blockIDs13 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs9_upper hi
  have hj' := blockIDs13_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_9_14_disjoint : Disjoint blockIDs9 blockIDs14 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs9_upper hi
  have hj' := blockIDs14_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_9_15_disjoint : Disjoint blockIDs9 blockIDs15 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs9_upper hi
  have hj' := blockIDs15_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_9_16_disjoint : Disjoint blockIDs9 blockIDs16 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs9_upper hi
  have hj' := blockIDs16_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_9_17_disjoint : Disjoint blockIDs9 blockIDs17 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs9_upper hi
  have hj' := blockIDs17_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_9_18_disjoint : Disjoint blockIDs9 blockIDs18 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs9_upper hi
  have hj' := blockIDs18_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_9_19_disjoint : Disjoint blockIDs9 blockIDs19 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs9_upper hi
  have hj' := blockIDs19_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_10_11_disjoint : Disjoint blockIDs10 blockIDs11 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs10_upper hi
  have hj' := blockIDs11_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_10_12_disjoint : Disjoint blockIDs10 blockIDs12 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs10_upper hi
  have hj' := blockIDs12_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_10_13_disjoint : Disjoint blockIDs10 blockIDs13 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs10_upper hi
  have hj' := blockIDs13_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_10_14_disjoint : Disjoint blockIDs10 blockIDs14 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs10_upper hi
  have hj' := blockIDs14_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_10_15_disjoint : Disjoint blockIDs10 blockIDs15 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs10_upper hi
  have hj' := blockIDs15_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_10_16_disjoint : Disjoint blockIDs10 blockIDs16 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs10_upper hi
  have hj' := blockIDs16_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_10_17_disjoint : Disjoint blockIDs10 blockIDs17 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs10_upper hi
  have hj' := blockIDs17_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_10_18_disjoint : Disjoint blockIDs10 blockIDs18 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs10_upper hi
  have hj' := blockIDs18_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_10_19_disjoint : Disjoint blockIDs10 blockIDs19 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs10_upper hi
  have hj' := blockIDs19_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_11_12_disjoint : Disjoint blockIDs11 blockIDs12 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs11_upper hi
  have hj' := blockIDs12_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_11_13_disjoint : Disjoint blockIDs11 blockIDs13 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs11_upper hi
  have hj' := blockIDs13_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_11_14_disjoint : Disjoint blockIDs11 blockIDs14 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs11_upper hi
  have hj' := blockIDs14_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_11_15_disjoint : Disjoint blockIDs11 blockIDs15 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs11_upper hi
  have hj' := blockIDs15_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_11_16_disjoint : Disjoint blockIDs11 blockIDs16 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs11_upper hi
  have hj' := blockIDs16_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_11_17_disjoint : Disjoint blockIDs11 blockIDs17 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs11_upper hi
  have hj' := blockIDs17_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_11_18_disjoint : Disjoint blockIDs11 blockIDs18 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs11_upper hi
  have hj' := blockIDs18_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_11_19_disjoint : Disjoint blockIDs11 blockIDs19 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs11_upper hi
  have hj' := blockIDs19_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_12_13_disjoint : Disjoint blockIDs12 blockIDs13 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs12_upper hi
  have hj' := blockIDs13_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_12_14_disjoint : Disjoint blockIDs12 blockIDs14 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs12_upper hi
  have hj' := blockIDs14_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_12_15_disjoint : Disjoint blockIDs12 blockIDs15 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs12_upper hi
  have hj' := blockIDs15_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_12_16_disjoint : Disjoint blockIDs12 blockIDs16 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs12_upper hi
  have hj' := blockIDs16_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_12_17_disjoint : Disjoint blockIDs12 blockIDs17 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs12_upper hi
  have hj' := blockIDs17_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_12_18_disjoint : Disjoint blockIDs12 blockIDs18 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs12_upper hi
  have hj' := blockIDs18_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_12_19_disjoint : Disjoint blockIDs12 blockIDs19 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs12_upper hi
  have hj' := blockIDs19_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_13_14_disjoint : Disjoint blockIDs13 blockIDs14 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs13_upper hi
  have hj' := blockIDs14_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_13_15_disjoint : Disjoint blockIDs13 blockIDs15 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs13_upper hi
  have hj' := blockIDs15_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_13_16_disjoint : Disjoint blockIDs13 blockIDs16 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs13_upper hi
  have hj' := blockIDs16_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_13_17_disjoint : Disjoint blockIDs13 blockIDs17 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs13_upper hi
  have hj' := blockIDs17_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_13_18_disjoint : Disjoint blockIDs13 blockIDs18 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs13_upper hi
  have hj' := blockIDs18_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_13_19_disjoint : Disjoint blockIDs13 blockIDs19 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs13_upper hi
  have hj' := blockIDs19_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_14_15_disjoint : Disjoint blockIDs14 blockIDs15 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs14_upper hi
  have hj' := blockIDs15_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_14_16_disjoint : Disjoint blockIDs14 blockIDs16 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs14_upper hi
  have hj' := blockIDs16_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_14_17_disjoint : Disjoint blockIDs14 blockIDs17 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs14_upper hi
  have hj' := blockIDs17_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_14_18_disjoint : Disjoint blockIDs14 blockIDs18 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs14_upper hi
  have hj' := blockIDs18_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_14_19_disjoint : Disjoint blockIDs14 blockIDs19 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs14_upper hi
  have hj' := blockIDs19_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_15_16_disjoint : Disjoint blockIDs15 blockIDs16 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs15_upper hi
  have hj' := blockIDs16_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_15_17_disjoint : Disjoint blockIDs15 blockIDs17 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs15_upper hi
  have hj' := blockIDs17_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_15_18_disjoint : Disjoint blockIDs15 blockIDs18 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs15_upper hi
  have hj' := blockIDs18_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_15_19_disjoint : Disjoint blockIDs15 blockIDs19 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs15_upper hi
  have hj' := blockIDs19_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_16_17_disjoint : Disjoint blockIDs16 blockIDs17 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs16_upper hi
  have hj' := blockIDs17_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_16_18_disjoint : Disjoint blockIDs16 blockIDs18 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs16_upper hi
  have hj' := blockIDs18_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_16_19_disjoint : Disjoint blockIDs16 blockIDs19 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs16_upper hi
  have hj' := blockIDs19_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_17_18_disjoint : Disjoint blockIDs17 blockIDs18 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs17_upper hi
  have hj' := blockIDs18_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_17_19_disjoint : Disjoint blockIDs17 blockIDs19 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs17_upper hi
  have hj' := blockIDs19_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_18_19_disjoint : Disjoint blockIDs18 blockIDs19 := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi' := blockIDs18_upper hi
  have hj' := blockIDs19_lower hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi' hj'
  omega

theorem blockIDs_pairwiseDisjoint :
    ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, i ≠ j → Disjoint (blockIDs i) (blockIDs j) := by
  intro i _ j _ hij
  fin_cases i <;> fin_cases j <;> first
      | contradiction
      | exact blockIDs_0_1_disjoint
      | contradiction
      | exact blockIDs_0_2_disjoint
      | contradiction
      | exact blockIDs_0_3_disjoint
      | contradiction
      | exact blockIDs_0_4_disjoint
      | contradiction
      | exact blockIDs_0_5_disjoint
      | contradiction
      | exact blockIDs_0_6_disjoint
      | contradiction
      | exact blockIDs_0_7_disjoint
      | contradiction
      | exact blockIDs_0_8_disjoint
      | contradiction
      | exact blockIDs_0_9_disjoint
      | contradiction
      | exact blockIDs_0_10_disjoint
      | contradiction
      | exact blockIDs_0_11_disjoint
      | contradiction
      | exact blockIDs_0_12_disjoint
      | contradiction
      | exact blockIDs_0_13_disjoint
      | contradiction
      | exact blockIDs_0_14_disjoint
      | contradiction
      | exact blockIDs_0_15_disjoint
      | contradiction
      | exact blockIDs_0_16_disjoint
      | contradiction
      | exact blockIDs_0_17_disjoint
      | contradiction
      | exact blockIDs_0_18_disjoint
      | contradiction
      | exact blockIDs_0_19_disjoint
      | contradiction
      | exact blockIDs_1_2_disjoint
      | contradiction
      | exact blockIDs_1_3_disjoint
      | contradiction
      | exact blockIDs_1_4_disjoint
      | contradiction
      | exact blockIDs_1_5_disjoint
      | contradiction
      | exact blockIDs_1_6_disjoint
      | contradiction
      | exact blockIDs_1_7_disjoint
      | contradiction
      | exact blockIDs_1_8_disjoint
      | contradiction
      | exact blockIDs_1_9_disjoint
      | contradiction
      | exact blockIDs_1_10_disjoint
      | contradiction
      | exact blockIDs_1_11_disjoint
      | contradiction
      | exact blockIDs_1_12_disjoint
      | contradiction
      | exact blockIDs_1_13_disjoint
      | contradiction
      | exact blockIDs_1_14_disjoint
      | contradiction
      | exact blockIDs_1_15_disjoint
      | contradiction
      | exact blockIDs_1_16_disjoint
      | contradiction
      | exact blockIDs_1_17_disjoint
      | contradiction
      | exact blockIDs_1_18_disjoint
      | contradiction
      | exact blockIDs_1_19_disjoint
      | contradiction
      | exact blockIDs_2_3_disjoint
      | contradiction
      | exact blockIDs_2_4_disjoint
      | contradiction
      | exact blockIDs_2_5_disjoint
      | contradiction
      | exact blockIDs_2_6_disjoint
      | contradiction
      | exact blockIDs_2_7_disjoint
      | contradiction
      | exact blockIDs_2_8_disjoint
      | contradiction
      | exact blockIDs_2_9_disjoint
      | contradiction
      | exact blockIDs_2_10_disjoint
      | contradiction
      | exact blockIDs_2_11_disjoint
      | contradiction
      | exact blockIDs_2_12_disjoint
      | contradiction
      | exact blockIDs_2_13_disjoint
      | contradiction
      | exact blockIDs_2_14_disjoint
      | contradiction
      | exact blockIDs_2_15_disjoint
      | contradiction
      | exact blockIDs_2_16_disjoint
      | contradiction
      | exact blockIDs_2_17_disjoint
      | contradiction
      | exact blockIDs_2_18_disjoint
      | contradiction
      | exact blockIDs_2_19_disjoint
      | contradiction
      | exact blockIDs_3_4_disjoint
      | contradiction
      | exact blockIDs_3_5_disjoint
      | contradiction
      | exact blockIDs_3_6_disjoint
      | contradiction
      | exact blockIDs_3_7_disjoint
      | contradiction
      | exact blockIDs_3_8_disjoint
      | contradiction
      | exact blockIDs_3_9_disjoint
      | contradiction
      | exact blockIDs_3_10_disjoint
      | contradiction
      | exact blockIDs_3_11_disjoint
      | contradiction
      | exact blockIDs_3_12_disjoint
      | contradiction
      | exact blockIDs_3_13_disjoint
      | contradiction
      | exact blockIDs_3_14_disjoint
      | contradiction
      | exact blockIDs_3_15_disjoint
      | contradiction
      | exact blockIDs_3_16_disjoint
      | contradiction
      | exact blockIDs_3_17_disjoint
      | contradiction
      | exact blockIDs_3_18_disjoint
      | contradiction
      | exact blockIDs_3_19_disjoint
      | contradiction
      | exact blockIDs_4_5_disjoint
      | contradiction
      | exact blockIDs_4_6_disjoint
      | contradiction
      | exact blockIDs_4_7_disjoint
      | contradiction
      | exact blockIDs_4_8_disjoint
      | contradiction
      | exact blockIDs_4_9_disjoint
      | contradiction
      | exact blockIDs_4_10_disjoint
      | contradiction
      | exact blockIDs_4_11_disjoint
      | contradiction
      | exact blockIDs_4_12_disjoint
      | contradiction
      | exact blockIDs_4_13_disjoint
      | contradiction
      | exact blockIDs_4_14_disjoint
      | contradiction
      | exact blockIDs_4_15_disjoint
      | contradiction
      | exact blockIDs_4_16_disjoint
      | contradiction
      | exact blockIDs_4_17_disjoint
      | contradiction
      | exact blockIDs_4_18_disjoint
      | contradiction
      | exact blockIDs_4_19_disjoint
      | contradiction
      | exact blockIDs_5_6_disjoint
      | contradiction
      | exact blockIDs_5_7_disjoint
      | contradiction
      | exact blockIDs_5_8_disjoint
      | contradiction
      | exact blockIDs_5_9_disjoint
      | contradiction
      | exact blockIDs_5_10_disjoint
      | contradiction
      | exact blockIDs_5_11_disjoint
      | contradiction
      | exact blockIDs_5_12_disjoint
      | contradiction
      | exact blockIDs_5_13_disjoint
      | contradiction
      | exact blockIDs_5_14_disjoint
      | contradiction
      | exact blockIDs_5_15_disjoint
      | contradiction
      | exact blockIDs_5_16_disjoint
      | contradiction
      | exact blockIDs_5_17_disjoint
      | contradiction
      | exact blockIDs_5_18_disjoint
      | contradiction
      | exact blockIDs_5_19_disjoint
      | contradiction
      | exact blockIDs_6_7_disjoint
      | contradiction
      | exact blockIDs_6_8_disjoint
      | contradiction
      | exact blockIDs_6_9_disjoint
      | contradiction
      | exact blockIDs_6_10_disjoint
      | contradiction
      | exact blockIDs_6_11_disjoint
      | contradiction
      | exact blockIDs_6_12_disjoint
      | contradiction
      | exact blockIDs_6_13_disjoint
      | contradiction
      | exact blockIDs_6_14_disjoint
      | contradiction
      | exact blockIDs_6_15_disjoint
      | contradiction
      | exact blockIDs_6_16_disjoint
      | contradiction
      | exact blockIDs_6_17_disjoint
      | contradiction
      | exact blockIDs_6_18_disjoint
      | contradiction
      | exact blockIDs_6_19_disjoint
      | contradiction
      | exact blockIDs_7_8_disjoint
      | contradiction
      | exact blockIDs_7_9_disjoint
      | contradiction
      | exact blockIDs_7_10_disjoint
      | contradiction
      | exact blockIDs_7_11_disjoint
      | contradiction
      | exact blockIDs_7_12_disjoint
      | contradiction
      | exact blockIDs_7_13_disjoint
      | contradiction
      | exact blockIDs_7_14_disjoint
      | contradiction
      | exact blockIDs_7_15_disjoint
      | contradiction
      | exact blockIDs_7_16_disjoint
      | contradiction
      | exact blockIDs_7_17_disjoint
      | contradiction
      | exact blockIDs_7_18_disjoint
      | contradiction
      | exact blockIDs_7_19_disjoint
      | contradiction
      | exact blockIDs_8_9_disjoint
      | contradiction
      | exact blockIDs_8_10_disjoint
      | contradiction
      | exact blockIDs_8_11_disjoint
      | contradiction
      | exact blockIDs_8_12_disjoint
      | contradiction
      | exact blockIDs_8_13_disjoint
      | contradiction
      | exact blockIDs_8_14_disjoint
      | contradiction
      | exact blockIDs_8_15_disjoint
      | contradiction
      | exact blockIDs_8_16_disjoint
      | contradiction
      | exact blockIDs_8_17_disjoint
      | contradiction
      | exact blockIDs_8_18_disjoint
      | contradiction
      | exact blockIDs_8_19_disjoint
      | contradiction
      | exact blockIDs_9_10_disjoint
      | contradiction
      | exact blockIDs_9_11_disjoint
      | contradiction
      | exact blockIDs_9_12_disjoint
      | contradiction
      | exact blockIDs_9_13_disjoint
      | contradiction
      | exact blockIDs_9_14_disjoint
      | contradiction
      | exact blockIDs_9_15_disjoint
      | contradiction
      | exact blockIDs_9_16_disjoint
      | contradiction
      | exact blockIDs_9_17_disjoint
      | contradiction
      | exact blockIDs_9_18_disjoint
      | contradiction
      | exact blockIDs_9_19_disjoint
      | contradiction
      | exact blockIDs_10_11_disjoint
      | contradiction
      | exact blockIDs_10_12_disjoint
      | contradiction
      | exact blockIDs_10_13_disjoint
      | contradiction
      | exact blockIDs_10_14_disjoint
      | contradiction
      | exact blockIDs_10_15_disjoint
      | contradiction
      | exact blockIDs_10_16_disjoint
      | contradiction
      | exact blockIDs_10_17_disjoint
      | contradiction
      | exact blockIDs_10_18_disjoint
      | contradiction
      | exact blockIDs_10_19_disjoint
      | contradiction
      | exact blockIDs_11_12_disjoint
      | contradiction
      | exact blockIDs_11_13_disjoint
      | contradiction
      | exact blockIDs_11_14_disjoint
      | contradiction
      | exact blockIDs_11_15_disjoint
      | contradiction
      | exact blockIDs_11_16_disjoint
      | contradiction
      | exact blockIDs_11_17_disjoint
      | contradiction
      | exact blockIDs_11_18_disjoint
      | contradiction
      | exact blockIDs_11_19_disjoint
      | contradiction
      | exact blockIDs_12_13_disjoint
      | contradiction
      | exact blockIDs_12_14_disjoint
      | contradiction
      | exact blockIDs_12_15_disjoint
      | contradiction
      | exact blockIDs_12_16_disjoint
      | contradiction
      | exact blockIDs_12_17_disjoint
      | contradiction
      | exact blockIDs_12_18_disjoint
      | contradiction
      | exact blockIDs_12_19_disjoint
      | contradiction
      | exact blockIDs_13_14_disjoint
      | contradiction
      | exact blockIDs_13_15_disjoint
      | contradiction
      | exact blockIDs_13_16_disjoint
      | contradiction
      | exact blockIDs_13_17_disjoint
      | contradiction
      | exact blockIDs_13_18_disjoint
      | contradiction
      | exact blockIDs_13_19_disjoint
      | contradiction
      | exact blockIDs_14_15_disjoint
      | contradiction
      | exact blockIDs_14_16_disjoint
      | contradiction
      | exact blockIDs_14_17_disjoint
      | contradiction
      | exact blockIDs_14_18_disjoint
      | contradiction
      | exact blockIDs_14_19_disjoint
      | contradiction
      | exact blockIDs_15_16_disjoint
      | contradiction
      | exact blockIDs_15_17_disjoint
      | contradiction
      | exact blockIDs_15_18_disjoint
      | contradiction
      | exact blockIDs_15_19_disjoint
      | contradiction
      | exact blockIDs_16_17_disjoint
      | contradiction
      | exact blockIDs_16_18_disjoint
      | contradiction
      | exact blockIDs_16_19_disjoint
      | contradiction
      | exact blockIDs_17_18_disjoint
      | contradiction
      | exact blockIDs_17_19_disjoint
      | contradiction
      | exact blockIDs_18_19_disjoint

theorem censusIDs_card : censusIDs.card = 2506 := by
  rw [censusIDs, Finset.card_biUnion blockIDs_pairwiseDisjoint]
  simp [blockIDs,blockIDs0_card, blockIDs1_card, blockIDs2_card, blockIDs3_card, blockIDs4_card, blockIDs5_card, blockIDs6_card, blockIDs7_card, blockIDs8_card, blockIDs9_card, blockIDs10_card, blockIDs11_card, blockIDs12_card, blockIDs13_card, blockIDs14_card, blockIDs15_card, blockIDs16_card, blockIDs17_card, blockIDs18_card, blockIDs19_card]
  norm_num

theorem terminalIDs_card : terminalIDs.card = 2506 := by
  rw [terminalIDs_eq_censusIDs, censusIDs_card]

end
end N11Formalization.EnergyTerminalBatchB13RefineSixteenResidual
