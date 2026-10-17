/-
n11-formalization —— **接口清单（轻量，只打印类型与身份；不证任何新命题）**。

写域：本文件（新件；evidence 先核，随后 src target build）。
**注意**：本文件**不证明** `hbound` ✗ —— 它把原主命题链条上**唯一剩余**的接口写成一条可读的 type，
并把已达到的「standalone 原 root 达到」的完整 type/axioms 打出来，便于集成方引用。
-/
import Mathlib
import N11Formalization.FlashAttainmentRstarConsumer
import N11Formalization.C892Hook

set_option pp.explicit true
set_option pp.universes false

noncomputable section

namespace N11Formalization.FlashAttainmentTypes

open N11Formalization

/-! ## §1 standalone 原 root 达到：完整（全显式）type -/

#check @N11Formalization.FlashAttainmentRstarConsumer.covers_of_specified_root_actual
#check @N11Formalization.FlashAttainmentRstarConsumer.covers_of_any_specified_root_actual
#check @N11Formalization.FlashAttainmentRstarConsumer.exists_root_covers_actual
#check @N11Formalization.FlashTilingHubChordSigns.actualSigns

/-! ## §2 C891 根的身份（源同一性字段，供集成对照） -/

#check @N11Formalization.C891RootSpec.root
#check @N11Formalization.C891RootSpec.root_mem
#check @N11Formalization.C891RootSpec.root_unique
#check @N11Formalization.Rstar
#check @N11Formalization.Rstar_mem_box
#check @N11Formalization.Rstar_lt_R0_of_bound
#check @N11Formalization.GridBridge.nd_box_final

/-! ## §3 原主命题：**唯一剩余接口** `hbound`（本文件不证它 ✗） -/

#check @N11Formalization.n11_main_of_c892_hook
-- `hbound : ∀ (r : ℝ) (c : Fin 11 → Point), 0 ≤ r → Covers c r → Rstar S ≤ r`
-- 即：**任意 11 个盘的覆盖半径下界**（全局最优性方向）；本文件只把它作为接口列出。

end N11Formalization.FlashAttainmentTypes
