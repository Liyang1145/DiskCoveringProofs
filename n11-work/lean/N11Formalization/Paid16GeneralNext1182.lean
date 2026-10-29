import N11Formalization.Paid16GeneralNext1182S01
import N11Formalization.Paid16GeneralNext1182S02
import N11Formalization.Paid16GeneralNext1182S03
import N11Formalization.Paid16GeneralNext1182S04
import N11Formalization.Paid16GeneralNext1182S05
import N11Formalization.Paid16GeneralNext1182S06
import N11Formalization.Paid16GeneralNext1182S07
import N11Formalization.Paid16GeneralNext1182S08

import N11Formalization.EnergyTerminalBatchB12

/-! Top aggregate of 1182 packets, assembled from 8 sub-aggregates.
The eight parts are consecutive integer intervals.  Their pairwise
disjointness is proved from literal membership bounds, not by kernel-reducing
168-element `Finset` values. -/
set_option autoImplicit false
namespace N11Formalization.Paid16GeneralNext1182
open Finset
noncomputable section

def part : Fin 8 → Finset (Fin 5011)
  | 0 => Paid16GeneralNext1182S01.newIDs
  | 1 => Paid16GeneralNext1182S02.newIDs
  | 2 => Paid16GeneralNext1182S03.newIDs
  | 3 => Paid16GeneralNext1182S04.newIDs
  | 4 => Paid16GeneralNext1182S05.newIDs
  | 5 => Paid16GeneralNext1182S06.newIDs
  | 6 => Paid16GeneralNext1182S07.newIDs
  | 7 => Paid16GeneralNext1182S08.newIDs
def newIDs : Finset (Fin 5011) := Finset.univ.biUnion part
theorem new_mem (n : Fin 5011) : n ∈ newIDs ↔ n ∈ Paid16GeneralNext1182S01.newIDs ∨ n ∈ Paid16GeneralNext1182S02.newIDs ∨ n ∈ Paid16GeneralNext1182S03.newIDs ∨ n ∈ Paid16GeneralNext1182S04.newIDs ∨ n ∈ Paid16GeneralNext1182S05.newIDs ∨ n ∈ Paid16GeneralNext1182S06.newIDs ∨ n ∈ Paid16GeneralNext1182S07.newIDs ∨ n ∈ Paid16GeneralNext1182S08.newIDs := by
  simp only [newIDs, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i <;> simp_all [part]
  · rintro (h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7)
    · exact ⟨0, by simpa [part] using h0⟩
    · exact ⟨1, by simpa [part] using h1⟩
    · exact ⟨2, by simpa [part] using h2⟩
    · exact ⟨3, by simpa [part] using h3⟩
    · exact ⟨4, by simpa [part] using h4⟩
    · exact ⟨5, by simpa [part] using h5⟩
    · exact ⟨6, by simpa [part] using h6⟩
    · exact ⟨7, by simpa [part] using h7⟩
private theorem block_s01_00_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S01.ids00) : 2565 ≤ n.val ∧ n.val ≤ 2585 := by
  rcases (Paid16GeneralNext1182S01.mem_ids00 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s01_01_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S01.ids01) : 2586 ≤ n.val ∧ n.val ≤ 2606 := by
  rcases (Paid16GeneralNext1182S01.mem_ids01 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s01_02_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S01.ids02) : 2607 ≤ n.val ∧ n.val ≤ 2629 := by
  rcases (Paid16GeneralNext1182S01.mem_ids02 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s01_03_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S01.ids03) : 2630 ≤ n.val ∧ n.val ≤ 2650 := by
  rcases (Paid16GeneralNext1182S01.mem_ids03 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s01_04_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S01.ids04) : 2651 ≤ n.val ∧ n.val ≤ 2672 := by
  rcases (Paid16GeneralNext1182S01.mem_ids04 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s01_05_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S01.ids05) : 2673 ≤ n.val ∧ n.val ≤ 2694 := by
  rcases (Paid16GeneralNext1182S01.mem_ids05 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s01_06_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S01.ids06) : 2695 ≤ n.val ∧ n.val ≤ 2715 := by
  rcases (Paid16GeneralNext1182S01.mem_ids06 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s01_07_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S01.ids07) : 2716 ≤ n.val ∧ n.val ≤ 2736 := by
  rcases (Paid16GeneralNext1182S01.mem_ids07 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s02_00_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S02.ids08) : 2737 ≤ n.val ∧ n.val ≤ 2757 := by
  rcases (Paid16GeneralNext1182S02.mem_ids08 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s02_01_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S02.ids09) : 2758 ≤ n.val ∧ n.val ≤ 2778 := by
  rcases (Paid16GeneralNext1182S02.mem_ids09 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s02_02_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S02.ids10) : 2779 ≤ n.val ∧ n.val ≤ 2799 := by
  rcases (Paid16GeneralNext1182S02.mem_ids10 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s02_03_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S02.ids11) : 2800 ≤ n.val ∧ n.val ≤ 2820 := by
  rcases (Paid16GeneralNext1182S02.mem_ids11 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s02_04_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S02.ids12) : 2821 ≤ n.val ∧ n.val ≤ 2841 := by
  rcases (Paid16GeneralNext1182S02.mem_ids12 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s02_05_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S02.ids13) : 2842 ≤ n.val ∧ n.val ≤ 2862 := by
  rcases (Paid16GeneralNext1182S02.mem_ids13 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s02_06_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S02.ids14) : 2863 ≤ n.val ∧ n.val ≤ 2884 := by
  rcases (Paid16GeneralNext1182S02.mem_ids14 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s02_07_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S02.ids15) : 2885 ≤ n.val ∧ n.val ≤ 2906 := by
  rcases (Paid16GeneralNext1182S02.mem_ids15 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s03_00_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S03.ids16) : 2907 ≤ n.val ∧ n.val ≤ 2927 := by
  rcases (Paid16GeneralNext1182S03.mem_ids16 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s03_01_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S03.ids17) : 2928 ≤ n.val ∧ n.val ≤ 2948 := by
  rcases (Paid16GeneralNext1182S03.mem_ids17 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s03_02_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S03.ids18) : 2949 ≤ n.val ∧ n.val ≤ 2976 := by
  rcases (Paid16GeneralNext1182S03.mem_ids18 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s03_03_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S03.ids19) : 2977 ≤ n.val ∧ n.val ≤ 3000 := by
  rcases (Paid16GeneralNext1182S03.mem_ids19 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s03_04_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S03.ids20) : 3001 ≤ n.val ∧ n.val ≤ 3021 := by
  rcases (Paid16GeneralNext1182S03.mem_ids20 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s03_05_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S03.ids21) : 3022 ≤ n.val ∧ n.val ≤ 3043 := by
  rcases (Paid16GeneralNext1182S03.mem_ids21 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s03_06_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S03.ids22) : 3044 ≤ n.val ∧ n.val ≤ 3066 := by
  rcases (Paid16GeneralNext1182S03.mem_ids22 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s03_07_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S03.ids23) : 3067 ≤ n.val ∧ n.val ≤ 3087 := by
  rcases (Paid16GeneralNext1182S03.mem_ids23 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s04_00_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S04.ids24) : 3088 ≤ n.val ∧ n.val ≤ 3109 := by
  rcases (Paid16GeneralNext1182S04.mem_ids24 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s04_01_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S04.ids25) : 3110 ≤ n.val ∧ n.val ≤ 3136 := by
  rcases (Paid16GeneralNext1182S04.mem_ids25 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s04_02_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S04.ids26) : 3137 ≤ n.val ∧ n.val ≤ 3160 := by
  rcases (Paid16GeneralNext1182S04.mem_ids26 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s04_03_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S04.ids27) : 3161 ≤ n.val ∧ n.val ≤ 3181 := by
  rcases (Paid16GeneralNext1182S04.mem_ids27 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s04_04_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S04.ids28) : 3183 ≤ n.val ∧ n.val ≤ 3203 := by
  rcases (Paid16GeneralNext1182S04.mem_ids28 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s04_05_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S04.ids29) : 3204 ≤ n.val ∧ n.val ≤ 3224 := by
  rcases (Paid16GeneralNext1182S04.mem_ids29 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s04_06_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S04.ids30) : 3225 ≤ n.val ∧ n.val ≤ 3245 := by
  rcases (Paid16GeneralNext1182S04.mem_ids30 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s04_07_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S04.ids31) : 3246 ≤ n.val ∧ n.val ≤ 3266 := by
  rcases (Paid16GeneralNext1182S04.mem_ids31 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s05_00_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S05.ids32) : 3267 ≤ n.val ∧ n.val ≤ 3287 := by
  rcases (Paid16GeneralNext1182S05.mem_ids32 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s05_01_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S05.ids33) : 3288 ≤ n.val ∧ n.val ≤ 3308 := by
  rcases (Paid16GeneralNext1182S05.mem_ids33 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s05_02_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S05.ids34) : 3309 ≤ n.val ∧ n.val ≤ 3329 := by
  rcases (Paid16GeneralNext1182S05.mem_ids34 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s05_03_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S05.ids35) : 3330 ≤ n.val ∧ n.val ≤ 3350 := by
  rcases (Paid16GeneralNext1182S05.mem_ids35 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s05_04_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S05.ids36) : 3351 ≤ n.val ∧ n.val ≤ 3371 := by
  rcases (Paid16GeneralNext1182S05.mem_ids36 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s05_05_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S05.ids37) : 3372 ≤ n.val ∧ n.val ≤ 3392 := by
  rcases (Paid16GeneralNext1182S05.mem_ids37 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s05_06_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S05.ids38) : 3393 ≤ n.val ∧ n.val ≤ 3413 := by
  rcases (Paid16GeneralNext1182S05.mem_ids38 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s05_07_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S05.ids39) : 3414 ≤ n.val ∧ n.val ≤ 3445 := by
  rcases (Paid16GeneralNext1182S05.mem_ids39 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s06_00_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S06.ids40) : 3446 ≤ n.val ∧ n.val ≤ 3466 := by
  rcases (Paid16GeneralNext1182S06.mem_ids40 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s06_01_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S06.ids41) : 3467 ≤ n.val ∧ n.val ≤ 3488 := by
  rcases (Paid16GeneralNext1182S06.mem_ids41 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s06_02_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S06.ids42) : 3492 ≤ n.val ∧ n.val ≤ 3526 := by
  rcases (Paid16GeneralNext1182S06.mem_ids42 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s06_03_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S06.ids43) : 3528 ≤ n.val ∧ n.val ≤ 3608 := by
  rcases (Paid16GeneralNext1182S06.mem_ids43 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s06_04_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S06.ids44) : 3609 ≤ n.val ∧ n.val ≤ 3721 := by
  rcases (Paid16GeneralNext1182S06.mem_ids44 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s06_05_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S06.ids45) : 3723 ≤ n.val ∧ n.val ≤ 3804 := by
  rcases (Paid16GeneralNext1182S06.mem_ids45 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s06_06_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S06.ids46) : 3805 ≤ n.val ∧ n.val ≤ 3868 := by
  rcases (Paid16GeneralNext1182S06.mem_ids46 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s06_07_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S06.ids47) : 3869 ≤ n.val ∧ n.val ≤ 3954 := by
  rcases (Paid16GeneralNext1182S06.mem_ids47 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s07_00_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S07.ids48) : 3955 ≤ n.val ∧ n.val ≤ 4040 := by
  rcases (Paid16GeneralNext1182S07.mem_ids48 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s07_01_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S07.ids49) : 4042 ≤ n.val ∧ n.val ≤ 4164 := by
  rcases (Paid16GeneralNext1182S07.mem_ids49 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s07_02_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S07.ids50) : 4166 ≤ n.val ∧ n.val ≤ 4290 := by
  rcases (Paid16GeneralNext1182S07.mem_ids50 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s07_03_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S07.ids51) : 4297 ≤ n.val ∧ n.val ≤ 4376 := by
  rcases (Paid16GeneralNext1182S07.mem_ids51 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s07_04_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S07.ids52) : 4377 ≤ n.val ∧ n.val ≤ 4503 := by
  rcases (Paid16GeneralNext1182S07.mem_ids52 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s07_05_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S07.ids53) : 4505 ≤ n.val ∧ n.val ≤ 4675 := by
  rcases (Paid16GeneralNext1182S07.mem_ids53 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s07_06_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S07.ids54) : 4690 ≤ n.val ∧ n.val ≤ 4799 := by
  rcases (Paid16GeneralNext1182S07.mem_ids54 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s07_07_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S07.ids55) : 4804 ≤ n.val ∧ n.val ≤ 4984 := by
  rcases (Paid16GeneralNext1182S07.mem_ids55 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem block_s08_00_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S08.ids56) : 4986 ≤ n.val ∧ n.val ≤ 5007 := by
  rcases (Paid16GeneralNext1182S08.mem_ids56 n).mp h with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals norm_num
private theorem part_s01_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S01.newIDs) : 2565 ≤ n.val ∧ n.val ≤ 2736 := by
  rcases (Paid16GeneralNext1182S01.new_mem n).mp h with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · have hb := block_s01_00_bounds n h0
    constructor <;> omega
  · have hb := block_s01_01_bounds n h1
    constructor <;> omega
  · have hb := block_s01_02_bounds n h2
    constructor <;> omega
  · have hb := block_s01_03_bounds n h3
    constructor <;> omega
  · have hb := block_s01_04_bounds n h4
    constructor <;> omega
  · have hb := block_s01_05_bounds n h5
    constructor <;> omega
  · have hb := block_s01_06_bounds n h6
    constructor <;> omega
  · have hb := block_s01_07_bounds n h7
    constructor <;> omega
private theorem part_s02_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S02.newIDs) : 2737 ≤ n.val ∧ n.val ≤ 2906 := by
  rcases (Paid16GeneralNext1182S02.new_mem n).mp h with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · have hb := block_s02_00_bounds n h0
    constructor <;> omega
  · have hb := block_s02_01_bounds n h1
    constructor <;> omega
  · have hb := block_s02_02_bounds n h2
    constructor <;> omega
  · have hb := block_s02_03_bounds n h3
    constructor <;> omega
  · have hb := block_s02_04_bounds n h4
    constructor <;> omega
  · have hb := block_s02_05_bounds n h5
    constructor <;> omega
  · have hb := block_s02_06_bounds n h6
    constructor <;> omega
  · have hb := block_s02_07_bounds n h7
    constructor <;> omega
private theorem part_s03_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S03.newIDs) : 2907 ≤ n.val ∧ n.val ≤ 3087 := by
  rcases (Paid16GeneralNext1182S03.new_mem n).mp h with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · have hb := block_s03_00_bounds n h0
    constructor <;> omega
  · have hb := block_s03_01_bounds n h1
    constructor <;> omega
  · have hb := block_s03_02_bounds n h2
    constructor <;> omega
  · have hb := block_s03_03_bounds n h3
    constructor <;> omega
  · have hb := block_s03_04_bounds n h4
    constructor <;> omega
  · have hb := block_s03_05_bounds n h5
    constructor <;> omega
  · have hb := block_s03_06_bounds n h6
    constructor <;> omega
  · have hb := block_s03_07_bounds n h7
    constructor <;> omega
private theorem part_s04_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S04.newIDs) : 3088 ≤ n.val ∧ n.val ≤ 3266 := by
  rcases (Paid16GeneralNext1182S04.new_mem n).mp h with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · have hb := block_s04_00_bounds n h0
    constructor <;> omega
  · have hb := block_s04_01_bounds n h1
    constructor <;> omega
  · have hb := block_s04_02_bounds n h2
    constructor <;> omega
  · have hb := block_s04_03_bounds n h3
    constructor <;> omega
  · have hb := block_s04_04_bounds n h4
    constructor <;> omega
  · have hb := block_s04_05_bounds n h5
    constructor <;> omega
  · have hb := block_s04_06_bounds n h6
    constructor <;> omega
  · have hb := block_s04_07_bounds n h7
    constructor <;> omega
private theorem part_s05_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S05.newIDs) : 3267 ≤ n.val ∧ n.val ≤ 3445 := by
  rcases (Paid16GeneralNext1182S05.new_mem n).mp h with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · have hb := block_s05_00_bounds n h0
    constructor <;> omega
  · have hb := block_s05_01_bounds n h1
    constructor <;> omega
  · have hb := block_s05_02_bounds n h2
    constructor <;> omega
  · have hb := block_s05_03_bounds n h3
    constructor <;> omega
  · have hb := block_s05_04_bounds n h4
    constructor <;> omega
  · have hb := block_s05_05_bounds n h5
    constructor <;> omega
  · have hb := block_s05_06_bounds n h6
    constructor <;> omega
  · have hb := block_s05_07_bounds n h7
    constructor <;> omega
private theorem part_s06_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S06.newIDs) : 3446 ≤ n.val ∧ n.val ≤ 3954 := by
  rcases (Paid16GeneralNext1182S06.new_mem n).mp h with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · have hb := block_s06_00_bounds n h0
    constructor <;> omega
  · have hb := block_s06_01_bounds n h1
    constructor <;> omega
  · have hb := block_s06_02_bounds n h2
    constructor <;> omega
  · have hb := block_s06_03_bounds n h3
    constructor <;> omega
  · have hb := block_s06_04_bounds n h4
    constructor <;> omega
  · have hb := block_s06_05_bounds n h5
    constructor <;> omega
  · have hb := block_s06_06_bounds n h6
    constructor <;> omega
  · have hb := block_s06_07_bounds n h7
    constructor <;> omega
private theorem part_s07_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S07.newIDs) : 3955 ≤ n.val ∧ n.val ≤ 4984 := by
  rcases (Paid16GeneralNext1182S07.new_mem n).mp h with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · have hb := block_s07_00_bounds n h0
    constructor <;> omega
  · have hb := block_s07_01_bounds n h1
    constructor <;> omega
  · have hb := block_s07_02_bounds n h2
    constructor <;> omega
  · have hb := block_s07_03_bounds n h3
    constructor <;> omega
  · have hb := block_s07_04_bounds n h4
    constructor <;> omega
  · have hb := block_s07_05_bounds n h5
    constructor <;> omega
  · have hb := block_s07_06_bounds n h6
    constructor <;> omega
  · have hb := block_s07_07_bounds n h7
    constructor <;> omega
private theorem part_s08_bounds (n : Fin 5011)
    (h : n ∈ Paid16GeneralNext1182S08.newIDs) : 4986 ≤ n.val ∧ n.val ≤ 5007 := by
  rcases (Paid16GeneralNext1182S08.new_mem n).mp h with h0
  · have hb := block_s08_00_bounds n h0
    constructor <;> omega
private theorem disjoint_s01_s02 : Disjoint Paid16GeneralNext1182S01.newIDs Paid16GeneralNext1182S02.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi := part_s01_bounds n hi
  have hj := part_s02_bounds n hj
  omega
private theorem disjoint_s01_s03 : Disjoint Paid16GeneralNext1182S01.newIDs Paid16GeneralNext1182S03.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi := part_s01_bounds n hi
  have hj := part_s03_bounds n hj
  omega
private theorem disjoint_s01_s04 : Disjoint Paid16GeneralNext1182S01.newIDs Paid16GeneralNext1182S04.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi := part_s01_bounds n hi
  have hj := part_s04_bounds n hj
  omega
private theorem disjoint_s01_s05 : Disjoint Paid16GeneralNext1182S01.newIDs Paid16GeneralNext1182S05.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi := part_s01_bounds n hi
  have hj := part_s05_bounds n hj
  omega
private theorem disjoint_s01_s06 : Disjoint Paid16GeneralNext1182S01.newIDs Paid16GeneralNext1182S06.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi := part_s01_bounds n hi
  have hj := part_s06_bounds n hj
  omega
private theorem disjoint_s01_s07 : Disjoint Paid16GeneralNext1182S01.newIDs Paid16GeneralNext1182S07.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi := part_s01_bounds n hi
  have hj := part_s07_bounds n hj
  omega
private theorem disjoint_s01_s08 : Disjoint Paid16GeneralNext1182S01.newIDs Paid16GeneralNext1182S08.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi := part_s01_bounds n hi
  have hj := part_s08_bounds n hj
  omega
private theorem disjoint_s02_s03 : Disjoint Paid16GeneralNext1182S02.newIDs Paid16GeneralNext1182S03.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi := part_s02_bounds n hi
  have hj := part_s03_bounds n hj
  omega
private theorem disjoint_s02_s04 : Disjoint Paid16GeneralNext1182S02.newIDs Paid16GeneralNext1182S04.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi := part_s02_bounds n hi
  have hj := part_s04_bounds n hj
  omega
private theorem disjoint_s02_s05 : Disjoint Paid16GeneralNext1182S02.newIDs Paid16GeneralNext1182S05.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi := part_s02_bounds n hi
  have hj := part_s05_bounds n hj
  omega
private theorem disjoint_s02_s06 : Disjoint Paid16GeneralNext1182S02.newIDs Paid16GeneralNext1182S06.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi := part_s02_bounds n hi
  have hj := part_s06_bounds n hj
  omega
private theorem disjoint_s02_s07 : Disjoint Paid16GeneralNext1182S02.newIDs Paid16GeneralNext1182S07.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi := part_s02_bounds n hi
  have hj := part_s07_bounds n hj
  omega
private theorem disjoint_s02_s08 : Disjoint Paid16GeneralNext1182S02.newIDs Paid16GeneralNext1182S08.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi := part_s02_bounds n hi
  have hj := part_s08_bounds n hj
  omega
private theorem disjoint_s03_s04 : Disjoint Paid16GeneralNext1182S03.newIDs Paid16GeneralNext1182S04.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi := part_s03_bounds n hi
  have hj := part_s04_bounds n hj
  omega
private theorem disjoint_s03_s05 : Disjoint Paid16GeneralNext1182S03.newIDs Paid16GeneralNext1182S05.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi := part_s03_bounds n hi
  have hj := part_s05_bounds n hj
  omega
private theorem disjoint_s03_s06 : Disjoint Paid16GeneralNext1182S03.newIDs Paid16GeneralNext1182S06.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi := part_s03_bounds n hi
  have hj := part_s06_bounds n hj
  omega
private theorem disjoint_s03_s07 : Disjoint Paid16GeneralNext1182S03.newIDs Paid16GeneralNext1182S07.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi := part_s03_bounds n hi
  have hj := part_s07_bounds n hj
  omega
private theorem disjoint_s03_s08 : Disjoint Paid16GeneralNext1182S03.newIDs Paid16GeneralNext1182S08.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi := part_s03_bounds n hi
  have hj := part_s08_bounds n hj
  omega
private theorem disjoint_s04_s05 : Disjoint Paid16GeneralNext1182S04.newIDs Paid16GeneralNext1182S05.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi := part_s04_bounds n hi
  have hj := part_s05_bounds n hj
  omega
private theorem disjoint_s04_s06 : Disjoint Paid16GeneralNext1182S04.newIDs Paid16GeneralNext1182S06.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi := part_s04_bounds n hi
  have hj := part_s06_bounds n hj
  omega
private theorem disjoint_s04_s07 : Disjoint Paid16GeneralNext1182S04.newIDs Paid16GeneralNext1182S07.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi := part_s04_bounds n hi
  have hj := part_s07_bounds n hj
  omega
private theorem disjoint_s04_s08 : Disjoint Paid16GeneralNext1182S04.newIDs Paid16GeneralNext1182S08.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi := part_s04_bounds n hi
  have hj := part_s08_bounds n hj
  omega
private theorem disjoint_s05_s06 : Disjoint Paid16GeneralNext1182S05.newIDs Paid16GeneralNext1182S06.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi := part_s05_bounds n hi
  have hj := part_s06_bounds n hj
  omega
private theorem disjoint_s05_s07 : Disjoint Paid16GeneralNext1182S05.newIDs Paid16GeneralNext1182S07.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi := part_s05_bounds n hi
  have hj := part_s07_bounds n hj
  omega
private theorem disjoint_s05_s08 : Disjoint Paid16GeneralNext1182S05.newIDs Paid16GeneralNext1182S08.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi := part_s05_bounds n hi
  have hj := part_s08_bounds n hj
  omega
private theorem disjoint_s06_s07 : Disjoint Paid16GeneralNext1182S06.newIDs Paid16GeneralNext1182S07.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi := part_s06_bounds n hi
  have hj := part_s07_bounds n hj
  omega
private theorem disjoint_s06_s08 : Disjoint Paid16GeneralNext1182S06.newIDs Paid16GeneralNext1182S08.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi := part_s06_bounds n hi
  have hj := part_s08_bounds n hj
  omega
private theorem disjoint_s07_s08 : Disjoint Paid16GeneralNext1182S07.newIDs Paid16GeneralNext1182S08.newIDs := by
  rw [Finset.disjoint_left]
  intro n hi hj
  have hi := part_s07_bounds n hi
  have hj := part_s08_bounds n hj
  omega
theorem lower_bound (n : Fin 5011) (hn : n ∈ newIDs) : 2565 ≤ n.val := by
  rcases (new_mem n).mp hn with h | h | h | h | h | h | h | h
  · have hb := (part_s01_bounds n h).1
    omega
  · have hb := (part_s02_bounds n h).1
    omega
  · have hb := (part_s03_bounds n h).1
    omega
  · have hb := (part_s04_bounds n h).1
    omega
  · have hb := (part_s05_bounds n h).1
    omega
  · have hb := (part_s06_bounds n h).1
    omega
  · have hb := (part_s07_bounds n h).1
    omega
  · have hb := (part_s08_bounds n h).1
    omega
theorem new_count : newIDs.card = 1182 := by
  have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin 8)) part := by
    intro i _ j _ hij
    change Disjoint (part i) (part j)
    fin_cases i
    · fin_cases j
      · exact (hij rfl).elim
      · simpa [part, Function.onFun] using disjoint_s01_s02
      · simpa [part, Function.onFun] using disjoint_s01_s03
      · simpa [part, Function.onFun] using disjoint_s01_s04
      · simpa [part, Function.onFun] using disjoint_s01_s05
      · simpa [part, Function.onFun] using disjoint_s01_s06
      · simpa [part, Function.onFun] using disjoint_s01_s07
      · simpa [part, Function.onFun] using disjoint_s01_s08
    · fin_cases j
      · simpa [part, Function.onFun] using disjoint_s01_s02.symm
      · exact (hij rfl).elim
      · simpa [part, Function.onFun] using disjoint_s02_s03
      · simpa [part, Function.onFun] using disjoint_s02_s04
      · simpa [part, Function.onFun] using disjoint_s02_s05
      · simpa [part, Function.onFun] using disjoint_s02_s06
      · simpa [part, Function.onFun] using disjoint_s02_s07
      · simpa [part, Function.onFun] using disjoint_s02_s08
    · fin_cases j
      · simpa [part, Function.onFun] using disjoint_s01_s03.symm
      · simpa [part, Function.onFun] using disjoint_s02_s03.symm
      · exact (hij rfl).elim
      · simpa [part, Function.onFun] using disjoint_s03_s04
      · simpa [part, Function.onFun] using disjoint_s03_s05
      · simpa [part, Function.onFun] using disjoint_s03_s06
      · simpa [part, Function.onFun] using disjoint_s03_s07
      · simpa [part, Function.onFun] using disjoint_s03_s08
    · fin_cases j
      · simpa [part, Function.onFun] using disjoint_s01_s04.symm
      · simpa [part, Function.onFun] using disjoint_s02_s04.symm
      · simpa [part, Function.onFun] using disjoint_s03_s04.symm
      · exact (hij rfl).elim
      · simpa [part, Function.onFun] using disjoint_s04_s05
      · simpa [part, Function.onFun] using disjoint_s04_s06
      · simpa [part, Function.onFun] using disjoint_s04_s07
      · simpa [part, Function.onFun] using disjoint_s04_s08
    · fin_cases j
      · simpa [part, Function.onFun] using disjoint_s01_s05.symm
      · simpa [part, Function.onFun] using disjoint_s02_s05.symm
      · simpa [part, Function.onFun] using disjoint_s03_s05.symm
      · simpa [part, Function.onFun] using disjoint_s04_s05.symm
      · exact (hij rfl).elim
      · simpa [part, Function.onFun] using disjoint_s05_s06
      · simpa [part, Function.onFun] using disjoint_s05_s07
      · simpa [part, Function.onFun] using disjoint_s05_s08
    · fin_cases j
      · simpa [part, Function.onFun] using disjoint_s01_s06.symm
      · simpa [part, Function.onFun] using disjoint_s02_s06.symm
      · simpa [part, Function.onFun] using disjoint_s03_s06.symm
      · simpa [part, Function.onFun] using disjoint_s04_s06.symm
      · simpa [part, Function.onFun] using disjoint_s05_s06.symm
      · exact (hij rfl).elim
      · simpa [part, Function.onFun] using disjoint_s06_s07
      · simpa [part, Function.onFun] using disjoint_s06_s08
    · fin_cases j
      · simpa [part, Function.onFun] using disjoint_s01_s07.symm
      · simpa [part, Function.onFun] using disjoint_s02_s07.symm
      · simpa [part, Function.onFun] using disjoint_s03_s07.symm
      · simpa [part, Function.onFun] using disjoint_s04_s07.symm
      · simpa [part, Function.onFun] using disjoint_s05_s07.symm
      · simpa [part, Function.onFun] using disjoint_s06_s07.symm
      · exact (hij rfl).elim
      · simpa [part, Function.onFun] using disjoint_s07_s08
    · fin_cases j
      · simpa [part, Function.onFun] using disjoint_s01_s08.symm
      · simpa [part, Function.onFun] using disjoint_s02_s08.symm
      · simpa [part, Function.onFun] using disjoint_s03_s08.symm
      · simpa [part, Function.onFun] using disjoint_s04_s08.symm
      · simpa [part, Function.onFun] using disjoint_s05_s08.symm
      · simpa [part, Function.onFun] using disjoint_s06_s08.symm
      · simpa [part, Function.onFun] using disjoint_s07_s08.symm
      · exact (hij rfl).elim
  rw [newIDs, Finset.card_biUnion hdisj]
  simp [Fin.sum_univ_succ, part,
      Paid16GeneralNext1182S01.new_count,
      Paid16GeneralNext1182S02.new_count,
      Paid16GeneralNext1182S03.new_count,
      Paid16GeneralNext1182S04.new_count,
      Paid16GeneralNext1182S05.new_count,
      Paid16GeneralNext1182S06.new_count,
      Paid16GeneralNext1182S07.new_count,
      Paid16GeneralNext1182S08.new_count]
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  rcases (new_mem n).mp hn with h | h | h | h | h | h | h | h
  · exact Paid16GeneralNext1182S01.new_terminal n h
  · exact Paid16GeneralNext1182S02.new_terminal n h
  · exact Paid16GeneralNext1182S03.new_terminal n h
  · exact Paid16GeneralNext1182S04.new_terminal n h
  · exact Paid16GeneralNext1182S05.new_terminal n h
  · exact Paid16GeneralNext1182S06.new_terminal n h
  · exact Paid16GeneralNext1182S07.new_terminal n h
  · exact Paid16GeneralNext1182S08.new_terminal n h
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  rcases (new_mem n).mp hn with h | h | h | h | h | h | h | h
  · exact Paid16GeneralNext1182S01.new_radius n h y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralNext1182S02.new_radius n h y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralNext1182S03.new_radius n h y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralNext1182S04.new_radius n h y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralNext1182S05.new_radius n h y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralNext1182S06.new_radius n h y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralNext1182S07.new_radius n h y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralNext1182S08.new_radius n h y hy0 hy1 hc C Z r hf
theorem disjoint_sharp : Disjoint newIDs Patch120SharpDispatch.sharpIDs := by
  rw [Finset.disjoint_left]
  intro a ha hb
  rcases (new_mem a).mp ha with h | h | h | h | h | h | h | h
  · exact (Finset.disjoint_left.mp Paid16GeneralNext1182S01.disjoint_sharp) (a := a) h hb
  · exact (Finset.disjoint_left.mp Paid16GeneralNext1182S02.disjoint_sharp) (a := a) h hb
  · exact (Finset.disjoint_left.mp Paid16GeneralNext1182S03.disjoint_sharp) (a := a) h hb
  · exact (Finset.disjoint_left.mp Paid16GeneralNext1182S04.disjoint_sharp) (a := a) h hb
  · exact (Finset.disjoint_left.mp Paid16GeneralNext1182S05.disjoint_sharp) (a := a) h hb
  · exact (Finset.disjoint_left.mp Paid16GeneralNext1182S06.disjoint_sharp) (a := a) h hb
  · exact (Finset.disjoint_left.mp Paid16GeneralNext1182S07.disjoint_sharp) (a := a) h hb
  · exact (Finset.disjoint_left.mp Paid16GeneralNext1182S08.disjoint_sharp) (a := a) h hb
end
end N11Formalization.Paid16GeneralNext1182
#check @N11Formalization.Paid16GeneralNext1182.new_count
#print axioms N11Formalization.Paid16GeneralNext1182.new_count
#print axioms N11Formalization.Paid16GeneralNext1182.new_radius
#print axioms N11Formalization.Paid16GeneralNext1182.new_terminal
#print axioms N11Formalization.Paid16GeneralNext1182.lower_bound
