import N11Formalization.Paid16GeneralH66
import N11Formalization.Paid16GeneralH67
import N11Formalization.Paid16GeneralH68
import N11Formalization.Paid16GeneralH69
import N11Formalization.Paid16GeneralH70
import N11Formalization.Paid16GeneralH71
import N11Formalization.Paid16GeneralH72
import N11Formalization.Paid16GeneralH73

/-! Sub-aggregate 6/8: 8 packet modules, 168 ids.
Cardinality is kernel-checked on <= 168-element literal sets only. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace N11Formalization.Paid16GeneralNext1182S06
open Finset
noncomputable section

def ids40 : Finset (Fin 5011) := {3446,3447,3448,3449,3450,3451,3452,3453,3454,3455,3456,3457,3458,3459,3460,3461,3462,3463,3464,3465,3466}
theorem mem_ids40 (n : Fin 5011) : n ∈ ids40 ↔ n = 3446 ∨ n = 3447 ∨ n = 3448 ∨ n = 3449 ∨ n = 3450 ∨ n = 3451 ∨ n = 3452 ∨ n = 3453 ∨ n = 3454 ∨ n = 3455 ∨ n = 3456 ∨ n = 3457 ∨ n = 3458 ∨ n = 3459 ∨ n = 3460 ∨ n = 3461 ∨ n = 3462 ∨ n = 3463 ∨ n = 3464 ∨ n = 3465 ∨ n = 3466 := by
  simp only [ids40, Finset.mem_insert, Finset.mem_singleton]
theorem ids40_card : ids40.card = 21 := by decide +kernel
theorem sub40 (n : Fin 5011) (hn : n ∈ ids40) : n ∈ Paid16GeneralH66.newIDs := by
  rcases (mem_ids40 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids41 : Finset (Fin 5011) := {3467,3468,3469,3470,3471,3472,3473,3474,3475,3476,3477,3478,3479,3481,3482,3483,3484,3485,3486,3487,3488}
theorem mem_ids41 (n : Fin 5011) : n ∈ ids41 ↔ n = 3467 ∨ n = 3468 ∨ n = 3469 ∨ n = 3470 ∨ n = 3471 ∨ n = 3472 ∨ n = 3473 ∨ n = 3474 ∨ n = 3475 ∨ n = 3476 ∨ n = 3477 ∨ n = 3478 ∨ n = 3479 ∨ n = 3481 ∨ n = 3482 ∨ n = 3483 ∨ n = 3484 ∨ n = 3485 ∨ n = 3486 ∨ n = 3487 ∨ n = 3488 := by
  simp only [ids41, Finset.mem_insert, Finset.mem_singleton]
theorem ids41_card : ids41.card = 21 := by decide +kernel
theorem sub41 (n : Fin 5011) (hn : n ∈ ids41) : n ∈ Paid16GeneralH67.newIDs := by
  rcases (mem_ids41 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids42 : Finset (Fin 5011) := {3492,3493,3494,3495,3498,3499,3500,3502,3504,3505,3506,3507,3510,3512,3513,3514,3516,3518,3523,3524,3526}
theorem mem_ids42 (n : Fin 5011) : n ∈ ids42 ↔ n = 3492 ∨ n = 3493 ∨ n = 3494 ∨ n = 3495 ∨ n = 3498 ∨ n = 3499 ∨ n = 3500 ∨ n = 3502 ∨ n = 3504 ∨ n = 3505 ∨ n = 3506 ∨ n = 3507 ∨ n = 3510 ∨ n = 3512 ∨ n = 3513 ∨ n = 3514 ∨ n = 3516 ∨ n = 3518 ∨ n = 3523 ∨ n = 3524 ∨ n = 3526 := by
  simp only [ids42, Finset.mem_insert, Finset.mem_singleton]
theorem ids42_card : ids42.card = 21 := by decide +kernel
theorem sub42 (n : Fin 5011) (hn : n ∈ ids42) : n ∈ Paid16GeneralH68.newIDs := by
  rcases (mem_ids42 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids43 : Finset (Fin 5011) := {3528,3534,3536,3538,3540,3542,3544,3547,3551,3555,3563,3565,3567,3571,3577,3579,3595,3597,3599,3603,3608}
theorem mem_ids43 (n : Fin 5011) : n ∈ ids43 ↔ n = 3528 ∨ n = 3534 ∨ n = 3536 ∨ n = 3538 ∨ n = 3540 ∨ n = 3542 ∨ n = 3544 ∨ n = 3547 ∨ n = 3551 ∨ n = 3555 ∨ n = 3563 ∨ n = 3565 ∨ n = 3567 ∨ n = 3571 ∨ n = 3577 ∨ n = 3579 ∨ n = 3595 ∨ n = 3597 ∨ n = 3599 ∨ n = 3603 ∨ n = 3608 := by
  simp only [ids43, Finset.mem_insert, Finset.mem_singleton]
theorem ids43_card : ids43.card = 21 := by decide +kernel
theorem sub43 (n : Fin 5011) (hn : n ∈ ids43) : n ∈ Paid16GeneralH69.newIDs := by
  rcases (mem_ids43 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids44 : Finset (Fin 5011) := {3609,3611,3617,3632,3635,3655,3662,3667,3669,3676,3678,3680,3682,3696,3698,3700,3704,3708,3710,3712,3721}
theorem mem_ids44 (n : Fin 5011) : n ∈ ids44 ↔ n = 3609 ∨ n = 3611 ∨ n = 3617 ∨ n = 3632 ∨ n = 3635 ∨ n = 3655 ∨ n = 3662 ∨ n = 3667 ∨ n = 3669 ∨ n = 3676 ∨ n = 3678 ∨ n = 3680 ∨ n = 3682 ∨ n = 3696 ∨ n = 3698 ∨ n = 3700 ∨ n = 3704 ∨ n = 3708 ∨ n = 3710 ∨ n = 3712 ∨ n = 3721 := by
  simp only [ids44, Finset.mem_insert, Finset.mem_singleton]
theorem ids44_card : ids44.card = 21 := by decide +kernel
theorem sub44 (n : Fin 5011) (hn : n ∈ ids44) : n ∈ Paid16GeneralH70.newIDs := by
  rcases (mem_ids44 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids45 : Finset (Fin 5011) := {3723,3741,3747,3750,3752,3753,3756,3759,3764,3766,3770,3774,3782,3787,3791,3793,3796,3797,3799,3801,3804}
theorem mem_ids45 (n : Fin 5011) : n ∈ ids45 ↔ n = 3723 ∨ n = 3741 ∨ n = 3747 ∨ n = 3750 ∨ n = 3752 ∨ n = 3753 ∨ n = 3756 ∨ n = 3759 ∨ n = 3764 ∨ n = 3766 ∨ n = 3770 ∨ n = 3774 ∨ n = 3782 ∨ n = 3787 ∨ n = 3791 ∨ n = 3793 ∨ n = 3796 ∨ n = 3797 ∨ n = 3799 ∨ n = 3801 ∨ n = 3804 := by
  simp only [ids45, Finset.mem_insert, Finset.mem_singleton]
theorem ids45_card : ids45.card = 21 := by decide +kernel
theorem sub45 (n : Fin 5011) (hn : n ∈ ids45) : n ∈ Paid16GeneralH71.newIDs := by
  rcases (mem_ids45 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids46 : Finset (Fin 5011) := {3805,3813,3816,3817,3820,3822,3823,3829,3830,3831,3832,3843,3844,3845,3846,3848,3849,3850,3860,3864,3868}
theorem mem_ids46 (n : Fin 5011) : n ∈ ids46 ↔ n = 3805 ∨ n = 3813 ∨ n = 3816 ∨ n = 3817 ∨ n = 3820 ∨ n = 3822 ∨ n = 3823 ∨ n = 3829 ∨ n = 3830 ∨ n = 3831 ∨ n = 3832 ∨ n = 3843 ∨ n = 3844 ∨ n = 3845 ∨ n = 3846 ∨ n = 3848 ∨ n = 3849 ∨ n = 3850 ∨ n = 3860 ∨ n = 3864 ∨ n = 3868 := by
  simp only [ids46, Finset.mem_insert, Finset.mem_singleton]
theorem ids46_card : ids46.card = 21 := by decide +kernel
theorem sub46 (n : Fin 5011) (hn : n ∈ ids46) : n ∈ Paid16GeneralH72.newIDs := by
  rcases (mem_ids46 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def ids47 : Finset (Fin 5011) := {3869,3872,3873,3877,3879,3882,3883,3902,3905,3917,3919,3921,3927,3929,3936,3938,3940,3942,3943,3952,3954}
theorem mem_ids47 (n : Fin 5011) : n ∈ ids47 ↔ n = 3869 ∨ n = 3872 ∨ n = 3873 ∨ n = 3877 ∨ n = 3879 ∨ n = 3882 ∨ n = 3883 ∨ n = 3902 ∨ n = 3905 ∨ n = 3917 ∨ n = 3919 ∨ n = 3921 ∨ n = 3927 ∨ n = 3929 ∨ n = 3936 ∨ n = 3938 ∨ n = 3940 ∨ n = 3942 ∨ n = 3943 ∨ n = 3952 ∨ n = 3954 := by
  simp only [ids47, Finset.mem_insert, Finset.mem_singleton]
theorem ids47_card : ids47.card = 21 := by decide +kernel
theorem sub47 (n : Fin 5011) (hn : n ∈ ids47) : n ∈ Paid16GeneralH73.newIDs := by
  rcases (mem_ids47 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨4, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨5, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨6, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨7, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨8, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨9, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨10, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨11, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨12, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨13, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨14, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨15, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨16, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨17, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨18, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨19, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨20, Finset.mem_univ _, rfl⟩
def newIDs : Finset (Fin 5011) := ids40 ∪ (ids41 ∪ (ids42 ∪ (ids43 ∪ (ids44 ∪ (ids45 ∪ (ids46 ∪ (ids47)))))))
theorem new_mem (n : Fin 5011) : n ∈ newIDs ↔ n ∈ ids40 ∨ n ∈ ids41 ∨ n ∈ ids42 ∨ n ∈ ids43 ∨ n ∈ ids44 ∨ n ∈ ids45 ∨ n ∈ ids46 ∨ n ∈ ids47 := by
  simp only [newIDs, Finset.mem_union]
theorem new_count : newIDs.card = 168 := by decide +kernel
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  rcases (new_mem n).mp hn with h | h | h | h | h | h | h | h
  · exact Paid16GeneralH66.new_terminal n (sub40 n h)
  · exact Paid16GeneralH67.new_terminal n (sub41 n h)
  · exact Paid16GeneralH68.new_terminal n (sub42 n h)
  · exact Paid16GeneralH69.new_terminal n (sub43 n h)
  · exact Paid16GeneralH70.new_terminal n (sub44 n h)
  · exact Paid16GeneralH71.new_terminal n (sub45 n h)
  · exact Paid16GeneralH72.new_terminal n (sub46 n h)
  · exact Paid16GeneralH73.new_terminal n (sub47 n h)
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  rcases (new_mem n).mp hn with h | h | h | h | h | h | h | h
  · exact Paid16GeneralH66.new_radius n (sub40 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH67.new_radius n (sub41 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH68.new_radius n (sub42 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH69.new_radius n (sub43 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH70.new_radius n (sub44 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH71.new_radius n (sub45 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH72.new_radius n (sub46 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH73.new_radius n (sub47 n h) y hy0 hy1 hc C Z r hf
theorem disjoint_sharp : Disjoint newIDs Patch120SharpDispatch.sharpIDs := by decide +kernel
end
end N11Formalization.Paid16GeneralNext1182S06
#print axioms N11Formalization.Paid16GeneralNext1182S06.new_count
#print axioms N11Formalization.Paid16GeneralNext1182S06.new_radius
