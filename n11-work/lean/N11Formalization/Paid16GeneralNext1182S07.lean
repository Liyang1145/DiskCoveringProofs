import N11Formalization.Paid16GeneralH74
import N11Formalization.Paid16GeneralH75
import N11Formalization.Paid16GeneralH76
import N11Formalization.Paid16GeneralH77
import N11Formalization.Paid16GeneralH78
import N11Formalization.Paid16GeneralH79
import N11Formalization.Paid16GeneralH80
import N11Formalization.Paid16GeneralH81

/-! Sub-aggregate 7/8: 8 packet modules, 168 ids.
Cardinality is kernel-checked on <= 168-element literal sets only. -/
set_option autoImplicit false
namespace N11Formalization.Paid16GeneralNext1182S07
open Finset
noncomputable section

def ids48 : Finset (Fin 5011) := {3955,3957,3959,3962,3963,3967,3981,3994,3996,3998,4000,4002,4008,4013,4018,4020,4022,4027,4036,4038,4040}
theorem mem_ids48 (n : Fin 5011) : n ∈ ids48 ↔ n = 3955 ∨ n = 3957 ∨ n = 3959 ∨ n = 3962 ∨ n = 3963 ∨ n = 3967 ∨ n = 3981 ∨ n = 3994 ∨ n = 3996 ∨ n = 3998 ∨ n = 4000 ∨ n = 4002 ∨ n = 4008 ∨ n = 4013 ∨ n = 4018 ∨ n = 4020 ∨ n = 4022 ∨ n = 4027 ∨ n = 4036 ∨ n = 4038 ∨ n = 4040 := by
  simp only [ids48, Finset.mem_insert, Finset.mem_singleton]
theorem ids48_card : ids48.card = 21 := by decide +kernel
theorem sub48 (n : Fin 5011) (hn : n ∈ ids48) : n ∈ Paid16GeneralH74.newIDs := by
  rcases (mem_ids48 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
def ids49 : Finset (Fin 5011) := {4042,4043,4052,4054,4056,4057,4075,4077,4079,4082,4084,4088,4090,4092,4106,4131,4140,4144,4148,4161,4164}
theorem mem_ids49 (n : Fin 5011) : n ∈ ids49 ↔ n = 4042 ∨ n = 4043 ∨ n = 4052 ∨ n = 4054 ∨ n = 4056 ∨ n = 4057 ∨ n = 4075 ∨ n = 4077 ∨ n = 4079 ∨ n = 4082 ∨ n = 4084 ∨ n = 4088 ∨ n = 4090 ∨ n = 4092 ∨ n = 4106 ∨ n = 4131 ∨ n = 4140 ∨ n = 4144 ∨ n = 4148 ∨ n = 4161 ∨ n = 4164 := by
  simp only [ids49, Finset.mem_insert, Finset.mem_singleton]
theorem ids49_card : ids49.card = 21 := by decide +kernel
theorem sub49 (n : Fin 5011) (hn : n ∈ ids49) : n ∈ Paid16GeneralH75.newIDs := by
  rcases (mem_ids49 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
def ids50 : Finset (Fin 5011) := {4166,4167,4177,4178,4194,4201,4205,4210,4214,4220,4239,4242,4251,4258,4263,4268,4270,4272,4277,4289,4290}
theorem mem_ids50 (n : Fin 5011) : n ∈ ids50 ↔ n = 4166 ∨ n = 4167 ∨ n = 4177 ∨ n = 4178 ∨ n = 4194 ∨ n = 4201 ∨ n = 4205 ∨ n = 4210 ∨ n = 4214 ∨ n = 4220 ∨ n = 4239 ∨ n = 4242 ∨ n = 4251 ∨ n = 4258 ∨ n = 4263 ∨ n = 4268 ∨ n = 4270 ∨ n = 4272 ∨ n = 4277 ∨ n = 4289 ∨ n = 4290 := by
  simp only [ids50, Finset.mem_insert, Finset.mem_singleton]
theorem ids50_card : ids50.card = 21 := by decide +kernel
theorem sub50 (n : Fin 5011) (hn : n ∈ ids50) : n ∈ Paid16GeneralH76.newIDs := by
  rcases (mem_ids50 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
def ids51 : Finset (Fin 5011) := {4297,4300,4310,4314,4318,4326,4328,4345,4346,4357,4359,4360,4361,4367,4368,4369,4370,4372,4373,4374,4376}
theorem mem_ids51 (n : Fin 5011) : n ∈ ids51 ↔ n = 4297 ∨ n = 4300 ∨ n = 4310 ∨ n = 4314 ∨ n = 4318 ∨ n = 4326 ∨ n = 4328 ∨ n = 4345 ∨ n = 4346 ∨ n = 4357 ∨ n = 4359 ∨ n = 4360 ∨ n = 4361 ∨ n = 4367 ∨ n = 4368 ∨ n = 4369 ∨ n = 4370 ∨ n = 4372 ∨ n = 4373 ∨ n = 4374 ∨ n = 4376 := by
  simp only [ids51, Finset.mem_insert, Finset.mem_singleton]
theorem ids51_card : ids51.card = 21 := by decide +kernel
theorem sub51 (n : Fin 5011) (hn : n ∈ ids51) : n ∈ Paid16GeneralH77.newIDs := by
  rcases (mem_ids51 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
def ids52 : Finset (Fin 5011) := {4377,4378,4379,4380,4381,4382,4391,4411,4412,4413,4415,4416,4432,4457,4483,4487,4494,4496,4499,4501,4503}
theorem mem_ids52 (n : Fin 5011) : n ∈ ids52 ↔ n = 4377 ∨ n = 4378 ∨ n = 4379 ∨ n = 4380 ∨ n = 4381 ∨ n = 4382 ∨ n = 4391 ∨ n = 4411 ∨ n = 4412 ∨ n = 4413 ∨ n = 4415 ∨ n = 4416 ∨ n = 4432 ∨ n = 4457 ∨ n = 4483 ∨ n = 4487 ∨ n = 4494 ∨ n = 4496 ∨ n = 4499 ∨ n = 4501 ∨ n = 4503 := by
  simp only [ids52, Finset.mem_insert, Finset.mem_singleton]
theorem ids52_card : ids52.card = 21 := by decide +kernel
theorem sub52 (n : Fin 5011) (hn : n ∈ ids52) : n ∈ Paid16GeneralH78.newIDs := by
  rcases (mem_ids52 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
def ids53 : Finset (Fin 5011) := {4505,4520,4522,4524,4526,4527,4530,4545,4550,4556,4564,4596,4605,4648,4652,4658,4662,4666,4668,4670,4675}
theorem mem_ids53 (n : Fin 5011) : n ∈ ids53 ↔ n = 4505 ∨ n = 4520 ∨ n = 4522 ∨ n = 4524 ∨ n = 4526 ∨ n = 4527 ∨ n = 4530 ∨ n = 4545 ∨ n = 4550 ∨ n = 4556 ∨ n = 4564 ∨ n = 4596 ∨ n = 4605 ∨ n = 4648 ∨ n = 4652 ∨ n = 4658 ∨ n = 4662 ∨ n = 4666 ∨ n = 4668 ∨ n = 4670 ∨ n = 4675 := by
  simp only [ids53, Finset.mem_insert, Finset.mem_singleton]
theorem ids53_card : ids53.card = 21 := by decide +kernel
theorem sub53 (n : Fin 5011) (hn : n ∈ ids53) : n ∈ Paid16GeneralH79.newIDs := by
  rcases (mem_ids53 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
def ids54 : Finset (Fin 5011) := {4690,4694,4696,4698,4700,4702,4732,4733,4739,4741,4750,4751,4760,4764,4768,4772,4780,4782,4784,4788,4799}
theorem mem_ids54 (n : Fin 5011) : n ∈ ids54 ↔ n = 4690 ∨ n = 4694 ∨ n = 4696 ∨ n = 4698 ∨ n = 4700 ∨ n = 4702 ∨ n = 4732 ∨ n = 4733 ∨ n = 4739 ∨ n = 4741 ∨ n = 4750 ∨ n = 4751 ∨ n = 4760 ∨ n = 4764 ∨ n = 4768 ∨ n = 4772 ∨ n = 4780 ∨ n = 4782 ∨ n = 4784 ∨ n = 4788 ∨ n = 4799 := by
  simp only [ids54, Finset.mem_insert, Finset.mem_singleton]
theorem ids54_card : ids54.card = 21 := by decide +kernel
theorem sub54 (n : Fin 5011) (hn : n ∈ ids54) : n ∈ Paid16GeneralH80.newIDs := by
  rcases (mem_ids54 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
def ids55 : Finset (Fin 5011) := {4804,4809,4811,4828,4890,4898,4904,4920,4927,4929,4931,4933,4944,4950,4952,4960,4964,4973,4975,4977,4984}
theorem mem_ids55 (n : Fin 5011) : n ∈ ids55 ↔ n = 4804 ∨ n = 4809 ∨ n = 4811 ∨ n = 4828 ∨ n = 4890 ∨ n = 4898 ∨ n = 4904 ∨ n = 4920 ∨ n = 4927 ∨ n = 4929 ∨ n = 4931 ∨ n = 4933 ∨ n = 4944 ∨ n = 4950 ∨ n = 4952 ∨ n = 4960 ∨ n = 4964 ∨ n = 4973 ∨ n = 4975 ∨ n = 4977 ∨ n = 4984 := by
  simp only [ids55, Finset.mem_insert, Finset.mem_singleton]
theorem ids55_card : ids55.card = 21 := by decide +kernel
theorem sub55 (n : Fin 5011) (hn : n ∈ ids55) : n ∈ Paid16GeneralH81.newIDs := by
  rcases (mem_ids55 n).mp hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
def newIDs : Finset (Fin 5011) := ids48 ∪ (ids49 ∪ (ids50 ∪ (ids51 ∪ (ids52 ∪ (ids53 ∪ (ids54 ∪ (ids55)))))))
theorem new_mem (n : Fin 5011) : n ∈ newIDs ↔ n ∈ ids48 ∨ n ∈ ids49 ∨ n ∈ ids50 ∨ n ∈ ids51 ∨ n ∈ ids52 ∨ n ∈ ids53 ∨ n ∈ ids54 ∨ n ∈ ids55 := by
  simp only [newIDs, Finset.mem_union]
theorem new_count : newIDs.card = 168 := by decide +kernel
theorem new_terminal (n : Fin 5011) (hn : n ∈ newIDs) :
    (DBMSourceTree.data n).terminal = true := by
  rcases (new_mem n).mp hn with h | h | h | h | h | h | h | h
  · exact Paid16GeneralH74.new_terminal n (sub48 n h)
  · exact Paid16GeneralH75.new_terminal n (sub49 n h)
  · exact Paid16GeneralH76.new_terminal n (sub50 n h)
  · exact Paid16GeneralH77.new_terminal n (sub51 n h)
  · exact Paid16GeneralH78.new_terminal n (sub52 n h)
  · exact Paid16GeneralH79.new_terminal n (sub53 n h)
  · exact Paid16GeneralH80.new_terminal n (sub54 n h)
  · exact Paid16GeneralH81.new_terminal n (sub55 n h)
theorem new_radius (n : Fin 5011) (hn : n ∈ newIDs)
    (y : Fin 9 → ℝ) (hy0 : ∀ q, 0 ≤ y q) (hy1 : ∑ q, y q = 1)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius < r := by
  rcases (new_mem n).mp hn with h | h | h | h | h | h | h | h
  · exact Paid16GeneralH74.new_radius n (sub48 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH75.new_radius n (sub49 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH76.new_radius n (sub50 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH77.new_radius n (sub51 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH78.new_radius n (sub52 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH79.new_radius n (sub53 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH80.new_radius n (sub54 n h) y hy0 hy1 hc C Z r hf
  · exact Paid16GeneralH81.new_radius n (sub55 n h) y hy0 hy1 hc C Z r hf
theorem disjoint_sharp : Disjoint newIDs Patch120SharpDispatch.sharpIDs := by decide +kernel
end
end N11Formalization.Paid16GeneralNext1182S07
#print axioms N11Formalization.Paid16GeneralNext1182S07.new_count
#print axioms N11Formalization.Paid16GeneralNext1182S07.new_radius
