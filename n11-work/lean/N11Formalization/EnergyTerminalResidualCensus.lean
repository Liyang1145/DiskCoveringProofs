import N11Formalization.EnergyTerminalBatchB13

/-! Literal census of the 389 B13 residual terminal ids.

`terminal_ids` below are reconstructed from `DBMSourceTreeData.nodeN`; the
packet ids are reconstructed from their checked-in packet arrays and manifests.
The literal chunks keep every `decide +kernel` below 101 elements.  The final
equality connects the literal list to the semantic filter in B13 via 51
source-index interval lemmas, each deciding at most 100 nodes. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace N11Formalization.EnergyTerminalResidualCensus
open Finset
noncomputable section

def chunk0 : Finset (Fin 5011) := {3,23,37,38,39,40,41,65,66,79,230,411,534,715,1409,2337,2341,2356,2360,2368,2370,2957,2965,2967,2988,3040,3045,3047,3108,3112,3116,3126,3145,3149,3150,3182,3420,3422,3431,3432,3440,3442,3480,3489,3490,3491,3496,3497,3501,3503,3511,3515,3517,3519,3520,3521,3522,3529,3531,3533,3535,3545,3549,3550,3557,3558,3564,3569,3573,3578,3589,3593,3606,3613,3615,3621,3623,3629,3633,3637,3639,3643,3653,3657,3664,3674,3683,3738,3739,3762,3765,3771,3773,3777,3778,3780,3781,3783,3785,3789}
theorem chunk0_card : chunk0.card = 100 := by decide +kernel
def chunk1 : Finset (Fin 5011) := {3792,3794,3795,3800,3802,3803,3807,3808,3809,3810,3811,3812,3814,3818,3821,3824,3825,3827,3836,3837,3838,3839,3840,3841,3851,3853,3854,3855,3856,3857,3858,3859,3861,3862,3863,3865,3866,3875,3888,3889,3890,3891,3892,3893,3894,3896,3897,3898,3900,3903,3904,3914,3923,3926,3930,3931,3932,3937,3944,3945,3948,3964,3979,4011,4015,4024,4051,4076,4086,4094,4096,4100,4104,4107,4108,4112,4138,4139,4150,4152,4154,4156,4158,4160,4162,4202,4204,4208,4212,4215,4216,4227,4230,4232,4233,4236,4237,4238,4243,4244}
theorem chunk1_card : chunk1.card = 100 := by decide +kernel
def chunk2 : Finset (Fin 5011) := {4246,4286,4291,4292,4293,4294,4296,4304,4305,4306,4308,4309,4311,4312,4313,4317,4319,4320,4321,4322,4323,4324,4325,4327,4329,4330,4331,4333,4335,4336,4337,4340,4341,4344,4347,4351,4365,4371,4385,4397,4399,4401,4403,4406,4419,4421,4422,4423,4424,4425,4426,4427,4428,4431,4433,4435,4447,4449,4451,4453,4459,4461,4465,4467,4468,4473,4475,4477,4479,4489,4491,4517,4518,4523,4528,4543,4547,4548,4551,4557,4560,4561,4562,4566,4567,4568,4570,4575,4577,4579,4581,4587,4590,4591,4597,4599,4602,4608,4612,4618}
theorem chunk2_card : chunk2.card = 100 := by decide +kernel
def chunk3 : Finset (Fin 5011) := {4620,4622,4633,4634,4639,4641,4643,4645,4646,4650,4654,4656,4660,4663,4671,4672,4673,4674,4678,4682,4683,4684,4685,4688,4692,4704,4706,4708,4710,4712,4714,4716,4717,4721,4723,4726,4727,4730,4735,4737,4744,4745,4747,4753,4755,4757,4761,4765,4770,4773,4775,4783,4785,4786,4787,4789,4792,4793,4794,4797,4801,4825,4829,4831,4843,4844,4879,4905,4921,4922,4923,4924,4926,4936,4937,4938,4939,4940,4941,4947,4954,4962,4963,4965,4966,4967,4971,4982,4992}
theorem chunk3_card : chunk3.card = 89 := by decide +kernel
def residualIDs : Finset (Fin 5011) := chunk0 ∪ (chunk1 ∪ (chunk2 ∪ (chunk3)))
private theorem chunk0_disjoint : Disjoint chunk0 (chunk1 ∪ (chunk2 ∪ (chunk3))) := by decide +kernel
private theorem chunk1_disjoint : Disjoint chunk1 (chunk2 ∪ (chunk3)) := by decide +kernel
private theorem chunk2_disjoint : Disjoint chunk2 (chunk3) := by decide +kernel
theorem residualIDs_card : residualIDs.card = 389 := by
  rw [residualIDs, Finset.card_union_of_disjoint chunk0_disjoint, chunk0_card]
  rw [Finset.card_union_of_disjoint chunk1_disjoint, chunk1_card]
  rw [Finset.card_union_of_disjoint chunk2_disjoint, chunk2_card]
  rw [chunk3_card]
  norm_num
private theorem mem_iff_block00 (n : Fin 5011)
    (hlo : 0 ≤ n.val) (hhi : n.val < 100) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block01 (n : Fin 5011)
    (hlo : 100 ≤ n.val) (hhi : n.val < 200) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block02 (n : Fin 5011)
    (hlo : 200 ≤ n.val) (hhi : n.val < 300) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block03 (n : Fin 5011)
    (hlo : 300 ≤ n.val) (hhi : n.val < 400) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block04 (n : Fin 5011)
    (hlo : 400 ≤ n.val) (hhi : n.val < 500) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block05 (n : Fin 5011)
    (hlo : 500 ≤ n.val) (hhi : n.val < 600) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block06 (n : Fin 5011)
    (hlo : 600 ≤ n.val) (hhi : n.val < 700) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block07 (n : Fin 5011)
    (hlo : 700 ≤ n.val) (hhi : n.val < 800) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block08 (n : Fin 5011)
    (hlo : 800 ≤ n.val) (hhi : n.val < 900) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block09 (n : Fin 5011)
    (hlo : 900 ≤ n.val) (hhi : n.val < 1000) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block10 (n : Fin 5011)
    (hlo : 1000 ≤ n.val) (hhi : n.val < 1100) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block11 (n : Fin 5011)
    (hlo : 1100 ≤ n.val) (hhi : n.val < 1200) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block12 (n : Fin 5011)
    (hlo : 1200 ≤ n.val) (hhi : n.val < 1300) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block13 (n : Fin 5011)
    (hlo : 1300 ≤ n.val) (hhi : n.val < 1400) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block14 (n : Fin 5011)
    (hlo : 1400 ≤ n.val) (hhi : n.val < 1500) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block15 (n : Fin 5011)
    (hlo : 1500 ≤ n.val) (hhi : n.val < 1600) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block16 (n : Fin 5011)
    (hlo : 1600 ≤ n.val) (hhi : n.val < 1700) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block17 (n : Fin 5011)
    (hlo : 1700 ≤ n.val) (hhi : n.val < 1800) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block18 (n : Fin 5011)
    (hlo : 1800 ≤ n.val) (hhi : n.val < 1900) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block19 (n : Fin 5011)
    (hlo : 1900 ≤ n.val) (hhi : n.val < 2000) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block20 (n : Fin 5011)
    (hlo : 2000 ≤ n.val) (hhi : n.val < 2100) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block21 (n : Fin 5011)
    (hlo : 2100 ≤ n.val) (hhi : n.val < 2200) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block22 (n : Fin 5011)
    (hlo : 2200 ≤ n.val) (hhi : n.val < 2300) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block23 (n : Fin 5011)
    (hlo : 2300 ≤ n.val) (hhi : n.val < 2400) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block24 (n : Fin 5011)
    (hlo : 2400 ≤ n.val) (hhi : n.val < 2500) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block25 (n : Fin 5011)
    (hlo : 2500 ≤ n.val) (hhi : n.val < 2600) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block26 (n : Fin 5011)
    (hlo : 2600 ≤ n.val) (hhi : n.val < 2700) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block27 (n : Fin 5011)
    (hlo : 2700 ≤ n.val) (hhi : n.val < 2800) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block28 (n : Fin 5011)
    (hlo : 2800 ≤ n.val) (hhi : n.val < 2900) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block29 (n : Fin 5011)
    (hlo : 2900 ≤ n.val) (hhi : n.val < 3000) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block30 (n : Fin 5011)
    (hlo : 3000 ≤ n.val) (hhi : n.val < 3100) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block31 (n : Fin 5011)
    (hlo : 3100 ≤ n.val) (hhi : n.val < 3200) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block32 (n : Fin 5011)
    (hlo : 3200 ≤ n.val) (hhi : n.val < 3300) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block33 (n : Fin 5011)
    (hlo : 3300 ≤ n.val) (hhi : n.val < 3400) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block34 (n : Fin 5011)
    (hlo : 3400 ≤ n.val) (hhi : n.val < 3500) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block35 (n : Fin 5011)
    (hlo : 3500 ≤ n.val) (hhi : n.val < 3600) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block36 (n : Fin 5011)
    (hlo : 3600 ≤ n.val) (hhi : n.val < 3700) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block37 (n : Fin 5011)
    (hlo : 3700 ≤ n.val) (hhi : n.val < 3800) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block38 (n : Fin 5011)
    (hlo : 3800 ≤ n.val) (hhi : n.val < 3900) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block39 (n : Fin 5011)
    (hlo : 3900 ≤ n.val) (hhi : n.val < 4000) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block40 (n : Fin 5011)
    (hlo : 4000 ≤ n.val) (hhi : n.val < 4100) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block41 (n : Fin 5011)
    (hlo : 4100 ≤ n.val) (hhi : n.val < 4200) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block42 (n : Fin 5011)
    (hlo : 4200 ≤ n.val) (hhi : n.val < 4300) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block43 (n : Fin 5011)
    (hlo : 4300 ≤ n.val) (hhi : n.val < 4400) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block44 (n : Fin 5011)
    (hlo : 4400 ≤ n.val) (hhi : n.val < 4500) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block45 (n : Fin 5011)
    (hlo : 4500 ≤ n.val) (hhi : n.val < 4600) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block46 (n : Fin 5011)
    (hlo : 4600 ≤ n.val) (hhi : n.val < 4700) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block47 (n : Fin 5011)
    (hlo : 4700 ≤ n.val) (hhi : n.val < 4800) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block48 (n : Fin 5011)
    (hlo : 4800 ≤ n.val) (hhi : n.val < 4900) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block49 (n : Fin 5011)
    (hlo : 4900 ≤ n.val) (hhi : n.val < 5000) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

private theorem mem_iff_block50 (n : Fin 5011)
    (hlo : 5000 ≤ n.val) (hhi : n.val < 5011) :
    n ∈ residualIDs ↔ n ∈ EnergyTerminalBatchB13.residualIDs := by
  interval_cases n.val <;>
    rw [EnergyTerminalBatchB13.mem_residualIDs_iff] <;> decide +kernel

theorem residualIDs_eq :
    residualIDs = EnergyTerminalBatchB13.residualIDs := by
  ext n
  have hcover : n.val < 100 ∨ (100 ≤ n.val ∧ n.val < 200) ∨ (200 ≤ n.val ∧ n.val < 300) ∨ (300 ≤ n.val ∧ n.val < 400) ∨ (400 ≤ n.val ∧ n.val < 500) ∨ (500 ≤ n.val ∧ n.val < 600) ∨ (600 ≤ n.val ∧ n.val < 700) ∨ (700 ≤ n.val ∧ n.val < 800) ∨ (800 ≤ n.val ∧ n.val < 900) ∨ (900 ≤ n.val ∧ n.val < 1000) ∨ (1000 ≤ n.val ∧ n.val < 1100) ∨ (1100 ≤ n.val ∧ n.val < 1200) ∨ (1200 ≤ n.val ∧ n.val < 1300) ∨ (1300 ≤ n.val ∧ n.val < 1400) ∨ (1400 ≤ n.val ∧ n.val < 1500) ∨ (1500 ≤ n.val ∧ n.val < 1600) ∨ (1600 ≤ n.val ∧ n.val < 1700) ∨ (1700 ≤ n.val ∧ n.val < 1800) ∨ (1800 ≤ n.val ∧ n.val < 1900) ∨ (1900 ≤ n.val ∧ n.val < 2000) ∨ (2000 ≤ n.val ∧ n.val < 2100) ∨ (2100 ≤ n.val ∧ n.val < 2200) ∨ (2200 ≤ n.val ∧ n.val < 2300) ∨ (2300 ≤ n.val ∧ n.val < 2400) ∨ (2400 ≤ n.val ∧ n.val < 2500) ∨ (2500 ≤ n.val ∧ n.val < 2600) ∨ (2600 ≤ n.val ∧ n.val < 2700) ∨ (2700 ≤ n.val ∧ n.val < 2800) ∨ (2800 ≤ n.val ∧ n.val < 2900) ∨ (2900 ≤ n.val ∧ n.val < 3000) ∨ (3000 ≤ n.val ∧ n.val < 3100) ∨ (3100 ≤ n.val ∧ n.val < 3200) ∨ (3200 ≤ n.val ∧ n.val < 3300) ∨ (3300 ≤ n.val ∧ n.val < 3400) ∨ (3400 ≤ n.val ∧ n.val < 3500) ∨ (3500 ≤ n.val ∧ n.val < 3600) ∨ (3600 ≤ n.val ∧ n.val < 3700) ∨ (3700 ≤ n.val ∧ n.val < 3800) ∨ (3800 ≤ n.val ∧ n.val < 3900) ∨ (3900 ≤ n.val ∧ n.val < 4000) ∨ (4000 ≤ n.val ∧ n.val < 4100) ∨ (4100 ≤ n.val ∧ n.val < 4200) ∨ (4200 ≤ n.val ∧ n.val < 4300) ∨ (4300 ≤ n.val ∧ n.val < 4400) ∨ (4400 ≤ n.val ∧ n.val < 4500) ∨ (4500 ≤ n.val ∧ n.val < 4600) ∨ (4600 ≤ n.val ∧ n.val < 4700) ∨ (4700 ≤ n.val ∧ n.val < 4800) ∨ (4800 ≤ n.val ∧ n.val < 4900) ∨ (4900 ≤ n.val ∧ n.val < 5000) ∨ 5000 ≤ n.val := by omega
  rcases hcover with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50
  · exact mem_iff_block00 n (Nat.zero_le _) h0
  · exact mem_iff_block01 n h1.1 h1.2
  · exact mem_iff_block02 n h2.1 h2.2
  · exact mem_iff_block03 n h3.1 h3.2
  · exact mem_iff_block04 n h4.1 h4.2
  · exact mem_iff_block05 n h5.1 h5.2
  · exact mem_iff_block06 n h6.1 h6.2
  · exact mem_iff_block07 n h7.1 h7.2
  · exact mem_iff_block08 n h8.1 h8.2
  · exact mem_iff_block09 n h9.1 h9.2
  · exact mem_iff_block10 n h10.1 h10.2
  · exact mem_iff_block11 n h11.1 h11.2
  · exact mem_iff_block12 n h12.1 h12.2
  · exact mem_iff_block13 n h13.1 h13.2
  · exact mem_iff_block14 n h14.1 h14.2
  · exact mem_iff_block15 n h15.1 h15.2
  · exact mem_iff_block16 n h16.1 h16.2
  · exact mem_iff_block17 n h17.1 h17.2
  · exact mem_iff_block18 n h18.1 h18.2
  · exact mem_iff_block19 n h19.1 h19.2
  · exact mem_iff_block20 n h20.1 h20.2
  · exact mem_iff_block21 n h21.1 h21.2
  · exact mem_iff_block22 n h22.1 h22.2
  · exact mem_iff_block23 n h23.1 h23.2
  · exact mem_iff_block24 n h24.1 h24.2
  · exact mem_iff_block25 n h25.1 h25.2
  · exact mem_iff_block26 n h26.1 h26.2
  · exact mem_iff_block27 n h27.1 h27.2
  · exact mem_iff_block28 n h28.1 h28.2
  · exact mem_iff_block29 n h29.1 h29.2
  · exact mem_iff_block30 n h30.1 h30.2
  · exact mem_iff_block31 n h31.1 h31.2
  · exact mem_iff_block32 n h32.1 h32.2
  · exact mem_iff_block33 n h33.1 h33.2
  · exact mem_iff_block34 n h34.1 h34.2
  · exact mem_iff_block35 n h35.1 h35.2
  · exact mem_iff_block36 n h36.1 h36.2
  · exact mem_iff_block37 n h37.1 h37.2
  · exact mem_iff_block38 n h38.1 h38.2
  · exact mem_iff_block39 n h39.1 h39.2
  · exact mem_iff_block40 n h40.1 h40.2
  · exact mem_iff_block41 n h41.1 h41.2
  · exact mem_iff_block42 n h42.1 h42.2
  · exact mem_iff_block43 n h43.1 h43.2
  · exact mem_iff_block44 n h44.1 h44.2
  · exact mem_iff_block45 n h45.1 h45.2
  · exact mem_iff_block46 n h46.1 h46.2
  · exact mem_iff_block47 n h47.1 h47.2
  · exact mem_iff_block48 n h48.1 h48.2
  · exact mem_iff_block49 n h49.1 h49.2
  · exact mem_iff_block50 n h50 n.isLt

theorem b13_residualIDs_card :
    EnergyTerminalBatchB13.residualIDs.card = 389 := by
  rw [← residualIDs_eq, residualIDs_card]

theorem residualIDs_sound :
    ∀ n ∈ residualIDs, (DBMSourceTree.data n).terminal = true ∧
      n ∉ Patch120SharpDispatch.sharpIDs ∧
      n ∉ EnergyTerminalBatchB13.paidIDs := by
  intro n hn
  rw [residualIDs_eq] at hn
  exact (EnergyTerminalBatchB13.mem_residualIDs_iff n).mp hn

def RemainingTerminalRadius : Prop :=
  ∀ n : Fin 5011, n ∈ residualIDs →
    ∀ (y : Fin 9 → ℝ), (∀ q, 0 ≤ y q) → (∑ q, y q = 1) →
      FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 n)
        (FlashLeafSplit.tlift y) →
      ∀ (C Z : Fin 11 → Point) (r : ℝ),
        ResumeNetwork.Feasible (SourceChartIsometry.chartAnchors y) C Z r →
          SourceExactRoot.sourceRadius ≤ r

theorem remaining_iff_b13 :
    RemainingTerminalRadius ↔ EnergyTerminalBatchB13.RemainingTerminalRadius := by
  rw [EnergyTerminalBatchB13.remaining_iff]
  constructor
  · intro h n hn
    rw [← residualIDs_eq] at hn
    exact h n hn
  · intro h n hn
    rw [residualIDs_eq] at hn
    exact h n hn
end
end N11Formalization.EnergyTerminalResidualCensus
#check @N11Formalization.EnergyTerminalResidualCensus.residualIDs_card
#check @N11Formalization.EnergyTerminalResidualCensus.residualIDs_eq
#check @N11Formalization.EnergyTerminalResidualCensus.b13_residualIDs_card
#check @N11Formalization.EnergyTerminalResidualCensus.remaining_iff_b13
#print axioms N11Formalization.EnergyTerminalResidualCensus.residualIDs_card
#print axioms N11Formalization.EnergyTerminalResidualCensus.residualIDs_eq
#print axioms N11Formalization.EnergyTerminalResidualCensus.b13_residualIDs_card
