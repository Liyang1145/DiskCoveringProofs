import N11Formalization.Patch120IntervalCore
import N11Formalization.DBMSourceTreeData
import N11Formalization.FlashLocalFrobeniusEnclosure

/-! All120 frozen source sharp-cell domains ->full original local ball.
Actual tree terminal/pinned-row bindings are kernel-paid; root/chart/rotation/
gain use the SAME source. This does not classify every other terminal's semantics. -/
set_option autoImplicit false
namespace N11Formalization.Patch120DomainPacket
open N11Formalization RatInterval Patch120IntervalCore SourceChartIsometry
noncomputable section
-- Finite evaluator stack only, default heartbeats/kernel unchanged.
set_option maxRecDepth 10000

def patchID : Fin 120 → Fin 5011 :=
 ![4436,4529,4589,4711,4713,4778,4795,4796,4805,4806,4807,4813,4814,4815,4816,4817,4818,4819,4820,4821,4822,4823,4824,4833,4834,4835,4836,4837,4838,4839,4840,4841,4842,4845,4846,4847,4848,4849,4851,4852,4853,4854,4855,4856,4857,4858,4859,4860,4861,4862,4863,4864,4865,4866,4869,4870,4871,4872,4873,4874,4875,4876,4877,4881,4882,4883,4884,4885,4886,4887,4888,4891,4892,4893,4894,4895,4896,4899,4900,4901,4902,4907,4908,4909,4910,4911,4912,4913,4914,4915,4916,4917,4918,4932,4935,4955,4956,4957,4958,4959,4970,4972,4974,4980,4981,4983,4985,4988,4989,4993,4996,4997,4999,5001,5003,5005,5006,5008,5009,5010]

def group : Fin 120 → Fin 16 :=
 ![12,12,12,12,12,12,6,6,12,12,12,9,12,12,12,12,12,12,12,15,12,2,2,12,12,12,12,12,12,12,12,13,13,14,15,14,13,13,12,12,12,12,12,12,14,14,12,12,14,14,14,14,14,14,15,15,15,15,15,8,15,15,13,15,8,15,8,12,14,14,14,15,15,15,8,8,15,12,12,15,8,15,15,15,8,12,12,12,12,12,12,12,12,12,5,13,10,5,1,10,7,12,0,11,15,15,11,9,10,4,0,11,14,9,4,14,7,3,14,7]

def UL : Fin 16 → Fin 9 → ℤ :=
 ![![-2160,-2056,-2048,-1984,-776,-232,0,180,720],![-2136,-2092,-2048,-1968,-748,-200,0,192,748],![-2160,-2056,-2048,-1984,-776,-224,0,176,720],![-2140,-2056,-2048,-1964,-748,-212,0,196,740],![-2156,-2056,-2048,-1984,-776,-228,0,172,720],![-2136,-2096,-2048,-1968,-752,-208,0,192,744],![-2160,-2056,-2048,-1984,-776,-224,0,172,720],![-2156,-2056,-2048,-1984,-772,-228,0,172,724],![-2160,-2112,-2048,-1984,-768,-224,0,176,736],![-2136,-2092,-2048,-1968,-752,-216,0,192,744],![-2136,-2080,-2048,-1968,-752,-200,0,192,744],![-2140,-2084,-2048,-1972,-752,-220,0,192,736],![-2152,-2080,-2048,-1980,-764,-220,0,176,724],![-2152,-2096,-2048,-1984,-760,-224,0,184,736],![-2160,-2084,-2048,-1984,-776,-232,0,168,720],![-2152,-2104,-2048,-1984,-760,-224,0,176,728]]

def UH : Fin 16 → Fin 9 → ℤ :=
 ![![-2128,-2016,-2012,-1960,-736,-192,0,216,752],![-2112,-2056,-2008,-1936,-720,-168,0,224,776],![-2128,-2024,-2000,-1960,-744,-192,0,216,752],![-2112,-2028,-2008,-1936,-720,-176,0,236,776],![-2128,-2024,-2004,-1960,-744,-196,0,200,748],![-2112,-2012,-2012,-1936,-720,-172,0,224,772],![-2128,-2024,-2004,-1960,-744,-192,0,200,748],![-2128,-2024,-2000,-1960,-744,-192,0,200,752],![-2120,-2056,-2024,-1952,-728,-184,0,216,760],![-2112,-2028,-2008,-1936,-720,-176,0,230,776],![-2112,-2056,-2008,-1936,-720,-164,0,232,776],![-2112,-2028,-2012,-1936,-720,-176,0,240,772],![-2112,-2032,-1988,-1940,-724,-176,0,220,764],![-2112,-2016,-2016,-1936,-720,-172,0,232,768],![-2112,-2032,-2014,-1942,-726,-176,0,218,770],![-2120,-2024,-2000,-1952,-736,-184,0,216,760]]

def XL : Fin 16 → Fin 9 → ℤ :=
 ![![-824158,-7302626,-4868794,-607785,-1744284,-1209042,0,-3086753,-1119585],![-3688017,-142978,-5584758,-4903574,-4608143,-5504831,0,-4518682,-5415374],![-824158,-5870697,-7016688,-607785,-312354,-1209042,0,-3086753,-1119585],![-3688017,-5154732,-5584758,-4903574,-4608143,-4072901,0,-6666577,-5415374],![-824158,-5870697,-6300723,-607785,-312354,-493077,0,-222893,-403620],![-3688017,-8018591,-4868794,-4903574,-4608143,-4788866,0,-4518682,-4699409],![-824158,-5870697,-6300723,-607785,-312354,-1209042,0,-222893,-403620],![-824158,-5870697,-7016688,-607785,-312354,-1209042,0,-222893,-1119585],![-2256088,-142978,-2720899,-2039715,-3176214,-2640971,0,-3086753,-2551514],![-3688017,-5154732,-5584758,-4903574,-4608143,-4072901,0,-5592630,-5415374],![-3688017,-142978,-5584758,-4903574,-4608143,-6220796,0,-5950612,-5415374],![-3688017,-5154732,-4868794,-4903574,-4608143,-4072901,0,-7382542,-4699409],![-3688017,-4438767,-9164583,-4187609,-3892178,-4072901,0,-3802717,-3267479],![-3688017,-7302626,-4152829,-4903574,-4608143,-4788866,0,-5950612,-3983444],![-3688017,-4438767,-4510811,-3829627,-3534196,-4072901,0,-3444735,-4341427],![-2256088,-5870697,-7016688,-2039715,-1744284,-2640971,0,-3086753,-2551514]]

def XH : Fin 16 → Fin 9 → ℤ :=
 ![![4903574,-142961,1574907,3688017,5415374,5950612,0,3356936,4608143],![607785,6300723,1574907,824158,403620,222893,0,1209042,-403611],![4903574,-142961,1574907,3688017,5415374,4518682,0,4072901,4608143],![1323750,-142961,1574907,108193,403620,2370788,0,493077,1028319],![4187609,-142961,1574907,3688017,5415374,5234647,0,4788866,4608143],![607785,7016688,1574907,824158,1119585,1654823,0,1209042,312354],![4903574,-142961,1574907,3688017,5415374,4518682,0,4788866,4608143],![4187609,-142961,1574907,3688017,4699409,5234647,0,4788866,3892178],![4903574,9880548,1574907,3688017,3983444,4518682,0,4072901,1744284],![607785,6300723,1574907,824158,1119585,3086753,0,1209042,312354],![607785,4152829,1574907,824158,1119585,222893,0,1209042,312354],![1323750,4868794,1574907,1540123,1119585,3802717,0,1209042,1744284],![3471644,4152829,1574907,2972052,3267479,3802717,0,4072901,3892178],![3471644,7016688,1574907,3688017,2551514,4518682,0,2640971,1744284],![4903574,4868794,1574907,3688017,5415374,5950612,0,5504831,4608143],![3471644,8448618,1574907,3688017,2551514,4518682,0,4072901,3176214]]

def UBox (g : Fin 16) (i : Fin 9) : RatInterval :=
  intv ((UL g i : ℚ)/4096) ((UH g i : ℚ)/4096)
def XBox (g : Fin 16) (i : Fin 9) : RatInterval :=
  intv ((XL g i : ℚ)/1000000000) ((XH g i : ℚ)/1000000000)

def Member (p : Fin 120) : Prop :=
  (DBMSourceTree.data (patchID p)).terminal=true ∧
  ∀ i : Fin 9,i≠6 →
    UL (group p) i≤-(DBMSourceTree.data (patchID p)).db (Patch120K5.f9 i) 6 ∧
    (DBMSourceTree.data (patchID p)).db 6 (Patch120K5.f9 i)≤UH (group p) i
private theorem node0 : DBMSourceTree.data (patchID 0)=DBMSourceTree.node4436 := rfl
private theorem member0 : Member 0 := by
  unfold Member
  rw [node0]
  decide +kernel
private theorem node1 : DBMSourceTree.data (patchID 1)=DBMSourceTree.node4529 := rfl
private theorem member1 : Member 1 := by
  unfold Member
  rw [node1]
  decide +kernel
private theorem node2 : DBMSourceTree.data (patchID 2)=DBMSourceTree.node4589 := rfl
private theorem member2 : Member 2 := by
  unfold Member
  rw [node2]
  decide +kernel
private theorem node3 : DBMSourceTree.data (patchID 3)=DBMSourceTree.node4711 := rfl
private theorem member3 : Member 3 := by
  unfold Member
  rw [node3]
  decide +kernel
private theorem node4 : DBMSourceTree.data (patchID 4)=DBMSourceTree.node4713 := rfl
private theorem member4 : Member 4 := by
  unfold Member
  rw [node4]
  decide +kernel
private theorem node5 : DBMSourceTree.data (patchID 5)=DBMSourceTree.node4778 := rfl
private theorem member5 : Member 5 := by
  unfold Member
  rw [node5]
  decide +kernel
private theorem node6 : DBMSourceTree.data (patchID 6)=DBMSourceTree.node4795 := rfl
private theorem member6 : Member 6 := by
  unfold Member
  rw [node6]
  decide +kernel
private theorem node7 : DBMSourceTree.data (patchID 7)=DBMSourceTree.node4796 := rfl
private theorem member7 : Member 7 := by
  unfold Member
  rw [node7]
  decide +kernel
private theorem node8 : DBMSourceTree.data (patchID 8)=DBMSourceTree.node4805 := rfl
private theorem member8 : Member 8 := by
  unfold Member
  rw [node8]
  decide +kernel
private theorem node9 : DBMSourceTree.data (patchID 9)=DBMSourceTree.node4806 := rfl
private theorem member9 : Member 9 := by
  unfold Member
  rw [node9]
  decide +kernel
private theorem node10 : DBMSourceTree.data (patchID 10)=DBMSourceTree.node4807 := rfl
private theorem member10 : Member 10 := by
  unfold Member
  rw [node10]
  decide +kernel
private theorem node11 : DBMSourceTree.data (patchID 11)=DBMSourceTree.node4813 := rfl
private theorem member11 : Member 11 := by
  unfold Member
  rw [node11]
  decide +kernel
private theorem node12 : DBMSourceTree.data (patchID 12)=DBMSourceTree.node4814 := rfl
private theorem member12 : Member 12 := by
  unfold Member
  rw [node12]
  decide +kernel
private theorem node13 : DBMSourceTree.data (patchID 13)=DBMSourceTree.node4815 := rfl
private theorem member13 : Member 13 := by
  unfold Member
  rw [node13]
  decide +kernel
private theorem node14 : DBMSourceTree.data (patchID 14)=DBMSourceTree.node4816 := rfl
private theorem member14 : Member 14 := by
  unfold Member
  rw [node14]
  decide +kernel
private theorem node15 : DBMSourceTree.data (patchID 15)=DBMSourceTree.node4817 := rfl
private theorem member15 : Member 15 := by
  unfold Member
  rw [node15]
  decide +kernel
private theorem node16 : DBMSourceTree.data (patchID 16)=DBMSourceTree.node4818 := rfl
private theorem member16 : Member 16 := by
  unfold Member
  rw [node16]
  decide +kernel
private theorem node17 : DBMSourceTree.data (patchID 17)=DBMSourceTree.node4819 := rfl
private theorem member17 : Member 17 := by
  unfold Member
  rw [node17]
  decide +kernel
private theorem node18 : DBMSourceTree.data (patchID 18)=DBMSourceTree.node4820 := rfl
private theorem member18 : Member 18 := by
  unfold Member
  rw [node18]
  decide +kernel
private theorem node19 : DBMSourceTree.data (patchID 19)=DBMSourceTree.node4821 := rfl
private theorem member19 : Member 19 := by
  unfold Member
  rw [node19]
  decide +kernel
private theorem node20 : DBMSourceTree.data (patchID 20)=DBMSourceTree.node4822 := rfl
private theorem member20 : Member 20 := by
  unfold Member
  rw [node20]
  decide +kernel
private theorem node21 : DBMSourceTree.data (patchID 21)=DBMSourceTree.node4823 := rfl
private theorem member21 : Member 21 := by
  unfold Member
  rw [node21]
  decide +kernel
private theorem node22 : DBMSourceTree.data (patchID 22)=DBMSourceTree.node4824 := rfl
private theorem member22 : Member 22 := by
  unfold Member
  rw [node22]
  decide +kernel
private theorem node23 : DBMSourceTree.data (patchID 23)=DBMSourceTree.node4833 := rfl
private theorem member23 : Member 23 := by
  unfold Member
  rw [node23]
  decide +kernel
private theorem node24 : DBMSourceTree.data (patchID 24)=DBMSourceTree.node4834 := rfl
private theorem member24 : Member 24 := by
  unfold Member
  rw [node24]
  decide +kernel
private theorem node25 : DBMSourceTree.data (patchID 25)=DBMSourceTree.node4835 := rfl
private theorem member25 : Member 25 := by
  unfold Member
  rw [node25]
  decide +kernel
private theorem node26 : DBMSourceTree.data (patchID 26)=DBMSourceTree.node4836 := rfl
private theorem member26 : Member 26 := by
  unfold Member
  rw [node26]
  decide +kernel
private theorem node27 : DBMSourceTree.data (patchID 27)=DBMSourceTree.node4837 := rfl
private theorem member27 : Member 27 := by
  unfold Member
  rw [node27]
  decide +kernel
private theorem node28 : DBMSourceTree.data (patchID 28)=DBMSourceTree.node4838 := rfl
private theorem member28 : Member 28 := by
  unfold Member
  rw [node28]
  decide +kernel
private theorem node29 : DBMSourceTree.data (patchID 29)=DBMSourceTree.node4839 := rfl
private theorem member29 : Member 29 := by
  unfold Member
  rw [node29]
  decide +kernel
private theorem node30 : DBMSourceTree.data (patchID 30)=DBMSourceTree.node4840 := rfl
private theorem member30 : Member 30 := by
  unfold Member
  rw [node30]
  decide +kernel
private theorem node31 : DBMSourceTree.data (patchID 31)=DBMSourceTree.node4841 := rfl
private theorem member31 : Member 31 := by
  unfold Member
  rw [node31]
  decide +kernel
private theorem node32 : DBMSourceTree.data (patchID 32)=DBMSourceTree.node4842 := rfl
private theorem member32 : Member 32 := by
  unfold Member
  rw [node32]
  decide +kernel
private theorem node33 : DBMSourceTree.data (patchID 33)=DBMSourceTree.node4845 := rfl
private theorem member33 : Member 33 := by
  unfold Member
  rw [node33]
  decide +kernel
private theorem node34 : DBMSourceTree.data (patchID 34)=DBMSourceTree.node4846 := rfl
private theorem member34 : Member 34 := by
  unfold Member
  rw [node34]
  decide +kernel
private theorem node35 : DBMSourceTree.data (patchID 35)=DBMSourceTree.node4847 := rfl
private theorem member35 : Member 35 := by
  unfold Member
  rw [node35]
  decide +kernel
private theorem node36 : DBMSourceTree.data (patchID 36)=DBMSourceTree.node4848 := rfl
private theorem member36 : Member 36 := by
  unfold Member
  rw [node36]
  decide +kernel
private theorem node37 : DBMSourceTree.data (patchID 37)=DBMSourceTree.node4849 := rfl
private theorem member37 : Member 37 := by
  unfold Member
  rw [node37]
  decide +kernel
private theorem node38 : DBMSourceTree.data (patchID 38)=DBMSourceTree.node4851 := rfl
private theorem member38 : Member 38 := by
  unfold Member
  rw [node38]
  decide +kernel
private theorem node39 : DBMSourceTree.data (patchID 39)=DBMSourceTree.node4852 := rfl
private theorem member39 : Member 39 := by
  unfold Member
  rw [node39]
  decide +kernel
private theorem node40 : DBMSourceTree.data (patchID 40)=DBMSourceTree.node4853 := rfl
private theorem member40 : Member 40 := by
  unfold Member
  rw [node40]
  decide +kernel
private theorem node41 : DBMSourceTree.data (patchID 41)=DBMSourceTree.node4854 := rfl
private theorem member41 : Member 41 := by
  unfold Member
  rw [node41]
  decide +kernel
private theorem node42 : DBMSourceTree.data (patchID 42)=DBMSourceTree.node4855 := rfl
private theorem member42 : Member 42 := by
  unfold Member
  rw [node42]
  decide +kernel
private theorem node43 : DBMSourceTree.data (patchID 43)=DBMSourceTree.node4856 := rfl
private theorem member43 : Member 43 := by
  unfold Member
  rw [node43]
  decide +kernel
private theorem node44 : DBMSourceTree.data (patchID 44)=DBMSourceTree.node4857 := rfl
private theorem member44 : Member 44 := by
  unfold Member
  rw [node44]
  decide +kernel
private theorem node45 : DBMSourceTree.data (patchID 45)=DBMSourceTree.node4858 := rfl
private theorem member45 : Member 45 := by
  unfold Member
  rw [node45]
  decide +kernel
private theorem node46 : DBMSourceTree.data (patchID 46)=DBMSourceTree.node4859 := rfl
private theorem member46 : Member 46 := by
  unfold Member
  rw [node46]
  decide +kernel
private theorem node47 : DBMSourceTree.data (patchID 47)=DBMSourceTree.node4860 := rfl
private theorem member47 : Member 47 := by
  unfold Member
  rw [node47]
  decide +kernel
private theorem node48 : DBMSourceTree.data (patchID 48)=DBMSourceTree.node4861 := rfl
private theorem member48 : Member 48 := by
  unfold Member
  rw [node48]
  decide +kernel
private theorem node49 : DBMSourceTree.data (patchID 49)=DBMSourceTree.node4862 := rfl
private theorem member49 : Member 49 := by
  unfold Member
  rw [node49]
  decide +kernel
private theorem node50 : DBMSourceTree.data (patchID 50)=DBMSourceTree.node4863 := rfl
private theorem member50 : Member 50 := by
  unfold Member
  rw [node50]
  decide +kernel
private theorem node51 : DBMSourceTree.data (patchID 51)=DBMSourceTree.node4864 := rfl
private theorem member51 : Member 51 := by
  unfold Member
  rw [node51]
  decide +kernel
private theorem node52 : DBMSourceTree.data (patchID 52)=DBMSourceTree.node4865 := rfl
private theorem member52 : Member 52 := by
  unfold Member
  rw [node52]
  decide +kernel
private theorem node53 : DBMSourceTree.data (patchID 53)=DBMSourceTree.node4866 := rfl
private theorem member53 : Member 53 := by
  unfold Member
  rw [node53]
  decide +kernel
private theorem node54 : DBMSourceTree.data (patchID 54)=DBMSourceTree.node4869 := rfl
private theorem member54 : Member 54 := by
  unfold Member
  rw [node54]
  decide +kernel
private theorem node55 : DBMSourceTree.data (patchID 55)=DBMSourceTree.node4870 := rfl
private theorem member55 : Member 55 := by
  unfold Member
  rw [node55]
  decide +kernel
private theorem node56 : DBMSourceTree.data (patchID 56)=DBMSourceTree.node4871 := rfl
private theorem member56 : Member 56 := by
  unfold Member
  rw [node56]
  decide +kernel
private theorem node57 : DBMSourceTree.data (patchID 57)=DBMSourceTree.node4872 := rfl
private theorem member57 : Member 57 := by
  unfold Member
  rw [node57]
  decide +kernel
private theorem node58 : DBMSourceTree.data (patchID 58)=DBMSourceTree.node4873 := rfl
private theorem member58 : Member 58 := by
  unfold Member
  rw [node58]
  decide +kernel
private theorem node59 : DBMSourceTree.data (patchID 59)=DBMSourceTree.node4874 := rfl
private theorem member59 : Member 59 := by
  unfold Member
  rw [node59]
  decide +kernel
private theorem node60 : DBMSourceTree.data (patchID 60)=DBMSourceTree.node4875 := rfl
private theorem member60 : Member 60 := by
  unfold Member
  rw [node60]
  decide +kernel
private theorem node61 : DBMSourceTree.data (patchID 61)=DBMSourceTree.node4876 := rfl
private theorem member61 : Member 61 := by
  unfold Member
  rw [node61]
  decide +kernel
private theorem node62 : DBMSourceTree.data (patchID 62)=DBMSourceTree.node4877 := rfl
private theorem member62 : Member 62 := by
  unfold Member
  rw [node62]
  decide +kernel
private theorem node63 : DBMSourceTree.data (patchID 63)=DBMSourceTree.node4881 := rfl
private theorem member63 : Member 63 := by
  unfold Member
  rw [node63]
  decide +kernel
private theorem node64 : DBMSourceTree.data (patchID 64)=DBMSourceTree.node4882 := rfl
private theorem member64 : Member 64 := by
  unfold Member
  rw [node64]
  decide +kernel
private theorem node65 : DBMSourceTree.data (patchID 65)=DBMSourceTree.node4883 := rfl
private theorem member65 : Member 65 := by
  unfold Member
  rw [node65]
  decide +kernel
private theorem node66 : DBMSourceTree.data (patchID 66)=DBMSourceTree.node4884 := rfl
private theorem member66 : Member 66 := by
  unfold Member
  rw [node66]
  decide +kernel
private theorem node67 : DBMSourceTree.data (patchID 67)=DBMSourceTree.node4885 := rfl
private theorem member67 : Member 67 := by
  unfold Member
  rw [node67]
  decide +kernel
private theorem node68 : DBMSourceTree.data (patchID 68)=DBMSourceTree.node4886 := rfl
private theorem member68 : Member 68 := by
  unfold Member
  rw [node68]
  decide +kernel
private theorem node69 : DBMSourceTree.data (patchID 69)=DBMSourceTree.node4887 := rfl
private theorem member69 : Member 69 := by
  unfold Member
  rw [node69]
  decide +kernel
private theorem node70 : DBMSourceTree.data (patchID 70)=DBMSourceTree.node4888 := rfl
private theorem member70 : Member 70 := by
  unfold Member
  rw [node70]
  decide +kernel
private theorem node71 : DBMSourceTree.data (patchID 71)=DBMSourceTree.node4891 := rfl
private theorem member71 : Member 71 := by
  unfold Member
  rw [node71]
  decide +kernel
private theorem node72 : DBMSourceTree.data (patchID 72)=DBMSourceTree.node4892 := rfl
private theorem member72 : Member 72 := by
  unfold Member
  rw [node72]
  decide +kernel
private theorem node73 : DBMSourceTree.data (patchID 73)=DBMSourceTree.node4893 := rfl
private theorem member73 : Member 73 := by
  unfold Member
  rw [node73]
  decide +kernel
private theorem node74 : DBMSourceTree.data (patchID 74)=DBMSourceTree.node4894 := rfl
private theorem member74 : Member 74 := by
  unfold Member
  rw [node74]
  decide +kernel
private theorem node75 : DBMSourceTree.data (patchID 75)=DBMSourceTree.node4895 := rfl
private theorem member75 : Member 75 := by
  unfold Member
  rw [node75]
  decide +kernel
private theorem node76 : DBMSourceTree.data (patchID 76)=DBMSourceTree.node4896 := rfl
private theorem member76 : Member 76 := by
  unfold Member
  rw [node76]
  decide +kernel
private theorem node77 : DBMSourceTree.data (patchID 77)=DBMSourceTree.node4899 := rfl
private theorem member77 : Member 77 := by
  unfold Member
  rw [node77]
  decide +kernel
private theorem node78 : DBMSourceTree.data (patchID 78)=DBMSourceTree.node4900 := rfl
private theorem member78 : Member 78 := by
  unfold Member
  rw [node78]
  decide +kernel
private theorem node79 : DBMSourceTree.data (patchID 79)=DBMSourceTree.node4901 := rfl
private theorem member79 : Member 79 := by
  unfold Member
  rw [node79]
  decide +kernel
private theorem node80 : DBMSourceTree.data (patchID 80)=DBMSourceTree.node4902 := rfl
private theorem member80 : Member 80 := by
  unfold Member
  rw [node80]
  decide +kernel
private theorem node81 : DBMSourceTree.data (patchID 81)=DBMSourceTree.node4907 := rfl
private theorem member81 : Member 81 := by
  unfold Member
  rw [node81]
  decide +kernel
private theorem node82 : DBMSourceTree.data (patchID 82)=DBMSourceTree.node4908 := rfl
private theorem member82 : Member 82 := by
  unfold Member
  rw [node82]
  decide +kernel
private theorem node83 : DBMSourceTree.data (patchID 83)=DBMSourceTree.node4909 := rfl
private theorem member83 : Member 83 := by
  unfold Member
  rw [node83]
  decide +kernel
private theorem node84 : DBMSourceTree.data (patchID 84)=DBMSourceTree.node4910 := rfl
private theorem member84 : Member 84 := by
  unfold Member
  rw [node84]
  decide +kernel
private theorem node85 : DBMSourceTree.data (patchID 85)=DBMSourceTree.node4911 := rfl
private theorem member85 : Member 85 := by
  unfold Member
  rw [node85]
  decide +kernel
private theorem node86 : DBMSourceTree.data (patchID 86)=DBMSourceTree.node4912 := rfl
private theorem member86 : Member 86 := by
  unfold Member
  rw [node86]
  decide +kernel
private theorem node87 : DBMSourceTree.data (patchID 87)=DBMSourceTree.node4913 := rfl
private theorem member87 : Member 87 := by
  unfold Member
  rw [node87]
  decide +kernel
private theorem node88 : DBMSourceTree.data (patchID 88)=DBMSourceTree.node4914 := rfl
private theorem member88 : Member 88 := by
  unfold Member
  rw [node88]
  decide +kernel
private theorem node89 : DBMSourceTree.data (patchID 89)=DBMSourceTree.node4915 := rfl
private theorem member89 : Member 89 := by
  unfold Member
  rw [node89]
  decide +kernel
private theorem node90 : DBMSourceTree.data (patchID 90)=DBMSourceTree.node4916 := rfl
private theorem member90 : Member 90 := by
  unfold Member
  rw [node90]
  decide +kernel
private theorem node91 : DBMSourceTree.data (patchID 91)=DBMSourceTree.node4917 := rfl
private theorem member91 : Member 91 := by
  unfold Member
  rw [node91]
  decide +kernel
private theorem node92 : DBMSourceTree.data (patchID 92)=DBMSourceTree.node4918 := rfl
private theorem member92 : Member 92 := by
  unfold Member
  rw [node92]
  decide +kernel
private theorem node93 : DBMSourceTree.data (patchID 93)=DBMSourceTree.node4932 := rfl
private theorem member93 : Member 93 := by
  unfold Member
  rw [node93]
  decide +kernel
private theorem node94 : DBMSourceTree.data (patchID 94)=DBMSourceTree.node4935 := rfl
private theorem member94 : Member 94 := by
  unfold Member
  rw [node94]
  decide +kernel
private theorem node95 : DBMSourceTree.data (patchID 95)=DBMSourceTree.node4955 := rfl
private theorem member95 : Member 95 := by
  unfold Member
  rw [node95]
  decide +kernel
private theorem node96 : DBMSourceTree.data (patchID 96)=DBMSourceTree.node4956 := rfl
private theorem member96 : Member 96 := by
  unfold Member
  rw [node96]
  decide +kernel
private theorem node97 : DBMSourceTree.data (patchID 97)=DBMSourceTree.node4957 := rfl
private theorem member97 : Member 97 := by
  unfold Member
  rw [node97]
  decide +kernel
private theorem node98 : DBMSourceTree.data (patchID 98)=DBMSourceTree.node4958 := rfl
private theorem member98 : Member 98 := by
  unfold Member
  rw [node98]
  decide +kernel
private theorem node99 : DBMSourceTree.data (patchID 99)=DBMSourceTree.node4959 := rfl
private theorem member99 : Member 99 := by
  unfold Member
  rw [node99]
  decide +kernel
private theorem node100 : DBMSourceTree.data (patchID 100)=DBMSourceTree.node4970 := rfl
private theorem member100 : Member 100 := by
  unfold Member
  rw [node100]
  decide +kernel
private theorem node101 : DBMSourceTree.data (patchID 101)=DBMSourceTree.node4972 := rfl
private theorem member101 : Member 101 := by
  unfold Member
  rw [node101]
  decide +kernel
private theorem node102 : DBMSourceTree.data (patchID 102)=DBMSourceTree.node4974 := rfl
private theorem member102 : Member 102 := by
  unfold Member
  rw [node102]
  decide +kernel
private theorem node103 : DBMSourceTree.data (patchID 103)=DBMSourceTree.node4980 := rfl
private theorem member103 : Member 103 := by
  unfold Member
  rw [node103]
  decide +kernel
private theorem node104 : DBMSourceTree.data (patchID 104)=DBMSourceTree.node4981 := rfl
private theorem member104 : Member 104 := by
  unfold Member
  rw [node104]
  decide +kernel
private theorem node105 : DBMSourceTree.data (patchID 105)=DBMSourceTree.node4983 := rfl
private theorem member105 : Member 105 := by
  unfold Member
  rw [node105]
  decide +kernel
private theorem node106 : DBMSourceTree.data (patchID 106)=DBMSourceTree.node4985 := rfl
private theorem member106 : Member 106 := by
  unfold Member
  rw [node106]
  decide +kernel
private theorem node107 : DBMSourceTree.data (patchID 107)=DBMSourceTree.node4988 := rfl
private theorem member107 : Member 107 := by
  unfold Member
  rw [node107]
  decide +kernel
private theorem node108 : DBMSourceTree.data (patchID 108)=DBMSourceTree.node4989 := rfl
private theorem member108 : Member 108 := by
  unfold Member
  rw [node108]
  decide +kernel
private theorem node109 : DBMSourceTree.data (patchID 109)=DBMSourceTree.node4993 := rfl
private theorem member109 : Member 109 := by
  unfold Member
  rw [node109]
  decide +kernel
private theorem node110 : DBMSourceTree.data (patchID 110)=DBMSourceTree.node4996 := rfl
private theorem member110 : Member 110 := by
  unfold Member
  rw [node110]
  decide +kernel
private theorem node111 : DBMSourceTree.data (patchID 111)=DBMSourceTree.node4997 := rfl
private theorem member111 : Member 111 := by
  unfold Member
  rw [node111]
  decide +kernel
private theorem node112 : DBMSourceTree.data (patchID 112)=DBMSourceTree.node4999 := rfl
private theorem member112 : Member 112 := by
  unfold Member
  rw [node112]
  decide +kernel
private theorem node113 : DBMSourceTree.data (patchID 113)=DBMSourceTree.node5001 := rfl
private theorem member113 : Member 113 := by
  unfold Member
  rw [node113]
  decide +kernel
private theorem node114 : DBMSourceTree.data (patchID 114)=DBMSourceTree.node5003 := rfl
private theorem member114 : Member 114 := by
  unfold Member
  rw [node114]
  decide +kernel
private theorem node115 : DBMSourceTree.data (patchID 115)=DBMSourceTree.node5005 := rfl
private theorem member115 : Member 115 := by
  unfold Member
  rw [node115]
  decide +kernel
private theorem node116 : DBMSourceTree.data (patchID 116)=DBMSourceTree.node5006 := rfl
private theorem member116 : Member 116 := by
  unfold Member
  rw [node116]
  decide +kernel
private theorem node117 : DBMSourceTree.data (patchID 117)=DBMSourceTree.node5008 := rfl
private theorem member117 : Member 117 := by
  unfold Member
  rw [node117]
  decide +kernel
private theorem node118 : DBMSourceTree.data (patchID 118)=DBMSourceTree.node5009 := rfl
private theorem member118 : Member 118 := by
  unfold Member
  rw [node118]
  decide +kernel
private theorem node119 : DBMSourceTree.data (patchID 119)=DBMSourceTree.node5010 := rfl
private theorem member119 : Member 119 := by
  unfold Member
  rw [node119]
  decide +kernel

theorem all_members (p : Fin 120) : Member p := by
  fin_cases p
  · exact member0
  · exact member1
  · exact member2
  · exact member3
  · exact member4
  · exact member5
  · exact member6
  · exact member7
  · exact member8
  · exact member9
  · exact member10
  · exact member11
  · exact member12
  · exact member13
  · exact member14
  · exact member15
  · exact member16
  · exact member17
  · exact member18
  · exact member19
  · exact member20
  · exact member21
  · exact member22
  · exact member23
  · exact member24
  · exact member25
  · exact member26
  · exact member27
  · exact member28
  · exact member29
  · exact member30
  · exact member31
  · exact member32
  · exact member33
  · exact member34
  · exact member35
  · exact member36
  · exact member37
  · exact member38
  · exact member39
  · exact member40
  · exact member41
  · exact member42
  · exact member43
  · exact member44
  · exact member45
  · exact member46
  · exact member47
  · exact member48
  · exact member49
  · exact member50
  · exact member51
  · exact member52
  · exact member53
  · exact member54
  · exact member55
  · exact member56
  · exact member57
  · exact member58
  · exact member59
  · exact member60
  · exact member61
  · exact member62
  · exact member63
  · exact member64
  · exact member65
  · exact member66
  · exact member67
  · exact member68
  · exact member69
  · exact member70
  · exact member71
  · exact member72
  · exact member73
  · exact member74
  · exact member75
  · exact member76
  · exact member77
  · exact member78
  · exact member79
  · exact member80
  · exact member81
  · exact member82
  · exact member83
  · exact member84
  · exact member85
  · exact member86
  · exact member87
  · exact member88
  · exact member89
  · exact member90
  · exact member91
  · exact member92
  · exact member93
  · exact member94
  · exact member95
  · exact member96
  · exact member97
  · exact member98
  · exact member99
  · exact member100
  · exact member101
  · exact member102
  · exact member103
  · exact member104
  · exact member105
  · exact member106
  · exact member107
  · exact member108
  · exact member109
  · exact member110
  · exact member111
  · exact member112
  · exact member113
  · exact member114
  · exact member115
  · exact member116
  · exact member117
  · exact member118
  · exact member119

theorem patchID_injective : Function.Injective patchID := by decide +kernel

private theorem xrow0 (i : Fin 9) : Contains (XBox 0 i) (xInput (UBox 0) i) := by
  fin_cases i
  · have hu : UBox 0 0=intv (-2160/4096 : ℚ) (-2128/4096) := rfl
    have hx : XBox 0 0=intv (-824158/1000000000 : ℚ) (4903574/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 0 1=intv (-2056/4096 : ℚ) (-2016/4096) := rfl
    have hx : XBox 0 1=intv (-7302626/1000000000 : ℚ) (-142961/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 0 2=intv (-2048/4096 : ℚ) (-2012/4096) := rfl
    have hx : XBox 0 2=intv (-4868794/1000000000 : ℚ) (1574907/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 0 3=intv (-1984/4096 : ℚ) (-1960/4096) := rfl
    have hx : XBox 0 3=intv (-607785/1000000000 : ℚ) (3688017/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 0 4=intv (-776/4096 : ℚ) (-736/4096) := rfl
    have hx : XBox 0 4=intv (-1744284/1000000000 : ℚ) (5415374/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 0 5=intv (-232/4096 : ℚ) (-192/4096) := rfl
    have hx : XBox 0 5=intv (-1209042/1000000000 : ℚ) (5950612/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · unfold Contains; decide +kernel
  · have hu : UBox 0 7=intv (180/4096 : ℚ) (216/4096) := rfl
    have hx : XBox 0 7=intv (-3086753/1000000000 : ℚ) (3356936/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 0 8=intv (720/4096 : ℚ) (752/4096) := rfl
    have hx : XBox 0 8=intv (-1119585/1000000000 : ℚ) (4608143/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
private theorem xrow1 (i : Fin 9) : Contains (XBox 1 i) (xInput (UBox 1) i) := by
  fin_cases i
  · have hu : UBox 1 0=intv (-2136/4096 : ℚ) (-2112/4096) := rfl
    have hx : XBox 1 0=intv (-3688017/1000000000 : ℚ) (607785/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 1 1=intv (-2092/4096 : ℚ) (-2056/4096) := rfl
    have hx : XBox 1 1=intv (-142978/1000000000 : ℚ) (6300723/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 1 2=intv (-2048/4096 : ℚ) (-2008/4096) := rfl
    have hx : XBox 1 2=intv (-5584758/1000000000 : ℚ) (1574907/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 1 3=intv (-1968/4096 : ℚ) (-1936/4096) := rfl
    have hx : XBox 1 3=intv (-4903574/1000000000 : ℚ) (824158/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 1 4=intv (-748/4096 : ℚ) (-720/4096) := rfl
    have hx : XBox 1 4=intv (-4608143/1000000000 : ℚ) (403620/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 1 5=intv (-200/4096 : ℚ) (-168/4096) := rfl
    have hx : XBox 1 5=intv (-5504831/1000000000 : ℚ) (222893/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · unfold Contains; decide +kernel
  · have hu : UBox 1 7=intv (192/4096 : ℚ) (224/4096) := rfl
    have hx : XBox 1 7=intv (-4518682/1000000000 : ℚ) (1209042/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 1 8=intv (748/4096 : ℚ) (776/4096) := rfl
    have hx : XBox 1 8=intv (-5415374/1000000000 : ℚ) (-403611/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
private theorem xrow2 (i : Fin 9) : Contains (XBox 2 i) (xInput (UBox 2) i) := by
  fin_cases i
  · have hu : UBox 2 0=intv (-2160/4096 : ℚ) (-2128/4096) := rfl
    have hx : XBox 2 0=intv (-824158/1000000000 : ℚ) (4903574/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 2 1=intv (-2056/4096 : ℚ) (-2024/4096) := rfl
    have hx : XBox 2 1=intv (-5870697/1000000000 : ℚ) (-142961/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 2 2=intv (-2048/4096 : ℚ) (-2000/4096) := rfl
    have hx : XBox 2 2=intv (-7016688/1000000000 : ℚ) (1574907/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 2 3=intv (-1984/4096 : ℚ) (-1960/4096) := rfl
    have hx : XBox 2 3=intv (-607785/1000000000 : ℚ) (3688017/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 2 4=intv (-776/4096 : ℚ) (-744/4096) := rfl
    have hx : XBox 2 4=intv (-312354/1000000000 : ℚ) (5415374/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 2 5=intv (-224/4096 : ℚ) (-192/4096) := rfl
    have hx : XBox 2 5=intv (-1209042/1000000000 : ℚ) (4518682/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · unfold Contains; decide +kernel
  · have hu : UBox 2 7=intv (176/4096 : ℚ) (216/4096) := rfl
    have hx : XBox 2 7=intv (-3086753/1000000000 : ℚ) (4072901/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 2 8=intv (720/4096 : ℚ) (752/4096) := rfl
    have hx : XBox 2 8=intv (-1119585/1000000000 : ℚ) (4608143/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
private theorem xrow3 (i : Fin 9) : Contains (XBox 3 i) (xInput (UBox 3) i) := by
  fin_cases i
  · have hu : UBox 3 0=intv (-2140/4096 : ℚ) (-2112/4096) := rfl
    have hx : XBox 3 0=intv (-3688017/1000000000 : ℚ) (1323750/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 3 1=intv (-2056/4096 : ℚ) (-2028/4096) := rfl
    have hx : XBox 3 1=intv (-5154732/1000000000 : ℚ) (-142961/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 3 2=intv (-2048/4096 : ℚ) (-2008/4096) := rfl
    have hx : XBox 3 2=intv (-5584758/1000000000 : ℚ) (1574907/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 3 3=intv (-1964/4096 : ℚ) (-1936/4096) := rfl
    have hx : XBox 3 3=intv (-4903574/1000000000 : ℚ) (108193/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 3 4=intv (-748/4096 : ℚ) (-720/4096) := rfl
    have hx : XBox 3 4=intv (-4608143/1000000000 : ℚ) (403620/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 3 5=intv (-212/4096 : ℚ) (-176/4096) := rfl
    have hx : XBox 3 5=intv (-4072901/1000000000 : ℚ) (2370788/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · unfold Contains; decide +kernel
  · have hu : UBox 3 7=intv (196/4096 : ℚ) (236/4096) := rfl
    have hx : XBox 3 7=intv (-6666577/1000000000 : ℚ) (493077/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 3 8=intv (740/4096 : ℚ) (776/4096) := rfl
    have hx : XBox 3 8=intv (-5415374/1000000000 : ℚ) (1028319/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
private theorem xrow4 (i : Fin 9) : Contains (XBox 4 i) (xInput (UBox 4) i) := by
  fin_cases i
  · have hu : UBox 4 0=intv (-2156/4096 : ℚ) (-2128/4096) := rfl
    have hx : XBox 4 0=intv (-824158/1000000000 : ℚ) (4187609/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 4 1=intv (-2056/4096 : ℚ) (-2024/4096) := rfl
    have hx : XBox 4 1=intv (-5870697/1000000000 : ℚ) (-142961/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 4 2=intv (-2048/4096 : ℚ) (-2004/4096) := rfl
    have hx : XBox 4 2=intv (-6300723/1000000000 : ℚ) (1574907/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 4 3=intv (-1984/4096 : ℚ) (-1960/4096) := rfl
    have hx : XBox 4 3=intv (-607785/1000000000 : ℚ) (3688017/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 4 4=intv (-776/4096 : ℚ) (-744/4096) := rfl
    have hx : XBox 4 4=intv (-312354/1000000000 : ℚ) (5415374/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 4 5=intv (-228/4096 : ℚ) (-196/4096) := rfl
    have hx : XBox 4 5=intv (-493077/1000000000 : ℚ) (5234647/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · unfold Contains; decide +kernel
  · have hu : UBox 4 7=intv (172/4096 : ℚ) (200/4096) := rfl
    have hx : XBox 4 7=intv (-222893/1000000000 : ℚ) (4788866/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 4 8=intv (720/4096 : ℚ) (748/4096) := rfl
    have hx : XBox 4 8=intv (-403620/1000000000 : ℚ) (4608143/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
private theorem xrow5 (i : Fin 9) : Contains (XBox 5 i) (xInput (UBox 5) i) := by
  fin_cases i
  · have hu : UBox 5 0=intv (-2136/4096 : ℚ) (-2112/4096) := rfl
    have hx : XBox 5 0=intv (-3688017/1000000000 : ℚ) (607785/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 5 1=intv (-2096/4096 : ℚ) (-2012/4096) := rfl
    have hx : XBox 5 1=intv (-8018591/1000000000 : ℚ) (7016688/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 5 2=intv (-2048/4096 : ℚ) (-2012/4096) := rfl
    have hx : XBox 5 2=intv (-4868794/1000000000 : ℚ) (1574907/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 5 3=intv (-1968/4096 : ℚ) (-1936/4096) := rfl
    have hx : XBox 5 3=intv (-4903574/1000000000 : ℚ) (824158/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 5 4=intv (-752/4096 : ℚ) (-720/4096) := rfl
    have hx : XBox 5 4=intv (-4608143/1000000000 : ℚ) (1119585/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 5 5=intv (-208/4096 : ℚ) (-172/4096) := rfl
    have hx : XBox 5 5=intv (-4788866/1000000000 : ℚ) (1654823/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · unfold Contains; decide +kernel
  · have hu : UBox 5 7=intv (192/4096 : ℚ) (224/4096) := rfl
    have hx : XBox 5 7=intv (-4518682/1000000000 : ℚ) (1209042/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 5 8=intv (744/4096 : ℚ) (772/4096) := rfl
    have hx : XBox 5 8=intv (-4699409/1000000000 : ℚ) (312354/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
private theorem xrow6 (i : Fin 9) : Contains (XBox 6 i) (xInput (UBox 6) i) := by
  fin_cases i
  · have hu : UBox 6 0=intv (-2160/4096 : ℚ) (-2128/4096) := rfl
    have hx : XBox 6 0=intv (-824158/1000000000 : ℚ) (4903574/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 6 1=intv (-2056/4096 : ℚ) (-2024/4096) := rfl
    have hx : XBox 6 1=intv (-5870697/1000000000 : ℚ) (-142961/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 6 2=intv (-2048/4096 : ℚ) (-2004/4096) := rfl
    have hx : XBox 6 2=intv (-6300723/1000000000 : ℚ) (1574907/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 6 3=intv (-1984/4096 : ℚ) (-1960/4096) := rfl
    have hx : XBox 6 3=intv (-607785/1000000000 : ℚ) (3688017/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 6 4=intv (-776/4096 : ℚ) (-744/4096) := rfl
    have hx : XBox 6 4=intv (-312354/1000000000 : ℚ) (5415374/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 6 5=intv (-224/4096 : ℚ) (-192/4096) := rfl
    have hx : XBox 6 5=intv (-1209042/1000000000 : ℚ) (4518682/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · unfold Contains; decide +kernel
  · have hu : UBox 6 7=intv (172/4096 : ℚ) (200/4096) := rfl
    have hx : XBox 6 7=intv (-222893/1000000000 : ℚ) (4788866/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 6 8=intv (720/4096 : ℚ) (748/4096) := rfl
    have hx : XBox 6 8=intv (-403620/1000000000 : ℚ) (4608143/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
private theorem xrow7 (i : Fin 9) : Contains (XBox 7 i) (xInput (UBox 7) i) := by
  fin_cases i
  · have hu : UBox 7 0=intv (-2156/4096 : ℚ) (-2128/4096) := rfl
    have hx : XBox 7 0=intv (-824158/1000000000 : ℚ) (4187609/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 7 1=intv (-2056/4096 : ℚ) (-2024/4096) := rfl
    have hx : XBox 7 1=intv (-5870697/1000000000 : ℚ) (-142961/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 7 2=intv (-2048/4096 : ℚ) (-2000/4096) := rfl
    have hx : XBox 7 2=intv (-7016688/1000000000 : ℚ) (1574907/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 7 3=intv (-1984/4096 : ℚ) (-1960/4096) := rfl
    have hx : XBox 7 3=intv (-607785/1000000000 : ℚ) (3688017/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 7 4=intv (-772/4096 : ℚ) (-744/4096) := rfl
    have hx : XBox 7 4=intv (-312354/1000000000 : ℚ) (4699409/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 7 5=intv (-228/4096 : ℚ) (-192/4096) := rfl
    have hx : XBox 7 5=intv (-1209042/1000000000 : ℚ) (5234647/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · unfold Contains; decide +kernel
  · have hu : UBox 7 7=intv (172/4096 : ℚ) (200/4096) := rfl
    have hx : XBox 7 7=intv (-222893/1000000000 : ℚ) (4788866/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 7 8=intv (724/4096 : ℚ) (752/4096) := rfl
    have hx : XBox 7 8=intv (-1119585/1000000000 : ℚ) (3892178/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
private theorem xrow8 (i : Fin 9) : Contains (XBox 8 i) (xInput (UBox 8) i) := by
  fin_cases i
  · have hu : UBox 8 0=intv (-2160/4096 : ℚ) (-2120/4096) := rfl
    have hx : XBox 8 0=intv (-2256088/1000000000 : ℚ) (4903574/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 8 1=intv (-2112/4096 : ℚ) (-2056/4096) := rfl
    have hx : XBox 8 1=intv (-142978/1000000000 : ℚ) (9880548/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 8 2=intv (-2048/4096 : ℚ) (-2024/4096) := rfl
    have hx : XBox 8 2=intv (-2720899/1000000000 : ℚ) (1574907/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 8 3=intv (-1984/4096 : ℚ) (-1952/4096) := rfl
    have hx : XBox 8 3=intv (-2039715/1000000000 : ℚ) (3688017/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 8 4=intv (-768/4096 : ℚ) (-728/4096) := rfl
    have hx : XBox 8 4=intv (-3176214/1000000000 : ℚ) (3983444/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 8 5=intv (-224/4096 : ℚ) (-184/4096) := rfl
    have hx : XBox 8 5=intv (-2640971/1000000000 : ℚ) (4518682/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · unfold Contains; decide +kernel
  · have hu : UBox 8 7=intv (176/4096 : ℚ) (216/4096) := rfl
    have hx : XBox 8 7=intv (-3086753/1000000000 : ℚ) (4072901/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 8 8=intv (736/4096 : ℚ) (760/4096) := rfl
    have hx : XBox 8 8=intv (-2551514/1000000000 : ℚ) (1744284/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
private theorem xrow9 (i : Fin 9) : Contains (XBox 9 i) (xInput (UBox 9) i) := by
  fin_cases i
  · have hu : UBox 9 0=intv (-2136/4096 : ℚ) (-2112/4096) := rfl
    have hx : XBox 9 0=intv (-3688017/1000000000 : ℚ) (607785/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 9 1=intv (-2092/4096 : ℚ) (-2028/4096) := rfl
    have hx : XBox 9 1=intv (-5154732/1000000000 : ℚ) (6300723/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 9 2=intv (-2048/4096 : ℚ) (-2008/4096) := rfl
    have hx : XBox 9 2=intv (-5584758/1000000000 : ℚ) (1574907/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 9 3=intv (-1968/4096 : ℚ) (-1936/4096) := rfl
    have hx : XBox 9 3=intv (-4903574/1000000000 : ℚ) (824158/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 9 4=intv (-752/4096 : ℚ) (-720/4096) := rfl
    have hx : XBox 9 4=intv (-4608143/1000000000 : ℚ) (1119585/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 9 5=intv (-216/4096 : ℚ) (-176/4096) := rfl
    have hx : XBox 9 5=intv (-4072901/1000000000 : ℚ) (3086753/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · unfold Contains; decide +kernel
  · have hu : UBox 9 7=intv (192/4096 : ℚ) (230/4096) := rfl
    have hx : XBox 9 7=intv (-5592630/1000000000 : ℚ) (1209042/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 9 8=intv (744/4096 : ℚ) (776/4096) := rfl
    have hx : XBox 9 8=intv (-5415374/1000000000 : ℚ) (312354/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
private theorem xrow10 (i : Fin 9) : Contains (XBox 10 i) (xInput (UBox 10) i) := by
  fin_cases i
  · have hu : UBox 10 0=intv (-2136/4096 : ℚ) (-2112/4096) := rfl
    have hx : XBox 10 0=intv (-3688017/1000000000 : ℚ) (607785/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 10 1=intv (-2080/4096 : ℚ) (-2056/4096) := rfl
    have hx : XBox 10 1=intv (-142978/1000000000 : ℚ) (4152829/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 10 2=intv (-2048/4096 : ℚ) (-2008/4096) := rfl
    have hx : XBox 10 2=intv (-5584758/1000000000 : ℚ) (1574907/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 10 3=intv (-1968/4096 : ℚ) (-1936/4096) := rfl
    have hx : XBox 10 3=intv (-4903574/1000000000 : ℚ) (824158/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 10 4=intv (-752/4096 : ℚ) (-720/4096) := rfl
    have hx : XBox 10 4=intv (-4608143/1000000000 : ℚ) (1119585/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 10 5=intv (-200/4096 : ℚ) (-164/4096) := rfl
    have hx : XBox 10 5=intv (-6220796/1000000000 : ℚ) (222893/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · unfold Contains; decide +kernel
  · have hu : UBox 10 7=intv (192/4096 : ℚ) (232/4096) := rfl
    have hx : XBox 10 7=intv (-5950612/1000000000 : ℚ) (1209042/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 10 8=intv (744/4096 : ℚ) (776/4096) := rfl
    have hx : XBox 10 8=intv (-5415374/1000000000 : ℚ) (312354/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
private theorem xrow11 (i : Fin 9) : Contains (XBox 11 i) (xInput (UBox 11) i) := by
  fin_cases i
  · have hu : UBox 11 0=intv (-2140/4096 : ℚ) (-2112/4096) := rfl
    have hx : XBox 11 0=intv (-3688017/1000000000 : ℚ) (1323750/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 11 1=intv (-2084/4096 : ℚ) (-2028/4096) := rfl
    have hx : XBox 11 1=intv (-5154732/1000000000 : ℚ) (4868794/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 11 2=intv (-2048/4096 : ℚ) (-2012/4096) := rfl
    have hx : XBox 11 2=intv (-4868794/1000000000 : ℚ) (1574907/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 11 3=intv (-1972/4096 : ℚ) (-1936/4096) := rfl
    have hx : XBox 11 3=intv (-4903574/1000000000 : ℚ) (1540123/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 11 4=intv (-752/4096 : ℚ) (-720/4096) := rfl
    have hx : XBox 11 4=intv (-4608143/1000000000 : ℚ) (1119585/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 11 5=intv (-220/4096 : ℚ) (-176/4096) := rfl
    have hx : XBox 11 5=intv (-4072901/1000000000 : ℚ) (3802717/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · unfold Contains; decide +kernel
  · have hu : UBox 11 7=intv (192/4096 : ℚ) (240/4096) := rfl
    have hx : XBox 11 7=intv (-7382542/1000000000 : ℚ) (1209042/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 11 8=intv (736/4096 : ℚ) (772/4096) := rfl
    have hx : XBox 11 8=intv (-4699409/1000000000 : ℚ) (1744284/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
private theorem xrow12 (i : Fin 9) : Contains (XBox 12 i) (xInput (UBox 12) i) := by
  fin_cases i
  · have hu : UBox 12 0=intv (-2152/4096 : ℚ) (-2112/4096) := rfl
    have hx : XBox 12 0=intv (-3688017/1000000000 : ℚ) (3471644/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 12 1=intv (-2080/4096 : ℚ) (-2032/4096) := rfl
    have hx : XBox 12 1=intv (-4438767/1000000000 : ℚ) (4152829/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 12 2=intv (-2048/4096 : ℚ) (-1988/4096) := rfl
    have hx : XBox 12 2=intv (-9164583/1000000000 : ℚ) (1574907/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 12 3=intv (-1980/4096 : ℚ) (-1940/4096) := rfl
    have hx : XBox 12 3=intv (-4187609/1000000000 : ℚ) (2972052/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 12 4=intv (-764/4096 : ℚ) (-724/4096) := rfl
    have hx : XBox 12 4=intv (-3892178/1000000000 : ℚ) (3267479/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 12 5=intv (-220/4096 : ℚ) (-176/4096) := rfl
    have hx : XBox 12 5=intv (-4072901/1000000000 : ℚ) (3802717/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · unfold Contains; decide +kernel
  · have hu : UBox 12 7=intv (176/4096 : ℚ) (220/4096) := rfl
    have hx : XBox 12 7=intv (-3802717/1000000000 : ℚ) (4072901/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 12 8=intv (724/4096 : ℚ) (764/4096) := rfl
    have hx : XBox 12 8=intv (-3267479/1000000000 : ℚ) (3892178/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
private theorem xrow13 (i : Fin 9) : Contains (XBox 13 i) (xInput (UBox 13) i) := by
  fin_cases i
  · have hu : UBox 13 0=intv (-2152/4096 : ℚ) (-2112/4096) := rfl
    have hx : XBox 13 0=intv (-3688017/1000000000 : ℚ) (3471644/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 13 1=intv (-2096/4096 : ℚ) (-2016/4096) := rfl
    have hx : XBox 13 1=intv (-7302626/1000000000 : ℚ) (7016688/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 13 2=intv (-2048/4096 : ℚ) (-2016/4096) := rfl
    have hx : XBox 13 2=intv (-4152829/1000000000 : ℚ) (1574907/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 13 3=intv (-1984/4096 : ℚ) (-1936/4096) := rfl
    have hx : XBox 13 3=intv (-4903574/1000000000 : ℚ) (3688017/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 13 4=intv (-760/4096 : ℚ) (-720/4096) := rfl
    have hx : XBox 13 4=intv (-4608143/1000000000 : ℚ) (2551514/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 13 5=intv (-224/4096 : ℚ) (-172/4096) := rfl
    have hx : XBox 13 5=intv (-4788866/1000000000 : ℚ) (4518682/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · unfold Contains; decide +kernel
  · have hu : UBox 13 7=intv (184/4096 : ℚ) (232/4096) := rfl
    have hx : XBox 13 7=intv (-5950612/1000000000 : ℚ) (2640971/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 13 8=intv (736/4096 : ℚ) (768/4096) := rfl
    have hx : XBox 13 8=intv (-3983444/1000000000 : ℚ) (1744284/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
private theorem xrow14 (i : Fin 9) : Contains (XBox 14 i) (xInput (UBox 14) i) := by
  fin_cases i
  · have hu : UBox 14 0=intv (-2160/4096 : ℚ) (-2112/4096) := rfl
    have hx : XBox 14 0=intv (-3688017/1000000000 : ℚ) (4903574/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 14 1=intv (-2084/4096 : ℚ) (-2032/4096) := rfl
    have hx : XBox 14 1=intv (-4438767/1000000000 : ℚ) (4868794/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 14 2=intv (-2048/4096 : ℚ) (-2014/4096) := rfl
    have hx : XBox 14 2=intv (-4510811/1000000000 : ℚ) (1574907/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 14 3=intv (-1984/4096 : ℚ) (-1942/4096) := rfl
    have hx : XBox 14 3=intv (-3829627/1000000000 : ℚ) (3688017/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 14 4=intv (-776/4096 : ℚ) (-726/4096) := rfl
    have hx : XBox 14 4=intv (-3534196/1000000000 : ℚ) (5415374/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 14 5=intv (-232/4096 : ℚ) (-176/4096) := rfl
    have hx : XBox 14 5=intv (-4072901/1000000000 : ℚ) (5950612/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · unfold Contains; decide +kernel
  · have hu : UBox 14 7=intv (168/4096 : ℚ) (218/4096) := rfl
    have hx : XBox 14 7=intv (-3444735/1000000000 : ℚ) (5504831/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 14 8=intv (720/4096 : ℚ) (770/4096) := rfl
    have hx : XBox 14 8=intv (-4341427/1000000000 : ℚ) (4608143/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
private theorem xrow15 (i : Fin 9) : Contains (XBox 15 i) (xInput (UBox 15) i) := by
  fin_cases i
  · have hu : UBox 15 0=intv (-2152/4096 : ℚ) (-2120/4096) := rfl
    have hx : XBox 15 0=intv (-2256088/1000000000 : ℚ) (3471644/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 15 1=intv (-2104/4096 : ℚ) (-2024/4096) := rfl
    have hx : XBox 15 1=intv (-5870697/1000000000 : ℚ) (8448618/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 15 2=intv (-2048/4096 : ℚ) (-2000/4096) := rfl
    have hx : XBox 15 2=intv (-7016688/1000000000 : ℚ) (1574907/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 15 3=intv (-1984/4096 : ℚ) (-1952/4096) := rfl
    have hx : XBox 15 3=intv (-2039715/1000000000 : ℚ) (3688017/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 15 4=intv (-760/4096 : ℚ) (-736/4096) := rfl
    have hx : XBox 15 4=intv (-1744284/1000000000 : ℚ) (2551514/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 15 5=intv (-224/4096 : ℚ) (-184/4096) := rfl
    have hx : XBox 15 5=intv (-2640971/1000000000 : ℚ) (4518682/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · unfold Contains; decide +kernel
  · have hu : UBox 15 7=intv (176/4096 : ℚ) (216/4096) := rfl
    have hx : XBox 15 7=intv (-3086753/1000000000 : ℚ) (4072901/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]
  · have hu : UBox 15 8=intv (728/4096 : ℚ) (760/4096) := rfl
    have hx : XBox 15 8=intv (-2551514/1000000000 : ℚ) (3176214/1000000000) := rfl
    simp only [xInput,deltaI,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val,Fin.reduceFinMk,hu,hx]
    norm_num [Contains,Fin.ext_iff,LI,DI,PI,piI,piLo,piHi,Patch120K5.Lq,
      Patch120K5.LQ,RatInterval.sub,RatInterval.mul,RatInterval.add,
      RatInterval.neg,ofRat,intv,ndBox,
      ndBoxLo_0,ndBoxLo_1,ndBoxLo_2,ndBoxLo_3,
      ndBoxHi_0,ndBoxHi_1,ndBoxHi_2,ndBoxHi_3]

theorem X_contains (g : Fin 16) (i : Fin 9) : Contains (XBox g i) (xInput (UBox g) i) := by
  fin_cases g
  · exact xrow0 i
  · exact xrow1 i
  · exact xrow2 i
  · exact xrow3 i
  · exact xrow4 i
  · exact xrow5 i
  · exact xrow6 i
  · exact xrow7 i
  · exact xrow8 i
  · exact xrow9 i
  · exact xrow10 i
  · exact xrow11 i
  · exact xrow12 i
  · exact xrow13 i
  · exact xrow14 i
  · exact xrow15 i
private theorem norm0 : (∑ i : Fin 9,(XBox 0 i).abs.hi^2)≤(729/50000 : ℚ)^2 := by
  decide +kernel
private theorem norm1 : (∑ i : Fin 9,(XBox 1 i).abs.hi^2)≤(729/50000 : ℚ)^2 := by
  decide +kernel
private theorem norm2 : (∑ i : Fin 9,(XBox 2 i).abs.hi^2)≤(729/50000 : ℚ)^2 := by
  decide +kernel
private theorem norm3 : (∑ i : Fin 9,(XBox 3 i).abs.hi^2)≤(729/50000 : ℚ)^2 := by
  decide +kernel
private theorem norm4 : (∑ i : Fin 9,(XBox 4 i).abs.hi^2)≤(729/50000 : ℚ)^2 := by
  decide +kernel
private theorem norm5 : (∑ i : Fin 9,(XBox 5 i).abs.hi^2)≤(729/50000 : ℚ)^2 := by
  decide +kernel
private theorem norm6 : (∑ i : Fin 9,(XBox 6 i).abs.hi^2)≤(729/50000 : ℚ)^2 := by
  decide +kernel
private theorem norm7 : (∑ i : Fin 9,(XBox 7 i).abs.hi^2)≤(729/50000 : ℚ)^2 := by
  decide +kernel
private theorem norm8 : (∑ i : Fin 9,(XBox 8 i).abs.hi^2)≤(729/50000 : ℚ)^2 := by
  decide +kernel
private theorem norm9 : (∑ i : Fin 9,(XBox 9 i).abs.hi^2)≤(729/50000 : ℚ)^2 := by
  decide +kernel
private theorem norm10 : (∑ i : Fin 9,(XBox 10 i).abs.hi^2)≤(729/50000 : ℚ)^2 := by
  decide +kernel
private theorem norm11 : (∑ i : Fin 9,(XBox 11 i).abs.hi^2)≤(729/50000 : ℚ)^2 := by
  decide +kernel
private theorem norm12 : (∑ i : Fin 9,(XBox 12 i).abs.hi^2)≤(729/50000 : ℚ)^2 := by
  decide +kernel
private theorem norm13 : (∑ i : Fin 9,(XBox 13 i).abs.hi^2)≤(729/50000 : ℚ)^2 := by
  decide +kernel
private theorem norm14 : (∑ i : Fin 9,(XBox 14 i).abs.hi^2)≤(729/50000 : ℚ)^2 := by
  decide +kernel
private theorem norm15 : (∑ i : Fin 9,(XBox 15 i).abs.hi^2)≤(729/50000 : ℚ)^2 := by
  decide +kernel

theorem all_norms (g : Fin 16) : (∑ i : Fin 9,(XBox g i).abs.hi^2)≤(729/50000 : ℚ)^2 := by
  fin_cases g
  · exact norm0
  · exact norm1
  · exact norm2
  · exact norm3
  · exact norm4
  · exact norm5
  · exact norm6
  · exact norm7
  · exact norm8
  · exact norm9
  · exact norm10
  · exact norm11
  · exact norm12
  · exact norm13
  · exact norm14
  · exact norm15

theorem UBox_mem (p : Fin 120) (y : Fin 9 → ℝ)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 (patchID p))
      (FlashLeafSplit.tlift y)) (i : Fin 9) (hi : i≠6) :
    (UBox (group p) i).Mem
      (FlashLeafSplit.tlift y (Patch120K5.f9 i)-FlashLeafSplit.tlift y 6) := by
  have h := (all_members p).2 i hi
  have hL := hc (Patch120K5.f9 i) 6
  have hH := hc 6 (Patch120K5.f9 i)
  simp only [DBMTreeKernel.matrix] at hL hH
  have hl : (UL (group p) i : ℝ)≤
      -(DBMSourceTree.data (patchID p)).db (Patch120K5.f9 i) 6 := by exact_mod_cast h.1
  have hh : ((DBMSourceTree.data (patchID p)).db 6 (Patch120K5.f9 i) : ℝ)≤
      (UH (group p) i : ℝ) := by exact_mod_cast h.2
  simp only [UBox,intv,mem_iff,Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat]
  constructor <;> linarith

/-- ALL120 cells have genuine SAME pinned displacement norm in original ball. -/
theorem actual_norm (p : Fin 120) (y : Fin 9 → ℝ)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 (patchID p))
      (FlashLeafSplit.tlift y)) :
    Real.sqrt (∑ j : Fin 9,displacement y j^2)≤(729/50000 : ℝ) := by
  have hmem (i : Fin 9) : (XBox (group p) i).Mem (displacement y i) :=
    mem_of_contains (X_contains (group p) i)
      (xInput_mem (UBox (group p)) y (UBox_mem p y hc) i)
  have h := FlashLocal.sum_sq_le_of_boxes_of_bound (displacement y) (XBox (group p))
    hmem (all_norms (group p))
  rw [Real.sqrt_le_left (by norm_num : (0 : ℝ)≤729/50000)]
  simpa only [Rat.cast_div,Rat.cast_ofNat] using h

theorem actual_gain (p : Fin 120) (y : Fin 9 → ℝ)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 (patchID p))
      (FlashLeafSplit.tlift y)) :
    (∑ j : Fin 9,displacement y j^2)/100000≤
      ResumeNetwork.V2 (chartAnchors y)-SourceExactRoot.sourceRadius^2 :=
  chart_gain_of_norm y (actual_norm p y hc)

/-- Actual all120 cell->radius consumers, ALL51 primal witnesses retained. -/
theorem actual_radius (p : Fin 120) (y : Fin 9 → ℝ)
    (hc : FlashLeafSplit.Cell (DBMTreeKernel.matrix DBMSourceTree.data 4096 (patchID p))
      (FlashLeafSplit.tlift y)) (C Z : Fin 11 → Point) (r : ℝ)
    (hf : ResumeNetwork.Feasible (chartAnchors y) C Z r) :
    SourceExactRoot.sourceRadius≤r :=
  chart_radius_of_norm y (actual_norm p y hc) C Z r hf

end
end N11Formalization.Patch120DomainPacket
#check @N11Formalization.Patch120DomainPacket.all_members
#check @N11Formalization.Patch120DomainPacket.patchID_injective
#check @N11Formalization.Patch120DomainPacket.X_contains
#check @N11Formalization.Patch120DomainPacket.all_norms
#check @N11Formalization.Patch120DomainPacket.actual_norm
#check @N11Formalization.Patch120DomainPacket.actual_gain
#check @N11Formalization.Patch120DomainPacket.actual_radius
#print axioms N11Formalization.Patch120DomainPacket.actual_radius
