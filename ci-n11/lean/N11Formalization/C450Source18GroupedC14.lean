import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/16),((-1:ℚ)/8),((780924769:ℚ)/1250000000),((6530254293:ℚ)/10000000000),((-9350762879:ℚ)/99200000000),((-100924769:ℚ)/6437500000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6058364437:ℚ)/10000000000),((5300173791601799797948242340417921552957263879292394671:ℚ)/77532662200927734375000000000000000000000000000000000000),((-73305234973200609503017:ℚ)/1444000000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((6486106947:ℚ)/10000000000),((1692249229:ℚ)/2500000000),((-2516747687:ℚ)/25750000000),((-1046106947:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((2741276807:ℚ)/5000000000),((828719620983757932281634506574600771810476331616504013887:ℚ)/12253242431250000000000000000000000000000000000000000000000),((-5227066799009179116761473:ℚ)/92416000000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((840591139:ℚ)/1250000000),((6888335403:ℚ)/10000000000),((-10425006209:ℚ)/106800000000),((-160591139:ℚ)/6793750000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((605826693:ℚ)/1250000000),((17435889948759033723362103316662007162631228419689548779:ℚ)/261631461563873291015625000000000000000000000000000000000),((-90050196408944023277137:ℚ)/1444000000000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((6844010573:ℚ)/10000000000),((280306141:ℚ)/400000000),((-431318423:ℚ)/4348000000),((-200572939:ℚ)/7900000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((112453663:ℚ)/250000000),((65960864448852132154264090732835623804613726707479827:ℚ)/993745166015625000000000000000000000000000000000000000),((-6031521880914469399770913:ℚ)/92416000000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((1392654731:ℚ)/2000000000),((285078093:ℚ)/400000000),((-445634279:ℚ)/4424000000),((-101551577:ℚ)/3750000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4122535277:ℚ)/10000000000),((10089343807028547173861417367388932671757394207701223:ℚ)/152564048767089843750000000000000000000000000000000000),((-251999670272548228716017:ℚ)/3696640000000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((7082519299:ℚ)/10000000000),((224581087:ℚ)/312500000),((-353743261:ℚ)/3515625000),((-1642519299:ℚ)/56725000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1855756031:ℚ)/5000000000),((843543994926841181123755299508909427072859874787508737:ℚ)/12833823239868164062500000000000000000000000000000000000),((-6568624225181749312592897:ℚ)/92416000000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((446383491:ℚ)/625000000),((1811558193:ℚ)/2500000000),((-2874674579:ℚ)/28362500000),((-106383491:ℚ)/3575000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((697768491:ℚ)/2000000000),((21261078718994224515309066806300693627275816344372558277:ℚ)/323975863427734375000000000000000000000000000000000000000),((-26183601649045975358857:ℚ)/361000000000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((3600874189:ℚ)/5000000000),((230171743:ℚ)/312500000),((-370515229:ℚ)/3575000000),((-880874189:ℚ)/29075000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((3251636129:ℚ)/10000000000),((721689670105127756932806149231928670190884364365930358089:ℚ)/10983613174853515625000000000000000000000000000000000000000),((-1709355291588453890595937:ℚ)/23104000000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((7320961713:ℚ)/10000000000),((7484742183:ℚ)/10000000000),((-12214226549:ℚ)/116300000000),((-9548029:ℚ)/300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((54363563:ℚ)/200000000),((59532743012719925787759623922906926898129803205983:ℚ)/908593750000000000000000000000000000000000000000000),((-7106384349223065924336793:ℚ)/92416000000000000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((7440160067:ℚ)/10000000000),((1544637667:ℚ)/2000000000),((-2585913001:ℚ)/23640000000),((-2000160067:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1027270841:ℚ)/5000000000),((9180565277929500864318649978890422340689346761374396402773:ℚ)/139735178125000000000000000000000000000000000000000000000000),((-7375515417246586001538433:ℚ)/92416000000000000000000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((1535702931:ℚ)/2000000000),((1024989161:ℚ)/1250000000),((-1794967483:ℚ)/15250000000),((-447702931:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((9138028029847792607287713561588162119608351795925645471:ℚ)/138316377600000000000000000000000000000000000000000000000),((-5357843:ℚ)/64000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((8155072753:ℚ)/10000000000),((10105167879:ℚ)/10000000000),((-20075503637:ℚ)/129600000000),((-2715072753:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((8966765001634588563250833008409761406680657560357043877611:ℚ)/129600000000000000000000000000000000000000000000000000000000),((-5357843:ℚ)/64000000)⟩
theorem valid11 : Valid source18 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((2011963927:ℚ)/2000000000),((1738915737:ℚ)/1250000000),((-3936747211:ℚ)/20000000000),((-923963927:ℚ)/22080000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1935305412163356621275333299739735619924443957648188207:ℚ)/25229491200000000000000000000000000000000000000000000000),((-5357843:ℚ)/64000000)⟩
theorem valid12 : Valid source18 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source18 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2269:ℚ)/3200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source18 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source18 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC14
#check @N11Formalization.C450Source18GroupedC14.bound
#print axioms N11Formalization.C450Source18GroupedC14.valid0
#print axioms N11Formalization.C450Source18GroupedC14.valid1
#print axioms N11Formalization.C450Source18GroupedC14.valid2
#print axioms N11Formalization.C450Source18GroupedC14.valid3
#print axioms N11Formalization.C450Source18GroupedC14.valid4
#print axioms N11Formalization.C450Source18GroupedC14.valid5
#print axioms N11Formalization.C450Source18GroupedC14.valid6
#print axioms N11Formalization.C450Source18GroupedC14.valid7
#print axioms N11Formalization.C450Source18GroupedC14.valid8
#print axioms N11Formalization.C450Source18GroupedC14.valid9
#print axioms N11Formalization.C450Source18GroupedC14.valid10
#print axioms N11Formalization.C450Source18GroupedC14.valid11
#print axioms N11Formalization.C450Source18GroupedC14.valid12
#print axioms N11Formalization.C450Source18GroupedC14.bound
#print axioms N11Formalization.C450Source18GroupedC14.endpoint_checks
