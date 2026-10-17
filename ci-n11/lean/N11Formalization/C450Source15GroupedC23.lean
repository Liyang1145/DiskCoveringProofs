import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC23
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((3:ℚ)/8),((7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/8),((7:ℚ)/16),((1483629141:ℚ)/2500000000),((6462570881:ℚ)/10000000000),((5490887423:ℚ)/13350000000),((1748322457:ℚ)/3200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((337379569:ℚ)/500000000),((1239501176897025007723961:ℚ)/89111250000000000000000000),((-3202690387633094391193526157:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((6410978513:ℚ)/10000000000),((6700671199:ℚ)/10000000000),((23392935539:ℚ)/55300000000),((18621566131:ℚ)/35600000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1133874417:ℚ)/2000000000),((160111916815450434860897651029823263:ℚ)/15290450000000000000000000000000000000),((-3273898995401135876051967437:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/8),((7:ℚ)/16),((3324566913:ℚ)/5000000000),((1363941219:ℚ)/2000000000),((12053700739:ℚ)/28125000000),((1619941219:ℚ)/3160000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1263989691:ℚ)/2500000000),((35525085507440819471290647719997781:ℚ)/3955078125000000000000000000000000000),((-132378371841069385553608757:ℚ)/591462400000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/8),((7:ℚ)/16),((26438261:ℚ)/39062500),((1387746299:ℚ)/2000000000),((95564783:ℚ)/223437500),((3835408031:ℚ)/7500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2361196017:ℚ)/5000000000),((70355733726287678431963639704983:ℚ)/7987890625000000000000000000000000),((-133064029183488437428420037:ℚ)/591462400000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((1721811359:ℚ)/2500000000),((1411549573:ℚ)/2000000000),((6205434077:ℚ)/14537500000),((11672847011:ℚ)/22880000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1091370639:ℚ)/2500000000),((4571587797670779199708990120599173:ℚ)/528347265625000000000000000000000000),((-133748760721709040186955973:ℚ)/591462400000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/8),((7:ℚ)/16),((3503143099:ℚ)/5000000000),((7117252803:ℚ)/10000000000),((12589429297:ℚ)/29312500000),((58780769621:ℚ)/116300000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1989461007:ℚ)/5000000000),((17221587141134232292798138687262629:ℚ)/2148056640625000000000000000000000000),((-3361463847082709940689487733:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((883225379:ℚ)/1250000000),((1435351129:ℚ)/2000000000),((3169676137:ℚ)/7387500000),((1691351129:ℚ)/3350000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1885845861:ℚ)/5000000000),((1086107237489901439982565619668689:ℚ)/136437890625000000000000000000000000),((-134800328702130544067465917:ℚ)/591462400000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/8),((7:ℚ)/16),((7125317579:ℚ)/10000000000),((3618128221:ℚ)/5000000000),((25535952737:ℚ)/59575000000),((29806897547:ℚ)/59100000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((3553011007:ℚ)/10000000000),((140329178681570921944176940810985587:ℚ)/17745903125000000000000000000000000000),((-844636712249780962021563317:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((1796207473:ℚ)/2500000000),((3647877621:ℚ)/5000000000),((6428622419:ℚ)/15012500000),((30015143347:ℚ)/59575000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((830153481:ℚ)/2500000000),((2214004482535613440700950241310883:ℚ)/281718945312500000000000000000000000),((-44566838810924177023427943:ℚ)/194560000000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/8),((7:ℚ)/16),((3622170013:ℚ)/5000000000),((3707373521:ℚ)/5000000000),((12946510039:ℚ)/30500000000),((30431614647:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3071383681:ℚ)/10000000000),((38569718444445846775769920536616803:ℚ)/4651250000000000000000000000000000000),((-848733944646428572024249517:ℚ)/3696640000000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((7363353959:ℚ)/10000000000),((7533731403:ℚ)/10000000000),((444916303:ℚ)/1050000000),((61696119821:ℚ)/122000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((15637641:ℚ)/62500000),((22613427129646034067349453841543:ℚ)/2756250000000000000000000000000000),((-3411962228194161559774096933:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((7482359771:ℚ)/10000000000),((1530541733:ℚ)/2000000000),((26607079313:ℚ)/62900000000),((595513911:ℚ)/1180000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((110110301:ℚ)/625000000),((5026674848356227861800268368898399:ℚ)/618189062500000000000000000000000000),((-2375055337857719:ℚ)/10240000000000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/8),((7:ℚ)/16),((7601357831:ℚ)/10000000000),((7890643143:ℚ)/10000000000),((26964073493:ℚ)/64800000000),((64194502001:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((187917981478962863665979317249190131:ℚ)/20995200000000000000000000000000000000),((-238764031:ℚ)/1024000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/8),((7:ℚ)/16),((3919666033:ℚ)/5000000000),((1958674899:ℚ)/2000000000),((13838998099:ℚ)/40000000000),((15502724293:ℚ)/25920000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((36344890647483747648694113542855939:ℚ)/2000000000000000000000000000000000000),((-238764031:ℚ)/1024000000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/8),((7:ℚ)/16),((24355783:ℚ)/25000000),((13596578049:ℚ)/10000000000),((83467349:ℚ)/276000000),((104136046343:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1092046573393889666609:ℚ)/38088000000000000000000),((-238764031:ℚ)/1024000000)⟩
theorem valid14 : Valid source15 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((1239:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((1239:ℚ)/1600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source15 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source15 nn0 nn1 Qcell ((1239:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC23
#check @N11Formalization.C450Source15GroupedC23.bound
#print axioms N11Formalization.C450Source15GroupedC23.valid0
#print axioms N11Formalization.C450Source15GroupedC23.valid1
#print axioms N11Formalization.C450Source15GroupedC23.valid2
#print axioms N11Formalization.C450Source15GroupedC23.valid3
#print axioms N11Formalization.C450Source15GroupedC23.valid4
#print axioms N11Formalization.C450Source15GroupedC23.valid5
#print axioms N11Formalization.C450Source15GroupedC23.valid6
#print axioms N11Formalization.C450Source15GroupedC23.valid7
#print axioms N11Formalization.C450Source15GroupedC23.valid8
#print axioms N11Formalization.C450Source15GroupedC23.valid9
#print axioms N11Formalization.C450Source15GroupedC23.valid10
#print axioms N11Formalization.C450Source15GroupedC23.valid11
#print axioms N11Formalization.C450Source15GroupedC23.valid12
#print axioms N11Formalization.C450Source15GroupedC23.valid13
#print axioms N11Formalization.C450Source15GroupedC23.valid14
#print axioms N11Formalization.C450Source15GroupedC23.bound
#print axioms N11Formalization.C450Source15GroupedC23.endpoint_checks
