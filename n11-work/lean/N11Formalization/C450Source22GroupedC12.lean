import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC12
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨((-5:ℚ)/16),((-1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-5:ℚ)/16),((-1:ℚ)/4),((6351422597:ℚ)/10000000000),((3325178323:ℚ)/5000000000),((-2045178323:ℚ)/9920000000),((-2991422597:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1453413951:ℚ)/2500000000),((751314087237166119669206456713089676010816329499637310063:ℚ)/4962090380859375000000000000000000000000000000000000000000),((-4926218765788731928052023:ℚ)/115520000000000000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-5:ℚ)/16),((-1:ℚ)/4),((1318145629:ℚ)/2000000000),((6889635979:ℚ)/10000000000),((-4329635979:ℚ)/20600000000),((-646145629:ℚ)/5340000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5212426301:ℚ)/10000000000),((1840821283492825904973540157648401340606377527954909909:ℚ)/12253242431250000000000000000000000000000000000000000000),((-242379577519044984720327:ℚ)/4620800000000000000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((6829903843:ℚ)/10000000000),((1752307123:ℚ)/2500000000),((-370769041:ℚ)/1780000000),((-3469903843:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((227032471:ℚ)/500000000),((823064766016199038225648117641020199295598284684908023821:ℚ)/5581471180029296875000000000000000000000000000000000000000),((-7199459533614266853059303:ℚ)/115520000000000000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((6949447313:ℚ)/10000000000),((89109897:ℚ)/125000000),((-57109897:ℚ)/271750000),((-3589447313:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2083853447:ℚ)/5000000000),((494990621153589780420107155363669099702870753663759924171:ℚ)/3365939095440673828125000000000000000000000000000000000000),((-7771973840214221952175343:ℚ)/115520000000000000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-5:ℚ)/16),((-1:ℚ)/4),((883620407:ℚ)/1250000000),((1812081821:ℚ)/2500000000),((-1172081821:ℚ)/5530000000),((-463620407:ℚ)/3515625000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((117512033:ℚ)/312500000),((18440038596930629810725637541797481207901502547058567:ℚ)/125708902487531304359436035156250000000000000000000000),((-130409100295488230997053:ℚ)/1805000000000000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-5:ℚ)/16),((-1:ℚ)/4),((1437690617:ℚ)/2000000000),((1473567293:ℚ)/2000000000),((-320522431:ℚ)/1500000000),((-765690617:ℚ)/5720000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3305958639:ℚ)/10000000000),((256775574002490323954762221883091064818556043469558653:ℚ)/1754524200000000000000000000000000000000000000000000000),((-356883633165916872433183:ℚ)/4620800000000000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-5:ℚ)/16),((-1:ℚ)/4),((7307918117:ℚ)/10000000000),((748732061:ℚ)/1000000000),((-492732061:ℚ)/2288000000),((-3947918117:ℚ)/29075000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2781386301:ℚ)/10000000000),((1604079417394992030472180235407751570383152404798681060197:ℚ)/10983613174853515625000000000000000000000000000000000000000),((-9499704252074052242728183:ℚ)/115520000000000000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-5:ℚ)/16),((-1:ℚ)/4),((3713679791:ℚ)/5000000000),((7606780941:ℚ)/10000000000),((-5046780941:ℚ)/23260000000),((-2033679791:ℚ)/14775000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((533881669:ℚ)/2500000000),((15821140369373977555739893182147226488455764246916759713:ℚ)/108539658190917968750000000000000000000000000000000000000),((-2519756881723327736741207:ℚ)/28880000000000000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-5:ℚ)/16),((-1:ℚ)/4),((1886694657:ℚ)/2500000000),((7845634661:ℚ)/10000000000),((-5285634661:ℚ)/23640000000),((-1046694657:ℚ)/7625000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1184145317:ℚ)/10000000000),((120419483583144852148349415522079338826636825511463429841:ℚ)/818760809326171875000000000000000000000000000000000000000),((-1998762219102778270254409:ℚ)/21660000000000000000000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-5:ℚ)/16),((-1:ℚ)/4),((3892776851:ℚ)/5000000000),((1664620421:ℚ)/2000000000),((-1152620421:ℚ)/4880000000),((-2212776851:ℚ)/16200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((40391702406392507008621081370958571466713801617839875819:ℚ)/270149175000000000000000000000000000000000000000000000000),((-12099283:ℚ)/128000000)⟩
theorem valid9 : Valid source22 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/16),((-1:ℚ)/4),((1032859737:ℚ)/1250000000),((10230614481:ℚ)/10000000000),((-7670614481:ℚ)/25920000000),((-612859737:ℚ)/5000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((5178340924792894204474633816169441228189457407794956271:ℚ)/31640625000000000000000000000000000000000000000000000000),((-12099283:ℚ)/128000000)⟩
theorem valid10 : Valid source22 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/16),((-1:ℚ)/4),((5084977431:ℚ)/5000000000),((561576483:ℚ)/400000000),((-459176483:ℚ)/1280000000),((-49347499:ℚ)/400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((27732579709520236880414238432781928943785737621079:ℚ)/150000000000000000000000000000000000000000000000000),((-12099283:ℚ)/128000000)⟩
theorem valid11 : Valid source22 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source22 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source22 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source22 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source22 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source22 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source22 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source22 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source22GroupedC12
#check @N11Formalization.C450Source22GroupedC12.bound
#print axioms N11Formalization.C450Source22GroupedC12.valid0
#print axioms N11Formalization.C450Source22GroupedC12.valid1
#print axioms N11Formalization.C450Source22GroupedC12.valid2
#print axioms N11Formalization.C450Source22GroupedC12.valid3
#print axioms N11Formalization.C450Source22GroupedC12.valid4
#print axioms N11Formalization.C450Source22GroupedC12.valid5
#print axioms N11Formalization.C450Source22GroupedC12.valid6
#print axioms N11Formalization.C450Source22GroupedC12.valid7
#print axioms N11Formalization.C450Source22GroupedC12.valid8
#print axioms N11Formalization.C450Source22GroupedC12.valid9
#print axioms N11Formalization.C450Source22GroupedC12.valid10
#print axioms N11Formalization.C450Source22GroupedC12.valid11
#print axioms N11Formalization.C450Source22GroupedC12.bound
#print axioms N11Formalization.C450Source22GroupedC12.endpoint_checks
