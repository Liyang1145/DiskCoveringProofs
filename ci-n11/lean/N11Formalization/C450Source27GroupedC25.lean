import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((2777541733:ℚ)/5000000000),((6118581799:ℚ)/10000000000),((3777541733:ℚ)/6675000000),((71707236191:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1877774137:ℚ)/2500000000),((-2683165920928152867162519165168539:ℚ)/24784066406250000000000000000000000),((-16908699914740228238407:ℚ)/40000000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((603438441:ℚ)/1000000000),((6358035891:ℚ)/10000000000),((803438441:ℚ)/1382500000),((73862323019:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((408399283:ℚ)/625000000),((-2074925992360898490129162668363347309710442731002943:ℚ)/16514880566406250000000000000000000000000000000000000),((-18530161659506421756804661:ℚ)/43320000000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/2),((9:ℚ)/16),((6273810481:ℚ)/10000000000),((6477712849:ℚ)/10000000000),((2757936827:ℚ)/4687500000),((74939415641:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1199412727:ℚ)/2000000000),((-28629565426509263187928078432049291151844955547456047:ℚ)/214576721191406250000000000000000000000000000000000000),((-6212098615893593062030727:ℚ)/14440000000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((1278694831:ℚ)/2000000000),((3298679333:ℚ)/5000000000),((152608621:ℚ)/260000000),((38008113997:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((571211489:ℚ)/1000000000),((-14639631366250139517831067771733339636816557526987:ℚ)/109850000000000000000000000000000000000000000000000),((-1553221727103390283597653:ℚ)/3610000000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((325655357:ℚ)/500000000),((1679243723:ℚ)/2500000000),((425655357:ℚ)/726875000),((19273193507:ℚ)/28600000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((676750653:ℚ)/1250000000),((-79858268444839151482433565958047508391459538455379:ℚ)/600066279220581054687500000000000000000000000000000),((-388316736145834933246833:ℚ)/902500000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((3316355481:ℚ)/5000000000),((273462519:ℚ)/400000000),((4316355481:ℚ)/7387500000),((3126762671:ℚ)/4652000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5100396997:ℚ)/10000000000),((-27899683482005143159184549034358278795821712636484229:ℚ)/209986441040039062500000000000000000000000000000000000),((-29820680108508511308541:ℚ)/69312000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((6752287047:ℚ)/10000000000),((1739031067:ℚ)/2500000000),((8752287047:ℚ)/15012500000),((19811279603:ℚ)/29550000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1192050389:ℚ)/2500000000),((-2804368048165843320242437809448188375590121934477071129:ℚ)/21146528332519531250000000000000000000000000000000000000),((-776451134376859901564081:ℚ)/1805000000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((687183673:ℚ)/1000000000),((176891501:ℚ)/250000000),((887183673:ℚ)/1525000000),((2008023509:ℚ)/3002500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2206595221:ℚ)/5000000000),((-2933441425753094510113754582710841803605592529360471:ℚ)/22166113281250000000000000000000000000000000000000000),((-817101360682372462007:ℚ)/1900000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((6991361261:ℚ)/10000000000),((914332463:ℚ)/1250000000),((8991361261:ℚ)/15725000000),((10308992167:ℚ)/15250000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((50366279:ℚ)/125000000),((-761914886439277955252983469828845123634595821063684963:ℚ)/6075639379882812500000000000000000000000000000000000000),((-771369912939227105125529:ℚ)/1805000000000000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((7230339481:ℚ)/10000000000),((7553570639:ℚ)/10000000000),((3076779827:ℚ)/5400000000),((84622135751:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((3131741961:ℚ)/10000000000),((-4555591024486276920640327121855715885668734854394303:ℚ)/36450000000000000000000000000000000000000000000000000),((-6163457452343065784053767:ℚ)/14440000000000000000000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((1867307563:ℚ)/2500000000),((378497177:ℚ)/400000000),((2367307563:ℚ)/5000000000),((4072074593:ℚ)/5184000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1857746899:ℚ)/10000000000),((-1868883537274694741778128841338151:ℚ)/31250000000000000000000000000000000),((-5234812127532201:ℚ)/12160000000000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((9377962659:ℚ)/10000000000),((6636399641:ℚ)/5000000000),((11377962659:ℚ)/27600000000),((68047596769:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-1359261239499897913307069:ℚ)/380880000000000000000000000),((-13858071:ℚ)/32000000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source27 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source27 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source27 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source27 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC25
#check @N11Formalization.C450Source27GroupedC25.bound
#print axioms N11Formalization.C450Source27GroupedC25.valid0
#print axioms N11Formalization.C450Source27GroupedC25.valid1
#print axioms N11Formalization.C450Source27GroupedC25.valid2
#print axioms N11Formalization.C450Source27GroupedC25.valid3
#print axioms N11Formalization.C450Source27GroupedC25.valid4
#print axioms N11Formalization.C450Source27GroupedC25.valid5
#print axioms N11Formalization.C450Source27GroupedC25.valid6
#print axioms N11Formalization.C450Source27GroupedC25.valid7
#print axioms N11Formalization.C450Source27GroupedC25.valid8
#print axioms N11Formalization.C450Source27GroupedC25.valid9
#print axioms N11Formalization.C450Source27GroupedC25.valid10
#print axioms N11Formalization.C450Source27GroupedC25.valid11
#print axioms N11Formalization.C450Source27GroupedC25.bound
#print axioms N11Formalization.C450Source27GroupedC25.endpoint_checks
