import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((1797378537:ℚ)/2500000000),((1857484171:ℚ)/2500000000),((-4644452513:ℚ)/4960000000),((-3393883253:ℚ)/4212500000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((1650827467:ℚ)/5000000000),((399911610739778370474417782761135462951:ℚ)/926918236718750000000000000000000000000),((189613169396589989290832881:ℚ)/184832000000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((913593129:ℚ)/1250000000),((1887235509:ℚ)/2500000000),((-4733706527:ℚ)/5055000000),((-5195151903:ℚ)/6437500000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((1388710383:ℚ)/5000000000),((45381137691535626786430485300614941769052737737134935191:ℚ)/105356883716583251953125000000000000000000000000000000000),((190780238701032121683678321:ℚ)/184832000000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((7427958071:ℚ)/10000000000),((7667938109:ℚ)/10000000000),((-19291814327:ℚ)/20600000000),((-42395706497:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((1065903881:ℚ)/5000000000),((156049989652660413869234279893304332987305824271206420053:ℚ)/362838827047729492187500000000000000000000000000000000000),((1059740159:ℚ)/1024000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((7547154241:ℚ)/10000000000),((38934627:ℚ)/50000000),((-98243881:ℚ)/104900000),((-43230079687:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((589977229:ℚ)/5000000000),((47639577197019469031243619865977221749115074119925112262461:ℚ)/110926872150000000000000000000000000000000000000000000000000),((1059740159:ℚ)/1024000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((153326689:ℚ)/200000000),((8262795531:ℚ)/10000000000),((-21076386593:ℚ)/21360000000),((-881286823:ℚ)/1144000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((1157666737173766508722800900636877682689252936944966007:ℚ)/2498442460800000000000000000000000000000000000000000000),((1059740159:ℚ)/1024000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((8142911683:ℚ)/10000000000),((1151778619:ℚ)/1250000000),(-1:ℚ),((-47400381781:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((7519331320864202319880444262624103650841775754723284789:ℚ)/15746400000000000000000000000000000000000000000000000000),((1059740159:ℚ)/1024000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((4547754477:ℚ)/5000000000),((1389534681:ℚ)/1250000000),(-1:ℚ),((-27034281339:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((12151985061753534016629519178370642018106041549954319793:ℚ)/25000000000000000000000000000000000000000000000000000000),((1059740159:ℚ)/1024000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((2199843759:ℚ)/2000000000),((14918680621:ℚ)/10000000000),(-1:ℚ),((-4492968771:ℚ)/7360000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((50267304951687535739314288432373011:ℚ)/99672064000000000000000000000000000),((1059740159:ℚ)/1024000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
private theorem node0_2 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((81:ℚ)/100) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_4 node4_8
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_8
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7]
theorem packet_count : packets.length = 8 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC02
#check @N11Formalization.C450Source31GroupedC02.bound
#print axioms N11Formalization.C450Source31GroupedC02.valid0
#print axioms N11Formalization.C450Source31GroupedC02.valid1
#print axioms N11Formalization.C450Source31GroupedC02.valid2
#print axioms N11Formalization.C450Source31GroupedC02.valid3
#print axioms N11Formalization.C450Source31GroupedC02.valid4
#print axioms N11Formalization.C450Source31GroupedC02.valid5
#print axioms N11Formalization.C450Source31GroupedC02.valid6
#print axioms N11Formalization.C450Source31GroupedC02.valid7
#print axioms N11Formalization.C450Source31GroupedC02.bound
#print axioms N11Formalization.C450Source31GroupedC02.endpoint_checks
