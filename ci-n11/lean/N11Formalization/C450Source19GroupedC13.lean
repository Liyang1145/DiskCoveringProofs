import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((786426957:ℚ)/1250000000),((3289820553:ℚ)/5000000000),((-1929820553:ℚ)/12400000000),((-8925057:ℚ)/125000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((372243533:ℚ)/625000000),((29645826439258334713340395694019401312865754641549:ℚ)/378417968750000000000000000000000000000000000000000),((-2783053119297685291721537:ℚ)/115520000000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((408140893:ℚ)/625000000),((6818495691:ℚ)/10000000000),((-4098495691:ℚ)/25750000000),((-168140893:ℚ)/2225000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((2685031689:ℚ)/5000000000),((137531652174982412699442478813344781245614582204417353:ℚ)/1772749194335937500000000000000000000000000000000000000),((-882523854948543425370337:ℚ)/28880000000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((6768996911:ℚ)/10000000000),((6937887177:ℚ)/10000000000),((-4217887177:ℚ)/26700000000),((-8786990733:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((590008921:ℚ)/1250000000),((54465229982189182515589649329883364900784447942603552547599:ℚ)/714428311043750000000000000000000000000000000000000000000000),((-273853450143602584056916473:ℚ)/7393280000000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((3444167699:ℚ)/5000000000),((141145129:ℚ)/200000000),((-86745129:ℚ)/543500000),((-4572503097:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((218104469:ℚ)/500000000),((1363657850183092259738676590914552187124097681828266000117:ℚ)/17951675175683593750000000000000000000000000000000000000000),((-74465362263020387661501313:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((87595669:ℚ)/125000000),((897075581:ℚ)/1250000000),((-557075581:ℚ)/3456250000),((-39595669:ℚ)/468750000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((39742763:ℚ)/100000000),((315844225770894457869499380765287436236622165152773:ℚ)/4171673208475112915039062500000000000000000000000000),((-50296762595624952179793:ℚ)/1155200000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/4),((-3:ℚ)/16),((11135863:ℚ)/15625000),((7236271177:ℚ)/10000000000),((-4516271177:ℚ)/28125000000),((-15407589:ℚ)/177265625),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((3546822621:ℚ)/10000000000),((78486145928309852760304299871921339306529490461:ℚ)/1044419208973646163940429687500000000000000000000),((-844646333054972825497:ℚ)/18050000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((7186594779:ℚ)/10000000000),((729593283:ℚ)/1000000000),((-457593283:ℚ)/2836250000),((-912707667:ℚ)/10400000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3313483013:ℚ)/10000000000),((1197095433450556897525815585304366077463353364799096795421:ℚ)/15951977600000000000000000000000000000000000000000000000000),((-358012382834091188059816433:ℚ)/7393280000000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((7246232767:ℚ)/10000000000),((3707620993:ℚ)/5000000000),((-2347620993:ℚ)/14300000000),((-10218698301:ℚ)/116300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((3063135497:ℚ)/10000000000),((9620297348429950126583303363050912105118687483071165312611:ℚ)/127809316943750000000000000000000000000000000000000000000000),((-370065200698193229976535257:ℚ)/7393280000000000000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((7365495771:ℚ)/10000000000),((7534533043:ℚ)/10000000000),((-4814533043:ℚ)/29075000000),((-3525495771:ℚ)/39400000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((622653783:ℚ)/2500000000),((8344540788812434590115579662518789176789388522934849674619:ℚ)/111144609987500000000000000000000000000000000000000000000000),((-394193637232189380056949233:ℚ)/7393280000000000000000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((3742371089:ℚ)/5000000000),((485816517:ℚ)/625000000),((-315816517:ℚ)/1846875000),((-5467113267:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((34875769:ℚ)/200000000),((21106190002006955368495832062658357926512986543243340172493:ℚ)/279470356250000000000000000000000000000000000000000000000000),((-104588151066582198794468473:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((772318833:ℚ)/1000000000),((103124303:ℚ)/125000000),((-69124303:ℚ)/381250000),((-14382179:ℚ)/160000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1954724577276934238345910543897089931822968707737:ℚ)/25600000000000000000000000000000000000000000000000),((-6118223:ℚ)/102400000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((8199913283:ℚ)/10000000000),((5077835203:ℚ)/5000000000),((-1239278401:ℚ)/5400000000),((-13079739849:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((18836341209731727555889447443184841159246831765027308579043:ℚ)/230400000000000000000000000000000000000000000000000000000000),((-6118223:ℚ)/102400000)⟩
theorem valid11 : Valid source19 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((5052583937:ℚ)/5000000000),((6981190029:ℚ)/5000000000),((-5621190029:ℚ)/20000000000),((-3132583937:ℚ)/36800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((21352874249840998969366556271748540025364956638340252417:ℚ)/233606400000000000000000000000000000000000000000000000000),((-6118223:ℚ)/102400000)⟩
theorem valid12 : Valid source19 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source19 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2269:ℚ)/3200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source19 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source19 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC13
#check @N11Formalization.C450Source19GroupedC13.bound
#print axioms N11Formalization.C450Source19GroupedC13.valid0
#print axioms N11Formalization.C450Source19GroupedC13.valid1
#print axioms N11Formalization.C450Source19GroupedC13.valid2
#print axioms N11Formalization.C450Source19GroupedC13.valid3
#print axioms N11Formalization.C450Source19GroupedC13.valid4
#print axioms N11Formalization.C450Source19GroupedC13.valid5
#print axioms N11Formalization.C450Source19GroupedC13.valid6
#print axioms N11Formalization.C450Source19GroupedC13.valid7
#print axioms N11Formalization.C450Source19GroupedC13.valid8
#print axioms N11Formalization.C450Source19GroupedC13.valid9
#print axioms N11Formalization.C450Source19GroupedC13.valid10
#print axioms N11Formalization.C450Source19GroupedC13.valid11
#print axioms N11Formalization.C450Source19GroupedC13.valid12
#print axioms N11Formalization.C450Source19GroupedC13.bound
#print axioms N11Formalization.C450Source19GroupedC13.endpoint_checks
