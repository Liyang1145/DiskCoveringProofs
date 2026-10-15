import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC17
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨(0:ℚ),((1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),(0:ℚ),((1:ℚ)/16),((3004112441:ℚ)/5000000000),((3166062471:ℚ)/5000000000),((464:ℚ)/2575),((12766062471:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6590800967:ℚ)/10000000000),((-2362529334698183531444495208688547:ℚ)/26677905273437500000000000000000000),((-912867403598917715323283971:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),(0:ℚ),((1:ℚ)/16),((6250111163:ℚ)/10000000000),((1643358319:ℚ)/2500000000),((232:ℚ)/1335),((6443358319:ℚ)/25750000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((3026046413:ℚ)/5000000000),((-17373034516106207949991315909387:ℚ)/206533886718750000000000000000000),((-236414341988849772962609491:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((6491677239:ℚ)/10000000000),((1673496323:ℚ)/2500000000),((928:ℚ)/5435),((6473496323:ℚ)/26700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((273423747:ℚ)/500000000),((-10305413968362167414323527918800603:ℚ)/125426318652343750000000000000000000),((-245319789340660492363420299:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),(0:ℚ),((1:ℚ)/16),((6612351047:ℚ)/10000000000),((1703618507:ℚ)/2500000000),((464:ℚ)/2765),((6503618507:ℚ)/27175000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((5155003161:ℚ)/10000000000),((-2955811618098624456151735124947:ℚ)/36863572692871093750000000000000),((-249374208509790581249238619:ℚ)/924160000000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),(0:ℚ),((1:ℚ)/16),((3366478599:ℚ)/5000000000),((3467451391:ℚ)/5000000000),((928:ℚ)/5625),((13067451391:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4823324791:ℚ)/10000000000),((-50397217895245760179016237763113:ℚ)/643730163574218750000000000000000),((-1013650003210949616850340211:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),(0:ℚ),((1:ℚ)/16),((3426749613:ℚ)/5000000000),((56442197:ℚ)/80000000),((116:ℚ)/715),((210042197:ℚ)/900000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4469345981:ℚ)/10000000000),((-174716985225083266639159888632827:ℚ)/2284536718750000000000000000000000),((-263613243022649572839579:ℚ)/946339840000000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),(0:ℚ),((1:ℚ)/16),((348699021:ℚ)/500000000),((1459171769:ℚ)/2000000000),((464:ℚ)/2955),((5299171769:ℚ)/22880000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4087232427:ℚ)/10000000000),((-81759018281511500877271879456163:ℚ)/1119927685546875000000000000000000),((-166792406350652157060041091:ℚ)/591462400000000000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),(0:ℚ),((1:ℚ)/16),((721477237:ℚ)/1000000000),((7536247411:ℚ)/10000000000),((232:ℚ)/1525),((26736247411:ℚ)/118200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((399694961:ℚ)/1250000000),((-774572582218992390487815304017203:ℚ)/11083056640625000000000000000000000),((-4296833969178189968672425451:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(0:ℚ),((1:ℚ)/16),((1491071047:ℚ)/2000000000),((801650797:ℚ)/1000000000),((58:ℚ)/405),((2721650797:ℚ)/12200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((1954117963:ℚ)/10000000000),((-8130252035737525769602964323:ℚ)/126562500000000000000000000000),((-58467390142105261:ℚ)/194560000000000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(0:ℚ),((1:ℚ)/16),((99199613:ℚ)/125000000),((9932492137:ℚ)/10000000000),((29:ℚ)/250),((29132492137:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-2348791084496587467788796664249:ℚ)/48828125000000000000000000000000),((-314136497:ℚ)/1024000000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(0:ℚ),((1:ℚ)/16),((9853022207:ℚ)/10000000000),((6875579977:ℚ)/5000000000),((29:ℚ)/345),((16475579977:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-803023963227337187860860769903:ℚ)/28516406250000000000000000000000),((-314136497:ℚ)/1024000000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
private theorem node0_2 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((61:ℚ)/80) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_5 node5_11
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_11
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10]
theorem packet_count : packets.length = 11 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC17
#check @N11Formalization.C450Source31GroupedC17.bound
#print axioms N11Formalization.C450Source31GroupedC17.valid0
#print axioms N11Formalization.C450Source31GroupedC17.valid1
#print axioms N11Formalization.C450Source31GroupedC17.valid2
#print axioms N11Formalization.C450Source31GroupedC17.valid3
#print axioms N11Formalization.C450Source31GroupedC17.valid4
#print axioms N11Formalization.C450Source31GroupedC17.valid5
#print axioms N11Formalization.C450Source31GroupedC17.valid6
#print axioms N11Formalization.C450Source31GroupedC17.valid7
#print axioms N11Formalization.C450Source31GroupedC17.valid8
#print axioms N11Formalization.C450Source31GroupedC17.valid9
#print axioms N11Formalization.C450Source31GroupedC17.valid10
#print axioms N11Formalization.C450Source31GroupedC17.bound
#print axioms N11Formalization.C450Source31GroupedC17.endpoint_checks
