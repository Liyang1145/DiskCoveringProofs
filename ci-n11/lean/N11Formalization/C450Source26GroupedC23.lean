import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC23
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((3:ℚ)/8),((7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/8),((7:ℚ)/16),((5696944247:ℚ)/10000000000),((6255408153:ℚ)/10000000000),((8256944247:ℚ)/17800000000),((59787857071:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1808354789:ℚ)/2500000000),((-2739949942224586298753681:ℚ)/158420000000000000000000000),((-358745778214581549430201879:ℚ)/887193600000000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((1235330771:ℚ)/2000000000),((3247486553:ℚ)/5000000000),((5241992313:ℚ)/11060000000),((30732405871:ℚ)/53400000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1243990207:ℚ)/2000000000),((-56341450080863686146720196395776621:ℚ)/1834854000000000000000000000000000000),((-30758700198849131996528093:ℚ)/73932800000000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/8),((7:ℚ)/16),((128325253:ℚ)/200000000),((6614702617:ℚ)/10000000000),((59841751:ℚ)/125000000),((62302918319:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1414103153:ℚ)/2500000000),((-2851613273372084103639157135461:ℚ)/78125000000000000000000000000000),((-6565386333189402193863887:ℚ)/15564800000000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/8),((7:ℚ)/16),((408500809:ℚ)/625000000),((3367199601:ℚ)/5000000000),((1705502427:ℚ)/3575000000),((31570397207:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((535523317:ℚ)/1000000000),((-2337451789490097335640986569890309:ℚ)/63903125000000000000000000000000000),((-93958842816928955018325031:ℚ)/221798400000000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((1663932401:ℚ)/2500000000),((6854064499:ℚ)/10000000000),((6911797203:ℚ)/14537500000),((5816222863:ℚ)/10400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5038010729:ℚ)/10000000000),((-58015998362988750074816450807774599:ℚ)/1585041796875000000000000000000000000),((-125803238628360501665460277:ℚ)/295731200000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((1355082861:ℚ)/2000000000),((6973700041:ℚ)/10000000000),((1867082861:ℚ)/3940000000),((64815900287:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2350733037:ℚ)/5000000000),((-4258411722279311673008828984751403:ℚ)/116427000000000000000000000000000000),((-126316701587009086139448637:ℚ)/295731200000000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((6895068613:ℚ)/10000000000),((7093307259:ℚ)/10000000000),((28365205839:ℚ)/60050000000),((65653150813:ℚ)/118200000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2170536547:ℚ)/5000000000),((-1974365197655247744385109503536027449:ℚ)/54090037500000000000000000000000000000),((-20024030769304508473342069:ℚ)/46694400000000000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/8),((7:ℚ)/16),((7014693991:ℚ)/10000000000),((7212887497:ℚ)/10000000000),((28724081973:ℚ)/61000000000),((66490212479:ℚ)/120100000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((493784149:ℚ)/1250000000),((-676877636878748093875575014584416947:ℚ)/18605000000000000000000000000000000000),((-127309733014171332801714493:ℚ)/295731200000000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((713429181:ℚ)/1000000000),((1490394397:ℚ)/2000000000),((2908287543:ℚ)/6290000000),((13632760779:ℚ)/24400000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((439863777:ℚ)/1250000000),((-3131081655454424982718660247156623:ℚ)/98910250000000000000000000000000000),((-5084001186360223927716693:ℚ)/11829248000000000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/8),((7:ℚ)/16),((1843352459:ℚ)/2500000000),((3845481339:ℚ)/5000000000),((91976017:ℚ)/200000000),((34918369373:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((30600161:ℚ)/125000000),((-6277294383705190684052098946691:ℚ)/200000000000000000000000000000000),((-13214017917781051:ℚ)/30400000000000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/8),((7:ℚ)/16),((3806216031:ℚ)/5000000000),((4800160641:ℚ)/5000000000),((15258648093:ℚ)/40000000000),((41601124487:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((94629337896573822375330823835681167:ℚ)/6000000000000000000000000000000000000),((-226349903:ℚ)/512000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/8),((7:ℚ)/16),((38087953:ℚ)/40000000),((13411274453:ℚ)/10000000000),((48327953:ℚ)/147200000),((109878921171:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((718921060633561007519:ℚ)/10833920000000000000000),((-226349903:ℚ)/512000000)⟩
theorem valid11 : Valid source26 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source26 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source26 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source26 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source26 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC23
#check @N11Formalization.C450Source26GroupedC23.bound
#print axioms N11Formalization.C450Source26GroupedC23.valid0
#print axioms N11Formalization.C450Source26GroupedC23.valid1
#print axioms N11Formalization.C450Source26GroupedC23.valid2
#print axioms N11Formalization.C450Source26GroupedC23.valid3
#print axioms N11Formalization.C450Source26GroupedC23.valid4
#print axioms N11Formalization.C450Source26GroupedC23.valid5
#print axioms N11Formalization.C450Source26GroupedC23.valid6
#print axioms N11Formalization.C450Source26GroupedC23.valid7
#print axioms N11Formalization.C450Source26GroupedC23.valid8
#print axioms N11Formalization.C450Source26GroupedC23.valid9
#print axioms N11Formalization.C450Source26GroupedC23.valid10
#print axioms N11Formalization.C450Source26GroupedC23.valid11
#print axioms N11Formalization.C450Source26GroupedC23.bound
#print axioms N11Formalization.C450Source26GroupedC23.endpoint_checks
