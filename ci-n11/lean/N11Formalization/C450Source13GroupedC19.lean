import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((761505823:ℚ)/1250000000),((412856839:ℚ)/625000000),((400501941:ℚ)/2225000000),((1718570517:ℚ)/6200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((320427321:ℚ)/500000000),((32895702759876952965339853211957321:ℚ)/1060559600000000000000000000000000000),((-834743894251035393693281:ℚ)/7220000000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((656832749:ℚ)/1000000000),((342185071:ℚ)/500000000),((1008832749:ℚ)/5530000000),((470185071:ℚ)/1780000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2635657741:ℚ)/5000000000),((62676228535406141991708349641220581651495512204162512761:ℚ)/2155858649210000000000000000000000000000000000000000000000),((-560361752445592487337089:ℚ)/4620800000000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((3403200843:ℚ)/5000000000),((6962684917:ℚ)/10000000000),((5163200843:ℚ)/28125000000),((28568054751:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4610650351:ℚ)/10000000000),((553352747008464004944217563824023350438721414414362911303:ℚ)/19568717910000000000000000000000000000000000000000000000000),((-14335697555606618991143761:ℚ)/115520000000000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((1:ℚ)/8),((3:ℚ)/16),((6925424187:ℚ)/10000000000),((1755543431:ℚ)/2500000000),((10445424187:ℚ)/56725000000),((798514477:ℚ)/3125000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((530639431:ℚ)/1250000000),((5482935762014511121854202050877113545021156321655592654643:ℚ)/196394386291503906250000000000000000000000000000000000000000),((-57996191392007070399252241:ℚ)/462080000000000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((1746233001:ℚ)/2500000000),((1770415159:ℚ)/2500000000),((2626233001:ℚ)/14300000000),((7231245477:ℚ)/28362500000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2025411067:ℚ)/5000000000),((649261135165488590983907700498094371201210491278319683347:ℚ)/23327897905072363281250000000000000000000000000000000000000),((-3645182285571585833228089:ℚ)/28880000000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/8),((3:ℚ)/16),((7044437607:ℚ)/10000000000),((7141145699:ℚ)/10000000000),((10564437607:ℚ)/57675000000),((29103437097:ℚ)/114400000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3847303059:ℚ)/10000000000),((7677975600195234211603584260954709336762164315490197433245247:ℚ)/276681916116320000000000000000000000000000000000000000000000000),((-58649658548565597784689961:ℚ)/462080000000000000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((1775985263:ℚ)/2500000000),((45003931:ℚ)/62500000),((2655985263:ℚ)/14537500000),((61003931:ℚ)/240312500),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((908250979:ℚ)/2500000000),((25972141641832731729974963225232718149288619696371401:ℚ)/938552386289247131347656250000000000000000000000000000),((-3686026102160580340872041:ℚ)/28880000000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/8),((3:ℚ)/16),((7163442391:ℚ)/10000000000),((7260110461:ℚ)/10000000000),((10683442391:ℚ)/58625000000),((29460331383:ℚ)/116300000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1702943037:ℚ)/5000000000),((2984195375814635777374969028503790221652929303712806323768617:ℚ)/108127173708708437500000000000000000000000000000000000000000000),((-59303194109598451758446409:ℚ)/462080000000000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((3611470839:ℚ)/5000000000),((1463918049:ℚ)/2000000000),((5371470839:ℚ)/29550000000),((846822021:ℚ)/3350000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((632636979:ℚ)/2000000000),((112967516755445217774883916591591076007050773482474583171:ℚ)/4103546929804687500000000000000000000000000000000000000000),((-14907497066795432933572969:ℚ)/115520000000000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((91030487:ℚ)/125000000),((7438544829:ℚ)/10000000000),((135030487:ℚ)/750625000),((9998544829:ℚ)/39400000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((1450493409:ℚ)/5000000000),((9137958903406301425965504529987152657775835678996904788380753:ℚ)/330830809817190000000000000000000000000000000000000000000000000),((-9368250056640785426541:ℚ)/72200000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((7401427703:ℚ)/10000000000),((236171657:ℚ)/312500000),((10921427703:ℚ)/61000000000),((789771:ℚ)/3125000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2290960999:ℚ)/10000000000),((15612175904611352069115826052487305257264053821:ℚ)/567779541015625000000000000000000000000000000000),((-60610479420497780441038601:ℚ)/462080000000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((1880102247:ℚ)/2500000000),((8033227559:ℚ)/10000000000),((2760102247:ℚ)/16200000000),((31779682677:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((289700973:ℚ)/2000000000),((105170553071377565701630400536772802339550824494692761609467:ℚ)/3723055852500000000000000000000000000000000000000000000000000),((-3829014580183260003247801:ℚ)/28880000000000000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((1999066533:ℚ)/2500000000),((2483866677:ℚ)/2500000000),((2879066533:ℚ)/20000000000),((3123866677:ℚ)/10800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((9010786819086651826433770076663395019809911755818009:ℚ)/295245000000000000000000000000000000000000000000000000),((-17091861:ℚ)/128000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((9898878813:ℚ)/10000000000),((13738093383:ℚ)/10000000000),((13418878813:ℚ)/110400000000),((48894280149:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((35634079131820246507096819182185029961417:ℚ)/975052800000000000000000000000000000000000),((-17091861:ℚ)/128000000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source13 nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source13 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source13 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC19
#check @N11Formalization.C450Source13GroupedC19.bound
#print axioms N11Formalization.C450Source13GroupedC19.valid0
#print axioms N11Formalization.C450Source13GroupedC19.valid1
#print axioms N11Formalization.C450Source13GroupedC19.valid2
#print axioms N11Formalization.C450Source13GroupedC19.valid3
#print axioms N11Formalization.C450Source13GroupedC19.valid4
#print axioms N11Formalization.C450Source13GroupedC19.valid5
#print axioms N11Formalization.C450Source13GroupedC19.valid6
#print axioms N11Formalization.C450Source13GroupedC19.valid7
#print axioms N11Formalization.C450Source13GroupedC19.valid8
#print axioms N11Formalization.C450Source13GroupedC19.valid9
#print axioms N11Formalization.C450Source13GroupedC19.valid10
#print axioms N11Formalization.C450Source13GroupedC19.valid11
#print axioms N11Formalization.C450Source13GroupedC19.valid12
#print axioms N11Formalization.C450Source13GroupedC19.valid13
#print axioms N11Formalization.C450Source13GroupedC19.bound
#print axioms N11Formalization.C450Source13GroupedC19.endpoint_checks
