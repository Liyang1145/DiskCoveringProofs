import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((1110908607:ℚ)/2000000000),((6114018023:ℚ)/10000000000),((12942177463:ℚ)/21360000000),((7650018023:ℚ)/9920000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7512138461:ℚ)/10000000000),((-32796641956639009920978469647459319:ℚ)/270708096000000000000000000000000000),((-1143108445421040530591195433:ℚ)/2957312000000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((301639959:ℚ)/500000000),((6353021271:ℚ)/10000000000),((3450759631:ℚ)/5530000000),((2629673757:ℚ)/3560000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6537818849:ℚ)/10000000000),((-148788084101412533129364518726288740140788375485660669:ℚ)/1056952356250000000000000000000000000000000000000000000),((-1147077637307126229696061257:ℚ)/2957312000000000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((9:ℚ)/16),((5:ℚ)/8),((6271757869:ℚ)/10000000000),((6472484467:ℚ)/10000000000),((71165820821:ℚ)/112500000000),((8008484467:ℚ)/11060000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6001847229:ℚ)/10000000000),((-148020015370236019564293243765446565334572042335669190359:ℚ)/988769531250000000000000000000000000000000000000000000000),((-1148885508784877119955771553:ℚ)/2957312000000000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((1278239987:ℚ)/2000000000),((3295961883:ℚ)/5000000000),((14448159883:ℚ)/22880000000),((1354653961:ℚ)/1875000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2858823651:ℚ)/5000000000),((-1017185962884900722583960052026744651748795267808544547:ℚ)/6805427200000000000000000000000000000000000000000000000),((-286644865126811183833884753:ℚ)/739328000000000000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((6510618817:ℚ)/10000000000),((6711340353:ℚ)/10000000000),((73315569353:ℚ)/116300000000),((8247340353:ℚ)/11440000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5420355211:ℚ)/10000000000),((-366745702615609377659575500139566807598373985404234665163:ℚ)/2457871479687500000000000000000000000000000000000000000000),((-1144158611358042097983697593:ℚ)/2957312000000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((3315007833:ℚ)/5000000000),((1366147067:ℚ)/2000000000),((37195070497:ℚ)/59100000000),((1673347067:ℚ)/2326000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5107656433:ℚ)/10000000000),((-48038805435402321266745630566760666628182608568330437203:ℚ)/322539173437500000000000000000000000000000000000000000000),((-45664920180126802586878353:ℚ)/118292480000000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((3374695777:ℚ)/5000000000),((1737527437:ℚ)/2500000000),((37732261993:ℚ)/60050000000),((2121527437:ℚ)/2955000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2388248017:ℚ)/5000000000),((-201176468844272958375002040182796656354138020402393697203:ℚ)/1353377813281250000000000000000000000000000000000000000000),((-71185792510520742701681313:ℚ)/184832000000000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((6868747487:ℚ)/10000000000),((1767366141:ℚ)/2500000000),((76538727383:ℚ)/122000000000),((2151366141:ℚ)/3002500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4422697347:ℚ)/10000000000),((-1683495754592458415858457187098528269401765483174857384413:ℚ)/11349050000000000000000000000000000000000000000000000000000),((-71012979751156507049179137:ℚ)/184832000000000000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((6988084407:ℚ)/10000000000),((1827029747:ℚ)/2500000000),((77612759663:ℚ)/125800000000),((2211029747:ℚ)/3050000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((4040284041:ℚ)/10000000000),((-436165428600182746145787296702634413220487324169921106013:ℚ)/3110727362500000000000000000000000000000000000000000000000),((-70396281166743427510911393:ℚ)/184832000000000000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((1806676171:ℚ)/2500000000),((7546705249:ℚ)/10000000000),((19940085539:ℚ)/32400000000),((9082705249:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((629445783:ℚ)/2000000000),((-122305829501987351594913928057751542630131902062219763:ℚ)/874800000000000000000000000000000000000000000000000000),((-1120009399441911196201264377:ℚ)/2957312000000000000000000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((1866314707:ℚ)/2500000000),((9453528347:ℚ)/10000000000),((20476832363:ℚ)/40000000000),((10989528347:ℚ)/12960000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1885828071:ℚ)/10000000000),((-1582814402669155518717094517767393381324833937337994737:ℚ)/25000000000000000000000000000000000000000000000000000000),((-23123606088503973:ℚ)/60800000000000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((4685940231:ℚ)/5000000000),((6630760257:ℚ)/5000000000),((49533462079:ℚ)/110400000000),((7398760257:ℚ)/8000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-2174437978382587954420691:ℚ)/380880000000000000000000000),((-391011639:ℚ)/1024000000)⟩
theorem valid11 : Valid source25 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source25 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source25 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC26
#check @N11Formalization.C450Source25GroupedC26.bound
#print axioms N11Formalization.C450Source25GroupedC26.valid0
#print axioms N11Formalization.C450Source25GroupedC26.valid1
#print axioms N11Formalization.C450Source25GroupedC26.valid2
#print axioms N11Formalization.C450Source25GroupedC26.valid3
#print axioms N11Formalization.C450Source25GroupedC26.valid4
#print axioms N11Formalization.C450Source25GroupedC26.valid5
#print axioms N11Formalization.C450Source25GroupedC26.valid6
#print axioms N11Formalization.C450Source25GroupedC26.valid7
#print axioms N11Formalization.C450Source25GroupedC26.valid8
#print axioms N11Formalization.C450Source25GroupedC26.valid9
#print axioms N11Formalization.C450Source25GroupedC26.valid10
#print axioms N11Formalization.C450Source25GroupedC26.valid11
#print axioms N11Formalization.C450Source25GroupedC26.bound
#print axioms N11Formalization.C450Source25GroupedC26.endpoint_checks
