import N11Formalization.C450Source30Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source30GroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source30Data
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/2),((9:ℚ)/16),((1368217471:ℚ)/2500000000),((725501083:ℚ)/1250000000),((1928217471:ℚ)/3218750000),((8849509747:ℚ)/12400000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3834145311:ℚ)/5000000000),((-1133939332766000334217970068598312591550670498175395915647:ℚ)/4078099600000000000000000000000000000000000000000000000000),((-74981942024901673330547:ℚ)/180500000000000000000000)⟩
theorem valid0 : Valid source30 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source30 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((5713154913:ℚ)/10000000000),((3022076053:ℚ)/5000000000),((7953154913:ℚ)/13350000000),((36478684477:ℚ)/51500000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((900141827:ℚ)/1250000000),((-1400870141966541679362806740123390982110433230750299134148349:ℚ)/5071576504101562500000000000000000000000000000000000000000000),((-148639139482822734888479:ℚ)/361000000000000000000000)⟩
theorem valid1 : Valid source30 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source30 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((5953238507:ℚ)/10000000000),((6164153411:ℚ)/10000000000),((8193238507:ℚ)/13587500000),((74037380699:ℚ)/106800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((6708060653:ℚ)/10000000000),((-93767061469305942915249635211210864531438699356437124099242643:ℚ)/333187806544400000000000000000000000000000000000000000000000000),((-1189128515827127389057177:ℚ)/2888000000000000000000000)⟩
theorem valid2 : Valid source30 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source30 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((6073211507:ℚ)/10000000000),((3142055533:ℚ)/5000000000),((8313211507:ℚ)/13825000000),((37558499797:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1612470849:ℚ)/2500000000),((-1344557385595249621624004980220033980481189353518572093399623:ℚ)/4794562135094323730468750000000000000000000000000000000000000),((-4622179417288842744087:ℚ)/11281250000000000000000)⟩
theorem valid3 : Valid source30 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/2),((9:ℚ)/16),((6193141859:ℚ)/10000000000),((3202013663:ℚ)/5000000000),((8433141859:ℚ)/14062500000),((38098122967:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3091309823:ℚ)/5000000000),((-31155714162360291123461084317148283352193398004171794711:ℚ)/111475443823242187500000000000000000000000000000000000000),((-36787747584748280088541:ℚ)/90250000000000000000000)⟩
theorem valid4 : Valid source30 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source30 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source30 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((3156515883:ℚ)/5000000000),((6523904293:ℚ)/10000000000),((4276515883:ℚ)/7150000000),((77275138637:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1181001151:ℚ)/2000000000),((-625847294304483280604269929175094809966548132501155047186447:ℚ)/2246594238281250000000000000000000000000000000000000000000000),((-1170918613228697871913813:ℚ)/2888000000000000000000000)⟩
theorem valid5 : Valid source30 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source30 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((6432883279:ℚ)/10000000000),((6643743929:ℚ)/10000000000),((8672883279:ℚ)/14537500000),((78353695361:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2807738213:ℚ)/5000000000),((-319528188913241672471269392583130828008884564321941190688128801:ℚ)/1150601232809600000000000000000000000000000000000000000000000000),((-1164410115700052340197617:ℚ)/2888000000000000000000000)⟩
theorem valid6 : Valid source30 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source30 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((1638174579:ℚ)/2500000000),((6763548067:ℚ)/10000000000),((2198174579:ℚ)/3693750000),((79431932603:ℚ)/116300000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1328013141:ℚ)/2500000000),((-79230331194027912064705556977383887527371054962973722521393819:ℚ)/286162602765576562500000000000000000000000000000000000000000000),((-1157682536081721635718493:ℚ)/2888000000000000000000000)⟩
theorem valid7 : Valid source30 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((3336239333:ℚ)/5000000000),((344165921:ℚ)/500000000),((4456239333:ℚ)/7506250000),((4025493289:ℚ)/5910000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((4992169247:ℚ)/10000000000),((-4756960403049561393281699870235242289614484003055096738577:ℚ)/17230771344645312500000000000000000000000000000000000000000),((-5753679866979565407159:ℚ)/14440000000000000000000)⟩
theorem valid8 : Valid source30 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source30 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((1698056501:ℚ)/2500000000),((3501528297:ℚ)/5000000000),((2258056501:ℚ)/3812500000),((40793754673:ℚ)/60050000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((930479869:ℚ)/2000000000),((-1386436897354203800432701402409149665338742267925570999212547:ℚ)/5035918843219531250000000000000000000000000000000000000000000),((-45140941584908494238521:ℚ)/114000000000000000000000)⟩
theorem valid9 : Valid source30 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source30 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source30 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((6911941897:ℚ)/10000000000),((905305291:ℚ)/1250000000),((247349781:ℚ)/425000000),((10467747619:ℚ)/15250000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((428798319:ℚ)/1000000000),((-430739438935241192918087879835648162385341997249396540329:ℚ)/1601501684570312500000000000000000000000000000000000000000),((-280738676794674010204377:ℚ)/722000000000000000000000)⟩
theorem valid10 : Valid source30 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source30 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((7151285137:ℚ)/10000000000),((7481716237:ℚ)/10000000000),((3130428379:ℚ)/5400000000),((85895446133:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((3453454377:ℚ)/10000000000),((-1287539374609050389802440196174719101571737535597290387769:ℚ)/4807038150000000000000000000000000000000000000000000000000),((-1107095509454855561875153:ℚ)/2888000000000000000000000)⟩
theorem valid11 : Valid source30 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source30 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source30 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((3695259549:ℚ)/5000000000),((9392848841:ℚ)/10000000000),((4815259549:ℚ)/10000000000),((103095639569:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((588332793:ℚ)/2500000000),((-102578516328677304232908722359982033713328434824953051497:ℚ)/503884800000000000000000000000000000000000000000000000000),((-93020338419480363:ℚ)/243200000000000000)⟩
theorem valid12 : Valid source30 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source30 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((9301401557:ℚ)/10000000000),((13205870843:ℚ)/10000000000),((11541401557:ℚ)/27600000000),((137412837587:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-538919210078258744868241724677424608705964832822332673457577:ℚ)/3385600000000000000000000000000000000000000000000000000000000),((-24697351:ℚ)/64000000)⟩
theorem valid13 : Valid source30 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source30 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source30 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source30 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source30 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source30 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1163:ℚ)/1600) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source30 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source30 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source30 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source30 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source30 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source30 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source30GroupedC25
#check @N11Formalization.C450Source30GroupedC25.bound
#print axioms N11Formalization.C450Source30GroupedC25.valid0
#print axioms N11Formalization.C450Source30GroupedC25.valid1
#print axioms N11Formalization.C450Source30GroupedC25.valid2
#print axioms N11Formalization.C450Source30GroupedC25.valid3
#print axioms N11Formalization.C450Source30GroupedC25.valid4
#print axioms N11Formalization.C450Source30GroupedC25.valid5
#print axioms N11Formalization.C450Source30GroupedC25.valid6
#print axioms N11Formalization.C450Source30GroupedC25.valid7
#print axioms N11Formalization.C450Source30GroupedC25.valid8
#print axioms N11Formalization.C450Source30GroupedC25.valid9
#print axioms N11Formalization.C450Source30GroupedC25.valid10
#print axioms N11Formalization.C450Source30GroupedC25.valid11
#print axioms N11Formalization.C450Source30GroupedC25.valid12
#print axioms N11Formalization.C450Source30GroupedC25.valid13
#print axioms N11Formalization.C450Source30GroupedC25.bound
#print axioms N11Formalization.C450Source30GroupedC25.endpoint_checks
