import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/4),((5:ℚ)/16),((5618192051:ℚ)/10000000000),((5961381299:ℚ)/10000000000),((11058192051:ℚ)/25750000000),((10441381299:ℚ)/19840000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7388614417:ℚ)/10000000000),((-17820713214435113530588768081846554707707040105934711734559:ℚ)/51274933935546875000000000000000000000000000000000000000000),((-247542424722039882079921277:ℚ)/739328000000000000000000000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((2930567881:ℚ)/5000000000),((3041324263:ℚ)/5000000000),((5650567881:ℚ)/13112500000),((5281324263:ℚ)/10300000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((431293143:ℚ)/625000000),((-6502858656358540096638308342062507681982148301652397674329:ℚ)/18686199592958068847656250000000000000000000000000000000000),((-62597689275757893249760613:ℚ)/184832000000000000000000000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((119649097:ℚ)/200000000),((3101911713:ℚ)/5000000000),((76149699:ℚ)/178000000),((5341911713:ℚ)/10490000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((6645974611:ℚ)/10000000000),((-1671438971229398634999647946213230129798196639457364611:ℚ)/4848428703556250000000000000000000000000000000000000000),((-62602314444137155137233013:ℚ)/184832000000000000000000000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((122073593:ℚ)/200000000),((3162455517:ℚ)/5000000000),((230873593:ℚ)/543500000),((5402455517:ℚ)/10680000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3191450383:ℚ)/5000000000),((-12219595431274475234065616444185761910262993421592155697:ℚ)/35766067321627734375000000000000000000000000000000000000),((-62593340331356080035325853:ℚ)/184832000000000000000000000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((6224815309:ℚ)/10000000000),((805739503:ℚ)/1250000000),((1666402187:ℚ)/3950000000),((1365739503:ℚ)/2717500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((6110350267:ℚ)/10000000000),((-3613318141853413304920535336429526682119287507141489246161:ℚ)/10666984830157470703125000000000000000000000000000000000000),((-3910674861580441402937293:ℚ)/11552000000000000000000000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/4),((5:ℚ)/16),((6345866603:ℚ)/10000000000),((6566842737:ℚ)/10000000000),((3928622201:ℚ)/9375000000),((1578120391:ℚ)/3160000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5826954397:ℚ)/10000000000),((-800924389107104413774943425848407185114843808141637733:ℚ)/2383813261985778808593750000000000000000000000000000000),((-250138861784605691312126613:ℚ)/739328000000000000000000000)⟩
theorem valid5 : Valid source36 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source36 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((404177373:ℚ)/625000000),((1337539043:ℚ)/2000000000),((744177373:ℚ)/1787500000),((2233539043:ℚ)/4500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1106201391:ℚ)/2000000000),((-481966145532954478881978583421028386762720415919161053:ℚ)/1445683392333984375000000000000000000000000000000000000),((-9997619184447527460338973:ℚ)/29573120000000000000000000)⟩
theorem valid6 : Valid source36 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((1317546707:ℚ)/2000000000),((3404238611:ℚ)/5000000000),((2405546707:ℚ)/5815000000),((513112601:ℚ)/1040000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1305083431:ℚ)/2500000000),((-34364993968222909012412372063416557731049792308354636027:ℚ)/103845070016796875000000000000000000000000000000000000000),((-62422035930323356286317117:ℚ)/184832000000000000000000000)⟩
theorem valid7 : Valid source36 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((6708557149:ℚ)/10000000000),((433074517:ℚ)/625000000),((12148557149:ℚ)/29550000000),((713074517:ℚ)/1453750000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4892089143:ℚ)/10000000000),((-995528760373700888252025827230245466576976121434604761762981:ℚ)/3029558939424902343750000000000000000000000000000000000000000),((-974148227765934086986603:ℚ)/2888000000000000000000000)⟩
theorem valid8 : Valid source36 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source36 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((17073281:ℚ)/25000000),((7170434411:ℚ)/10000000000),((30673281:ℚ)/76250000),((3883478137:ℚ)/7880000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4542423323:ℚ)/10000000000),((-17267141126820581985037592891316317514807263682198831:ℚ)/53765293145751953125000000000000000000000000000000000),((-245852063012178614654442317:ℚ)/739328000000000000000000000)⟩
theorem valid9 : Valid source36 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source36 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((7070631007:ℚ)/10000000000),((1530449249:ℚ)/2000000000),((12510631007:ℚ)/32400000000),((2426449249:ℚ)/4880000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((3754405097:ℚ)/10000000000),((-40619888704732987917673950061188481557683207089199747143309:ℚ)/131832797400000000000000000000000000000000000000000000000000),((-315308548193170819:ℚ)/972800000000000000)⟩
theorem valid10 : Valid source36 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((377629087:ℚ)/500000000),((299153777:ℚ)/312500000),((649629087:ℚ)/2000000000),((439153777:ℚ)/810000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((1117653221:ℚ)/10000000000),((-14316319848751802152689130113374191885156286188081214269:ℚ)/54675000000000000000000000000000000000000000000000000000),((-16489537107866179:ℚ)/48640000000000000)⟩
theorem valid11 : Valid source36 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((9473675823:ℚ)/10000000000),((13397030249:ℚ)/10000000000),((14913675823:ℚ)/55200000000),((17877030249:ℚ)/32000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-88147973377477700825637253053938347165369577348724701549:ℚ)/394210800000000000000000000000000000000000000000000000000),((-17432401:ℚ)/51200000)⟩
theorem valid12 : Valid source36 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source36 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source36 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source36 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source36GroupedC21
#check @N11Formalization.C450Source36GroupedC21.bound
#print axioms N11Formalization.C450Source36GroupedC21.valid0
#print axioms N11Formalization.C450Source36GroupedC21.valid1
#print axioms N11Formalization.C450Source36GroupedC21.valid2
#print axioms N11Formalization.C450Source36GroupedC21.valid3
#print axioms N11Formalization.C450Source36GroupedC21.valid4
#print axioms N11Formalization.C450Source36GroupedC21.valid5
#print axioms N11Formalization.C450Source36GroupedC21.valid6
#print axioms N11Formalization.C450Source36GroupedC21.valid7
#print axioms N11Formalization.C450Source36GroupedC21.valid8
#print axioms N11Formalization.C450Source36GroupedC21.valid9
#print axioms N11Formalization.C450Source36GroupedC21.valid10
#print axioms N11Formalization.C450Source36GroupedC21.valid11
#print axioms N11Formalization.C450Source36GroupedC21.valid12
#print axioms N11Formalization.C450Source36GroupedC21.bound
#print axioms N11Formalization.C450Source36GroupedC21.endpoint_checks
