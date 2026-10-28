import N11Formalization.C450Source20Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source20GroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source20Data
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((5696549641:ℚ)/10000000000),((3121701033:ℚ)/5000000000),((20929648923:ℚ)/35600000000),((3729701033:ℚ)/4960000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3617101783:ℚ)/5000000000),((-86599840481025244673298315605274839:ℚ)/5639752000000000000000000000000000000),((-1331305064320615065299497813:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source20 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source20 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((6173582553:ℚ)/10000000000),((1620454847:ℚ)/2500000000),((67082242977:ℚ)/110600000000),((641484949:ℚ)/890000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1245376693:ℚ)/2000000000),((-99685184670433154737169761936809495973618489337792890143:ℚ)/4227809425000000000000000000000000000000000000000000000000),((-334711736783795132116469253:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid source20 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((6411993627:ℚ)/10000000000),((6720175439:ℚ)/10000000000),((69227942643:ℚ)/114400000000),((7936175439:ℚ)/11060000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((2833442271:ℚ)/5000000000),((-112510303257288867142748173681545513408218159675970336893:ℚ)/4678731200000000000000000000000000000000000000000000000000),((-5360609753069122324501785957:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source20 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source20 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source20 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((6650343849:ℚ)/10000000000),((3419666189:ℚ)/5000000000),((71373094641:ℚ)/116300000000),((4027666189:ℚ)/5720000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1010534097:ℚ)/2000000000),((-33808764442919765401223203975742388380901263868868947231:ℚ)/1228935739843750000000000000000000000000000000000000000000),((-70724733233065211488499103:ℚ)/194560000000000000000000000)⟩
theorem valid3 : Valid source20 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((3384749009:ℚ)/5000000000),((6958476169:ℚ)/10000000000),((12074247027:ℚ)/19700000000),((8174476169:ℚ)/11630000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2359310501:ℚ)/5000000000),((-164799508207468108614401037617831718633992114692946997:ℚ)/5972947656250000000000000000000000000000000000000000000),((-5377259148033175555625929237:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source20 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((861079891:ℚ)/1250000000),((88470093:ℚ)/125000000),((9189719019:ℚ)/15012500000),((103670093:ℚ)/147750000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((4361143393:ℚ)/10000000000),((-292381768802275765543236454001004459788408484685723509:ℚ)/10573264166259765625000000000000000000000000000000000000),((-840510423992800615136333:ℚ)/2310400000000000000000000)⟩
theorem valid5 : Valid source20 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source20 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((1401553561:ℚ)/2000000000),((359836339:ℚ)/500000000),((14917982049:ℚ)/24400000000),((420636339:ℚ)/600500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((993471941:ℚ)/2500000000),((-1257352560118629528068437427324071560161245292609833319:ℚ)/45396200000000000000000000000000000000000000000000000000),((-13452756221942497852289357:ℚ)/36966400000000000000000000)⟩
theorem valid6 : Valid source20 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source20 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((890860579:ℚ)/1250000000),((7315834741:ℚ)/10000000000),((3152581737:ℚ)/5162500000),((8531834741:ℚ)/12200000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1773539531:ℚ)/5000000000),((-2980165542412680892887474159254090280404210847359303:ℚ)/107490534973144531250000000000000000000000000000000000),((-5382766535706170188304442077:ℚ)/14786560000000000000000000000)⟩
theorem valid7 : Valid source20 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source20 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((3622995079:ℚ)/5000000000),((3717465921:ℚ)/5000000000),((38366955711:ℚ)/62900000000),((617923703:ℚ)/885000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((3064193939:ℚ)/10000000000),((-21064612432874448598089226715129474198745358470536849:ℚ)/759454922485351562500000000000000000000000000000000000),((-1346064728167493631136353797:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source20 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source20 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source20 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((3682542449:ℚ)/5000000000),((959136923:ℚ)/1250000000),((1440847483:ℚ)/2400000000),((1111136923:ℚ)/1572500000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((249280743:ℚ)/1000000000),((-359958414689575932816795024831491942811480569465911:ℚ)/14400000000000000000000000000000000000000000000000000),((-44254671030075559:ℚ)/121600000000000000)⟩
theorem valid9 : Valid source20 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source20 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source20 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((950405491:ℚ)/1250000000),((9577265527:ℚ)/10000000000),((9993649419:ℚ)/20000000000),((10793265527:ℚ)/12960000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((772817884480993050707857635789643:ℚ)/375000000000000000000000000000000000),((-374325103:ℚ)/1024000000)⟩
theorem valid10 : Valid source20 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source20 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((4753692867:ℚ)/5000000000),((267643087:ℚ)/200000000),((16181078601:ℚ)/36800000000),((291963087:ℚ)/320000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((4091037804624752459799451:ℚ)/169280000000000000000000000),((-374325103:ℚ)/1024000000)⟩
theorem valid11 : Valid source20 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source20 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source20 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source20 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source20 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source20 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source20 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source20 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source20 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source20 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source20 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source20 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source20GroupedC26
#check @N11Formalization.C450Source20GroupedC26.bound
#print axioms N11Formalization.C450Source20GroupedC26.valid0
#print axioms N11Formalization.C450Source20GroupedC26.valid1
#print axioms N11Formalization.C450Source20GroupedC26.valid2
#print axioms N11Formalization.C450Source20GroupedC26.valid3
#print axioms N11Formalization.C450Source20GroupedC26.valid4
#print axioms N11Formalization.C450Source20GroupedC26.valid5
#print axioms N11Formalization.C450Source20GroupedC26.valid6
#print axioms N11Formalization.C450Source20GroupedC26.valid7
#print axioms N11Formalization.C450Source20GroupedC26.valid8
#print axioms N11Formalization.C450Source20GroupedC26.valid9
#print axioms N11Formalization.C450Source20GroupedC26.valid10
#print axioms N11Formalization.C450Source20GroupedC26.valid11
#print axioms N11Formalization.C450Source20GroupedC26.bound
#print axioms N11Formalization.C450Source20GroupedC26.endpoint_checks
