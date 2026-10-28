import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((2003:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((7089522633:ℚ)/10000000000),((45378639:ℚ)/62500000),((-115335917:ℚ)/124000000),((-40986658431:ℚ)/50075000000),((398569427:ℚ)/400000000),(1:ℚ),((845998389:ℚ)/10000000000),((3686021317:ℚ)/10000000000),((11432855618492000555549816316656394964653:ℚ)/29880440029750000000000000000000000000000),((114571787192744214829131:ℚ)/115520000000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((2003:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((2003:ℚ)/3200),((1011:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((7149092511:ℚ)/10000000000),((7320063543:ℚ)/10000000000),((-18632190629:ℚ)/20030000000),((-13801215859:ℚ)/16850000000),((9929701407:ℚ)/10000000000),((62276473:ℚ)/62500000),((18538009:ℚ)/156250000),((865491689:ℚ)/2500000000),((85207969934411935006328611651259885912277277934104617991:ℚ)/222814116160244873046875000000000000000000000000000000000),((2942524843693149597527699739:ℚ)/2957312000000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((2003:ℚ)/3200) ((1011:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1011:ℚ)/1600),((4063:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7208658709:ℚ)/10000000000),((7349803447:ℚ)/10000000000),((-18721410341:ℚ)/20220000000),((-2460035939:ℚ)/2987500000),((4956442379:ℚ)/5000000000),((2482425353:ℚ)/2500000000),((1320924081:ℚ)/10000000000),((1611526521:ℚ)/5000000000),((69565081410252119096916093952278127087309005848797218158311:ℚ)/184458762347034375000000000000000000000000000000000000000000),((2947275438784593112119094299:ℚ)/2957312000000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4063:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((4063:ℚ)/6400),((2041:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((361922023:ℚ)/500000000),((7379542861:ℚ)/10000000000),((-18810628583:ℚ)/20315000000),((-2101454161:ℚ)/2551250000),((247409071:ℚ)/250000000),((9912884763:ℚ)/10000000000),((1440948769:ℚ)/10000000000),((774239077:ℚ)/2500000000),((1461064721331365024409780261580227665300772880021627976612879:ℚ)/3874815754641803906250000000000000000000000000000000000000000),((2952030734430212995487932131:ℚ)/2957312000000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((4063:ℚ)/6400) ((2041:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2041:ℚ)/3200),((4101:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((726822133:ℚ)/1000000000),((3704640897:ℚ)/5000000000),((-9449922691:ℚ)/10205000000),((-4223754931:ℚ)/5126250000),((4940065779:ℚ)/5000000000),((1979272569:ℚ)/2000000000),((774947369:ℚ)/5000000000),((2965685969:ℚ)/10000000000),((43195624875310130262524300524595400333387281253462244631551:ℚ)/114576082046888718750000000000000000000000000000000000000000),((739197682958763776082285099:ℚ)/739328000000000000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4101:ℚ)/6400),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((7298001331:ℚ)/10000000000),((7439020251:ℚ)/10000000000),((-18989060753:ℚ)/20505000000),((-42446009317:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((9880131563:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((282852113:ℚ)/1000000000),((215480492298781964548251715640905657471693039276578528946123:ℚ)/571654712008835156250000000000000000000000000000000000000000),((2961555431568751865256634611:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((4101:ℚ)/6400) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((3663890237:ℚ)/5000000000),((1874623941:ℚ)/2500000000),((-4791871823:ℚ)/5150000000),((-21327231659:ℚ)/25987500000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((2684557719:ℚ)/10000000000),((29120114269187388982452346896571106587554081032040210257:ℚ)/76262126962280273437500000000000000000000000000000000000),((185693683840104915547155891:ℚ)/184832000000000000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((7387336237:ℚ)/10000000000),((1889492363:ℚ)/2500000000),((-4836477089:ℚ)/5197500000),((-43071353659:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((1185612841:ℚ)/5000000000),((1595439830341786476270997911367557588326935374185255074789:ℚ)/4180252428493066406250000000000000000000000000000000000000),((186291329413029028322891859:ℚ)/184832000000000000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((930861089:ℚ)/1250000000),((1919227887:ℚ)/2500000000),((-4925683661:ℚ)/5245000000),((-5436027623:ℚ)/6675000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((2010683117:ℚ)/10000000000),((8382047714710284633829864996896878663098214070663576674357:ℚ)/21429782486083593750000000000000000000000000000000000000000),((1034428869:ℚ)/1024000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((267:ℚ)/400),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((7565984147:ℚ)/10000000000),((1630523197:ℚ)/2000000000),((-4225969591:ℚ)/4272000000),((-4029262639:ℚ)/5200000000),((9558216781:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((149176903:ℚ)/500000000),((236619761:ℚ)/2500000000),((110343844173500939425143088981163595754211127526184940727:ℚ)/247048208409600000000000000000000000000000000000000000000),((1034428869:ℚ)/1024000000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((4021125347:ℚ)/5000000000),((1820755311:ℚ)/2000000000),(-1:ℚ),((-23827877429:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((51223739952031512200225441962558501:ℚ)/109350000000000000000000000000000000),((1034428869:ℚ)/1024000000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((1798867341:ℚ)/2000000000),((275135883:ℚ)/250000000),(-1:ℚ),((-10864071387:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((29127020311617416350286862874391969:ℚ)/60000000000000000000000000000000000),((1034428869:ℚ)/1024000000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((2179463391:ℚ)/2000000000),((7403690763:ℚ)/5000000000),(-1:ℚ),((-4509414579:ℚ)/7360000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((874285362012116624437257:ℚ)/1692800000000000000000000),((1034428869:ℚ)/1024000000)⟩
theorem valid12 : Valid source28 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet12 valid12
private theorem node1_3 :
    CellBound source28 nn0 nn1 Qcell ((2003:ℚ)/3200) ((4063:ℚ)/6400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((4063:ℚ)/6400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source28 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source28 nn0 nn1 Qcell ((4063:ℚ)/6400) ((103:ℚ)/160) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source28 nn0 nn1 Qcell ((2079:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((81:ℚ)/100) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((69:ℚ)/50) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_13
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_13
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12]
theorem packet_count : packets.length = 13 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC02
#check @N11Formalization.C450Source28GroupedC02.bound
#print axioms N11Formalization.C450Source28GroupedC02.valid0
#print axioms N11Formalization.C450Source28GroupedC02.valid1
#print axioms N11Formalization.C450Source28GroupedC02.valid2
#print axioms N11Formalization.C450Source28GroupedC02.valid3
#print axioms N11Formalization.C450Source28GroupedC02.valid4
#print axioms N11Formalization.C450Source28GroupedC02.valid5
#print axioms N11Formalization.C450Source28GroupedC02.valid6
#print axioms N11Formalization.C450Source28GroupedC02.valid7
#print axioms N11Formalization.C450Source28GroupedC02.valid8
#print axioms N11Formalization.C450Source28GroupedC02.valid9
#print axioms N11Formalization.C450Source28GroupedC02.valid10
#print axioms N11Formalization.C450Source28GroupedC02.valid11
#print axioms N11Formalization.C450Source28GroupedC02.valid12
#print axioms N11Formalization.C450Source28GroupedC02.bound
#print axioms N11Formalization.C450Source28GroupedC02.endpoint_checks
