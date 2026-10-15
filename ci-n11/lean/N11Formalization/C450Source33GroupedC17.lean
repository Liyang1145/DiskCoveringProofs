import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC17
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨(0:ℚ),((1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),(0:ℚ),((1:ℚ)/16),((5986959697:ℚ)/10000000000),((3158472981:ℚ)/5000000000),((496:ℚ)/2575),((13398472981:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((6636357837:ℚ)/10000000000),((-1417295386163355750761986672729879762641473:ℚ)/10081062211200000000000000000000000000000000),((-871963048659422473485704711:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((6229469567:ℚ)/10000000000),((6437920013:ℚ)/10000000000),((992:ℚ)/5245),((26917920013:ℚ)/103000000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((3049833899:ℚ)/5000000000),((-1053325647018077264541105238685365173953403241:ℚ)/7653867353275625000000000000000000000000000000),((-3625005244864178606934487319:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),(0:ℚ),((1:ℚ)/16),((1587646067:ℚ)/2500000000),((819851597:ℚ)/1250000000),((248:ℚ)/1335),((3379851597:ℚ)/13112500000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((1453916029:ℚ)/2500000000),((-275627330129620270294439662814923114225201:ℚ)/2045430859312792968750000000000000000000000),((-57610054775296545161281559:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),(0:ℚ),((1:ℚ)/16),((3235806197:ℚ)/5000000000),((1335925733:ℚ)/2000000000),((992:ℚ)/5435),((1810641911:ℚ)/7120000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2759518421:ℚ)/5000000000),((-10745412166559932015104830838217257408540511:ℚ)/81387673194104000000000000000000000000000000),((-149952033051149779659486439:ℚ)/591462400000000000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),(0:ℚ),((1:ℚ)/16),((6592558657:ℚ)/10000000000),((272014871:ℚ)/400000000),((496:ℚ)/2765),((1091214871:ℚ)/4348000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((5207587373:ℚ)/10000000000),((-27710819279378636371969830143781477257393:ℚ)/214090652335192500000000000000000000000000),((-6096448182188331278082991:ℚ)/23658496000000000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),(0:ℚ),((1:ℚ)/16),((1678356857:ℚ)/2500000000),((3460522959:ℚ)/5000000000),((992:ℚ)/5625),((13700522959:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1219608733:ℚ)/2500000000),((-2624223057974076601948611615567756598667:ℚ)/20668645019531250000000000000000000000000),((-967871016119117078592296031:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),(0:ℚ),((1:ℚ)/16),((6834222771:ℚ)/10000000000),((3520827319:ℚ)/5000000000),((124:ℚ)/715),((13760827319:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((90553523:ℚ)/200000000),((-480405309632037034657073848248248247055727:ℚ)/3855155712890625000000000000000000000000000),((-51742305070162275026089269:ℚ)/194560000000000000000000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),(0:ℚ),((1:ℚ)/16),((6954948469:ℚ)/10000000000),((7282688809:ℚ)/10000000000),((496:ℚ)/2955),((27762688809:ℚ)/114400000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4149789723:ℚ)/10000000000),((-22549317062329882249435798071739786022043247:ℚ)/187608278972400000000000000000000000000000000),((-209422875490263272669084149:ℚ)/778240000000000000000000000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),(0:ℚ),((1:ℚ)/16),((1439240959:ℚ)/2000000000),((470218637:ℚ)/625000000),((248:ℚ)/1525),((1750218637:ℚ)/7387500000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((409298993:ℚ)/1250000000),((-599727226504225781118908057828754313009:ℚ)/5161468141992187500000000000000000000000),((-16012101105035133669439919:ℚ)/57760000000000000000000000)⟩
theorem valid8 : Valid source33 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source33 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),(0:ℚ),((1:ℚ)/16),((7437221891:ℚ)/10000000000),((8004523723:ℚ)/10000000000),((62:ℚ)/405),((28484523723:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((259175787:ℚ)/1250000000),((-359617240099553509447110183185750904323051:ℚ)/3295819935000000000000000000000000000000000),((-55769005735374341:ℚ)/194560000000000000)⟩
theorem valid9 : Valid source33 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(0:ℚ),((1:ℚ)/16),((7918624879:ℚ)/10000000000),((4961411091:ℚ)/5000000000),((31:ℚ)/250),((15201411091:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-1304359886764121046605017323246828331:ℚ)/14580000000000000000000000000000000000),((-300475093:ℚ)/1024000000)⟩
theorem valid10 : Valid source33 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(0:ℚ),((1:ℚ)/16),((393522573:ℚ)/400000000),((13744176951:ℚ)/10000000000),((31:ℚ)/345),((34224176951:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-1063475200638023367858852931671651102760199:ℚ)/15768432000000000000000000000000000000000000),((-300475093:ℚ)/1024000000)⟩
theorem valid11 : Valid source33 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC17
#check @N11Formalization.C450Source33GroupedC17.bound
#print axioms N11Formalization.C450Source33GroupedC17.valid0
#print axioms N11Formalization.C450Source33GroupedC17.valid1
#print axioms N11Formalization.C450Source33GroupedC17.valid2
#print axioms N11Formalization.C450Source33GroupedC17.valid3
#print axioms N11Formalization.C450Source33GroupedC17.valid4
#print axioms N11Formalization.C450Source33GroupedC17.valid5
#print axioms N11Formalization.C450Source33GroupedC17.valid6
#print axioms N11Formalization.C450Source33GroupedC17.valid7
#print axioms N11Formalization.C450Source33GroupedC17.valid8
#print axioms N11Formalization.C450Source33GroupedC17.valid9
#print axioms N11Formalization.C450Source33GroupedC17.valid10
#print axioms N11Formalization.C450Source33GroupedC17.valid11
#print axioms N11Formalization.C450Source33GroupedC17.bound
#print axioms N11Formalization.C450Source33GroupedC17.endpoint_checks
