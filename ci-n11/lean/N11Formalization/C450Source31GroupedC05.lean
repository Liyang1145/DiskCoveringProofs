import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((3470004069:ℚ)/5000000000),((896087519:ℚ)/1250000000),((-2108262557:ℚ)/3100000000),((-9523348253:ℚ)/16850000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((104957059:ℚ)/250000000),((13570267885617544679138874852259013587:ℚ)/37076729468750000000000000000000000000),((32770063312117577516569709:ℚ)/57760000000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((882481053:ℚ)/1250000000),((3614272371:ℚ)/5000000000),((-8522817113:ℚ)/12637500000),((-7307291583:ℚ)/12756250000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((3792908937:ℚ)/10000000000),((296483796352417349948517063086437859402890685060314818871:ℚ)/819747793686962127685546875000000000000000000000000000000),((2039903408097355571808621:ℚ)/3610000000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((7119753137:ℚ)/10000000000),((911047571:ℚ)/1250000000),((-2153142713:ℚ)/3189062500),((-59117284507:ℚ)/103000000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((1786999273:ℚ)/5000000000),((201511722631682192683697845398739690615630095611603930290481:ℚ)/557563951750000000000000000000000000000000000000000000000000),((130324516668779368204595861:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((7179647951:ℚ)/10000000000),((58785663:ℚ)/80000000),((-139236989:ℚ)/206000000),((-59776127461:ℚ)/103950000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((1670733267:ℚ)/5000000000),((599727659663127575278459502202693094855342143780145741:ℚ)/1660528921508789062500000000000000000000000000000000000),((130092680807552044370110869:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((7239533141:ℚ)/10000000000),((7408026897:ℚ)/10000000000),((-17584080691:ℚ)/25987500000),((-60434864551:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3092235353:ℚ)/10000000000),((5413611713942050841700536320214789311865893118861231272821067:ℚ)/14998953932943750000000000000000000000000000000000000000000000),((129858310677241155849382989:ℚ)/231040000000000000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((1824852243:ℚ)/2500000000),((7467837861:ℚ)/10000000000),((-17763513583:ℚ)/26225000000),((-15273374673:ℚ)/26462500000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1410938623:ℚ)/5000000000),((43823662221135844220960212722419423217939927538762878228211:ℚ)/121492122290490722656250000000000000000000000000000000000000),((8101337901038879484161181:ℚ)/14440000000000000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((3679637851:ℚ)/5000000000),((3763820493:ℚ)/5000000000),((-8971461479:ℚ)/13231250000),((-30876016361:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((315450503:ℚ)/1250000000),((6725293318756133224030758523223460513111345888588736596933:ℚ)/18655242162500000000000000000000000000000000000000000000000),((32345492036404784546457069:ℚ)/57760000000000000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((927391697:ℚ)/1250000000),((3883389589:ℚ)/5000000000),((-9330168767:ℚ)/13350000000),((-7801308667:ℚ)/13825000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((546502629:ℚ)/2500000000),((33363389279159891059529407059002251800163887611559391027:ℚ)/89989247167968750000000000000000000000000000000000000000),((2018059848897179969777621:ℚ)/3610000000000000000000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((7658481159:ℚ)/10000000000),((8005807487:ℚ)/10000000000),((-19377422461:ℚ)/27650000000),((-65043292749:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((1913338436205912776903003064843954021261463305016675890909359:ℚ)/5174676707200000000000000000000000000000000000000000000000000),((355073:ℚ)/640000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((394885233:ℚ)/500000000),((2240254327:ℚ)/2500000000),((-5560762981:ℚ)/7150000000),((-1127912521:ℚ)/2160000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((33884672683656455245001342812609841475374053518921167:ℚ)/83397600000000000000000000000000000000000000000000000),((355073:ℚ)/640000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((2213394709:ℚ)/2500000000),((10868450233:ℚ)/10000000000),((-27965350699:ℚ)/32400000000),((-19547341799:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((71717925635239293540126322961888640941:ℚ)/162000000000000000000000000000000000000),((355073:ℚ)/640000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((2152391429:ℚ)/2000000000),((7338577503:ℚ)/5000000000),((-19695732509:ℚ)/20000000000),((-19836305719:ℚ)/44160000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((165437123538441947890952117:ℚ)/325017600000000000000000000),((355073:ℚ)/640000)⟩
theorem valid11 : Valid source31 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source31 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source31 nn0 nn1 Qcell ((2079:ℚ)/3200) ((2117:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source31 nn0 nn1 Qcell ((2117:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source31 nn0 nn1 Qcell ((2117:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC05
#check @N11Formalization.C450Source31GroupedC05.bound
#print axioms N11Formalization.C450Source31GroupedC05.valid0
#print axioms N11Formalization.C450Source31GroupedC05.valid1
#print axioms N11Formalization.C450Source31GroupedC05.valid2
#print axioms N11Formalization.C450Source31GroupedC05.valid3
#print axioms N11Formalization.C450Source31GroupedC05.valid4
#print axioms N11Formalization.C450Source31GroupedC05.valid5
#print axioms N11Formalization.C450Source31GroupedC05.valid6
#print axioms N11Formalization.C450Source31GroupedC05.valid7
#print axioms N11Formalization.C450Source31GroupedC05.valid8
#print axioms N11Formalization.C450Source31GroupedC05.valid9
#print axioms N11Formalization.C450Source31GroupedC05.valid10
#print axioms N11Formalization.C450Source31GroupedC05.valid11
#print axioms N11Formalization.C450Source31GroupedC05.bound
#print axioms N11Formalization.C450Source31GroupedC05.endpoint_checks
