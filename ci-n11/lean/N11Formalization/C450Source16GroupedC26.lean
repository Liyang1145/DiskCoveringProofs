import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC26
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨((9:ℚ)/16),((5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((9:ℚ)/16),((5:ℚ)/8),((362955197:ℚ)/625000000),((1585980647:ℚ)/2500000000),((3826596773:ℚ)/6675000000),((1825980647:ℚ)/2480000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((27387741:ℚ)/39062500),((-12120929430852397023942139213657:ℚ)/929402490234375000000000000000000),((-13322587897256621581434269:ℚ)/48640000000000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((12272553:ℚ)/19531250),((3290988121:ℚ)/5000000000),((127952977:ℚ)/216015625),((3770988121:ℚ)/5340000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1194865337:ℚ)/2000000000),((-176212373730264300523586498867889077034359235133:ℚ)/9449890460819005966186523437500000000000000000000),((-53627460967225779966909981:ℚ)/194560000000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((9:ℚ)/16),((5:ℚ)/8),((5217291:ℚ)/8000000),((1363998599:ℚ)/2000000000),((4920329:ℚ)/8320000),((1555998599:ℚ)/2212000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5392246239:ℚ)/10000000000),((-65873319462389481438938485232825409010811:ℚ)/3461120000000000000000000000000000000000000),((-8602448699213205596360541:ℚ)/31129600000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((1351928519:ℚ)/2000000000),((1734747167:ℚ)/2500000000),((13959356671:ℚ)/23260000000),((1974747167:ℚ)/2860000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((237353529:ℚ)/500000000),((-15785229756611452318439300286454680635504283772324819:ℚ)/737361443906250000000000000000000000000000000000000000),((-13482985192416265722008749:ℚ)/48640000000000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((6878644017:ℚ)/10000000000),((352898821:ℚ)/500000000),((70867796153:ℚ)/118200000000),((400898821:ℚ)/581500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4392173703:ℚ)/10000000000),((-2080003225559925260922232748148637320002992138769652677:ℚ)/96761752031250000000000000000000000000000000000000000000),((-539995268766337250745381:ℚ)/1945600000000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((6997637331:ℚ)/10000000000),((7176956627:ℚ)/10000000000),((71938735979:ℚ)/120100000000),((8136956627:ℚ)/11820000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((4008189937:ℚ)/10000000000),((-8758161435856326598036101084641770012309028294405283071:ℚ)/406013343984375000000000000000000000000000000000000000000),((-216266330400155141575217589:ℚ)/778240000000000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((9:ℚ)/16),((5:ℚ)/8),((7116622923:ℚ)/10000000000),((7295929643:ℚ)/10000000000),((73009606307:ℚ)/122000000000),((8255929643:ℚ)/12010000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1792876583:ℚ)/5000000000),((-3068973988929021897423284472467351882474387415483600829:ℚ)/141863125000000000000000000000000000000000000000000000000),((-216532433053978734066944709:ℚ)/778240000000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((9:ℚ)/16),((5:ℚ)/8),((1808900289:ℚ)/2500000000),((7414895801:ℚ)/10000000000),((2645728943:ℚ)/4425000000),((8374895801:ℚ)/12200000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((3109191153:ℚ)/10000000000),((-4077137199814613414321813256392765912501807147849:ℚ)/188030090332031250000000000000000000000000000000000),((-216796416684391287016741341:ℚ)/778240000000000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((9:ℚ)/16),((5:ℚ)/8),((735457237:ℚ)/1000000000),((7533855413:ℚ)/10000000000),((7515115133:ℚ)/12580000000),((8493855413:ℚ)/12390000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((637067787:ℚ)/2500000000),((-194080412020270291674943033551566570867481037947:ℚ)/8934763793945312500000000000000000000000000000000),((-11424120127977107952797191:ℚ)/40960000000000000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((9:ℚ)/16),((5:ℚ)/8),((7473536883:ℚ)/10000000000),((7771756151:ℚ)/10000000000),((76221831947:ℚ)/129600000000),((8731756151:ℚ)/12580000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((73072539:ℚ)/400000000),((-125442832249294298043581152256685199020316034585647183:ℚ)/6298560000000000000000000000000000000000000000000000000),((-13586115353604903:ℚ)/48640000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((9:ℚ)/16),((5:ℚ)/8),((481965437:ℚ)/625000000),((4837137751:ℚ)/5000000000),((4897688933:ℚ)/10000000000),((5317137751:ℚ)/6480000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-75142598874809071792325697607891:ℚ)/46875000000000000000000000000000000),((-286574437:ℚ)/1024000000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((9:ℚ)/16),((5:ℚ)/8),((384561009:ℚ)/400000000),((2695446121:ℚ)/2000000000),((3819449081:ℚ)/8832000000),((2887446121:ℚ)/3200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((63725625974949822270557:ℚ)/4875264000000000000000000),((-286574437:ℚ)/1024000000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source16 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source16 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC26
#check @N11Formalization.C450Source16GroupedC26.bound
#print axioms N11Formalization.C450Source16GroupedC26.valid0
#print axioms N11Formalization.C450Source16GroupedC26.valid1
#print axioms N11Formalization.C450Source16GroupedC26.valid2
#print axioms N11Formalization.C450Source16GroupedC26.valid3
#print axioms N11Formalization.C450Source16GroupedC26.valid4
#print axioms N11Formalization.C450Source16GroupedC26.valid5
#print axioms N11Formalization.C450Source16GroupedC26.valid6
#print axioms N11Formalization.C450Source16GroupedC26.valid7
#print axioms N11Formalization.C450Source16GroupedC26.valid8
#print axioms N11Formalization.C450Source16GroupedC26.valid9
#print axioms N11Formalization.C450Source16GroupedC26.valid10
#print axioms N11Formalization.C450Source16GroupedC26.valid11
#print axioms N11Formalization.C450Source16GroupedC26.bound
#print axioms N11Formalization.C450Source16GroupedC26.endpoint_checks
