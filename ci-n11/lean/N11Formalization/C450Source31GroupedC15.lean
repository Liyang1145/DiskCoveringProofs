import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/8),((-1:ℚ)/16),((3079112441:ℚ)/5000000000),((647878491:ℚ)/1000000000),((280121509:ℚ)/5150000000),((6520887559:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1252289673:ℚ)/2000000000),((-10344310236821146391401620039624478733126714868795583:ℚ)/853692968750000000000000000000000000000000000000000000),((-649403576342214816923368189:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((6400111163:ℚ)/10000000000),((6599443361:ℚ)/10000000000),((2680556639:ℚ)/52450000000),((12799888837:ℚ)/103000000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2847970989:ℚ)/5000000000),((-2313660227573776119530435269902196323874093969606829357:ℚ)/225453251757812500000000000000000000000000000000000000000),((-2771950748682728059135464261:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((260837279:ℚ)/400000000),((3360016161:ℚ)/5000000000),((1279983839:ℚ)/26700000000),((507162721:ℚ)/4196000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((269699653:ℚ)/500000000),((-9197300400554902711252911585099381732679887752584639:ℚ)/1101514062500000000000000000000000000000000000000000000),((-4574983084564369006078029:ℚ)/23658496000000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((6641677239:ℚ)/10000000000),((1710138887:ℚ)/2500000000),((609861113:ℚ)/13587500000),((4186107587:ℚ)/35600000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((5076179363:ℚ)/10000000000),((-102217019380894179056113528922801140260779981159110139:ℚ)/15678289831542968750000000000000000000000000000000000000),((-2946945505845406601635928349:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((6762351047:ℚ)/10000000000),((3480508263:ℚ)/5000000000),((1159491737:ℚ)/27650000000),((12437648953:ℚ)/108700000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4739267839:ℚ)/10000000000),((-200798164259127322350236755094390955100468642843091:ℚ)/42129797363281250000000000000000000000000000000000000),((-8406361621442667759049461:ℚ)/40960000000000000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((3441478599:ℚ)/5000000000),((7081418499:ℚ)/10000000000),((2198581501:ℚ)/56250000000),((6158521401:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4378808449:ℚ)/10000000000),((-496288542943018615846835701147250565674769076681061:ℚ)/160932540893554687500000000000000000000000000000000000),((-780654981366548559599206269:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((3501749613:ℚ)/5000000000),((900220561:ℚ)/1250000000),((259779439:ℚ)/7150000000),((2032750129:ℚ)/18750000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((3988375371:ℚ)/10000000000),((-3352898346026498248445500231231805583756650141871253:ℚ)/2284536718750000000000000000000000000000000000000000000),((-802679464888356142541231061:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((356199021:ℚ)/500000000),((7442299589:ℚ)/10000000000),((1837700411:ℚ)/59100000000),((603800979:ℚ)/5720000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3558065219:ℚ)/10000000000),((59647668834193120805870971805653654466473724468238127:ℚ)/35837685937500000000000000000000000000000000000000000000),((-8247481018355516305065429:ℚ)/36966400000000000000000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((736477237:ℚ)/1000000000),((7682642207:ℚ)/10000000000),((1597357793:ℚ)/61000000000),((1183522763:ℚ)/11820000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((99778949:ℚ)/400000000),((6366780715889574096847413208656062370179572571131371181:ℚ)/1418631250000000000000000000000000000000000000000000000000),((-34760788994058212850234661:ℚ)/147865600000000000000000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((1521071047:ℚ)/2000000000),((408140961:ℚ)/500000000),((55859039:ℚ)/3240000000),((2318928953:ℚ)/24400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2829272290365865168812522224898235479156491537483:ℚ)/291600000000000000000000000000000000000000000000000),((-50552987:ℚ)/204800000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((101074613:ℚ)/125000000),((10078872043:ℚ)/10000000000),((-266290681:ℚ)/21600000000),((138925387:ℚ)/1620000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3909562055499160955046203213992273610077858454555401:ℚ)/145800000000000000000000000000000000000000000000000000),((-50552987:ℚ)/204800000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((10003022207:ℚ)/10000000000),((694927269:ℚ)/500000000),((-230927269:ℚ)/4000000000),((9196977793:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((901974706156541179520869512411109:ℚ)/16000000000000000000000000000000000),((-50552987:ℚ)/204800000)⟩
theorem valid11 : Valid source31 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC15
#check @N11Formalization.C450Source31GroupedC15.bound
#print axioms N11Formalization.C450Source31GroupedC15.valid0
#print axioms N11Formalization.C450Source31GroupedC15.valid1
#print axioms N11Formalization.C450Source31GroupedC15.valid2
#print axioms N11Formalization.C450Source31GroupedC15.valid3
#print axioms N11Formalization.C450Source31GroupedC15.valid4
#print axioms N11Formalization.C450Source31GroupedC15.valid5
#print axioms N11Formalization.C450Source31GroupedC15.valid6
#print axioms N11Formalization.C450Source31GroupedC15.valid7
#print axioms N11Formalization.C450Source31GroupedC15.valid8
#print axioms N11Formalization.C450Source31GroupedC15.valid9
#print axioms N11Formalization.C450Source31GroupedC15.valid10
#print axioms N11Formalization.C450Source31GroupedC15.valid11
#print axioms N11Formalization.C450Source31GroupedC15.bound
#print axioms N11Formalization.C450Source31GroupedC15.endpoint_checks
