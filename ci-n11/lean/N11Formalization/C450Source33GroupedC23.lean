import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC23
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((3:ℚ)/8),((7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((3:ℚ)/8),((7:ℚ)/16),((110644491:ℚ)/200000000),((2934518759:ℚ)/5000000000),((530333473:ℚ)/1030000000),((30781631313:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7555065997:ℚ)/10000000000),((-2468460960119855298351752909487295554219269894326964672423:ℚ)/7855290880000000000000000000000000000000000000000000000000),((-1441412741720959097102119641:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((3:ℚ)/8),((7:ℚ)/16),((5773767143:ℚ)/10000000000),((3055137831:ℚ)/5000000000),((27241301429:ℚ)/53400000000),((31625964817:ℚ)/51500000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1415870283:ℚ)/2000000000),((-1770355089403557539911116602907300435223109714981803627003:ℚ)/5698400566406250000000000000000000000000000000000000000000),((-1434037954788125661011448921:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((6015015207:ℚ)/10000000000),((1557698627:ℚ)/2500000000),((27965045621:ℚ)/54350000000),((16023890389:ℚ)/26700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((6576197409:ℚ)/10000000000),((-1351341776919770790170171004144207751615784966043963116393:ℚ)/4310444829375000000000000000000000000000000000000000000000),((-360365037479573386524005169:ℚ)/924160000000000000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((6135538741:ℚ)/10000000000),((6351251263:ℚ)/10000000000),((28326616223:ℚ)/55300000000),((64938758841:ℚ)/108700000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1262441429:ℚ)/2000000000),((-308943041811413502622944897298567969424938738770883369303:ℚ)/990867917353515625000000000000000000000000000000000000000),((-5748008410831479052735765609:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/8),((7:ℚ)/16),((391000001:ℚ)/625000000),((3235824581:ℚ)/5000000000),((1793000003:ℚ)/3515625000),((32890772067:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((75480751:ℚ)/125000000),((-164644769636166876360500958385117223004851255861930773:ℚ)/530835446777343750000000000000000000000000000000000000),((-1432239388388722017541049921:ℚ)/3696640000000000000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/8),((7:ℚ)/16),((1594100569:ℚ)/2500000000),((6591991217:ℚ)/10000000000),((7262301707:ℚ)/14300000000),((66623938519:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((287676479:ℚ)/500000000),((-39272607975007256455150561347623491787867350130937127392041:ℚ)/127254638671875000000000000000000000000000000000000000000000),((-5708689391345548585387270729:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((3:ℚ)/8),((7:ℚ)/16),((6496748541:ℚ)/10000000000),((6712280237:ℚ)/10000000000),((29410245623:ℚ)/58150000000),((67465961659:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5455629069:ℚ)/10000000000),((-30387082619460037744368863005681527929192753285825393423779:ℚ)/98933897920000000000000000000000000000000000000000000000000),((-5687205193547614069833006609:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((3:ℚ)/8),((7:ℚ)/16),((1654260407:ℚ)/2500000000),((1366503769:ℚ)/2000000000),((7442781221:ℚ)/14775000000),((13661526383:ℚ)/23260000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((128561741:ℚ)/250000000),((-355307985027458708304354245568056953233233135987645424361:ℚ)/1162081635596250000000000000000000000000000000000000000000),((-11925276092720218377551459:ℚ)/31129600000000000000000000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((3:ℚ)/8),((7:ℚ)/16),((6737284167:ℚ)/10000000000),((884106809:ℚ)/1250000000),((30131852501:ℚ)/61000000000),((2916249221:ℚ)/4925000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2405518049:ℚ)/5000000000),((-4091728148460077835713861168344584877968214244294600819:ℚ)/13663117763671875000000000000000000000000000000000000000),((-87021018535935975209506041:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid source33 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source33 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((3:ℚ)/8),((7:ℚ)/16),((6977627277:ℚ)/10000000000),((7553018773:ℚ)/10000000000),((30852881831:ℚ)/64800000000),((73351131411:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((203757099:ℚ)/500000000),((-26508647326100974094566862628285878082315768731442583335763:ℚ)/91927305000000000000000000000000000000000000000000000000000),((-5364639301605233237796649569:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source33 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/8),((7:ℚ)/16),((7457805183:ℚ)/10000000000),((1893742309:ℚ)/2000000000),((32293415549:ℚ)/80000000000),((17352196163:ℚ)/25920000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((484361439:ℚ)/2500000000),((-7937358360116251185958252587649267476883391065239689393:ℚ)/32651735040000000000000000000000000000000000000000000000),((-72615781520225241:ℚ)/194560000000000000)⟩
theorem valid10 : Valid source33 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/8),((7:ℚ)/16),((1874707829:ℚ)/2000000000),((332176019:ℚ)/250000000),((7608123487:ℚ)/22080000000),((2837232133:ℚ)/4000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-47778127169789887918281349570472442968685029679780163:ℚ)/230000000000000000000000000000000000000000000000000000),((-385967059:ℚ)/1024000000)⟩
theorem valid11 : Valid source33 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC23
#check @N11Formalization.C450Source33GroupedC23.bound
#print axioms N11Formalization.C450Source33GroupedC23.valid0
#print axioms N11Formalization.C450Source33GroupedC23.valid1
#print axioms N11Formalization.C450Source33GroupedC23.valid2
#print axioms N11Formalization.C450Source33GroupedC23.valid3
#print axioms N11Formalization.C450Source33GroupedC23.valid4
#print axioms N11Formalization.C450Source33GroupedC23.valid5
#print axioms N11Formalization.C450Source33GroupedC23.valid6
#print axioms N11Formalization.C450Source33GroupedC23.valid7
#print axioms N11Formalization.C450Source33GroupedC23.valid8
#print axioms N11Formalization.C450Source33GroupedC23.valid9
#print axioms N11Formalization.C450Source33GroupedC23.valid10
#print axioms N11Formalization.C450Source33GroupedC23.valid11
#print axioms N11Formalization.C450Source33GroupedC23.bound
#print axioms N11Formalization.C450Source33GroupedC23.endpoint_checks
