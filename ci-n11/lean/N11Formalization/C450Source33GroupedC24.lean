import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((7:ℚ)/16),((1:ℚ)/2),((5460098357:ℚ)/10000000000),((2898849073:ℚ)/5000000000),((58060688499:ℚ)/103000000000),((134801583:ℚ)/200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((7692479513:ℚ)/10000000000),((-168831435877211640176660352880729304778716262943833:ℚ)/515000000000000000000000000000000000000000000000000),((-1490432670251528268402369:ℚ)/3610000000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((5701341043:ℚ)/10000000000),((754838809:ℚ)/1250000000),((59749387301:ℚ)/106800000000),((1074838809:ℚ)/1609375000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((3612337179:ℚ)/5000000000),((-56538006249492381941839410671678730911699965469141299:ℚ)/173901384472846984863281250000000000000000000000000000),((-92413636065556988507291:ℚ)/225625000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((2971155761:ℚ)/5000000000),((6159122591:ℚ)/10000000000),((30718090327:ℚ)/54350000000),((2906374197:ℚ)/4450000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((105174319:ℚ)/156250000),((-19737529503893130984816951319771168123470867982221327643:ℚ)/59867289296875000000000000000000000000000000000000000000),((-5925588906560197255963841:ℚ)/14440000000000000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((303135193:ℚ)/500000000),((6279476439:ℚ)/10000000000),((3113946351:ℚ)/5530000000),((8839476439:ℚ)/13587500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((6472845881:ℚ)/10000000000),((-1906067898105030520959624194916110662428335839790601451:ℚ)/5805866703243255615234375000000000000000000000000000000),((-5898905237436536416865681:ℚ)/14440000000000000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/16),((1:ℚ)/2),((1236607727:ℚ)/2000000000),((799971881:ℚ)/1250000000),((12624254089:ℚ)/22500000000),((159995983:ℚ)/246875000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1551379511:ℚ)/2500000000),((-108102125014883693716070661049801434222372694039:ℚ)/330608412623405456542968750000000000000000000000),((-91734535774296992813771:ℚ)/225625000000000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((6303318841:ℚ)/10000000000),((6520021241:ℚ)/10000000000),((63963231887:ℚ)/114400000000),((1008891249:ℚ)/1562500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((148198011:ℚ)/250000000),((-111051538958229740107651007577431428308786921356857151:ℚ)/340938568115234375000000000000000000000000000000000000),((-5841905101064168394558641:ℚ)/14440000000000000000000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((1284709453:ℚ)/2000000000),((6640217651:ℚ)/10000000000),((12960966171:ℚ)/23260000000),((9200217651:ℚ)/14300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5638503417:ℚ)/10000000000),((-62708867566562921160426768596879420233956649850834947851:ℚ)/193230269375000000000000000000000000000000000000000000000),((-5811590638423172704443561:ℚ)/14440000000000000000000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((6543726507:ℚ)/10000000000),((3380183367:ℚ)/5000000000),((65646085549:ℚ)/118200000000),((4660183367:ℚ)/7268750000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5335310231:ℚ)/10000000000),((-11468885163332369578903593126649183868583152296535497889:ℚ)/35463917101936340332031250000000000000000000000000000000),((-1445016951203324495413329:ℚ)/3610000000000000000000000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((1332771799:ℚ)/2000000000),((7000531969:ℚ)/10000000000),((13297402593:ℚ)/24400000000),((9560531969:ℚ)/14775000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((5015808789:ℚ)/10000000000),((-116751260194689182042426806606764474992211819296036753711:ℚ)/368904179619140625000000000000000000000000000000000000000),((-298786484739830772872859:ℚ)/760000000000000000000000)⟩
theorem valid8 : Valid source33 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source33 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((6903992641:ℚ)/10000000000),((3740193203:ℚ)/5000000000),((68167948487:ℚ)/129600000000),((5020193203:ℚ)/7625000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((862614187:ℚ)/2000000000),((-6825713301507089002493779366420620060467788380641189171:ℚ)/22443189697265625000000000000000000000000000000000000000),((-1364084268202257512311049:ℚ)/3610000000000000000000000)⟩
theorem valid9 : Valid source33 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((3691894813:ℚ)/5000000000),((4697570441:ℚ)/5000000000),((35763263691:ℚ)/80000000000),((5977570441:ℚ)/8100000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((2391010441:ℚ)/10000000000),((-248225579255069089815059115201562387838663350378145899:ℚ)/996451875000000000000000000000000000000000000000000000),((-581663743183269:ℚ)/1520000000000000)⟩
theorem valid10 : Valid source33 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((1859674017:ℚ)/2000000000),((3303094841:ℚ)/2500000000),((16985718119:ℚ)/44160000000),((3943094841:ℚ)/5000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-276916666425332043162328983952026401635266974628767237:ℚ)/1347656250000000000000000000000000000000000000000000000),((-3097753:ℚ)/8000000)⟩
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
end N11Formalization.C450Source33GroupedC24
#check @N11Formalization.C450Source33GroupedC24.bound
#print axioms N11Formalization.C450Source33GroupedC24.valid0
#print axioms N11Formalization.C450Source33GroupedC24.valid1
#print axioms N11Formalization.C450Source33GroupedC24.valid2
#print axioms N11Formalization.C450Source33GroupedC24.valid3
#print axioms N11Formalization.C450Source33GroupedC24.valid4
#print axioms N11Formalization.C450Source33GroupedC24.valid5
#print axioms N11Formalization.C450Source33GroupedC24.valid6
#print axioms N11Formalization.C450Source33GroupedC24.valid7
#print axioms N11Formalization.C450Source33GroupedC24.valid8
#print axioms N11Formalization.C450Source33GroupedC24.valid9
#print axioms N11Formalization.C450Source33GroupedC24.valid10
#print axioms N11Formalization.C450Source33GroupedC24.valid11
#print axioms N11Formalization.C450Source33GroupedC24.bound
#print axioms N11Formalization.C450Source33GroupedC24.endpoint_checks
