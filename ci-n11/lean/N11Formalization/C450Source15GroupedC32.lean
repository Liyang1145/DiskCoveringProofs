import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC32
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((15:ℚ)/16),(1:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((15:ℚ)/16),(1:ℚ),((5639999997:ℚ)/10000000000),((1546261709:ℚ)/2500000000),((18583999991:ℚ)/21360000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1836476377:ℚ)/2500000000),((-436509090718878183661529053904315200268094928524913283:ℚ)/5075776800000000000000000000000000000000000000000000000),((-845105984796119181520679833:ℚ)/2957312000000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((15:ℚ)/16),(1:ℚ),((6114999997:ℚ)/10000000000),((401414447:ℚ)/625000000),((20008999991:ℚ)/22120000000),(1:ℚ),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6357859119:ℚ)/10000000000),((-102021294930509200125571176847466486604402336971165881:ℚ)/1056952356250000000000000000000000000000000000000000000),((-833634678038331102670679833:ℚ)/2957312000000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3176249999:ℚ)/5000000000),((6660209863:ℚ)/10000000000),((796980769:ℚ)/880000000),(1:ℚ),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((5811073867:ℚ)/10000000000),((-411206653075348916796734613359469740522623863814671:ℚ)/4259200000000000000000000000000000000000000000000000),((-205491387248631440907575537:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3294999999:ℚ)/5000000000),((6778997289:ℚ)/10000000000),((10716999997:ℚ)/11630000000),(1:ℚ),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5214350013:ℚ)/10000000000),((-997354895934790759207097621525990619504398417235775723:ℚ)/9831485918750000000000000000000000000000000000000000000),((-204062859071568772770075537:ℚ)/739328000000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3354374999:ℚ)/5000000000),((6897783511:ℚ)/10000000000),((10895124997:ℚ)/11820000000),(1:ℚ),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4891549141:ℚ)/10000000000),((-87189238232217870730230863072250825568792934236129049:ℚ)/860104462500000000000000000000000000000000000000000000),((-202606121237453090176325537:ℚ)/739328000000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3413749999:ℚ)/5000000000),((6957176189:ℚ)/10000000000),((11073249997:ℚ)/11915000000),(1:ℚ),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((2273927607:ℚ)/5000000000),((-1096777952957821909494458661545305546378004322739187123:ℚ)/10572121786718750000000000000000000000000000000000000000),((-201893201588676055232575537:ℚ)/739328000000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3443437499:ℚ)/5000000000),((3508284293:ℚ)/5000000000),((11162312497:ℚ)/12010000000),(1:ℚ),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((436663521:ℚ)/1000000000),((-280657316722407972220425991713868230913257162906796607:ℚ)/2706755626562500000000000000000000000000000000000000000),((-201165307627537703429450537:ℚ)/739328000000000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((6946249997:ℚ)/10000000000),((7075960711:ℚ)/10000000000),((22502749991:ℚ)/24210000000),(1:ℚ),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((4178087251:ℚ)/10000000000),((-765938475598541659991753675838409447296583882644370363:ℚ)/7390658573437500000000000000000000000000000000000000000),((-801750200875280422783179833:ℚ)/2957312000000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((15:ℚ)/16),(1:ℚ),((3502812499:ℚ)/5000000000),((7135352569:ℚ)/10000000000),((11340437497:ℚ)/12200000000),(1:ℚ),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1990583357:ℚ)/5000000000),((-1175617571424761266430060944262223555335445040979861567:ℚ)/11349050000000000000000000000000000000000000000000000000),((-199709929300737382360700537:ℚ)/739328000000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((7064999997:ℚ)/10000000000),((3597372083:ℚ)/5000000000),((22858999991:ℚ)/24590000000),(1:ℚ),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((1887279843:ℚ)/5000000000),((-601381568167312729965674385996162564950041364732175281:ℚ)/5808120538671875000000000000000000000000000000000000000),((-795929779188592548170679833:ℚ)/2957312000000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((7124374997:ℚ)/10000000000),((7254135509:ℚ)/10000000000),((23037124991:ℚ)/24780000000),(1:ℚ),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((3556574507:ℚ)/10000000000),((-3280929936516373722843248677669023923485652323519790827:ℚ)/31700248650000000000000000000000000000000000000000000000),((-793020386484976185539429833:ℚ)/2957312000000000000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3591874999:ℚ)/5000000000),((7372917453:ℚ)/10000000000),((11607624997:ℚ)/12580000000),(1:ℚ),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((3324969903:ℚ)/10000000000),((-314714300107666027484402447221878179258936592191135483:ℚ)/3110727362500000000000000000000000000000000000000000000),((-196784632834277149901325537:ℚ)/739328000000000000000000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((1277:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3651249999:ℚ)/5000000000),((7491698447:ℚ)/10000000000),((11785749997:ℚ)/12770000000),(1:ℚ),((2337671911:ℚ)/2500000000),((9372267491:ℚ)/10000000000),((181171659:ℚ)/500000000),((1403617151:ℚ)/5000000000),((-82275328844526820145360482046665576199827737055447507:ℚ)/813453489453125000000000000000000000000000000000000000),((-195330623400731390357575537:ℚ)/739328000000000000000000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((629:ℚ)/800) ((1277:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1277:ℚ)/1600),((81:ℚ)/100),((15:ℚ)/16),(1:ℚ),((7421249997:ℚ)/10000000000),((7610478531:ℚ)/10000000000),((23927749991:ℚ)/25920000000),(1:ℚ),((9331481479:ℚ)/10000000000),((9350687649:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2173132131:ℚ)/10000000000),((-407639510233728972657153037678161223953701695817183347:ℚ)/4031078400000000000000000000000000000000000000000000000),((-776033169692813088733179833:ℚ)/2957312000000000000000000000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell ((1277:ℚ)/1600) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((15:ℚ)/16),(1:ℚ),((3769999999:ℚ)/5000000000),((9510862681:ℚ)/10000000000),((12141999997:ℚ)/16000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((628694953:ℚ)/5000000000),((-88191654107980846058848844311579279169139762762056747:ℚ)/1600000000000000000000000000000000000000000000000000000),((-194041843096730451020075537:ℚ)/739328000000000000000000000)⟩
theorem valid14 : Valid source15 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((15:ℚ)/16),(1:ℚ),((4719999999:ℚ)/5000000000),((831957099:ℚ)/625000000),((14991999997:ℚ)/22080000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-30901489932301696126635631855862867:ℚ)/897048576000000000000000000000000000),((-10751191:ℚ)/40960000)⟩
theorem valid15 : Valid source15 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((2383:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source15 nn0 nn1 Qcell ((2383:ℚ)/3200) ((2421:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source15 nn0 nn1 Qcell ((1163:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((2421:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source15 nn0 nn1 Qcell ((2421:ℚ)/3200) ((2459:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source15 nn0 nn1 Qcell ((2459:ℚ)/3200) ((629:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source15 nn0 nn1 Qcell ((2421:ℚ)/3200) ((629:ℚ)/800) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source15 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source15 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source15 nn0 nn1 Qcell ((2421:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC32
#check @N11Formalization.C450Source15GroupedC32.bound
#print axioms N11Formalization.C450Source15GroupedC32.valid0
#print axioms N11Formalization.C450Source15GroupedC32.valid1
#print axioms N11Formalization.C450Source15GroupedC32.valid2
#print axioms N11Formalization.C450Source15GroupedC32.valid3
#print axioms N11Formalization.C450Source15GroupedC32.valid4
#print axioms N11Formalization.C450Source15GroupedC32.valid5
#print axioms N11Formalization.C450Source15GroupedC32.valid6
#print axioms N11Formalization.C450Source15GroupedC32.valid7
#print axioms N11Formalization.C450Source15GroupedC32.valid8
#print axioms N11Formalization.C450Source15GroupedC32.valid9
#print axioms N11Formalization.C450Source15GroupedC32.valid10
#print axioms N11Formalization.C450Source15GroupedC32.valid11
#print axioms N11Formalization.C450Source15GroupedC32.valid12
#print axioms N11Formalization.C450Source15GroupedC32.valid13
#print axioms N11Formalization.C450Source15GroupedC32.valid14
#print axioms N11Formalization.C450Source15GroupedC32.valid15
#print axioms N11Formalization.C450Source15GroupedC32.bound
#print axioms N11Formalization.C450Source15GroupedC32.endpoint_checks
