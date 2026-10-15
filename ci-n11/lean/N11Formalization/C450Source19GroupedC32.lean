import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC32
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((15:ℚ)/16),(1:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((15:ℚ)/16),(1:ℚ),((2739999999:ℚ)/5000000000),((1508326099:ℚ)/2500000000),((9307999997:ℚ)/10680000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1913689989:ℚ)/2500000000),((-244380582054217657117449288505872475062850111013136239:ℚ)/1903416300000000000000000000000000000000000000000000000),((-127429393621134425320214863:ℚ)/369664000000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((15:ℚ)/16),(1:ℚ),((2977499999:ℚ)/5000000000),((3135474317:ℚ)/5000000000),((10020499997:ℚ)/11060000000),(1:ℚ),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1676082799:ℚ)/2500000000),((-57663619356215109186417023325075379159682319001729373:ℚ)/396357133593750000000000000000000000000000000000000000),((-125210238679288267075214863:ℚ)/369664000000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3096249999:ℚ)/5000000000),((6508583283:ℚ)/10000000000),((10376749997:ℚ)/11440000000),(1:ℚ),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((309203829:ℚ)/500000000),((-1361332126660232908229138397403382911299043412767477439:ℚ)/9357462400000000000000000000000000000000000000000000000),((-122854392860419321252714863:ℚ)/369664000000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3214999999:ℚ)/5000000000),((1325479461:ℚ)/2000000000),((10732999997:ℚ)/11630000000),(1:ℚ),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((562259693:ℚ)/1000000000),((-1508579684527643635676129194104066566570152253746518831:ℚ)/9831485918750000000000000000000000000000000000000000000),((-121760050461484195710214863:ℚ)/369664000000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3274374999:ℚ)/5000000000),((6746209267:ℚ)/10000000000),((10911124997:ℚ)/11820000000),(1:ℚ),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((42578393:ℚ)/80000000),((-43952111935565702132467281596207149432132836733636951:ℚ)/286701487500000000000000000000000000000000000000000000),((-120587486543582770423964863:ℚ)/369664000000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3333749999:ℚ)/5000000000),((6865019267:ℚ)/10000000000),((11089249997:ℚ)/12010000000),(1:ℚ),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((5005835761:ℚ)/10000000000),((-1243857814846789081143417690250401353234039552012335037:ℚ)/8120266879687500000000000000000000000000000000000000000),((-119416458307935183567714863:ℚ)/369664000000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3393124999:ℚ)/5000000000),((173110589:ℚ)/250000000),((11267374997:ℚ)/12105000000),(1:ℚ),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((2334947821:ℚ)/5000000000),((-1305098049601610690286229949763853553636400860622046637:ℚ)/8314490895117187500000000000000000000000000000000000000),((-118874618158550471941464863:ℚ)/369664000000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((15:ℚ)/16),(1:ℚ),((3422812499:ℚ)/5000000000),((6983827397:ℚ)/10000000000),((11356437497:ℚ)/12200000000),(1:ℚ),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2246629233:ℚ)/5000000000),((-5341251188854204519424975971218356808482581175699447897:ℚ)/34047150000000000000000000000000000000000000000000000000),((-118290441911846812739589863:ℚ)/369664000000000000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3452499999:ℚ)/5000000000),((7043230787:ℚ)/10000000000),((11445499997:ℚ)/12295000000),(1:ℚ),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((2154949653:ℚ)/5000000000),((-113835162509802911783103507631365713431285167488753191:ℚ)/726015067333984375000000000000000000000000000000000000),((-117706649126091153305214863:ℚ)/369664000000000000000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3482187499:ℚ)/5000000000),((3551316871:ℚ)/5000000000),((11534562497:ℚ)/12390000000),(1:ℚ),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((823783409:ℚ)/2000000000),((-1862974011991544772150724215222029525928899094244979891:ℚ)/11887593243750000000000000000000000000000000000000000000),((-117123239674493021958339863:ℚ)/369664000000000000000000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3511874999:ℚ)/5000000000),((1444287677:ℚ)/2000000000),((11623624997:ℚ)/12580000000),(1:ℚ),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((3919193783:ℚ)/10000000000),((-1426972869365882942403575915358943428434018750863878653:ℚ)/9332182087500000000000000000000000000000000000000000000),((-115912578290888803978964863:ℚ)/369664000000000000000000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((1277:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3571249999:ℚ)/5000000000),((36701207:ℚ)/50000000),((11801749997:ℚ)/12770000000),(1:ℚ),((2337671911:ℚ)/2500000000),((9372267491:ℚ)/10000000000),((181171659:ℚ)/500000000),((3487440591:ℚ)/10000000000),((-124335934685606779195366447527841444176377385650271479:ℚ)/813453489453125000000000000000000000000000000000000000),((-114747683665908482522714863:ℚ)/369664000000000000000000000)⟩
theorem valid11 : Valid source19 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source19 nn0 nn1 Qcell ((629:ℚ)/800) ((1277:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1277:ℚ)/1600),((81:ℚ)/100),((15:ℚ)/16),(1:ℚ),((3630624999:ℚ)/5000000000),((372952143:ℚ)/500000000),((11979874997:ℚ)/12960000000),(1:ℚ),((9331481479:ℚ)/10000000000),((9350687649:ℚ)/10000000000),((735446993:ℚ)/2000000000),((93653573:ℚ)/312500000),((-692963004589872376869515830229925843136776118047789653:ℚ)/4534963200000000000000000000000000000000000000000000000),((-113584320422871835016464863:ℚ)/369664000000000000000000000)⟩
theorem valid12 : Valid source19 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source19 nn0 nn1 Qcell ((1277:ℚ)/1600) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),((343:ℚ)/400),((15:ℚ)/16),(1:ℚ),((3689999999:ℚ)/5000000000),((7934234439:ℚ)/10000000000),((12157999997:ℚ)/13720000000),(1:ℚ),((57977633:ℚ)/62500000),((2332870371:ℚ)/2500000000),((1913736159:ℚ)/5000000000),((241197493:ℚ)/1000000000),((-84196719627203182012827110722343321476413861097911:ℚ)/630525109375000000000000000000000000000000000000000),((-112188378038714311060214863:ℚ)/369664000000000000000000000)⟩
theorem valid13 : Valid source19 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((343:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((343:ℚ)/400),((181:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3927499999:ℚ)/5000000000),((1051175737:ℚ)/1250000000),((12870499997:ℚ)/14480000000),(1:ℚ),((9252071821:ℚ)/10000000000),((1855284257:ℚ)/2000000000),((1946075537:ℚ)/5000000000),(0:ℚ),((-2556092713807086188768131037875689329992899547660205359:ℚ)/18975171200000000000000000000000000000000000000000000000),((-155630753:ℚ)/512000000)⟩
theorem valid14 : Valid source19 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source19 nn0 nn1 Qcell ((343:ℚ)/400) ((181:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((15:ℚ)/16),(1:ℚ),((4164999999:ℚ)/5000000000),((9359699923:ℚ)/10000000000),((13582999997:ℚ)/16000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-743286830321247489887692207179336352321886057304745399:ℚ)/6400000000000000000000000000000000000000000000000000000),((-155630753:ℚ)/512000000)⟩
theorem valid15 : Valid source19 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source19 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((15:ℚ)/16),(1:ℚ),((4639999999:ℚ)/5000000000),((6580235547:ℚ)/5000000000),((652521739:ℚ)/960000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-9993527870624415761237690887091:ℚ)/221184000000000000000000000000000),((-155630753:ℚ)/512000000)⟩
theorem valid16 : Valid source19 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((61:ℚ)/80) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source19 nn0 nn1 Qcell ((1239:ℚ)/1600) ((1277:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((1277:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source19 nn0 nn1 Qcell ((1277:ℚ)/1600) ((343:ℚ)/400) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source19 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source19 nn0 nn1 Qcell ((343:ℚ)/400) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source19 nn0 nn1 Qcell ((1277:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC32
#check @N11Formalization.C450Source19GroupedC32.bound
#print axioms N11Formalization.C450Source19GroupedC32.valid0
#print axioms N11Formalization.C450Source19GroupedC32.valid1
#print axioms N11Formalization.C450Source19GroupedC32.valid2
#print axioms N11Formalization.C450Source19GroupedC32.valid3
#print axioms N11Formalization.C450Source19GroupedC32.valid4
#print axioms N11Formalization.C450Source19GroupedC32.valid5
#print axioms N11Formalization.C450Source19GroupedC32.valid6
#print axioms N11Formalization.C450Source19GroupedC32.valid7
#print axioms N11Formalization.C450Source19GroupedC32.valid8
#print axioms N11Formalization.C450Source19GroupedC32.valid9
#print axioms N11Formalization.C450Source19GroupedC32.valid10
#print axioms N11Formalization.C450Source19GroupedC32.valid11
#print axioms N11Formalization.C450Source19GroupedC32.valid12
#print axioms N11Formalization.C450Source19GroupedC32.valid13
#print axioms N11Formalization.C450Source19GroupedC32.valid14
#print axioms N11Formalization.C450Source19GroupedC32.valid15
#print axioms N11Formalization.C450Source19GroupedC32.valid16
#print axioms N11Formalization.C450Source19GroupedC32.bound
#print axioms N11Formalization.C450Source19GroupedC32.endpoint_checks
