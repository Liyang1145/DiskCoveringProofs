import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC20
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((3:ℚ)/16),((1:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((3:ℚ)/16),((1:ℚ)/4),((3037672791:ℚ)/5000000000),((3294213149:ℚ)/5000000000),((12313018373:ℚ)/53400000000),((4174213149:ℚ)/12400000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6445211213:ℚ)/10000000000),((4995795203154752548964157548829917079:ℚ)/235974511000000000000000000000000000000),((-85617104398479530933488683:ℚ)/739328000000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((3275695309:ℚ)/5000000000),((1706581151:ℚ)/2500000000),((13027085927:ℚ)/55300000000),((2146581151:ℚ)/6675000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5315448241:ℚ)/10000000000),((4699396219974159601468293890832466043264779553175772861:ℚ)/241683372564697265625000000000000000000000000000000000000),((-88847063347397472219468083:ℚ)/739328000000000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((3:ℚ)/16),((1:ℚ)/4),((1697339779:ℚ)/2500000000),((3472631821:ℚ)/5000000000),((6692019337:ℚ)/28125000000),((4352631821:ℚ)/13825000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1165200123:ℚ)/2500000000),((74545462273142569174793862729303346917693604265615137:ℚ)/3981265850830078125000000000000000000000000000000000000),((-22615848560506181499236563:ℚ)/184832000000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((3:ℚ)/16),((1:ℚ)/4),((6908331463:ℚ)/10000000000),((3532098193:ℚ)/5000000000),((27124994389:ℚ)/114400000000),((4412098193:ℚ)/14062500000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1074848671:ℚ)/2500000000),((183389105607845645801029424089202740263110306650282740721:ℚ)/9872728586196899414062500000000000000000000000000000000000),((-365087632850123926798883467:ℚ)/2957312000000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((3:ℚ)/16),((1:ℚ)/4),((1756824101:ℚ)/2500000000),((1424732099:ℚ)/2000000000),((6870472303:ℚ)/28837500000),((1776732099:ℚ)/5720000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3906958979:ℚ)/10000000000),((592188307843390578553989225391951756642601388279254531561:ℚ)/32423662044881250000000000000000000000000000000000000000000),((-23020164512525592173023043:ℚ)/184832000000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((7086776213:ℚ)/10000000000),((3591561573:ℚ)/5000000000),((27660328639:ℚ)/116300000000),((4471561573:ℚ)/14418750000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3696037729:ℚ)/10000000000),((42712684311203496858907219046423520418243052236654183577:ℚ)/2346380965723117828369140625000000000000000000000000000000),((-369940488758028159676026467:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((3:ℚ)/16),((1:ℚ)/4),((223320447:ℚ)/312500000),((7242584373:ℚ)/10000000000),((869961341:ℚ)/3664062500),((9002584373:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3472955721:ℚ)/10000000000),((2918258105203864049204848037424378608825615614735680703:ℚ)/160817762831115722656250000000000000000000000000000000000),((-362850180406083960315387:ℚ)/2888000000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((7205730721:ℚ)/10000000000),((7302044211:ℚ)/10000000000),((28017192163:ℚ)/118200000000),((9062044211:ℚ)/29312500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3235193777:ℚ)/10000000000),((1726956989380230171194644630702868048350866385617996424933:ℚ)/95453328241848945617675781250000000000000000000000000000000),((-373176921306352768562309563:ℚ)/2957312000000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((3:ℚ)/16),((1:ℚ)/4),((7265205503:ℚ)/10000000000),((7361502693:ℚ)/10000000000),((28195616509:ℚ)/119150000000),((9121502693:ℚ)/29550000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1489617233:ℚ)/5000000000),((344206137734462780001977915388541719968582662953522680494223:ℚ)/19079163086131494140625000000000000000000000000000000000000000),((-1038214680074507221820867:ℚ)/8192000000000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((3:ℚ)/16),((1:ℚ)/4),((732467869:ℚ)/1000000000),((1855239963:ℚ)/2500000000),((2837403607:ℚ)/12010000000),((2295239963:ℚ)/7446875000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((337487743:ℚ)/1250000000),((1046654040988169448184683209844103870691445664525531516069:ℚ)/58171230458392760157585144042968750000000000000000000000000),((-3764143204027364287154323:ℚ)/29573120000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((3:ℚ)/16),((1:ℚ)/4),((92301879:ℚ)/125000000),((7539870323:ℚ)/10000000000),((356905637:ℚ)/1525000000),((9299870323:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2389005653:ℚ)/10000000000),((712600134910049279834316862158952725450480163371742061251:ℚ)/39343115962652587890625000000000000000000000000000000000000),((-59067716407103339913963:ℚ)/462080000000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((3:ℚ)/16),((1:ℚ)/4),((1500617811:ℚ)/2000000000),((972209587:ℚ)/1250000000),((156266309:ℚ)/680000000),((1192209587:ℚ)/3812500000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((799331989:ℚ)/5000000000),((470276685037674592250552054085225074112910785294941:ℚ)/25638794898986816406250000000000000000000000000000000),((-15250889968726900746092403:ℚ)/118292480000000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((3:ℚ)/16),((1:ℚ)/4),((7740949383:ℚ)/10000000000),((8015465069:ℚ)/10000000000),((29622848149:ℚ)/129600000000),((575027357:ℚ)/1850000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((98388409531166338785099950334818811789591247500494507:ℚ)/5409087451171875000000000000000000000000000000000000000),((-132933557:ℚ)/1024000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((3:ℚ)/16),((1:ℚ)/4),((1595757707:ℚ)/2000000000),((9917278271:ℚ)/10000000000),((6067273121:ℚ)/32000000000),((11677278271:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((5925580035851346082951708767632137089570747962456389:ℚ)/276792187500000000000000000000000000000000000000000000),((-132933557:ℚ)/1024000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((3:ℚ)/16),((1:ℚ)/4),((2470230219:ℚ)/2500000000),((13719405571:ℚ)/10000000000),((391769159:ℚ)/2400000000),((15479405571:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((79966177548329104664939784029675083:ℚ)/3000000000000000000000000000000000000),((-132933557:ℚ)/1024000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source12 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC20
#check @N11Formalization.C450Source12GroupedC20.bound
#print axioms N11Formalization.C450Source12GroupedC20.valid0
#print axioms N11Formalization.C450Source12GroupedC20.valid1
#print axioms N11Formalization.C450Source12GroupedC20.valid2
#print axioms N11Formalization.C450Source12GroupedC20.valid3
#print axioms N11Formalization.C450Source12GroupedC20.valid4
#print axioms N11Formalization.C450Source12GroupedC20.valid5
#print axioms N11Formalization.C450Source12GroupedC20.valid6
#print axioms N11Formalization.C450Source12GroupedC20.valid7
#print axioms N11Formalization.C450Source12GroupedC20.valid8
#print axioms N11Formalization.C450Source12GroupedC20.valid9
#print axioms N11Formalization.C450Source12GroupedC20.valid10
#print axioms N11Formalization.C450Source12GroupedC20.valid11
#print axioms N11Formalization.C450Source12GroupedC20.valid12
#print axioms N11Formalization.C450Source12GroupedC20.valid13
#print axioms N11Formalization.C450Source12GroupedC20.valid14
#print axioms N11Formalization.C450Source12GroupedC20.bound
#print axioms N11Formalization.C450Source12GroupedC20.endpoint_checks
