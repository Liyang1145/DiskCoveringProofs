import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((6038176413:ℚ)/10000000000),((6551763263:ℚ)/10000000000),((2172725471:ℚ)/4450000000),((63445869367:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((203943021:ℚ)/312500000),((-4170777365616685195221:ℚ)/9901250000000000000000000),((-1677255749554182173466469913:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((1628371069:ℚ)/2500000000),((3394687261:ℚ)/5000000000),((1748371069:ℚ)/3456250000),((32792185349:ℚ)/53400000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((270652111:ℚ)/500000000),((-1263994177682656005233881984709165834272082018997881:ℚ)/774135026550292968750000000000000000000000000000000000),((-105740478479003152709665497:ℚ)/924160000000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/2),((9:ℚ)/16),((843890291:ℚ)/1250000000),((6908177331:ℚ)/10000000000),((903890291:ℚ)/1757812500),((66653595979:ℚ)/110600000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4771539629:ℚ)/10000000000),((-24634023575457659866418191267668374955107998392899:ℚ)/11315569281578063964843750000000000000000000000000000),((-26550935153502334351721337:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((6869937853:ℚ)/10000000000),((1405395677:ℚ)/2000000000),((7349937853:ℚ)/14300000000),((13544561093:ℚ)/22500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4419036351:ℚ)/10000000000),((-3714984315968799860876001535260451064960063534578129:ℚ)/1661481250000000000000000000000000000000000000000000000),((-1702995017408843293688859993:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/2),((9:ℚ)/16),((8735939:ℚ)/12500000),((7086378281:ℚ)/10000000000),((18671878:ℚ)/36046875),((68257404529:ℚ)/114400000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((807610341:ℚ)/2000000000),((-1091538532719544660030776852239857464546560251:ℚ)/439110819447040557861328125000000000000000000000),((-2666796201162316899417:ℚ)/23104000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((704815709:ℚ)/1000000000),((714577777:ℚ)/1000000000),((752815709:ℚ)/1453750000),((6879199993:ℚ)/11535000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3834241923:ℚ)/10000000000),((-1927081620689370177034079096521275811403083626227:ℚ)/768084837402343750000000000000000000000000000000000),((-17086341140396445234237337:ℚ)/147865600000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/2),((9:ℚ)/16),((1776890619:ℚ)/2500000000),((7205176861:ℚ)/10000000000),((1896890619:ℚ)/3664062500),((69326591749:ℚ)/116300000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1809785599:ℚ)/5000000000),((-27790407940192895920458538486183651024587059524719:ℚ)/10980208963155746459960937500000000000000000000000000),((-106907719135440447703256297:ℚ)/924160000000000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((895870921:ℚ)/1250000000),((3632287783:ℚ)/5000000000),((955870921:ℚ)/1846875000),((34930590047:ℚ)/58625000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3391973897:ℚ)/10000000000),((-930303817171635736230910046114742386540920697541:ℚ)/364559793472290039062500000000000000000000000000000),((-26756527270650001750119457:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((1:ℚ)/2),((9:ℚ)/16),((361318589:ℚ)/500000000),((1830993473:ℚ)/2500000000),((385318589:ℚ)/744687500),((17598941257:ℚ)/29550000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((3148643653:ℚ)/10000000000),((-19913135076147836172937131779367781077513573969301:ℚ)/7743253261756896972656250000000000000000000000000000),((-4285792079575317214697817:ℚ)/36966400000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((3642887861:ℚ)/5000000000),((7383371849:ℚ)/10000000000),((3882887861:ℚ)/7506250000),((70930346641:ℚ)/119150000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((360699793:ℚ)/1250000000),((-427960053961313547629220028862093491977326922081043:ℚ)/165207252597808837890625000000000000000000000000000000),((-429055191473917421729596617:ℚ)/3696640000000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((1:ℚ)/2),((9:ℚ)/16),((3672589603:ℚ)/5000000000),((1488553889:ℚ)/2000000000),((3912589603:ℚ)/7565625000),((14292985001:ℚ)/24020000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((1298424269:ℚ)/5000000000),((-784351158712688560261689987874114044972239921811149:ℚ)/300726667213439941406250000000000000000000000000000000),((-429532386947223178987555993:ℚ)/3696640000000000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((7404582243:ℚ)/10000000000),((7502166689:ℚ)/10000000000),((7884582243:ℚ)/15250000000),((71999500201:ℚ)/121050000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1136305781:ℚ)/5000000000),((-58184494938704841388758586570795984245178858372694581:ℚ)/22166113281250000000000000000000000000000000000000000000),((-1720043177752134836241806873:ℚ)/14786560000000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((7463984843:ℚ)/10000000000),((1547950461:ℚ)/2000000000),((7943984843:ℚ)/15725000000),((14827554149:ℚ)/24400000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1894749041:ℚ)/10000000000),((-12802905787710660027176480603044793555463665136129301:ℚ)/6075639379882812500000000000000000000000000000000000000),((-1721961655999000228497264073:ℚ)/14786560000000000000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((7701591071:ℚ)/10000000000),((7977332897:ℚ)/10000000000),((8181591071:ℚ)/16200000000),((76275996073:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-2144489290306353541657687963769360437912305612279491:ℚ)/984150000000000000000000000000000000000000000000000000),((-119554899:ℚ)/1024000000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((1587838213:ℚ)/2000000000),((9877839769:ℚ)/10000000000),((1683838213:ℚ)/4000000000),((93380557921:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((80980252724807967576626401060843:ℚ)/60000000000000000000000000000000000),((-119554899:ℚ)/1024000000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((9839819951:ℚ)/10000000000),((1709804337:ℚ)/1250000000),((10319819951:ℚ)/27600000000),((15948239033:ℚ)/20000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1697669350462188857913419:ℚ)/380880000000000000000000000),((-119554899:ℚ)/1024000000)⟩
theorem valid15 : Valid eighth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC25
#check @N11Formalization.C450EighthGroupedC25.bound
#print axioms N11Formalization.C450EighthGroupedC25.valid0
#print axioms N11Formalization.C450EighthGroupedC25.valid1
#print axioms N11Formalization.C450EighthGroupedC25.valid2
#print axioms N11Formalization.C450EighthGroupedC25.valid3
#print axioms N11Formalization.C450EighthGroupedC25.valid4
#print axioms N11Formalization.C450EighthGroupedC25.valid5
#print axioms N11Formalization.C450EighthGroupedC25.valid6
#print axioms N11Formalization.C450EighthGroupedC25.valid7
#print axioms N11Formalization.C450EighthGroupedC25.valid8
#print axioms N11Formalization.C450EighthGroupedC25.valid9
#print axioms N11Formalization.C450EighthGroupedC25.valid10
#print axioms N11Formalization.C450EighthGroupedC25.valid11
#print axioms N11Formalization.C450EighthGroupedC25.valid12
#print axioms N11Formalization.C450EighthGroupedC25.valid13
#print axioms N11Formalization.C450EighthGroupedC25.valid14
#print axioms N11Formalization.C450EighthGroupedC25.valid15
#print axioms N11Formalization.C450EighthGroupedC25.bound
#print axioms N11Formalization.C450EighthGroupedC25.endpoint_checks
