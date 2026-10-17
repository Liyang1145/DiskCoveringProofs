import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((403812697:ℚ)/625000000),((844482183:ℚ)/1250000000),((-6480339647:ℚ)/12400000000),((-328812697:ℚ)/804687500),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((693200521:ℚ)/1250000000),((225113493169324646444413825293101742486964143457663:ℚ)/3785774521529674530029296875000000000000000000000000),((616846052141235198957469:ℚ)/3040000000000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((6699206043:ℚ)/10000000000),((6874955189:ℚ)/10000000000),((-52914596701:ℚ)/103000000000),((-5499206043:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((983641607:ℚ)/2000000000),((260887523784371636074827703764254763442270306163482523:ℚ)/4535485338096618652343750000000000000000000000000000000),((156355907735606595840251109:ℚ)/778240000000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((681828831:ℚ)/1000000000),((6994040489:ℚ)/10000000000),((-53986364401:ℚ)/104900000000),((-187276277:ℚ)/445000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((4575370547:ℚ)/10000000000),((103837319431147159958903730081411296629545661591859:ℚ)/1805450393066406250000000000000000000000000000000000),((1555745328152345682406701:ℚ)/7782400000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-9:ℚ)/16),((-1:ℚ)/2),((1734339677:ℚ)/2500000000),((7053578687:ℚ)/10000000000),((-54522208183:ℚ)/106800000000),((-1434339677:ℚ)/3367187500),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((841365367:ℚ)/2000000000),((176139609249715711181998582731235128281536898018947:ℚ)/3110736520757200196385383605957031250000000000000000),((9674445626094043575392789:ℚ)/48640000000000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((6996889653:ℚ)/10000000000),((355655701:ℚ)/500000000),((-2752901309:ℚ)/5387500000),((-5796889653:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2005355301:ℚ)/5000000000),((4783313805245319332939261702624367374221735602694115549:ℚ)/84466786467437744140625000000000000000000000000000000000),((8126245634874806894130951:ℚ)/40960000000000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((7056417861:ℚ)/10000000000),((1793161641:ℚ)/2500000000),((-13898454769:ℚ)/27175000000),((-1952139287:ℚ)/4568750000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((951270363:ℚ)/2500000000),((6745122903548126520267888508833807252207849271976871:ℚ)/119097554688453674316406250000000000000000000000000000),((154005695850044848354077861:ℚ)/778240000000000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-9:ℚ)/16),((-1:ℚ)/2),((1423188681:ℚ)/2000000000),((7202411813:ℚ)/10000000000),((-55861706317:ℚ)/109650000000),((-1183188681:ℚ)/2753125000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((1794150017:ℚ)/5000000000),((16748022881863835476963141836521624275388335029159613:ℚ)/297937525374293327331542968750000000000000000000000000),((6144488638779857569067901:ℚ)/31129600000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((7145705199:ℚ)/10000000000),((7232176391:ℚ)/10000000000),((-56129587519:ℚ)/110125000000),((-849386457:ℚ)/1975000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((695015579:ℚ)/2000000000),((465763264601580550262957927979031948561512275452079:ℚ)/8284899883270263671875000000000000000000000000000000),((153415285161811014361459341:ℚ)/778240000000000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((448466647:ℚ)/625000000),((7261940307:ℚ)/10000000000),((-56397462763:ℚ)/110600000000),((-746933294:ℚ)/1735546875),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3358202793:ℚ)/10000000000),((19047220829743307457229991895856526343447979604283259:ℚ)/338778206480930093675851821899414062500000000000000000),((598508699405678878478269:ℚ)/3040000000000000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((3602613437:ℚ)/5000000000),((7291703571:ℚ)/10000000000),((-56665332139:ℚ)/111075000000),((-3002613437:ℚ)/6971875000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3237278519:ℚ)/10000000000),((137792886054057790056379663020349860747182736765232099:ℚ)/2450608198504298925399780273437500000000000000000000000),((38255260392461266165475029:ℚ)/194560000000000000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-9:ℚ)/16),((-1:ℚ)/2),((7234986771:ℚ)/10000000000),((735122817:ℚ)/1000000000),((-5720105353:ℚ)/11155000000),((-2011662257:ℚ)/4687500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1555916237:ℚ)/5000000000),((11917510722602129300006944534754122200360045938607163:ℚ)/210375292226672172546386718750000000000000000000000000),((152823728696357620366697781:ℚ)/778240000000000000000000000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((1823626181:ℚ)/2500000000),((1482150051:ℚ)/2000000000),((-11547350459:ℚ)/22500000000),((-1523626181:ℚ)/3545312500),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((711239831:ℚ)/2500000000),((1479214516821792572695402739734223275305712245989:ℚ)/26110480224341154098510742187500000000000000000000),((9526795035643399868692901:ℚ)/48640000000000000000000000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((294160811:ℚ)/400000000),((7470269889:ℚ)/10000000000),((-58272429001:ℚ)/113450000000),((-18935447:ℚ)/44000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((637787841:ℚ)/2500000000),((855499908766278375079885153039138301912946699549:ℚ)/15100195000000000000000000000000000000000000000000),((243253123695128890616261:ℚ)/1245184000000000000000000)⟩
theorem valid12 : Valid source16 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source16 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((1853383371:ℚ)/2500000000),((7589302041:ℚ)/10000000000),((-4564901413:ℚ)/8800000000),((-1553383371:ℚ)/3634375000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2219732319:ℚ)/10000000000),((2370115613707439232850063982748357137550340212008343:ℚ)/41254556696414947509765625000000000000000000000000000),((9477323348625165125742981:ℚ)/48640000000000000000000000)⟩
theorem valid13 : Valid source16 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((470784569:ℚ)/625000000),((1927081273:ℚ)/2500000000),((-15103731457:ℚ)/29075000000),((-395784569:ℚ)/923437500),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1333247851:ℚ)/10000000000),((38048912371143349766452877182209929501812649667427:ℚ)/662473499700427055358886718750000000000000000000000),((589232747771096778103901:ℚ)/3040000000000000000000000)⟩
theorem valid14 : Valid source16 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-9:ℚ)/16),((-1:ℚ)/2),((1912891007:ℚ)/2500000000),((1589269119:ℚ)/2000000000),((-12511422071:ℚ)/23640000000),((-1612891007:ℚ)/3812500000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((150712022593903031900884258695324554158013862926489791:ℚ)/2558627529144287109375000000000000000000000000000000000),((197885437:ℚ)/1024000000)⟩
theorem valid15 : Valid source16 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source16 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((7889561417:ℚ)/10000000000),((8422294759:ℚ)/10000000000),((-66840652831:ℚ)/122000000000),((-6689561417:ℚ)/16200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((415670151016166759989516614572798199638842636747006697:ℚ)/6753729375000000000000000000000000000000000000000000000),((197885437:ℚ)/1024000000)⟩
theorem valid16 : Valid source16 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((2091367111:ℚ)/2500000000),((2065037547:ℚ)/2000000000),((-16793337923:ℚ)/25920000000),((-1791367111:ℚ)/5000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((306603539938109920465158928576226781800653301453381447:ℚ)/4081466880000000000000000000000000000000000000000000000),((197885437:ℚ)/1024000000)⟩
theorem valid17 : Valid source16 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((5134116537:ℚ)/5000000000),((353214517:ℚ)/250000000),((-2954930653:ℚ)/4000000000),((-1511372179:ℚ)/4600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((179650038855816585712224177954523121269868521692496993:ℚ)/1983750000000000000000000000000000000000000000000000000),((197885437:ℚ)/1024000000)⟩
theorem valid18 : Valid source16 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source16 nn0 nn1 Qcell ((1049:ℚ)/1600) ((431:ℚ)/640) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source16 nn0 nn1 Qcell ((431:ℚ)/640) ((2193:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source16 nn0 nn1 Qcell ((881:ℚ)/1280) ((4443:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source16 nn0 nn1 Qcell ((2193:ℚ)/3200) ((4443:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source16 nn0 nn1 Qcell ((431:ℚ)/640) ((4443:ℚ)/6400) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((4443:ℚ)/6400) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source16 nn0 nn1 Qcell ((4443:ℚ)/6400) ((45:ℚ)/64) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source16 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source16 nn0 nn1 Qcell ((4443:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source16 nn0 nn1 Qcell ((4443:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC08
#check @N11Formalization.C450Source16GroupedC08.bound
#print axioms N11Formalization.C450Source16GroupedC08.valid0
#print axioms N11Formalization.C450Source16GroupedC08.valid1
#print axioms N11Formalization.C450Source16GroupedC08.valid2
#print axioms N11Formalization.C450Source16GroupedC08.valid3
#print axioms N11Formalization.C450Source16GroupedC08.valid4
#print axioms N11Formalization.C450Source16GroupedC08.valid5
#print axioms N11Formalization.C450Source16GroupedC08.valid6
#print axioms N11Formalization.C450Source16GroupedC08.valid7
#print axioms N11Formalization.C450Source16GroupedC08.valid8
#print axioms N11Formalization.C450Source16GroupedC08.valid9
#print axioms N11Formalization.C450Source16GroupedC08.valid10
#print axioms N11Formalization.C450Source16GroupedC08.valid11
#print axioms N11Formalization.C450Source16GroupedC08.valid12
#print axioms N11Formalization.C450Source16GroupedC08.valid13
#print axioms N11Formalization.C450Source16GroupedC08.valid14
#print axioms N11Formalization.C450Source16GroupedC08.valid15
#print axioms N11Formalization.C450Source16GroupedC08.valid16
#print axioms N11Formalization.C450Source16GroupedC08.valid17
#print axioms N11Formalization.C450Source16GroupedC08.valid18
#print axioms N11Formalization.C450Source16GroupedC08.bound
#print axioms N11Formalization.C450Source16GroupedC08.endpoint_checks
