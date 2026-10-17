import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((2976758983:ℚ)/5000000000),((6478533549:ℚ)/10000000000),((40617866779:ℚ)/53400000000),((47589734843:ℚ)/49600000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1341493819:ℚ)/2000000000),((-31156326485969204525788439489498763617:ℚ)/1903416300000000000000000000000000000000),((-853781161574347851851787317:ℚ)/5544960000000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((6428623451:ℚ)/10000000000),((839510493:ℚ)/1250000000),((87412104863:ℚ)/110600000000),((6156573451:ℚ)/6675000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5625993591:ℚ)/10000000000),((-473073610769275704371762408709167113035382342819609309723:ℚ)/25366856550000000000000000000000000000000000000000000000000),((-13295212649460407776541333:ℚ)/86640000000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((13:ℚ)/16),((7:ℚ)/8),((1666542689:ℚ)/2500000000),((1366971573:ℚ)/2000000000),((22625054957:ℚ)/28125000000),((1430971573:ℚ)/1580000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5009478777:ℚ)/10000000000),((-914467394439226994104951196097759397644527218682503817:ℚ)/46348571777343750000000000000000000000000000000000000000),((-33977969445100609983833093:ℚ)/221798400000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((6784943209:ℚ)/10000000000),((695363099:ℚ)/1000000000),((92044261717:ℚ)/114400000000),((5091541693:ℚ)/5625000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2336856759:ℚ)/5000000000),((-16792422980277883548697944644753304972390747110097838201:ℚ)/850678400000000000000000000000000000000000000000000000000),((-2826681545810489509970039:ℚ)/18483200000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((6903714917:ℚ)/10000000000),((7013017267:ℚ)/10000000000),((93588293921:ℚ)/115350000000),((51331120869:ℚ)/57200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((862788991:ℚ)/2000000000),((-145728326478312106200092908988310674493168933624504673909:ℚ)/7194391665820312500000000000000000000000000000000000000000),((-282427309263481658439282471:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((6963100503:ℚ)/10000000000),((44202521:ℚ)/62500000),((94360306539:ℚ)/116300000000),((323417647:ℚ)/360468750),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((4123103859:ℚ)/10000000000),((-7965469429228663524724308891968348013544229953410364597:ℚ)/393259436750000000000000000000000000000000000000000000000),((-11022907446896294315999:ℚ)/72200000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((13:ℚ)/16),((7:ℚ)/8),((1404497183:ℚ)/2000000000),((7131789273:ℚ)/10000000000),((2718066197:ℚ)/3350000000),((52162524911:ℚ)/58150000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((122610813:ℚ)/312500000),((-3569366785865645171125773376911877299100105137423553:ℚ)/176228320312500000000000000000000000000000000000000000),((-845836556088983610630094493:ℚ)/5544960000000000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((7081871159:ℚ)/10000000000),((7191175011:ℚ)/10000000000),((95904325067:ℚ)/118200000000),((7511175011:ℚ)/8375000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((928465681:ℚ)/2500000000),((-5806703030378201043933350630490931088702679486190974709:ℚ)/286701487500000000000000000000000000000000000000000000000),((-845113720232554807997697557:ℚ)/5544960000000000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((13:ℚ)/16),((7:ℚ)/8),((3570628119:ℚ)/5000000000),((1444173563:ℚ)/2000000000),((48338165547:ℚ)/59337500000),((3519071647:ℚ)/3940000000),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((3492226559:ℚ)/10000000000),((-26769176457562953318940830981257841171873299890870150589:ℚ)/1305773202185058593750000000000000000000000000000000000000),((-11263363530507969936967991:ℚ)/73932800000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((7170948717:ℚ)/10000000000),((7250560577:ℚ)/10000000000),((97062333321:ℚ)/119150000000),((52993924039:ℚ)/59337500000),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((105506071:ℚ)/312500000),((-54179550185711297470383685860441087280580777551312103823:ℚ)/2643030446679687500000000000000000000000000000000000000000),((-281463594772242904594756431:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((1800160289:ℚ)/2500000000),((913743247:ℚ)/1250000000),((24362083757:ℚ)/30025000000),((6676202729:ℚ)/7446875000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((814048353:ℚ)/2500000000),((-214131212790455558035618012440319888501339165423519979:ℚ)/10573264166259765625000000000000000000000000000000000000),((-4394102855632875251373551:ℚ)/28880000000000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((3630012959:ℚ)/5000000000),((1842332803:ℚ)/2500000000),((49110168467:ℚ)/60525000000),((13456329621:ℚ)/15012500000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((375295641:ℚ)/1250000000),((-3118170324330205483105185995485794283550421207894969581:ℚ)/153972053613281250000000000000000000000000000000000000000),((-17561346084980312977831751:ℚ)/115520000000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((3659705263:ℚ)/5000000000),((29018423:ℚ)/39062500),((49496168419:ℚ)/61000000000),((847515844:ℚ)/945703125),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((681442479:ℚ)/2500000000),((-28728664962132523832735357967075360022973767561919458997:ℚ)/1418631250000000000000000000000000000000000000000000000000),((-4283759438444315294931:ℚ)/28203125000000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((922349373:ℚ)/1250000000),((7547485977:ℚ)/10000000000),((4156847283:ℚ)/5162500000),((55072401839:ℚ)/61000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2418603809:ℚ)/10000000000),((-4253098262544840289968988922731987444918141569427741:ℚ)/214981069946289062500000000000000000000000000000000000),((-840774602050246318752286493:ℚ)/5544960000000000000000000000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((3748781733:ℚ)/5000000000),((7666255071:ℚ)/10000000000),((50654162529:ℚ)/62900000000),((7986255071:ℚ)/8850000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1643707939:ℚ)/10000000000),((-30061419436923679126203298382089033009894804522945383:ℚ)/1518909844970703125000000000000000000000000000000000000),((-19393693:ℚ)/128000000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((7616331389:ℚ)/10000000000),((7903791579:ℚ)/10000000000),((102852308057:ℚ)/129600000000),((57566541053:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-9539749050254408151351541778793958237355415373365025733:ℚ)/503884800000000000000000000000000000000000000000000000000),((-19393693:ℚ)/128000000)⟩
theorem valid15 : Valid eighth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound eighth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((7853865659:ℚ)/10000000000),((1960804241:ℚ)/2000000000),((105940253567:ℚ)/160000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-49723020050927037114028347828049142943031109766686378323:ℚ)/4800000000000000000000000000000000000000000000000000000000),((-19393693:ℚ)/128000000)⟩
theorem valid16 : Valid eighth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((1950816241:ℚ)/2000000000),((2720858149:ℚ)/2000000000),((1136026571:ℚ)/1920000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-9882373910726937823167622180991:ℚ)/1769472000000000000000000000000000),((-19393693:ℚ)/128000000)⟩
theorem valid17 : Valid eighth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet17 valid17
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
private theorem node7_9 :
    CellBound eighth nn0 nn1 Qcell ((469:ℚ)/640) ((4747:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((4747:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((4747:ℚ)/6400) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((4747:ℚ)/6400) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound eighth nn0 nn1 Qcell ((4747:ℚ)/6400) ((1201:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound eighth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound eighth nn0 nn1 Qcell ((4747:ℚ)/6400) ((61:ℚ)/80) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound eighth nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound eighth nn0 nn1 Qcell ((4747:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC30
#check @N11Formalization.C450EighthGroupedC30.bound
#print axioms N11Formalization.C450EighthGroupedC30.valid0
#print axioms N11Formalization.C450EighthGroupedC30.valid1
#print axioms N11Formalization.C450EighthGroupedC30.valid2
#print axioms N11Formalization.C450EighthGroupedC30.valid3
#print axioms N11Formalization.C450EighthGroupedC30.valid4
#print axioms N11Formalization.C450EighthGroupedC30.valid5
#print axioms N11Formalization.C450EighthGroupedC30.valid6
#print axioms N11Formalization.C450EighthGroupedC30.valid7
#print axioms N11Formalization.C450EighthGroupedC30.valid8
#print axioms N11Formalization.C450EighthGroupedC30.valid9
#print axioms N11Formalization.C450EighthGroupedC30.valid10
#print axioms N11Formalization.C450EighthGroupedC30.valid11
#print axioms N11Formalization.C450EighthGroupedC30.valid12
#print axioms N11Formalization.C450EighthGroupedC30.valid13
#print axioms N11Formalization.C450EighthGroupedC30.valid14
#print axioms N11Formalization.C450EighthGroupedC30.valid15
#print axioms N11Formalization.C450EighthGroupedC30.valid16
#print axioms N11Formalization.C450EighthGroupedC30.valid17
#print axioms N11Formalization.C450EighthGroupedC30.bound
#print axioms N11Formalization.C450EighthGroupedC30.endpoint_checks
