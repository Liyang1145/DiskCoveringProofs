import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((5946985953:ℚ)/10000000000),((404395263:ℚ)/625000000),((6458985953:ℚ)/10680000000),((4808347893:ℚ)/6200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((840160567:ℚ)/1250000000),((-3082205994380844226094041806053521:ℚ)/304546608000000000000000000000000000),((-2503000870545754909631362537:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((6422378651:ℚ)/10000000000),((3353992483:ℚ)/5000000000),((6934378651:ℚ)/11060000000),((39773917313:ℚ)/53400000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5641379863:ℚ)/10000000000),((-45610625008059348048169706873219055856962745155762421:ℚ)/3623836650000000000000000000000000000000000000000000000),((-6949055250308886562754713:ℚ)/40960000000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/8),((11:ℚ)/16),((6660054739:ℚ)/10000000000),((1706702817:ℚ)/2500000000),((796894971:ℚ)/1250000000),((20213730987:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5026209643:ℚ)/10000000000),((-167480395150233230949278130260988773413244272422841:ℚ)/12207031250000000000000000000000000000000000000000000),((-2511499177063434514107203153:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((6778888317:ℚ)/10000000000),((3472817517:ℚ)/5000000000),((7290888317:ℚ)/11440000000),((4564554743:ℚ)/6250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2345682877:ℚ)/5000000000),((-11720249592334890926676915389544421281113730084753933:ℚ)/850678400000000000000000000000000000000000000000000000),((-2512965844622373727055742577:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((1724429779:ℚ)/2500000000),((1751261501:ℚ)/2500000000),((617476593:ℚ)/961250000),((20703876511:ℚ)/28600000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2166386971:ℚ)/5000000000),((-19855966094256967601954068019953353607392290924763:ℚ)/1387807034301757812500000000000000000000000000000000),((-157152930064189751594988113:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((1739283379:ℚ)/2500000000),((7064456387:ℚ)/10000000000),((1867283379:ℚ)/2907500000),((83469020257:ℚ)/115350000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((4142652813:ℚ)/10000000000),((-88033260944846400465599656668839009444183451467881:ℚ)/6144678699218750000000000000000000000000000000000000),((-157199549235447034337306513:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((5:ℚ)/8),((11:ℚ)/16),((877068409:ℚ)/1250000000),((1780966549:ℚ)/2500000000),((941068409:ℚ)/1465625000),((21030632039:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((394393179:ℚ)/1000000000),((-30241996432148854047470833378573780969348354467311:ℚ)/2108200120925903320312500000000000000000000000000000),((-39311598234166840192771033:ℚ)/231040000000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((17689901:ℚ)/25000000),((1795818861:ℚ)/2500000000),((18969901:ℚ)/29550000),((3027715353:ℚ)/4187500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3735234667:ℚ)/10000000000),((-64337765859746747634330463489034882055736919:ℚ)/4479710742187500000000000000000000000000000000),((-15729346117323894781393:ℚ)/92416000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((3567686457:ℚ)/5000000000),((3621342073:ℚ)/5000000000),((3823686457:ℚ)/5957500000),((42714762803:ℚ)/59100000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((702956157:ℚ)/2000000000),((-57002532853844733775356527189760500083900052685379201:ℚ)/3964545670019531250000000000000000000000000000000000000),((-629363015796786759524500057:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((7194784829:ℚ)/10000000000),((1460418463:ℚ)/2000000000),((7706784829:ℚ)/12010000000),((17216603093:ℚ)/23830000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((3280196263:ℚ)/10000000000),((-9739637446547634438342512061807150881302572675476111:ℚ)/676688906640625000000000000000000000000000000000000000),((-2518212340313429480752995313:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((22669363:ℚ)/31250000),((3680749981:ℚ)/5000000000),((24269363:ℚ)/37828125),((43368249791:ℚ)/60050000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((3028194299:ℚ)/10000000000),((-2166296308596781792881932577821241921898111673:ℚ)/150363333606719970703125000000000000000000000000),((-24599377053077027909617:ℚ)/144400000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((182840173:ℚ)/250000000),((7420907101:ℚ)/10000000000),((195640173:ℚ)/305000000),((87389978111:ℚ)/121050000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((688498179:ℚ)/2500000000),((-2557099686704089095181882661849974962090631106863:ℚ)/177328906250000000000000000000000000000000000000000),((-4362437107019181620777:ℚ)/25600000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((3686508561:ℚ)/5000000000),((3769859949:ℚ)/5000000000),((66822179:ℚ)/105000000),((44348459439:ℚ)/61000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((612536003:ℚ)/2500000000),((-1205019516025150705327880554108266695546756021:ℚ)/86132812500000000000000000000000000000000000000),((-630128682179078567583674953:ℚ)/3696640000000000000000000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((7491835907:ℚ)/10000000000),((7658530797:ℚ)/10000000000),((8003835907:ℚ)/12580000000),((30001279589:ℚ)/41300000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1689142097:ℚ)/10000000000),((-170355700028351448301428761122553515871201130737993:ℚ)/12151278759765625000000000000000000000000000000000000),((-6986336895305550409832137:ℚ)/40960000000000000000000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((7610652611:ℚ)/10000000000),((3948073617:ℚ)/5000000000),((8122652611:ℚ)/12960000000),((46308809787:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-6661757261379280282872607916971227316484040642449363:ℚ)/503884800000000000000000000000000000000000000000000000),((-174757187:ℚ)/1024000000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((1962070037:ℚ)/2500000000),((2449219879:ℚ)/2500000000),((2090070037:ℚ)/4000000000),((28381418669:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-370827366546743433987683216154335878995902842212229:ℚ)/75000000000000000000000000000000000000000000000000000),((-174757187:ℚ)/1024000000)⟩
theorem valid15 : Valid tenth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((4874541113:ℚ)/5000000000),((3399434737:ℚ)/2500000000),((1710180371:ℚ)/3680000000),((38833782107:ℚ)/40000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2810013456405837692143:ℚ)/3385600000000000000000000),((-174757187:ℚ)/1024000000)⟩
theorem valid16 : Valid tenth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound tenth nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC27
#check @N11Formalization.C450TenthGroupedC27.bound
#print axioms N11Formalization.C450TenthGroupedC27.valid0
#print axioms N11Formalization.C450TenthGroupedC27.valid1
#print axioms N11Formalization.C450TenthGroupedC27.valid2
#print axioms N11Formalization.C450TenthGroupedC27.valid3
#print axioms N11Formalization.C450TenthGroupedC27.valid4
#print axioms N11Formalization.C450TenthGroupedC27.valid5
#print axioms N11Formalization.C450TenthGroupedC27.valid6
#print axioms N11Formalization.C450TenthGroupedC27.valid7
#print axioms N11Formalization.C450TenthGroupedC27.valid8
#print axioms N11Formalization.C450TenthGroupedC27.valid9
#print axioms N11Formalization.C450TenthGroupedC27.valid10
#print axioms N11Formalization.C450TenthGroupedC27.valid11
#print axioms N11Formalization.C450TenthGroupedC27.valid12
#print axioms N11Formalization.C450TenthGroupedC27.valid13
#print axioms N11Formalization.C450TenthGroupedC27.valid14
#print axioms N11Formalization.C450TenthGroupedC27.valid15
#print axioms N11Formalization.C450TenthGroupedC27.valid16
#print axioms N11Formalization.C450TenthGroupedC27.bound
#print axioms N11Formalization.C450TenthGroupedC27.endpoint_checks
