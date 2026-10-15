import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC24
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((7:ℚ)/16),((1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((7:ℚ)/16),((1:ℚ)/2),((6076515147:ℚ)/10000000000),((658507681:ℚ)/1000000000),((45735606029:ℚ)/106800000000),((706507681:ℚ)/1240000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6442649423:ℚ)/10000000000),((1201927212309427131108167:ℚ)/570312000000000000000000000),((-485225259943466269666274077:ℚ)/5544960000000000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((3275881629:ℚ)/5000000000),((1364532019:ℚ)/2000000000),((310521157:ℚ)/700000000),((1460532019:ℚ)/2670000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5314480813:ℚ)/10000000000),((939391933293819280656887170363:ℚ)/735000000000000000000000000000000),((-122657905285717972273664173:ℚ)/1386240000000000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/16),((1:ℚ)/2),((6789374517:ℚ)/10000000000),((3470724813:ℚ)/5000000000),((50725621619:ℚ)/112500000000),((3710724813:ℚ)/6912500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4660755399:ℚ)/10000000000),((5775615719743118479381176688669003:ℚ)/6328125000000000000000000000000000000),((-493377553028580998484889117:ℚ)/5544960000000000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((7:ℚ)/16),((1:ℚ)/2),((3454088663:ℚ)/5000000000),((1400168779:ℚ)/2000000000),((25778620641:ℚ)/56725000000),((1496168779:ℚ)/2812500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((268742577:ℚ)/625000000),((1191770541493640826044871014139843:ℚ)/1608862812500000000000000000000000000),((-41230100822205143184077319:ℚ)/462080000000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((7:ℚ)/16),((1:ℚ)/2),((6967578067:ℚ)/10000000000),((1765059461:ℚ)/2500000000),((51973046469:ℚ)/114400000000),((1885059461:ℚ)/3545312500),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((4108376959:ℚ)/10000000000),((85329139050878822148488148227273:ℚ)/118976000000000000000000000000000000),((-165151903782649507924736239:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((7:ℚ)/16),((1:ℚ)/2),((351348919:ℚ)/500000000),((177990787:ℚ)/250000000),((2619442433:ℚ)/5767500000),((189990787:ℚ)/357500000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1954028809:ℚ)/5000000000),((1925724362112876942785029058633:ℚ)/2772004687500000000000000000000000),((-413459995821773776826311:ℚ)/4620800000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((1771594569:ℚ)/2500000000),((1794756203:ℚ)/2500000000),((13201161983:ℚ)/29075000000),((1914756203:ℚ)/3604687500),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3697486889:ℚ)/10000000000),((56913513534577735173523445856791:ℚ)/84535562500000000000000000000000000),((-31053128804487980732360533:ℚ)/346560000000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((7:ℚ)/16),((1:ℚ)/2),((1429155553:ℚ)/2000000000),((7238417847:ℚ)/10000000000),((10644088871:ℚ)/23450000000),((7718417847:ℚ)/14537500000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1737398757:ℚ)/5000000000),((269233341210489701763470320506509:ℚ)/412426875000000000000000000000000000),((-6633998787804252271945559:ℚ)/73932800000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((900647107:ℚ)/1250000000),((228056581:ℚ)/312500000),((6704529749:ℚ)/14775000000),((486113162:ℚ)/916015625),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((647497081:ℚ)/2000000000),((34564488848309150367050563648283:ℚ)/54575156250000000000000000000000000),((-2595060102585269026789199:ℚ)/28880000000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((7:ℚ)/16),((1:ℚ)/2),((7264575561:ℚ)/10000000000),((7357203053:ℚ)/10000000000),((54052028927:ℚ)/119150000000),((7837203053:ℚ)/14775000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((2982056917:ℚ)/10000000000),((13092811173143364634952390097513943:ℚ)/21295083750000000000000000000000000000),((-498954952811330483225987413:ℚ)/5544960000000000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/16),((1:ℚ)/2),((7323973887:ℚ)/10000000000),((7416595239:ℚ)/10000000000),((54467817209:ℚ)/120100000000),((7896595239:ℚ)/14893750000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((168961043:ℚ)/625000000),((1076840723922850613546426055016949:ℚ)/1803001250000000000000000000000000000),((-499660148478567561904415557:ℚ)/5544960000000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((7:ℚ)/16),((1:ℚ)/2),((1845842961:ℚ)/2500000000),((3767689403:ℚ)/5000000000),((13720900727:ℚ)/30500000000),((4007689403:ℚ)/7506250000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2393330473:ℚ)/10000000000),((321410874630141406880542154070421:ℚ)/465125000000000000000000000000000000),((-31272945423940624354435813:ℚ)/346560000000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((7:ℚ)/16),((1:ℚ)/2),((1875541671:ℚ)/2500000000),((7772942897:ℚ)/10000000000),((13928791697:ℚ)/31450000000),((8252942897:ℚ)/15250000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1606270099:ℚ)/10000000000),((214941195877627565252910070392849:ℚ)/247275625000000000000000000000000000),((-31361651972862132217449973:ℚ)/346560000000000000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/16),((1:ℚ)/2),((77397523:ℚ)/100000000),((8010503229:ℚ)/10000000000),((63753629:ℚ)/144000000),((8490503229:ℚ)/15725000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((8368051957807985211338914837:ℚ)/10368000000000000000000000000000),((-11610357:ℚ)/128000000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((7:ℚ)/16),((1:ℚ)/2),((1994333223:ℚ)/2500000000),((2477720671:ℚ)/2500000000),((14760332561:ℚ)/40000000000),((2597720671:ℚ)/4050000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1758065371953736538659930896570151:ℚ)/600000000000000000000000000000000000),((-11610357:ℚ)/128000000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/16),((1:ℚ)/2),((2469459941:ℚ)/2500000000),((6855664039:ℚ)/5000000000),((18086219587:ℚ)/55200000000),((7095664039:ℚ)/10000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((773072576123993382630503:ℚ)/152352000000000000000000000),((-11610357:ℚ)/128000000)⟩
theorem valid15 : Valid seventh packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound seventh nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC24
#check @N11Formalization.C450SeventhGroupedC24.bound
#print axioms N11Formalization.C450SeventhGroupedC24.valid0
#print axioms N11Formalization.C450SeventhGroupedC24.valid1
#print axioms N11Formalization.C450SeventhGroupedC24.valid2
#print axioms N11Formalization.C450SeventhGroupedC24.valid3
#print axioms N11Formalization.C450SeventhGroupedC24.valid4
#print axioms N11Formalization.C450SeventhGroupedC24.valid5
#print axioms N11Formalization.C450SeventhGroupedC24.valid6
#print axioms N11Formalization.C450SeventhGroupedC24.valid7
#print axioms N11Formalization.C450SeventhGroupedC24.valid8
#print axioms N11Formalization.C450SeventhGroupedC24.valid9
#print axioms N11Formalization.C450SeventhGroupedC24.valid10
#print axioms N11Formalization.C450SeventhGroupedC24.valid11
#print axioms N11Formalization.C450SeventhGroupedC24.valid12
#print axioms N11Formalization.C450SeventhGroupedC24.valid13
#print axioms N11Formalization.C450SeventhGroupedC24.valid14
#print axioms N11Formalization.C450SeventhGroupedC24.valid15
#print axioms N11Formalization.C450SeventhGroupedC24.bound
#print axioms N11Formalization.C450SeventhGroupedC24.endpoint_checks
