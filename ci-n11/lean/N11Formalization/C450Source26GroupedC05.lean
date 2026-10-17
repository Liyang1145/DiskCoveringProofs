import N11Formalization.C450Source26Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source26GroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source26Data
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((3410340889:ℚ)/5000000000),((1406807091:ℚ)/2000000000),((-3452421273:ℚ)/4960000000),((-9837916593:ℚ)/16850000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((1142059017:ℚ)/2500000000),((22454315963514278418135293926072431925461154773395817351793:ℚ)/86613352422400000000000000000000000000000000000000000000000),((604322341851158676704253:ℚ)/1155200000000000000000000)⟩
theorem valid0 : Valid source26 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((6940175279:ℚ)/10000000000),((3546867689:ℚ)/5000000000),((-2906867689:ℚ)/4212500000),((-60341928069:ℚ)/102050000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((4197742777:ℚ)/10000000000),((308150242465467232904304412199660284594339114467517016641:ℚ)/1216370239179939270019531250000000000000000000000000000000),((2413351761623468937461613:ℚ)/4620800000000000000000000)⟩
theorem valid1 : Valid source26 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source26 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((4101:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((54686809:ℚ)/78125000),((7123583063:ℚ)/10000000000),((-17530749189:ℚ)/25512500000),((-317703266:ℚ)/533984375),((4940065779:ℚ)/5000000000),((1979272569:ℚ)/2000000000),((774947369:ℚ)/5000000000),((2000256783:ℚ)/5000000000),((12144307087307208162905081132233615842894691176536847857773629:ℚ)/48485972220363064575195312500000000000000000000000000000000000),((1177414964288119839939:ℚ)/2256250000000000000000)⟩
theorem valid2 : Valid source26 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source26 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((4101:ℚ)/6400),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((1405955431:ℚ)/2000000000),((357671463:ℚ)/500000000),((-293671463:ℚ)/427187500),((-12265509741:ℚ)/20600000000),((9864186891:ℚ)/10000000000),((9880131563:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((3898378949:ℚ)/10000000000),((124368798625674862390282644702155218478293539955774457357:ℚ)/496228048618780517578125000000000000000000000000000000000),((96431632623832757266173:ℚ)/184832000000000000000000)⟩
theorem valid3 : Valid source26 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source26 nn0 nn1 Qcell ((4101:ℚ)/6400) ((103:ℚ)/160) :=
  cell_of_packet source26 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7059641101:ℚ)/10000000000),((7183273987:ℚ)/10000000000),((-17709821961:ℚ)/25750000000),((-61656052111:ℚ)/103475000000),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((3793645627:ℚ)/10000000000),((4584592237151434905415486710448294072181881638854933453786089:ℚ)/18281110353874023437500000000000000000000000000000000000000000),((2410229565173607313851093:ℚ)/4620800000000000000000000)⟩
theorem valid4 : Valid source26 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4139:ℚ)/6400),((2079:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((1772375853:ℚ)/2500000000),((3606558633:ℚ)/5000000000),((-8899675899:ℚ)/12934375000),((-15496134383:ℚ)/25987500000),((4916570841:ℚ)/5000000000),((1969704979:ℚ)/2000000000),((1829340989:ℚ)/10000000000),((3686091507:ℚ)/10000000000),((333375318532867654431858613315172349303567931593570601891201:ℚ)/1328533970507206392288208007812500000000000000000000000000000),((150603881013546974025237:ℚ)/288800000000000000000000)⟩
theorem valid5 : Valid source26 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source26 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((444960257:ℚ)/625000000),((7242959117:ℚ)/10000000000),((-662551013:ℚ)/962500000),((-3894562827:ℚ)/6526562500),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((357546143:ℚ)/1000000000),((50441031725707191288031397074664339933437944155811350597:ℚ)/200893470205688476562500000000000000000000000000000000000),((9410501598308336411157:ℚ)/18050000000000000000000)⟩
theorem valid6 : Valid source26 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source26 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((7149223223:ℚ)/10000000000),((181819989:ℚ)/250000000),((-449459967:ℚ)/652656250),((-62641455453:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((173072993:ℚ)/500000000),((30742189688133910987462454820140046882372256165101468838393:ℚ)/122367044725168507385253906250000000000000000000000000000000),((2408508504545964925394397:ℚ)/4620800000000000000000000)⟩
theorem valid7 : Valid source26 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source26 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-3:ℚ)/4),((-11:ℚ)/16),((3589540383:ℚ)/5000000000),((7302638613:ℚ)/10000000000),((-18067915839:ℚ)/26225000000),((-31484944213:ℚ)/52687500000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((3343741337:ℚ)/10000000000),((201372004539383574383148885396187122669138434018154500757359:ℚ)/801090639542188476562500000000000000000000000000000000000000),((601980595711562248081677:ℚ)/1155200000000000000000000)⟩
theorem valid8 : Valid source26 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source26 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source26 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((7208936763:ℚ)/10000000000),((1466495259:ℚ)/2000000000),((-1210495259:ℚ)/1756250000),((-63298304393:ℚ)/105850000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((805474453:ℚ)/2500000000),((38162806893382281290612296840500886332075627164892599035099:ℚ)/151733244752882385253906250000000000000000000000000000000000),((2407330044522622015981317:ℚ)/4620800000000000000000000)⟩
theorem valid9 : Valid source26 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source26 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source26 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((1447758247:ℚ)/2000000000),((58898501:ℚ)/80000000),((-145975503:ℚ)/211700000),((-12725340717:ℚ)/21265000000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((619088307:ℚ)/2000000000),((269916952681888880956374441490348640130869082887100119487:ℚ)/1072589044734778231250000000000000000000000000000000000000),((96269259602488548877437:ℚ)/184832000000000000000000)⟩
theorem valid10 : Valid source26 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source26 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source26 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((3634322101:ℚ)/5000000000),((3696073811:ℚ)/5000000000),((-9168221433:ℚ)/13290625000),((-10659181037:ℚ)/17800000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((2963781427:ℚ)/10000000000),((29263447765681789960200281244548789477894947727203866934667:ℚ)/116224113909934425354003906250000000000000000000000000000000),((601531679996374294917093:ℚ)/1155200000000000000000000)⟩
theorem valid11 : Valid source26 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source26 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source26 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-3:ℚ)/4),((-11:ℚ)/16),((3649247843:ℚ)/5000000000),((1490362737:ℚ)/2000000000),((-1234362737:ℚ)/1780000000),((-32141726273:ℚ)/53875000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((282618957:ℚ)/1000000000),((19557461902498450575823491789900531195591737171793666451:ℚ)/76731882661523437500000000000000000000000000000000000000),((601607432759448904659957:ℚ)/1155200000000000000000000)⟩
theorem valid12 : Valid source26 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source26 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((183954857:ℚ)/250000000),((117366791:ℚ)/156250000),((-584200746:ℚ)/841796875),((-1623503427:ℚ)/2717500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((158081031:ℚ)/625000000),((8990123672809424242693986366408876129813847682537118155053:ℚ)/35241226931243762373924255371093750000000000000000000000000),((1503243149081120115357:ℚ)/2888000000000000000000)⟩
theorem valid13 : Valid source26 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source26 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source26 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((1854471793:ℚ)/2500000000),((3815390831:ℚ)/5000000000),((-9526172493:ℚ)/13587500000),((-2342741389:ℚ)/3950000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((43871201:ℚ)/200000000),((399164685080734405292889082110174416418730548371745500997:ℚ)/1528878231854057312011718750000000000000000000000000000000),((150300499131968549584557:ℚ)/288800000000000000000000)⟩
theorem valid14 : Valid source26 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source26 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((1507451289:ℚ)/2000000000),((393466993:ℚ)/500000000),((-988400979:ℚ)/1382500000),((-13381964179:ℚ)/22880000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1285855011:ℚ)/10000000000),((3540203827800400271954461103539453038754202267263464089:ℚ)/12988953565478515625000000000000000000000000000000000000),((95941893745801880345853:ℚ)/184832000000000000000000)⟩
theorem valid15 : Valid source26 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source26 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source26 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((311037313:ℚ)/400000000),((4411474329:ℚ)/5000000000),((-11314422987:ℚ)/14300000000),((-2781410443:ℚ)/5184000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((93863346259526490649109693181474836222248610517901664263:ℚ)/279512268750000000000000000000000000000000000000000000000),((4146843:ℚ)/8000000)⟩
theorem valid16 : Valid source26 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source26 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((1745988847:ℚ)/2000000000),((335253157:ℚ)/312500000),((-98417719:ℚ)/112500000),((-16005877317:ℚ)/32000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((171629837431812089866210321149052661068293546251303:ℚ)/427148437500000000000000000000000000000000000000000),((4146843:ℚ)/8000000)⟩
theorem valid17 : Valid source26 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source26 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((10635670401:ℚ)/10000000000),((14534139439:ℚ)/10000000000),((-39762418317:ℚ)/40000000000),((-100992374411:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((40085586731043281874141785004970847076511:ℚ)/76176000000000000000000000000000000000000),((4146843:ℚ)/8000000)⟩
theorem valid18 : Valid source26 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source26 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source26 nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source26 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source26 nn0 nn1 Qcell ((4177:ℚ)/6400) ((843:ℚ)/1280) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source26 nn0 nn1 Qcell ((2079:ℚ)/3200) ((843:ℚ)/1280) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source26 nn0 nn1 Qcell ((103:ℚ)/160) ((843:ℚ)/1280) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((843:ℚ)/1280) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source26 nn0 nn1 Qcell ((843:ℚ)/1280) ((4253:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound source26 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source26 nn0 nn1 Qcell ((4253:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound source26 nn0 nn1 Qcell ((843:ℚ)/1280) ((1087:ℚ)/1600) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound source26 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source26 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound source26 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound source26 nn0 nn1 Qcell ((843:ℚ)/1280) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound source26 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound source26 nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source26GroupedC05
#check @N11Formalization.C450Source26GroupedC05.bound
#print axioms N11Formalization.C450Source26GroupedC05.valid0
#print axioms N11Formalization.C450Source26GroupedC05.valid1
#print axioms N11Formalization.C450Source26GroupedC05.valid2
#print axioms N11Formalization.C450Source26GroupedC05.valid3
#print axioms N11Formalization.C450Source26GroupedC05.valid4
#print axioms N11Formalization.C450Source26GroupedC05.valid5
#print axioms N11Formalization.C450Source26GroupedC05.valid6
#print axioms N11Formalization.C450Source26GroupedC05.valid7
#print axioms N11Formalization.C450Source26GroupedC05.valid8
#print axioms N11Formalization.C450Source26GroupedC05.valid9
#print axioms N11Formalization.C450Source26GroupedC05.valid10
#print axioms N11Formalization.C450Source26GroupedC05.valid11
#print axioms N11Formalization.C450Source26GroupedC05.valid12
#print axioms N11Formalization.C450Source26GroupedC05.valid13
#print axioms N11Formalization.C450Source26GroupedC05.valid14
#print axioms N11Formalization.C450Source26GroupedC05.valid15
#print axioms N11Formalization.C450Source26GroupedC05.valid16
#print axioms N11Formalization.C450Source26GroupedC05.valid17
#print axioms N11Formalization.C450Source26GroupedC05.valid18
#print axioms N11Formalization.C450Source26GroupedC05.bound
#print axioms N11Formalization.C450Source26GroupedC05.endpoint_checks
