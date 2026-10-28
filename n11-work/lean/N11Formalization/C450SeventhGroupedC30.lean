import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC30
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((13:ℚ)/16),((7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((13:ℚ)/16),((7:ℚ)/8),((748613899:ℚ)/1250000000),((3255740833:ℚ)/5000000000),((10131980687:ℚ)/13350000000),((23750185831:ℚ)/24800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1658047047:ℚ)/2500000000),((-138630169807400745950587120005635479:ℚ)/11896351875000000000000000000000000000),((-7721867305815371218827527:ℚ)/57760000000000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((1292797737:ℚ)/2000000000),((337450833:ℚ)/500000000),((17446370581:ℚ)/22120000000),((819385277:ℚ)/890000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1107627887:ℚ)/2000000000),((-1357543044263141901243138903017462468183461157095222327:ℚ)/101467426200000000000000000000000000000000000000000000000),((-230997104231587747922581:ℚ)/1732800000000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((13:ℚ)/16),((7:ℚ)/8),((6701523437:ℚ)/10000000000),((6867783269:ℚ)/10000000000),((90319804681:ℚ)/112500000000),((49994482883:ℚ)/55300000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1227936783:ℚ)/2500000000),((-21055840769065225268818752117578383856840541098783701307:ℚ)/1483154296875000000000000000000000000000000000000000000000),((-30755661582146705165338223:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((13:ℚ)/16),((7:ℚ)/8),((1705072483:ℚ)/2500000000),((6986549327:ℚ)/10000000000),((22965942279:ℚ)/28600000000),((50825845289:ℚ)/56250000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1142351199:ℚ)/2500000000),((-94417333654128513324642081657380455760343398187742349:ℚ)/6645925000000000000000000000000000000000000000000000000),((-30711692816872076165054247:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((6939055879:ℚ)/10000000000),((3522966079:ℚ)/5000000000),((31135908809:ℚ)/38450000000),((25620762553:ℚ)/28600000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((4201355299:ℚ)/10000000000),((-1944712451443137809497558352706882716315568277282440683:ℚ)/133229475292968750000000000000000000000000000000000000000),((-7672425565602321079253063:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((27337651:ℚ)/39062500),((7105314861:ℚ)/10000000000),((367889463:ℚ)/454296875),((17219068009:ℚ)/19225000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((500685843:ℚ)/1250000000),((-684325217221796782410736562352846195370625496527:ℚ)/46880178064107894897460937500000000000000000000000),((-92003122775854496417252509:ℚ)/693120000000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((13:ℚ)/16),((7:ℚ)/8),((1411564261:ℚ)/2000000000),((3582348719:ℚ)/5000000000),((18990335393:ℚ)/23450000000),((26036441033:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3800106157:ℚ)/10000000000),((-63027948693098304946747282420323373484120253658834613:ℚ)/4317593847656250000000000000000000000000000000000000000),((-7661427201196163746186023:ℚ)/57760000000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((4709:ℚ)/6400),((13:ℚ)/16),((7:ℚ)/8),((7117203831:ℚ)/10000000000),((7194388681:ℚ)/10000000000),((95723649803:ℚ)/117725000000),((52280720767:ℚ)/58625000000),((9493134321:ℚ)/10000000000),((4750922509:ℚ)/5000000000),((1598759513:ℚ)/5000000000),((3583574521:ℚ)/10000000000),((-18848010724590947099638373829455935795321163558015651867:ℚ)/1274665195666503906250000000000000000000000000000000000000),((-30634707866795192807034423:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((4709:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4709:ℚ)/6400),((591:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((893361881:ℚ)/1250000000),((3612039947:ℚ)/5000000000),((4004568151:ℚ)/4925000000),((26244279629:ℚ)/29431250000),((4742306471:ℚ)/5000000000),((4746567163:ℚ)/5000000000),((806129637:ℚ)/2500000000),((216904863:ℚ)/625000000),((-1379933263997624930902052681474647700480994237330079:ℚ)/93327307128906250000000000000000000000000000000000000),((-7655926474770608980355087:ℚ)/57760000000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((13:ℚ)/16),((7:ℚ)/8),((1435317247:ℚ)/2000000000),((3626885539:ℚ)/5000000000),((19299124211:ℚ)/23735000000),((26348198773:ℚ)/29550000000),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((6707457:ℚ)/20000000),((-1853397803346664310820813027100170262258853487130938617:ℚ)/125354227409765625000000000000000000000000000000000000000),((-7653175725319735120119103:ℚ)/57760000000000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((7206277393:ℚ)/10000000000),((7283462231:ℚ)/10000000000),((96881606109:ℚ)/119150000000),((52904235617:ℚ)/59337500000),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((3232930373:ℚ)/10000000000),((-19538107429879452956704414366865445158394225164586325701:ℚ)/1321515223339843750000000000000000000000000000000000000000),((-30601698874129024085391223:ℚ)/231040000000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((3617984261:ℚ)/5000000000),((1835711113:ℚ)/2500000000),((48633795393:ℚ)/60050000000),((13329977791:ℚ)/14893750000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1553805381:ℚ)/5000000000),((-617467976840194647870215129987363411303923388559552393:ℚ)/42293056665039062500000000000000000000000000000000000000),((-1911230483052333562993367:ℚ)/14440000000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((13:ℚ)/16),((7:ℚ)/8),((7295350693:ℚ)/10000000000),((11565979:ℚ)/15625000),((32679853003:ℚ)/40350000000),((83961853:ℚ)/93828125),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((568198151:ℚ)/2000000000),((-333043915598567086329639349734479359123805105245836467:ℚ)/22810674609375000000000000000000000000000000000000000000),((-37301846267235657769:ℚ)/282031250000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((13:ℚ)/16),((7:ℚ)/8),((459670797:ℚ)/625000000),((7461608557:ℚ)/10000000000),((6175720361:ℚ)/7625000000),((54151259899:ℚ)/60525000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((19901827:ℚ)/78125000),((-20227909940340959824590423695056787194153579245037009:ℚ)/1385382080078125000000000000000000000000000000000000000),((-30535653073257444600999007:ℚ)/231040000000000000000000000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((13:ℚ)/16),((7:ℚ)/8),((74141147:ℚ)/100000000),((7580372229:ℚ)/10000000000),((995834911:ℚ)/1239000000),((54982605603:ℚ)/61000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((443251183:ℚ)/2000000000),((-2352925601182240205352575661487079580437578011671:ℚ)/165105461718750000000000000000000000000000000000000),((-91474805775340889817230989:ℚ)/693120000000000000000000000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((13:ℚ)/16),((7:ℚ)/8),((3766439139:ℚ)/5000000000),((7518687:ℚ)/9765625),((50563708807:ℚ)/62900000000),((145348824:ℚ)/161328125),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((1330025293:ℚ)/10000000000),((-10828957378554659043544827408269878454743057799965943:ℚ)/759454922485351562500000000000000000000000000000000000),((-844441:ℚ)/6400000)⟩
theorem valid15 : Valid seventh packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound seventh nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((13:ℚ)/16),((7:ℚ)/8),((1530328289:ℚ)/2000000000),((7936660839:ℚ)/10000000000),((6844755919:ℚ)/8640000000),((57476625873:ℚ)/62900000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-1016428616071594851343940136137177808369360932314357:ℚ)/74649600000000000000000000000000000000000000000000000),((-844441:ℚ)/6400000)⟩
theorem valid16 : Valid seventh packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound seventh nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((13:ℚ)/16),((7:ℚ)/8),((7889166621:ℚ)/10000000000),((2459205073:ℚ)/2500000000),((105759166073:ℚ)/160000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-17304994858174234674751315638506594846414431204449936131:ℚ)/2400000000000000000000000000000000000000000000000000000000),((-844441:ℚ)/6400000)⟩
theorem valid17 : Valid seventh packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((13:ℚ)/16),((7:ℚ)/8),((391572999:ℚ)/400000000),((13637007467:ℚ)/10000000000),((5218448987:ℚ)/8832000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-312648222155921853589624957942969:ℚ)/86116663296000000000000000000000000),((-844441:ℚ)/6400000)⟩
theorem valid18 : Valid seventh packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet18 valid18
private theorem node0_2 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((591:ℚ)/800) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node12_14 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound seventh nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf11 node12_14
private theorem node9_14 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join node9_11 node11_14
private theorem node14_16 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf14 leaf15
private theorem node17_19 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound seventh nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf16 node17_19
private theorem node14_19 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node14_16 node16_19
private theorem node9_19 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_14 node14_19
private theorem node0_19 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_19
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_19
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18]
theorem packet_count : packets.length = 19 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC30
#check @N11Formalization.C450SeventhGroupedC30.bound
#print axioms N11Formalization.C450SeventhGroupedC30.valid0
#print axioms N11Formalization.C450SeventhGroupedC30.valid1
#print axioms N11Formalization.C450SeventhGroupedC30.valid2
#print axioms N11Formalization.C450SeventhGroupedC30.valid3
#print axioms N11Formalization.C450SeventhGroupedC30.valid4
#print axioms N11Formalization.C450SeventhGroupedC30.valid5
#print axioms N11Formalization.C450SeventhGroupedC30.valid6
#print axioms N11Formalization.C450SeventhGroupedC30.valid7
#print axioms N11Formalization.C450SeventhGroupedC30.valid8
#print axioms N11Formalization.C450SeventhGroupedC30.valid9
#print axioms N11Formalization.C450SeventhGroupedC30.valid10
#print axioms N11Formalization.C450SeventhGroupedC30.valid11
#print axioms N11Formalization.C450SeventhGroupedC30.valid12
#print axioms N11Formalization.C450SeventhGroupedC30.valid13
#print axioms N11Formalization.C450SeventhGroupedC30.valid14
#print axioms N11Formalization.C450SeventhGroupedC30.valid15
#print axioms N11Formalization.C450SeventhGroupedC30.valid16
#print axioms N11Formalization.C450SeventhGroupedC30.valid17
#print axioms N11Formalization.C450SeventhGroupedC30.valid18
#print axioms N11Formalization.C450SeventhGroupedC30.bound
#print axioms N11Formalization.C450SeventhGroupedC30.endpoint_checks
