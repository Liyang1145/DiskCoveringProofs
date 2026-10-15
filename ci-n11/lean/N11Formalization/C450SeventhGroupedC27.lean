import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((6032549917:ℚ)/10000000000),((654817391:ℚ)/1000000000),((2117516639:ℚ)/3560000000),((7586991301:ℚ)/9920000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((408647381:ℚ)/625000000),((-21389955187163647820819528656237:ℚ)/5639752000000000000000000000000000),((-207929679783544607568106059:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((6507724329:ℚ)/10000000000),((6785736667:ℚ)/10000000000),((6827724329:ℚ)/11060000000),((78483103337:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((5427733283:ℚ)/10000000000),((-63184859496715275491035127895747311895736868577923483:ℚ)/12683428275000000000000000000000000000000000000000000000),((-625391474158558084538119913:ℚ)/5544960000000000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/8),((11:ℚ)/16),((3372651271:ℚ)/5000000000),((1380903291:ℚ)/2000000000),((3532651271:ℚ)/5625000000),((15957936201:ℚ)/22120000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2394093451:ℚ)/5000000000),((-1024786473154460650463438236827376864458005793088597:ℚ)/185394287109375000000000000000000000000000000000000000),((-52185510045517528431911171:ℚ)/462080000000000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((3432044833:ℚ)/5000000000),((3511647627:ℚ)/5000000000),((276311141:ℚ)/440000000),((13516041299:ℚ)/18750000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4436995457:ℚ)/10000000000),((-134693186006989008977675203577084193347381492911:ℚ)/24200000000000000000000000000000000000000000000000),((-52220983433810889559627059:ℚ)/462080000000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((1745718889:ℚ)/2500000000),((7082684297:ℚ)/10000000000),((608572963:ℚ)/961250000),((81749527267:ℚ)/114400000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((4057682649:ℚ)/10000000000),((-12116734845375764351107909829340272273758226509969:ℚ)/2081710551452636718750000000000000000000000000000000),((-13064230282941792604356451:ℚ)/115520000000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((3521134029:ℚ)/5000000000),((7142073111:ℚ)/10000000000),((3681134029:ℚ)/5815000000),((27467601407:ℚ)/38450000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3854902111:ℚ)/10000000000),((-143411703178247618203735901327402431436622495506981:ℚ)/24578714796875000000000000000000000000000000000000000),((-156825192295187422390971713:ℚ)/1386240000000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((5:ℚ)/8),((11:ℚ)/16),((7101660273:ℚ)/10000000000),((7201461701:ℚ)/10000000000),((7421660273:ℚ)/11725000000),((83056078711:ℚ)/116300000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3641439559:ℚ)/10000000000),((-3156348767501710179669530479341113281882941337921253:ℚ)/539699230957031250000000000000000000000000000000000000),((-627519877724611055617888697:ℚ)/5544960000000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((4709:ℚ)/6400),((5:ℚ)/8),((11:ℚ)/16),((716105221:ℚ)/1000000000),((7231155913:ℚ)/10000000000),((748105221:ℚ)/1177250000),((83382715043:ℚ)/117250000000),((9493134321:ℚ)/10000000000),((4750922509:ℚ)/5000000000),((1598759513:ℚ)/5000000000),((3415288513:ℚ)/10000000000),((-7609609174362261568273681580013548551842211428181:ℚ)/1274665195666503906250000000000000000000000000000000),((-2092467930753670364256571:ℚ)/18483200000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((4709:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4709:ℚ)/6400),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((287629923:ℚ)/400000000),((907606259:ℚ)/1250000000),((300429923:ℚ)/472800000),((10463668849:ℚ)/14715625000),((4742306471:ℚ)/5000000000),((4746567163:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3296643279:ℚ)/10000000000),((-493402933118550408072167096888818302330309765043:ℚ)/82570028400000000000000000000000000000000000000000),((-2782719788731930805177:ℚ)/24576000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((3610221937:ℚ)/5000000000),((732023823:ℚ)/1000000000),((3770221937:ℚ)/5957500000),((2812087351:ℚ)/3940000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((3173733323:ℚ)/10000000000),((-11642914980605567742001078074613787087147020070274971:ℚ)/1982272835009765625000000000000000000000000000000000000),((-52330189473698702898283539:ℚ)/462080000000000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((909979409:ℚ)/1250000000),((368981309:ℚ)/500000000),((949979409:ℚ)/1501250000),((4250794399:ℚ)/5957500000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((1456469811:ℚ)/5000000000),((-3889089447903681181207199605362750407326341902521:ℚ)/660829010391235351562500000000000000000000000000000),((-3271799797430405080500211:ℚ)/28880000000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((5:ℚ)/8),((11:ℚ)/16),((7339226411:ℚ)/10000000000),((3719506963:ℚ)/5000000000),((7659226411:ℚ)/12105000000),((42834576593:ℚ)/60050000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((1313589593:ℚ)/5000000000),((-3631409668722598758156057687699629913994954383824851:ℚ)/615888214453125000000000000000000000000000000000000000),((-209470080500231712728801051:ℚ)/1848320000000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((462413581:ℚ)/625000000),((3749200737:ℚ)/5000000000),((482413581:ℚ)/762500000),((14387069369:ℚ)/20175000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2307187891:ℚ)/10000000000),((-8183005325537030854349785147255202291333537622349:ℚ)/1385382080078125000000000000000000000000000000000000),((-818536868316941731232891:ℚ)/7220000000000000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((3729003967:ℚ)/5000000000),((7617175993:ℚ)/10000000000),((3889003967:ℚ)/6195000000),((87628935923:ℚ)/122000000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1936059659:ℚ)/10000000000),((-39302475202577530303515605101735961737975742731261:ℚ)/6879394238281250000000000000000000000000000000000000),((-52405315101316149995542259:ℚ)/462080000000000000000000000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((757678849:ℚ)/1000000000),((773594977:ℚ)/1000000000),((46451697:ℚ)/74000000),((8893544747:ℚ)/12390000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((78175469:ℚ)/1000000000),((-7091915960609102257064015321382453778037873:ℚ)/1236645507812500000000000000000000000000000000),((-2097742976232181453641331:ℚ)/18483200000000000000000000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((7695568123:ℚ)/10000000000),((7973495233:ℚ)/10000000000),((2671856041:ℚ)/4320000000),((91548447563:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-50151903634412164965128937631160358206743922255683:ℚ)/9331200000000000000000000000000000000000000000000000),((-908087:ℚ)/8000000)⟩
theorem valid15 : Valid seventh packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound seventh nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((396656239:ℚ)/500000000),((4936890589:ℚ)/5000000000),((412656239:ℚ)/800000000),((56225796479:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-477285735203686684697998317998947499469031713317:ℚ)/300000000000000000000000000000000000000000000000000),((-908087:ℚ)/8000000)⟩
theorem valid16 : Valid seventh packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((2458370283:ℚ)/2500000000),((6837058411:ℚ)/5000000000),((2538370283:ℚ)/5520000000),((77127642521:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1673963599016486418743:ℚ)/1523520000000000000000000),((-908087:ℚ)/8000000)⟩
theorem valid17 : Valid seventh packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet17 valid17
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
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound seventh nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_9 node9_18
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_18
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17]
theorem packet_count : packets.length = 18 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC27
#check @N11Formalization.C450SeventhGroupedC27.bound
#print axioms N11Formalization.C450SeventhGroupedC27.valid0
#print axioms N11Formalization.C450SeventhGroupedC27.valid1
#print axioms N11Formalization.C450SeventhGroupedC27.valid2
#print axioms N11Formalization.C450SeventhGroupedC27.valid3
#print axioms N11Formalization.C450SeventhGroupedC27.valid4
#print axioms N11Formalization.C450SeventhGroupedC27.valid5
#print axioms N11Formalization.C450SeventhGroupedC27.valid6
#print axioms N11Formalization.C450SeventhGroupedC27.valid7
#print axioms N11Formalization.C450SeventhGroupedC27.valid8
#print axioms N11Formalization.C450SeventhGroupedC27.valid9
#print axioms N11Formalization.C450SeventhGroupedC27.valid10
#print axioms N11Formalization.C450SeventhGroupedC27.valid11
#print axioms N11Formalization.C450SeventhGroupedC27.valid12
#print axioms N11Formalization.C450SeventhGroupedC27.valid13
#print axioms N11Formalization.C450SeventhGroupedC27.valid14
#print axioms N11Formalization.C450SeventhGroupedC27.valid15
#print axioms N11Formalization.C450SeventhGroupedC27.valid16
#print axioms N11Formalization.C450SeventhGroupedC27.valid17
#print axioms N11Formalization.C450SeventhGroupedC27.bound
#print axioms N11Formalization.C450SeventhGroupedC27.endpoint_checks
