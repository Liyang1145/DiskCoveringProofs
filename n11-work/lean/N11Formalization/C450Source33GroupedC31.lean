import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC31
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((7:ℚ)/8),((15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((7:ℚ)/8),((15:ℚ)/16),((4983979299:ℚ)/10000000000),((2662224297:ℚ)/5000000000),((44807855093:ℚ)/51500000000),(1:ℚ),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((4277860253:ℚ)/5000000000),((-4164859802659739:ℚ)/12875000000000000),((-998665653627271508900927873:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((5222071801:ℚ)/10000000000),((1112590163:ℚ)/2000000000),((15491500869:ℚ)/17800000000),(1:ℚ),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((8132859953:ℚ)/10000000000),((-283825529344626843163277:ℚ)/869140625000000000000000),((-985337348214650975647458473:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((5460121993:ℚ)/10000000000),((5682175489:ℚ)/10000000000),((48140853951:ℚ)/54350000000),((21142526467:ℚ)/21360000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7692434803:ℚ)/10000000000),((-6820665199777667315750584959706368925970291325375725889751:ℚ)/19862529773760000000000000000000000000000000000000000000000),((-979067378506773442317003977:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((697391577:ℚ)/1250000000),((72517297:ℚ)/125000000),((6121741039:ℚ)/6912500000),((268751891:ℚ)/271750000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1492922603:ℚ)/2000000000),((-64080720788635498480123624303240718411801645176511:ℚ)/185787734503784179687500000000000000000000000000000),((-15194296254849588747138217:ℚ)/28880000000000000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((356133391:ℚ)/625000000),((732622751:ℚ)/1250000000),((3112933737:ℚ)/3485937500),((2709868253:ℚ)/2765000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((18077633:ℚ)/25000000),((-1495445404233078248480896315940599291027225122670748853:ℚ)/4210822690703125000000000000000000000000000000000000000),((-3786412770086207653696913:ℚ)/7220000000000000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((7:ℚ)/8),((15:ℚ)/16),((5757631851:ℚ)/10000000000),((370036029:ℚ)/625000000),((50223422957:ℚ)/56250000000),((1366108087:ℚ)/1394375000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((711193859:ℚ)/1000000000),((-235836483970932437785298889690179341152739419652273:ℚ)/663030418853759765625000000000000000000000000000000),((-966013332139789569668108273:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((581712737:ℚ)/1000000000),((2990083613:ℚ)/5000000000),((5063989159:ℚ)/5672500000),((11018250839:ℚ)/11250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((6991158149:ℚ)/10000000000),((-719277138162712634341787835913299648822738061501641088123:ℚ)/2019166259765625000000000000000000000000000000000000000000),((-9627072989008374669831737:ℚ)/18483200000000000000000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((91822201:ℚ)/156250000),((377484649:ℚ)/625000000),((797755407:ℚ)/893750000),((1388453947:ℚ)/1418125000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1717155319:ℚ)/2500000000),((-3637174781939897839190632369002665574451388934473037:ℚ)/10195759573895263671875000000000000000000000000000000),((-117114692881189319468749:ℚ)/225625000000000000000000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((7:ℚ)/8),((15:ℚ)/16),((1187222477:ℚ)/2000000000),((6069546641:ℚ)/10000000000),((10294557339:ℚ)/11487500000),((22304639923:ℚ)/22880000000),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((6744229487:ℚ)/10000000000),((-1864719929050471520371009058491777721794443425019404781103:ℚ)/5159704767360000000000000000000000000000000000000000000000),((-38314268432115644873506017:ℚ)/73932800000000000000000000)⟩
theorem valid8 : Valid source33 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet source33 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((298292871:ℚ)/500000000),((609933803:ℚ)/1000000000),((2584050097:ℚ)/2883750000),((2239401409:ℚ)/2297500000),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((668130483:ℚ)/1000000000),((-1580803738781837888053550077117361281540946720010671299:ℚ)/4371537223176269531250000000000000000000000000000000000),((-2390516994310641548032393:ℚ)/4620800000000000000000000)⟩
theorem valid9 : Valid source33 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source33 nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2307:ℚ)/3200),((4633:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((299780099:ℚ)/500000000),((3064564281:ℚ)/5000000000),((2594460693:ℚ)/2895625000),((11241692843:ℚ)/11535000000),((1905827251:ℚ)/2000000000),((1907725537:ℚ)/2000000000),((3080928657:ℚ)/10000000000),((661787543:ℚ)/1000000000),((-21440121050492792378259750716740887929678621676995807969:ℚ)/59256207267103125000000000000000000000000000000000000000),((-2386393641596842334511073:ℚ)/4620800000000000000000000)⟩
theorem valid10 : Valid source33 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source33 nn0 nn1 Qcell ((2307:ℚ)/3200) ((4633:ℚ)/6400) :=
  cell_of_packet source33 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4633:ℚ)/6400),((1163:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((6025346071:ℚ)/10000000000),((6158918249:ℚ)/10000000000),((52097422497:ℚ)/58150000000),((22572754747:ℚ)/23165000000),((9519843613:ℚ)/10000000000),((476456813:ℚ)/500000000),((622285377:ℚ)/2000000000),((655392629:ℚ)/1000000000),((-8177759622072904576804021542315776611435353767587963553:ℚ)/22588981740494335937500000000000000000000000000000000000),((-952908686835895707014323593:ℚ)/1848320000000000000000000000)⟩
theorem valid11 : Valid source33 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source33 nn0 nn1 Qcell ((4633:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1163:ℚ)/1600),((4671:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((3027544849:ℚ)/5000000000),((61887071:ℚ)/100000000),((26152813943:ℚ)/29193750000),((226621213:ℚ)/232600000),((148605427:ℚ)/156250000),((4759921809:ℚ)/5000000000),((98156347:ℚ)/312500000),((3244720851:ℚ)/5000000000),((-3326869829716723205143316373520782090436235408509411:ℚ)/9184574145296250000000000000000000000000000000000000),((-237815121944706486605570073:ℚ)/462080000000000000000000000)⟩
theorem valid12 : Valid source33 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((4671:ℚ)/6400) :=
  cell_of_packet source33 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4671:ℚ)/6400),((469:ℚ)/640),((7:ℚ)/8),((15:ℚ)/16),((6084832867:ℚ)/10000000000),((3109247563:ℚ)/5000000000),((52513830069:ℚ)/58625000000),((11375742689:ℚ)/11677500000),((9501845013:ℚ)/10000000000),((9510747333:ℚ)/10000000000),((792422551:ℚ)/2500000000),((6424405197:ℚ)/10000000000),((-72499744164736668755481028920072568330909969071795932633:ℚ)/200044079549912109375000000000000000000000000000000000000),((-949612858816779402383165697:ℚ)/1848320000000000000000000000)⟩
theorem valid13 : Valid source33 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source33 nn0 nn1 Qcell ((4671:ℚ)/6400) ((469:ℚ)/640) :=
  cell_of_packet source33 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((469:ℚ)/640),((4709:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((191080487:ℚ)/312500000),((195258823:ℚ)/312500000),((1647563409:ℚ)/1839453125),((101968067:ℚ)/104687500),((9493134321:ℚ)/10000000000),((4750922509:ℚ)/5000000000),((1598759513:ℚ)/5000000000),((1589699873:ℚ)/2500000000),((-306106776895460814616928830162423484352598679637651:ℚ)/844176391959190368652343750000000000000000000000000),((-925747850993380843504737:ℚ)/1805000000000000000000000)⟩
theorem valid14 : Valid source33 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source33 nn0 nn1 Qcell ((469:ℚ)/640) ((4709:ℚ)/6400) :=
  cell_of_packet source33 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4709:ℚ)/6400),((591:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((1228863571:ℚ)/2000000000),((6278068741:ℚ)/10000000000),((10586044997:ℚ)/11820000000),((22930206223:ℚ)/23545000000),((4742306471:ℚ)/5000000000),((4746567163:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3146303217:ℚ)/5000000000),((-437287817226159102644032234634055279409106806195186682609:ℚ)/1205323409022246093750000000000000000000000000000000000000),((-37852772357210016948978593:ℚ)/73932800000000000000000000)⟩
theorem valid15 : Valid source33 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source33 nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((6174059683:ℚ)/10000000000),((126157087:ℚ)/200000000),((53138417781:ℚ)/59337500000),((460391261:ℚ)/472800000),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((194556467:ℚ)/312500000),((-341456907494220505598280162632772915805993116691357157:ℚ)/940703819555520000000000000000000000000000000000000000),((-944673386813222565442964097:ℚ)/1848320000000000000000000000)⟩
theorem valid16 : Valid source33 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet source33 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((1550950269:ℚ)/2500000000),((3168819587:ℚ)/5000000000),((13336651883:ℚ)/14893750000),((11554458761:ℚ)/11867500000),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((1539595233:ℚ)/2500000000),((-226005622585301182623908481644581995040596095917432047791:ℚ)/622331508161398925781250000000000000000000000000000000000),((-58939252026516185002993953:ℚ)/115520000000000000000000000)⟩
theorem valid17 : Valid source33 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source33 nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((2383:ℚ)/3200),((957:ℚ)/1280),((7:ℚ)/8),((15:ℚ)/16),((3116771019:ℚ)/5000000000),((318371161:ℚ)/500000000),((26777397133:ℚ)/29906250000),((1159913483:ℚ)/1191500000),((75681297:ℚ)/80000000),((2367032267:ℚ)/2500000000),((1650403157:ℚ)/5000000000),((6090307237:ℚ)/10000000000),((-22975308999766333504362006830258626858154854135458263:ℚ)/63234503436811523437500000000000000000000000000000000),((-235345811335720473611291953:ℚ)/462080000000000000000000000)⟩
theorem valid18 : Valid source33 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source33 nn0 nn1 Qcell ((2383:ℚ)/3200) ((957:ℚ)/1280) :=
  cell_of_packet source33 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((957:ℚ)/1280),((1201:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((3131641287:ℚ)/5000000000),((6397206499:ℚ)/10000000000),((26881489009:ℚ)/30025000000),((23287619497:ℚ)/23925000000),((4726187811:ℚ)/5000000000),((946016213:ℚ)/1000000000),((831186567:ℚ)/2500000000),((6021563539:ℚ)/10000000000),((-4151918459617753534969296504507074470190084288163697009:ℚ)/11421847429394531250000000000000000000000000000000000000),((-234934756229253957853871337:ℚ)/462080000000000000000000000)⟩
theorem valid19 : Valid source33 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source33 nn0 nn1 Qcell ((957:ℚ)/1280) ((1201:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((6293022689:ℚ)/10000000000),((807096349:ℚ)/1250000000),((53971158823:ℚ)/60525000000),((2933289047:ℚ)/3002500000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((2976063133:ℚ)/5000000000),((-14735186394123326115572615881096484824056216262011617891:ℚ)/40956596074423828125000000000000000000000000000000000000),((-936341348446809082158850233:ℚ)/1848320000000000000000000000)⟩
theorem valid20 : Valid source33 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source33 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/8),((15:ℚ)/16),((3176250839:ℚ)/5000000000),((6516332123:ℚ)/10000000000),((27193755873:ℚ)/30500000000),((23644996369:ℚ)/24210000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((72638373:ℚ)/125000000),((-194835912435352441324660121194349046328045902785637922573:ℚ)/540996207575625000000000000000000000000000000000000000000),((-233263955707518946072933833:ℚ)/462080000000000000000000000)⟩
theorem valid21 : Valid source33 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source33 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source33 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((1602994761:ℚ)/2500000000),((10274829:ℚ)/15625000),((13700963327:ℚ)/15368750000),((37224487:ℚ)/38125000),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((1133384057:ℚ)/2000000000),((-7675508803619848932006471108257679612756689351509:ℚ)/21291590843200683593750000000000000000000000000000),((-58110784596145999890607433:ℚ)/115520000000000000000000000)⟩
theorem valid22 : Valid source33 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source33 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((6471454823:ℚ)/10000000000),((1658861543:ℚ)/2500000000),((55220183761:ℚ)/61950000000),((6000584629:ℚ)/6147500000),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((1103886453:ℚ)/2000000000),((-9273723479521546530122164636260264525075590703483388421:ℚ)/25700933383623046875000000000000000000000000000000000000),((-926491536474293750056029417:ℚ)/1848320000000000000000000000)⟩
theorem valid23 : Valid source33 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source33 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((6530929053:ℚ)/10000000000),((844318647:ℚ)/1250000000),((55636503371:ℚ)/62900000000),((3044955941:ℚ)/3097500000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((214733103:ℚ)/400000000),((-576427698257312698018677610689892598676139430728591:ℚ)/1629921210222244262695312500000000000000000000000000),((-919705512190138503666547457:ℚ)/1848320000000000000000000000)⟩
theorem valid24 : Valid source33 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source33 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/8),((15:ℚ)/16),((3324936503:ℚ)/5000000000),((6992724001:ℚ)/10000000000),((9411518507:ℚ)/10800000000),((25074172003:ℚ)/25160000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((5053950249:ℚ)/10000000000),((-91273909155336075154508014625418226834088634689220430937:ℚ)/268766844120000000000000000000000000000000000000000000000),((-226535389386536258780498057:ℚ)/462080000000000000000000000)⟩
theorem valid25 : Valid source33 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source33 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((81:ℚ)/100),((343:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((6887743811:ℚ)/10000000000),((7468961073:ℚ)/10000000000),((58134206677:ℚ)/68600000000),(1:ℚ),((57977633:ℚ)/62500000),((2332870371:ℚ)/2500000000),((1913736159:ℚ)/5000000000),((1090982841:ℚ)/2500000000),((-7509835107882622584140851:ℚ)/22968750000000000000000000),((-879045307473180160602599233:ℚ)/1848320000000000000000000000)⟩
theorem valid26 : Valid source33 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((343:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((343:ℚ)/400),((181:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((736342367:ℚ)/1000000000),((993133479:ℚ)/1250000000),((6146396569:ℚ)/7240000000),(1:ℚ),((9252071821:ℚ)/10000000000),((1855284257:ℚ)/2000000000),((1946075537:ℚ)/5000000000),((625413019:ℚ)/2500000000),((-5951268118856922006319597:ℚ)/18100000000000000000000000),((-8733320264679361549744697:ℚ)/18483200000000000000000000)⟩
theorem valid27 : Valid source33 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source33 nn0 nn1 Qcell ((343:ℚ)/400) ((181:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((7:ℚ)/8),((15:ℚ)/16),((313561281:ℚ)/400000000),((8896964989:ℚ)/10000000000),((2591728967:ℚ)/3200000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-193942539273802078580713:ℚ)/625000000000000000000000),((-30276271:ℚ)/64000000)⟩
theorem valid28 : Valid source33 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source33 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/8),((15:ℚ)/16),((137344923:ℚ)/156250000),((6350968377:ℚ)/5000000000),((1116414461:ℚ)/1725000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-94053979322803:ℚ)/431250000000000),((-30276271:ℚ)/64000000)⟩
theorem valid29 : Valid source33 packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet29 valid29
private theorem node1_3 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source33 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2269:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source33 nn0 nn1 Qcell ((2269:ℚ)/3200) ((919:ℚ)/1280) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source33 nn0 nn1 Qcell ((919:ℚ)/1280) ((4633:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source33 nn0 nn1 Qcell ((2269:ℚ)/3200) ((4633:ℚ)/6400) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source33 nn0 nn1 Qcell ((4633:ℚ)/6400) ((4671:ℚ)/6400) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source33 nn0 nn1 Qcell ((4671:ℚ)/6400) ((4709:ℚ)/6400) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source33 nn0 nn1 Qcell ((4633:ℚ)/6400) ((4709:ℚ)/6400) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source33 nn0 nn1 Qcell ((2269:ℚ)/3200) ((4709:ℚ)/6400) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((4709:ℚ)/6400) :=
  cell_join node0_7 node7_15
private theorem node16_18 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source33 nn0 nn1 Qcell ((4709:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_join leaf15 node16_18
private theorem node18_20 :
    CellBound source33 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join leaf18 leaf19
private theorem node20_22 :
    CellBound source33 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf20 leaf21
private theorem node18_22 :
    CellBound source33 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join node18_20 node20_22
private theorem node15_22 :
    CellBound source33 nn0 nn1 Qcell ((4709:ℚ)/6400) ((61:ℚ)/80) :=
  cell_join node15_18 node18_22
private theorem node22_24 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf22 leaf23
private theorem node24_26 :
    CellBound source33 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf24 leaf25
private theorem node22_26 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join node22_24 node24_26
private theorem node26_28 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_join leaf26 leaf27
private theorem node28_30 :
    CellBound source33 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf28 leaf29
private theorem node26_30 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join node26_28 node28_30
private theorem node22_30 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node22_26 node26_30
private theorem node15_30 :
    CellBound source33 nn0 nn1 Qcell ((4709:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node15_22 node22_30
private theorem node0_30 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_15 node15_30
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_30
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29]
theorem packet_count : packets.length = 30 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC31
#check @N11Formalization.C450Source33GroupedC31.bound
#print axioms N11Formalization.C450Source33GroupedC31.valid0
#print axioms N11Formalization.C450Source33GroupedC31.valid1
#print axioms N11Formalization.C450Source33GroupedC31.valid2
#print axioms N11Formalization.C450Source33GroupedC31.valid3
#print axioms N11Formalization.C450Source33GroupedC31.valid4
#print axioms N11Formalization.C450Source33GroupedC31.valid5
#print axioms N11Formalization.C450Source33GroupedC31.valid6
#print axioms N11Formalization.C450Source33GroupedC31.valid7
#print axioms N11Formalization.C450Source33GroupedC31.valid8
#print axioms N11Formalization.C450Source33GroupedC31.valid9
#print axioms N11Formalization.C450Source33GroupedC31.valid10
#print axioms N11Formalization.C450Source33GroupedC31.valid11
#print axioms N11Formalization.C450Source33GroupedC31.valid12
#print axioms N11Formalization.C450Source33GroupedC31.valid13
#print axioms N11Formalization.C450Source33GroupedC31.valid14
#print axioms N11Formalization.C450Source33GroupedC31.valid15
#print axioms N11Formalization.C450Source33GroupedC31.valid16
#print axioms N11Formalization.C450Source33GroupedC31.valid17
#print axioms N11Formalization.C450Source33GroupedC31.valid18
#print axioms N11Formalization.C450Source33GroupedC31.valid19
#print axioms N11Formalization.C450Source33GroupedC31.valid20
#print axioms N11Formalization.C450Source33GroupedC31.valid21
#print axioms N11Formalization.C450Source33GroupedC31.valid22
#print axioms N11Formalization.C450Source33GroupedC31.valid23
#print axioms N11Formalization.C450Source33GroupedC31.valid24
#print axioms N11Formalization.C450Source33GroupedC31.valid25
#print axioms N11Formalization.C450Source33GroupedC31.valid26
#print axioms N11Formalization.C450Source33GroupedC31.valid27
#print axioms N11Formalization.C450Source33GroupedC31.valid28
#print axioms N11Formalization.C450Source33GroupedC31.valid29
#print axioms N11Formalization.C450Source33GroupedC31.bound
#print axioms N11Formalization.C450Source33GroupedC31.endpoint_checks
