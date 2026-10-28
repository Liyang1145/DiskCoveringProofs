import N11Formalization.C450Source36Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source36GroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source36Data
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((11:ℚ)/16),((3:ℚ)/4),((20321827:ℚ)/40000000),((1356572909:ℚ)/2500000000),((310580097:ℚ)/412000000),((5469718727:ℚ)/6200000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((8386316257:ℚ)/10000000000),((-999438535247806702913552788888652803:ℚ)/3068473000000000000000000000000000000),((-121863219604929475712928191:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid source36 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source36 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((1064109983:ℚ)/2000000000),((1133306783:ℚ)/2000000000),((5352403271:ℚ)/7120000000),((4519920349:ℚ)/5150000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((159059501:ℚ)/200000000),((-48934218240630476143809880773061900515844120073253629:ℚ)/148395848083496093750000000000000000000000000000000000),((-76900473124970722218403879:ℚ)/147865600000000000000000000)⟩
theorem valid1 : Valid source36 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source36 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source36 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((5560455731:ℚ)/10000000000),((1446645491:ℚ)/2500000000),((82925013041:ℚ)/108700000000),((5739936473:ℚ)/6675000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1875183217:ℚ)/2500000000),((-118266214452112317732862783653326755905943889170951928477:ℚ)/336753502294921875000000000000000000000000000000000000000),((-119281023804198295504804991:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid source36 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((1420086161:ℚ)/2500000000),((2953292353:ℚ)/5000000000),((21060947771:ℚ)/27650000000),((11659877059:ℚ)/13587500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((908294553:ℚ)/1250000000),((-71564308686354598200172388924122116873261344157924694001:ℚ)/203205334613513946533203125000000000000000000000000000000),((-473559297989418265913898599:ℚ)/924160000000000000000000000)⟩
theorem valid3 : Valid source36 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((2900096941:ℚ)/5000000000),((238662793:ℚ)/400000000),((42781066351:ℚ)/55775000000),((939988379:ℚ)/1106000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((7025709571:ℚ)/10000000000),((-30447650626355740030566059096664991203867216268511187:ℚ)/84216453814062500000000000000000000000000000000000000),((-3019225909244744440649239:ℚ)/5914624000000000000000000)⟩
theorem valid4 : Valid source36 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source36 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((11:ℚ)/16),((3:ℚ)/4),((5860104267:ℚ)/10000000000),((1506636121:ℚ)/2500000000),((86221146937:ℚ)/112500000000),((5919908363:ℚ)/6971875000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6902822043:ℚ)/10000000000),((-13472129222029026577194580080271618277426270514553607:ℚ)/37230711996182799339294433593750000000000000000000000),((-117483391107063197702412151:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid source36 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source36 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source36 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((592000549:ℚ)/1000000000),((6086508949:ℚ)/10000000000),((8688006039:ℚ)/11345000000),((23859526847:ℚ)/28125000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1355619423:ℚ)/2000000000),((-142823529564183603658617132777319100289342424733501244587:ℚ)/394368410110473632812500000000000000000000000000000000000),((-1872391385091672669360745711:ℚ)/3696640000000000000000000000)⟩
theorem valid6 : Valid source36 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((747487223:ℚ)/1250000000),((6146463481:ℚ)/10000000000),((10942359453:ℚ)/14300000000),((24039390443:ℚ)/28362500000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((831428511:ℚ)/1250000000),((-3695434985872404120605949259958754815888709558316163533989:ℚ)/10195759573895263671875000000000000000000000000000000000000),((-1864987574754244495410902071:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source36 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source36 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((5898224:ℚ)/9765625),((6206408329:ℚ)/10000000000),((689043712:ℚ)/901171875),((24219224987:ℚ)/28600000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((6522698351:ℚ)/10000000000),((-2389662249055799540452736308548387344280628047707319641:ℚ)/6588032762695312500000000000000000000000000000000000000),((-1857522826454143725320073751:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source36 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((4633:ℚ)/6400),((11:ℚ)/16),((3:ℚ)/4),((1219931297:ℚ)/2000000000),((3118188599:ℚ)/5000000000),((17771244267:ℚ)/23165000000),((12154565797:ℚ)/14418750000),((1905827251:ℚ)/2000000000),((1907725537:ℚ)/2000000000),((3080928657:ℚ)/10000000000),((3195890017:ℚ)/5000000000),((-637044360799488277776173802027911769816704519545531230941:ℚ)/1736021697278411865234375000000000000000000000000000000000),((-463441900093051303913045911:ℚ)/924160000000000000000000000)⟩
theorem valid9 : Valid source36 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source36 nn0 nn1 Qcell ((2307:ℚ)/3200) ((4633:ℚ)/6400) :=
  cell_of_packet source36 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4633:ℚ)/6400),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((1532397731:ℚ)/2500000000),((783292967:ℚ)/1250000000),((22296375041:ℚ)/29075000000),((3049878901:ℚ)/3619531250),((9519843613:ℚ)/10000000000),((476456813:ℚ)/500000000),((622285377:ℚ)/2000000000),((6325456737:ℚ)/10000000000),((-31629801977569206364996893503642954481483357214664947789:ℚ)/86170126878716796636581420898437500000000000000000000000),((-28906205307250622630197879:ℚ)/57760000000000000000000000)⟩
theorem valid10 : Valid source36 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source36 nn0 nn1 Qcell ((4633:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((11:ℚ)/16),((3:ℚ)/4),((3079761661:ℚ)/5000000000),((3163134967:ℚ)/5000000000),((44757378271:ℚ)/58625000000),((12289404901:ℚ)/14537500000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((6258532419:ℚ)/10000000000),((-4907114748940434974439785950231881893746846900971104590667:ℚ)/13508692077813720703125000000000000000000000000000000000000),((-460602628560734327183705879:ℚ)/924160000000000000000000000)⟩
theorem valid11 : Valid source36 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source36 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source36 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((6219382091:ℚ)/10000000000),((127723743:ℚ)/200000000),((90173203001:ℚ)/118200000000),((70738747:ℚ)/83750000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1530700009:ℚ)/2500000000),((-98592459429338834380491320860475615554079665708637:ℚ)/271226399230957031250000000000000000000000000000000),((-733905179889849472630439:ℚ)/1478656000000000000000000)⟩
theorem valid12 : Valid source36 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source36 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((6279232989:ℚ)/10000000000),((6446095603:ℚ)/10000000000),((90831562879:ℚ)/119150000000),((24938286809:ℚ)/29550000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((5984410397:ℚ)/10000000000),((-209685198238054716821028066120283670226882797996858647738501:ℚ)/576458137726171875000000000000000000000000000000000000000000),((-1827054445731497395118825599:ℚ)/3696640000000000000000000000)⟩
theorem valid13 : Valid source36 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source36 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((6339076209:ℚ)/10000000000),((1301199101:ℚ)/2000000000),((91489838299:ℚ)/120100000000),((5023597303:ℚ)/5957500000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((365198203:ℚ)/625000000),((-216633079467878498600792536214516669928524042470193863949:ℚ)/595177418711682128906250000000000000000000000000000000000),((-72771400075444684058465311:ℚ)/147865600000000000000000000)⟩
theorem valid14 : Valid source36 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source36 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((99982999:ℚ)/156250000),((6565887059:ℚ)/10000000000),((159979221:ℚ)/210156250),((25297661177:ℚ)/30025000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((356179203:ℚ)/625000000),((-6215269216197596391546834193322979547630089565743649267199:ℚ)/17065248364343261718750000000000000000000000000000000000000),((-1811454618110293177884067391:ℚ)/3696640000000000000000000000)⟩
theorem valid15 : Valid source36 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source36 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source36 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((6458740347:ℚ)/10000000000),((3312885233:ℚ)/5000000000),((92806143817:ℚ)/122000000000),((12738655699:ℚ)/15131250000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((44410047:ℚ)/80000000),((-721993215239425469910615764158637335930881547779403021133:ℚ)/1981187283602142333984375000000000000000000000000000000000),((-450890823436479536692131079:ℚ)/924160000000000000000000000)⟩
theorem valid16 : Valid source36 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source36 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source36 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((3259280809:ℚ)/5000000000),((1686378399:ℚ)/2500000000),((46732088899:ℚ)/61950000000),((6459135197:ℚ)/7625000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((2700031173:ℚ)/5000000000),((-613396458653461748980200724645661714479622081719250456827:ℚ)/1716488397216796875000000000000000000000000000000000000000),((-111724863922180196259510311:ℚ)/231040000000000000000000000)⟩
theorem valid17 : Valid source36 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source36 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((3319091701:ℚ)/5000000000),((6865226361:ℚ)/10000000000),((47390008711:ℚ)/62900000000),((3742239869:ℚ)/4425000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((5085628617:ℚ)/10000000000),((-774885708170548698435486516809505658030775889087791137:ℚ)/2164959338378906250000000000000000000000000000000000000),((-1771388586600123860627512631:ℚ)/3696640000000000000000000000)⟩
theorem valid18 : Valid source36 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source36 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source36 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((6757778571:ℚ)/10000000000),((3552283111:ℚ)/5000000000),((96095564281:ℚ)/129600000000),((13456849333:ℚ)/15725000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((297027109:ℚ)/625000000),((-9164075533071274779312795116552706174258528614321909129:ℚ)/26601448095703125000000000000000000000000000000000000000),((-1203766489053390507903071:ℚ)/2560000000000000000000000)⟩
theorem valid19 : Valid source36 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source36 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source36 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((437305863:ℚ)/625000000),((100761881:ℚ)/125000000),((6170364493:ℚ)/9050000000),((372285643:ℚ)/405000000),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((2005348299:ℚ)/5000000000),((-1851679410538665526492599915015746745617066466692309:ℚ)/7045226147460937500000000000000000000000000000000000),((-115406629:ℚ)/256000000)⟩
theorem valid20 : Valid source36 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source36 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((159049993:ℚ)/200000000),((9016111749:ℚ)/10000000000),((2184749923:ℚ)/3200000000),((32648335247:ℚ)/36200000000),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-10344007635118300956215973465597238288011609019259033327:ℚ)/37060881250000000000000000000000000000000000000000000000),((-115406629:ℚ)/256000000)⟩
theorem valid21 : Valid source36 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source36 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source36 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((556689543:ℚ)/625000000),((12829614963:ℚ)/10000000000),((7483584973:ℚ)/13800000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-123096402360353:ℚ)/1380000000000000),((-115406629:ℚ)/256000000)⟩
theorem valid22 : Valid source36 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source36 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source36 nn0 nn1 packet22 valid22
private theorem node0_2 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source36 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source36 nn0 nn1 Qcell ((267:ℚ)/400) ((2231:ℚ)/3200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source36 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source36 nn0 nn1 Qcell ((2231:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source36 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source36 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source36 nn0 nn1 Qcell ((2231:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_5 node5_11
private theorem node12_14 :
    CellBound source36 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source36 nn0 nn1 Qcell ((1163:ℚ)/1600) ((2383:ℚ)/3200) :=
  cell_join leaf11 node12_14
private theorem node15_17 :
    CellBound source36 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source36 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf14 node15_17
private theorem node11_17 :
    CellBound source36 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join node11_14 node14_17
private theorem node18_20 :
    CellBound source36 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf17 node18_20
private theorem node21_23 :
    CellBound source36 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound source36 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf20 node21_23
private theorem node17_23 :
    CellBound source36 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node17_20 node20_23
private theorem node11_23 :
    CellBound source36 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node11_17 node17_23
private theorem node0_23 :
    CellBound source36 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_23
theorem bound : CellBound source36 nn0 nn1 Qcell (31/50) (69/50) := node0_23
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22]
theorem packet_count : packets.length = 23 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source36GroupedC28
#check @N11Formalization.C450Source36GroupedC28.bound
#print axioms N11Formalization.C450Source36GroupedC28.valid0
#print axioms N11Formalization.C450Source36GroupedC28.valid1
#print axioms N11Formalization.C450Source36GroupedC28.valid2
#print axioms N11Formalization.C450Source36GroupedC28.valid3
#print axioms N11Formalization.C450Source36GroupedC28.valid4
#print axioms N11Formalization.C450Source36GroupedC28.valid5
#print axioms N11Formalization.C450Source36GroupedC28.valid6
#print axioms N11Formalization.C450Source36GroupedC28.valid7
#print axioms N11Formalization.C450Source36GroupedC28.valid8
#print axioms N11Formalization.C450Source36GroupedC28.valid9
#print axioms N11Formalization.C450Source36GroupedC28.valid10
#print axioms N11Formalization.C450Source36GroupedC28.valid11
#print axioms N11Formalization.C450Source36GroupedC28.valid12
#print axioms N11Formalization.C450Source36GroupedC28.valid13
#print axioms N11Formalization.C450Source36GroupedC28.valid14
#print axioms N11Formalization.C450Source36GroupedC28.valid15
#print axioms N11Formalization.C450Source36GroupedC28.valid16
#print axioms N11Formalization.C450Source36GroupedC28.valid17
#print axioms N11Formalization.C450Source36GroupedC28.valid18
#print axioms N11Formalization.C450Source36GroupedC28.valid19
#print axioms N11Formalization.C450Source36GroupedC28.valid20
#print axioms N11Formalization.C450Source36GroupedC28.valid21
#print axioms N11Formalization.C450Source36GroupedC28.valid22
#print axioms N11Formalization.C450Source36GroupedC28.bound
#print axioms N11Formalization.C450Source36GroupedC28.endpoint_checks
