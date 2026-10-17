import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC09
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((-1:ℚ)/2),((-7:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/2),((-7:ℚ)/16),((3142445541:ℚ)/5000000000),((1638535947:ℚ)/2500000000),((-1538535947:ℚ)/3100000000),((-20077118787:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2985591173:ℚ)/5000000000),((150906430065957970615131830142376099964775804987196419053:ℚ)/13232241015625000000000000000000000000000000000000000000000),((27297146993428170106427:ℚ)/338437500000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/2),((-7:ℚ)/16),((6522487371:ℚ)/10000000000),((6791763263:ℚ)/10000000000),((-6391763263:ℚ)/12875000000),((-13939137199:ℚ)/35600000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5390007131:ℚ)/10000000000),((41309739766811803831905288448270474606067501721181990497:ℚ)/3630590350000000000000000000000000000000000000000000000000),((145219740055033464087919:ℚ)/1805000000000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((1352015361:ℚ)/2000000000),((1382113973:ℚ)/2000000000),((-434037991:ℚ)/890000000),((-8696107527:ℚ)/21740000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1186455117:ℚ)/2500000000),((31604561691751454112821584553683262948233386785382947087:ℚ)/2857713244175000000000000000000000000000000000000000000000),((5788982443643845155479:ℚ)/72200000000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((859858647:ℚ)/1250000000),((6969972431:ℚ)/10000000000),((-6569972431:ℚ)/13587500000),((-1846336843:ℚ)/4568750000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((274467309:ℚ)/625000000),((883499718641287739151695705520336501561049962375928429:ℚ)/80986337188148498535156250000000000000000000000000000000),((144477869764454854196511:ℚ)/1805000000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((693826481:ℚ)/1000000000),((3514687261:ℚ)/5000000000),((-3314687261:ℚ)/6853125000),((-4472785367:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((525488309:ℚ)/1250000000),((526794634322535842351337532932622473591113528823054757:ℚ)/48289510776171875000000000000000000000000000000000000000),((36097472067590978983871:ℚ)/451250000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((699766009:ℚ)/1000000000),((886097019:ℚ)/1250000000),((-836097019:ℚ)/1728125000),((-4514362063:ℚ)/11155000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((801622637:ℚ)/2000000000),((1635473590872247760340142763670646868534814661522008119:ℚ)/149921491509350585937500000000000000000000000000000000000),((13528359593067825345541:ℚ)/169218750000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-1:ℚ)/2),((-7:ℚ)/16),((441065939:ℚ)/625000000),((7118476797:ℚ)/10000000000),((-6718476797:ℚ)/13943750000),((-2847461573:ℚ)/7001562500),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((3802823437:ℚ)/10000000000),((1037369207390714043089555056364641507964596272815069143:ℚ)/95718193400416851043701171875000000000000000000000000000),((432539932732076026939877:ℚ)/5415000000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-1:ℚ)/2),((-7:ℚ)/16),((1771688091:ℚ)/2500000000),((7148177331:ℚ)/10000000000),((-6748177331:ℚ)/14003125000),((-3813938879:ℚ)/9375000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((739224919:ℚ)/2000000000),((1465449444399793311671509985545224604590386601042169237:ℚ)/135213509202003479003906250000000000000000000000000000000),((432409971097597362740933:ℚ)/5415000000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-1:ℚ)/2),((-7:ℚ)/16),((7116449621:ℚ)/10000000000),((1794469439:ℚ)/2500000000),((-1694469439:ℚ)/3515625000),((-45975147347:ℚ)/112975000000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((28691223:ℚ)/80000000),((439543022705457706470319387688076288988565837317420010083:ℚ)/40554549474169921875000000000000000000000000000000000000000),((281432588596134737253:ℚ)/3525390625000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((1786536699:ℚ)/2500000000),((900947259:ℚ)/1250000000),((-850947259:ℚ)/1765234375),((-11545756893:ℚ)/28362500000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((694674263:ℚ)/2000000000),((8730476265874930554658702801615506484365903254207548347:ℚ)/805500655846725463867187500000000000000000000000000000000),((3376182716229472343809:ℚ)/42304687500000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-1:ℚ)/2),((-7:ℚ)/16),((717584389:ℚ)/1000000000),((7237278281:ℚ)/10000000000),((-6837278281:ℚ)/14181250000),((-4639090723:ℚ)/11392500000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((419586881:ℚ)/1250000000),((37879290420894114734902671429646505616112379467105053989:ℚ)/3494784288678662109375000000000000000000000000000000000000),((144007588624383223061711:ℚ)/1805000000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-1:ℚ)/2),((-7:ℚ)/16),((900692613:ℚ)/1250000000),((1453395677:ℚ)/2000000000),((-457798559:ℚ)/949375000),((-5824848291:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((129439173:ℚ)/400000000),((150454784689321546539748454802153770614406383498493861549:ℚ)/13880845103125000000000000000000000000000000000000000000000),((5758594542207181649079:ℚ)/72200000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((-1:ℚ)/2),((-7:ℚ)/16),((7235237839:ℚ)/10000000000),((456042399:ℚ)/625000000),((-431042399:ℚ)/893750000),((-46806664873:ℚ)/114875000000),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((1555376681:ℚ)/5000000000),((22028343910146622551027423993293789477914888559209571948117:ℚ)/2032281608953857421875000000000000000000000000000000000000000),((26985428877613710479273:ℚ)/338437500000000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((-1:ℚ)/2),((-7:ℚ)/16),((908116837:ℚ)/1250000000),((7326378281:ℚ)/10000000000),((-6926378281:ℚ)/14359375000),((-5876817859:ℚ)/14418750000),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2980448133:ℚ)/10000000000),((10935401477906141737340087888668555563416965221069667:ℚ)/1008857107679575681686401367187500000000000000000000000),((143879860000131134761711:ℚ)/1805000000000000000000000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/2),((-7:ℚ)/16),((291785259:ℚ)/400000000),((738577777:ℚ)/1000000000),((-232859259:ℚ)/480625000),((-1888896813:ℚ)/4652000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2844365059:ℚ)/10000000000),((2638722130382460140677160908362920556909716585054485997:ℚ)/241933205488600000000000000000000000000000000000000000000),((1438745050581298509979:ℚ)/18050000000000000000000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-1:ℚ)/2),((-7:ℚ)/16),((7354024807:ℚ)/10000000000),((7445176861:ℚ)/10000000000),((-7045176861:ℚ)/14537500000),((-47638173649:ℚ)/117250000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1275563867:ℚ)/5000000000),((191674724384576930255020949214266084127243916739924339033369:ℚ)/17574765756884765625000000000000000000000000000000000000000000),((143790691941923256340071:ℚ)/1805000000000000000000000)⟩
theorem valid15 : Valid seventh packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet seventh nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-1:ℚ)/2),((-7:ℚ)/16),((3706708921:ℚ)/5000000000),((3752287783:ℚ)/5000000000),((-3552287783:ℚ)/7328125000),((-24026962447:ℚ)/59100000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1110211683:ℚ)/5000000000),((274950507865974674206808191282483042439805786801722315849:ℚ)/25211812057031250000000000000000000000000000000000000000000),((35926868556563571270839:ℚ)/451250000000000000000000)⟩
theorem valid16 : Valid seventh packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/2),((-7:ℚ)/16),((7472810587:ℚ)/10000000000),((7742166689:ℚ)/10000000000),((-7342166689:ℚ)/14775000000),((-48469674109:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((229008309:ℚ)/1250000000),((37847834092654243825513949427412602063148557491657263904299:ℚ)/3353644275000000000000000000000000000000000000000000000000000),((1209860405071221:ℚ)/15200000000000000)⟩
theorem valid17 : Valid seventh packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/2),((-7:ℚ)/16),((7710378801:ℚ)/10000000000),((8217332897:ℚ)/10000000000),((-7817332897:ℚ)/15250000000),((-5570294623:ℚ)/14400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2225665807748038250687780655790431951163068712997631649:ℚ)/189734400000000000000000000000000000000000000000000000000),((158817:ℚ)/2000000)⟩
theorem valid18 : Valid seventh packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/2),((-7:ℚ)/16),((1023187903:ℚ)/1250000000),((10117839769:ℚ)/10000000000),((-3239279923:ℚ)/5400000000),((-6682315321:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((9404255043543258424908128962175568522131297309938901467:ℚ)/675000000000000000000000000000000000000000000000000000000),((158817:ℚ)/2000000)⟩
theorem valid19 : Valid seventh packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/2),((-7:ℚ)/16),((10085882679:ℚ)/10000000000),((1739804337:ℚ)/1250000000),((-1689804337:ℚ)/2500000000),((-22253726251:ℚ)/73600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((311920620996972172388801117859948465160439628350567251:ℚ)/19372558593750000000000000000000000000000000000000000000),((158817:ℚ)/2000000)⟩
theorem valid20 : Valid seventh packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((4481:ℚ)/6400) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound seventh nn0 nn1 Qcell ((4481:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound seventh nn0 nn1 Qcell ((919:ℚ)/1280) ((1163:ℚ)/1600) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC09
#check @N11Formalization.C450SeventhGroupedC09.bound
#print axioms N11Formalization.C450SeventhGroupedC09.valid0
#print axioms N11Formalization.C450SeventhGroupedC09.valid1
#print axioms N11Formalization.C450SeventhGroupedC09.valid2
#print axioms N11Formalization.C450SeventhGroupedC09.valid3
#print axioms N11Formalization.C450SeventhGroupedC09.valid4
#print axioms N11Formalization.C450SeventhGroupedC09.valid5
#print axioms N11Formalization.C450SeventhGroupedC09.valid6
#print axioms N11Formalization.C450SeventhGroupedC09.valid7
#print axioms N11Formalization.C450SeventhGroupedC09.valid8
#print axioms N11Formalization.C450SeventhGroupedC09.valid9
#print axioms N11Formalization.C450SeventhGroupedC09.valid10
#print axioms N11Formalization.C450SeventhGroupedC09.valid11
#print axioms N11Formalization.C450SeventhGroupedC09.valid12
#print axioms N11Formalization.C450SeventhGroupedC09.valid13
#print axioms N11Formalization.C450SeventhGroupedC09.valid14
#print axioms N11Formalization.C450SeventhGroupedC09.valid15
#print axioms N11Formalization.C450SeventhGroupedC09.valid16
#print axioms N11Formalization.C450SeventhGroupedC09.valid17
#print axioms N11Formalization.C450SeventhGroupedC09.valid18
#print axioms N11Formalization.C450SeventhGroupedC09.valid19
#print axioms N11Formalization.C450SeventhGroupedC09.valid20
#print axioms N11Formalization.C450SeventhGroupedC09.bound
#print axioms N11Formalization.C450SeventhGroupedC09.endpoint_checks
