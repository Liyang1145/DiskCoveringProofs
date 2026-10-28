import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((629758017:ℚ)/1000000000),((6569441023:ℚ)/10000000000),((-55924969207:ℚ)/99200000000),((-581758017:ℚ)/1287500000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1485355629:ℚ)/2500000000),((1105543325986730062809384069989917092598813016220632129453581:ℚ)/97091395276800000000000000000000000000000000000000000000000000),((340019484488616539603933:ℚ)/3610000000000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((6535169479:ℚ)/10000000000),((850881239:ℚ)/1250000000),((-7257931151:ℚ)/12875000000),((-6055169479:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1339351913:ℚ)/2500000000),((1352197729207693508292311029166748390249770678659693945439:ℚ)/118865074314880371093750000000000000000000000000000000000000),((679253267800064070532101:ℚ)/7220000000000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((1693188107:ℚ)/2500000000),((13851703:ℚ)/20000000),((-118265327:ℚ)/213600000),((-1573188107:ℚ)/3396875000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2354595817:ℚ)/5000000000),((132165672846706353510754605525098188919653942566909109:ℚ)/11994761035598400000000000000000000000000000000000000000),((570901727388670851:ℚ)/6080000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((6891541727:ℚ)/10000000000),((6985251623:ℚ)/10000000000),((-59667264607:ℚ)/108700000000),((-6411541727:ℚ)/13706250000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((54401167:ℚ)/125000000),((5817817389237266929283168004081634962330377600508151985522663:ℚ)/536183464491080468750000000000000000000000000000000000000000000),((677295652656298817157641:ℚ)/7220000000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((1390187173:ℚ)/2000000000),((3522325657:ℚ)/5000000000),((-30100930913:ℚ)/54825000000),((-1294187173:ℚ)/2765000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((260179117:ℚ)/625000000),((80122172154799199794724050601742540651069303349290926128811:ℚ)/7382058560893508148193359375000000000000000000000000000000000),((677112333619292278785259:ℚ)/7220000000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((280413187:ℚ)/400000000),((1420810117:ℚ)/2000000000),((-12147291053:ℚ)/22120000000),((-261213187:ℚ)/557750000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3965168687:ℚ)/10000000000),((16318564325377755656809525418871582931339707678913561801539:ℚ)/1503095267673387500000000000000000000000000000000000000000000),((27077255823050022543381:ℚ)/288800000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((1767430791:ℚ)/2500000000),((1426750013:ℚ)/2000000000),((-12200750117:ℚ)/22310000000),((-1647430791:ℚ)/3500781250),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((1878830711:ℚ)/5000000000),((300360897904264850464809053145162468183673665646031227291837:ℚ)/27871388930080268875000000000000000000000000000000000000000000),((1691524001682997689761:ℚ)/18050000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-9:ℚ)/16),((-1:ℚ)/2),((7099419791:ℚ)/10000000000),((1432689889:ℚ)/2000000000),((-12254209001:ℚ)/22405000000),((-6619419791:ℚ)/14062500000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((3649708021:ℚ)/10000000000),((119864108826328950896266263001490652363955686882847361:ℚ)/11120643536256408691406250000000000000000000000000000000),((1424253937563997546811:ℚ)/15200000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((356455817:ℚ)/500000000),((1798287181:ℚ)/2500000000),((-15384584629:ℚ)/28125000000),((-332455817:ℚ)/706093750),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((707722937:ℚ)/2000000000),((5101789990488668856364225448542491938437279898040398008674367:ℚ)/473250458049774169921875000000000000000000000000000000000000000),((169108058806064131660551:ℚ)/1805000000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((3579406407:ℚ)/5000000000),((1444569581:ℚ)/2000000000),((-12361126229:ℚ)/22595000000),((-3339406407:ℚ)/7090625000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((1712037643:ℚ)/5000000000),((5002622857288085987007347193973552726910480409982650736861:ℚ)/463976579745304295898437500000000000000000000000000000000000),((13526888906047218202747:ℚ)/144400000000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((1797127303:ℚ)/2500000000),((1813136747:ℚ)/2500000000),((-15518230723:ℚ)/28362500000),((-1677127303:ℚ)/3560156250),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((3305731121:ℚ)/10000000000),((15966561382866141032490892239034116770863656158364189299441107:ℚ)/1480613161228272344970703125000000000000000000000000000000000000),((169064312644785193337269:ℚ)/1805000000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((7218205537:ℚ)/10000000000),((910280747:ℚ)/1250000000),((-7792526723:ℚ)/14240625000),((-6738205537:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((3183157303:ℚ)/10000000000),((5837013503693243746744972606524659841237845962493584513:ℚ)/541196361825656890869140625000000000000000000000000000000),((35587929002104498388641:ℚ)/380000000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((-9:ℚ)/16),((-1:ℚ)/2),((1811975447:ℚ)/2500000000),((1827986217:ℚ)/2500000000),((-15651875953:ℚ)/28600000000),((-1691975447:ℚ)/3589843750),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((3055844351:ℚ)/10000000000),((1998021976927663068321155857693114849398354868150288648138579:ℚ)/185225339109525000000000000000000000000000000000000000000000000),((507063485011553273577647:ℚ)/5415000000000000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((3638798983:ℚ)/5000000000),((3670821833:ℚ)/5000000000),((-31437396497:ℚ)/57437500000),((-3398798983:ℚ)/7209375000),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((730793133:ℚ)/2500000000),((1328170273859723147492940995690893350399418001812110450553:ℚ)/123109574876314133405685424804687500000000000000000000000000),((337999618750856745218237:ℚ)/3610000000000000000000000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((7307294073:ℚ)/10000000000),((1480208197:ℚ)/2000000000),((-12681873773:ℚ)/23070000000),((-6827294073:ℚ)/14537500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2784375309:ℚ)/10000000000),((188023897164446586293690680992303182497864792636498723058839:ℚ)/17299397584083403125000000000000000000000000000000000000000000),((27042496725208967988111:ℚ)/288800000000000000000000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-9:ℚ)/16),((-1:ℚ)/2),((1841671519:ℚ)/2500000000),((7460437943:ℚ)/10000000000),((-63943941487:ℚ)/116300000000),((-1721671519:ℚ)/3664062500),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((62106333:ℚ)/250000000),((35262618017265537738980712582185693045533031972690177547923821:ℚ)/3243815211261253125000000000000000000000000000000000000000000000),((42243485299209921480031:ℚ)/451250000000000000000000)⟩
theorem valid15 : Valid seventh packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet seventh nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((7426077803:ℚ)/10000000000),((7519834547:ℚ)/10000000000),((-64478510923:ℚ)/117250000000),((-6946077803:ℚ)/14775000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2143470067:ℚ)/10000000000),((4782246577653033021491550767042604029418562255050459974328787:ℚ)/439848936538439941406250000000000000000000000000000000000000000),((675731492029816548824461:ℚ)/7220000000000000000000000)⟩
theorem valid16 : Valid seventh packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-9:ℚ)/16),((-1:ℚ)/2),((3742734631:ℚ)/5000000000),((3878708799:ℚ)/5000000000),((-33308379191:ℚ)/59100000000),((-3502734631:ℚ)/7625000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1738265619:ℚ)/10000000000),((81539387397415423934368277244930877624841571643787983856093:ℚ)/7201009586165625000000000000000000000000000000000000000000000),((45519221735513031:ℚ)/486400000000000000)⟩
theorem valid17 : Valid seventh packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((7723032531:ℚ)/10000000000),((4116284541:ℚ)/5000000000),((-35446560869:ℚ)/61000000000),((-2414344177:ℚ)/5400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((6135723266730705452668622355657016424289235803768573320341:ℚ)/517091090625000000000000000000000000000000000000000000000000),((2392573:ℚ)/25600000)⟩
theorem valid18 : Valid seventh packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((4099073967:ℚ)/5000000000),((10133031059:ℚ)/10000000000),((-87997279531:ℚ)/129600000000),((-3859073967:ℚ)/10000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((300119910739413474961582549947632464905315946113405095953:ℚ)/20407334400000000000000000000000000000000000000000000000000),((2392573:ℚ)/25600000)⟩
theorem valid19 : Valid seventh packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((2019699977:ℚ)/2000000000),((6966786649:ℚ)/5000000000),((-61101079841:ℚ)/80000000000),((-1923699977:ℚ)/5520000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((33582562148301879997927441546184637399658069744050084277321:ℚ)/1904400000000000000000000000000000000000000000000000000000000),((2392573:ℚ)/25600000)⟩
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
end N11Formalization.C450SeventhGroupedC08
#check @N11Formalization.C450SeventhGroupedC08.bound
#print axioms N11Formalization.C450SeventhGroupedC08.valid0
#print axioms N11Formalization.C450SeventhGroupedC08.valid1
#print axioms N11Formalization.C450SeventhGroupedC08.valid2
#print axioms N11Formalization.C450SeventhGroupedC08.valid3
#print axioms N11Formalization.C450SeventhGroupedC08.valid4
#print axioms N11Formalization.C450SeventhGroupedC08.valid5
#print axioms N11Formalization.C450SeventhGroupedC08.valid6
#print axioms N11Formalization.C450SeventhGroupedC08.valid7
#print axioms N11Formalization.C450SeventhGroupedC08.valid8
#print axioms N11Formalization.C450SeventhGroupedC08.valid9
#print axioms N11Formalization.C450SeventhGroupedC08.valid10
#print axioms N11Formalization.C450SeventhGroupedC08.valid11
#print axioms N11Formalization.C450SeventhGroupedC08.valid12
#print axioms N11Formalization.C450SeventhGroupedC08.valid13
#print axioms N11Formalization.C450SeventhGroupedC08.valid14
#print axioms N11Formalization.C450SeventhGroupedC08.valid15
#print axioms N11Formalization.C450SeventhGroupedC08.valid16
#print axioms N11Formalization.C450SeventhGroupedC08.valid17
#print axioms N11Formalization.C450SeventhGroupedC08.valid18
#print axioms N11Formalization.C450SeventhGroupedC08.valid19
#print axioms N11Formalization.C450SeventhGroupedC08.valid20
#print axioms N11Formalization.C450SeventhGroupedC08.bound
#print axioms N11Formalization.C450SeventhGroupedC08.endpoint_checks
