import N11Formalization.C450EighthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450EighthGroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450EighthData
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((801113899:ℚ)/1250000000),((3349631291:ℚ)/5000000000),((-9664893873:ℚ)/9920000000),((-5327797293:ℚ)/6437500000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1134887013:ℚ)/2000000000),((3963350923021767328276816600577504064599073:ℚ)/202273740160000000000000000000000000000000000),((6192599674478160817427639:ℚ)/28880000000000000000000000)⟩
theorem valid0 : Valid eighth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet eighth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((830806421:ℚ)/1250000000),((340901297:ℚ)/500000000),((-984303891:ℚ)/1030000000),((-5535644947:ℚ)/6556250000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2531620741:ℚ)/5000000000),((525156438422728805436790196923844805839580550058617837:ℚ)/29356393640795898437500000000000000000000000000000000000),((6202922643785866191034199:ℚ)/28880000000000000000000000)⟩
theorem valid1 : Valid eighth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound eighth nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((1353044073:ℚ)/2000000000),((3468394411:ℚ)/5000000000),((-10021183233:ℚ)/10490000000),((-9023308511:ℚ)/10680000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((1182747173:ℚ)/2500000000),((9176560068610868491435157510280954508554670716971716200311:ℚ)/514314779666006250000000000000000000000000000000000000000000),((47718599761718394478028093:ℚ)/221798400000000000000000000)⟩
theorem valid2 : Valid eighth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound eighth nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet eighth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-15:ℚ)/16),((-7:ℚ)/8),((1376797737:ℚ)/2000000000),((6996170093:ℚ)/10000000000),((-6740170093:ℚ)/7120000000),((-9189584159:ℚ)/10775000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1093901631:ℚ)/2500000000),((21464189937972576310057062781515870747402268287814690373993:ℚ)/1257175165526400000000000000000000000000000000000000000000000),((47758198839173217668509373:ℚ)/221798400000000000000000000)⟩
theorem valid3 : Valid eighth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet eighth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((6943372603:ℚ)/10000000000),((1411110251:ℚ)/2000000000),((-4079730753:ℚ)/4310000000),((-46363608221:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4187408247:ℚ)/10000000000),((10087519665662794233482311964534832693232130350466582329951:ℚ)/591249676330493750000000000000000000000000000000000000000000),((398318844010541512036864951:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid eighth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound eighth nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((1400551273:ℚ)/2000000000),((1417048359:ℚ)/2000000000),((-4097545077:ℚ)/4348000000),((-9355858911:ℚ)/10917500000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((997722891:ℚ)/2500000000),((10222827925775670395108967879717676477456096609724826094739:ℚ)/612343376751039175000000000000000000000000000000000000000000),((15939350181081719414992831:ℚ)/73932800000000000000000000)⟩
theorem valid5 : Valid eighth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((1758112047:ℚ)/2500000000),((7114932309:ℚ)/10000000000),((-20576796927:ℚ)/21835000000),((-11746784329:ℚ)/13706250000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((972280181:ℚ)/2500000000),((474797275968299761303000854066300866908278656415750642118699:ℚ)/28446195097669310156250000000000000000000000000000000000000000),((3934052478989738444630687:ℚ)/18240000000000000000000000)⟩
theorem valid6 : Valid eighth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound eighth nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-15:ℚ)/16),((-7:ℚ)/8),((282485599:ℚ)/400000000),((7144622797:ℚ)/10000000000),((-6888622797:ℚ)/7310000000),((-1887799193:ℚ)/2202500000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((1892378589:ℚ)/5000000000),((735374627228845451810533402640198913255950488087015825073:ℚ)/44067205362856250000000000000000000000000000000000000000000),((638108062758242512145039:ℚ)/2957312000000000000000000)⟩
theorem valid7 : Valid eighth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound eighth nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet eighth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-15:ℚ)/16),((-7:ℚ)/8),((1772957931:ℚ)/2500000000),((358715663:ℚ)/500000000),((-1037746989:ℚ)/1101250000),((-1692957931:ℚ)/1975000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((735515947:ℚ)/2000000000),((869151034035019439986826967439708566682186687926506523:ℚ)/52094510811535644531250000000000000000000000000000000000),((74809578485948267017578437:ℚ)/346560000000000000000000000)⟩
theorem valid8 : Valid eighth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound eighth nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((8867:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7121523437:ℚ)/10000000000),((7189158481:ℚ)/10000000000),((-20799475443:ℚ)/22120000000),((-47610664059:ℚ)/55418750000),((2409799777:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((673601917:ℚ)/2500000000),((891833571:ℚ)/2500000000),((12541808319990413366011710189211308195739483557455447993508523:ℚ)/759785082017071600000000000000000000000000000000000000000000000),((21003517646203747763805789:ℚ)/97280000000000000000000000)⟩
theorem valid9 : Valid eighth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound eighth nn0 nn1 Qcell ((553:ℚ)/800) ((8867:ℚ)/12800) :=
  cell_of_packet eighth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8867:ℚ)/12800),((4443:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((11150577:ℚ)/15625000),((7204003697:ℚ)/10000000000),((-20844011091:ℚ)/22167500000),((-298216156:ℚ)/347109375),((4816708251:ℚ)/5000000000),((9639199113:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3510970901:ℚ)/10000000000),((7394353055916686021138589181867656358634262340088917511795159:ℚ)/447983006968488293847656250000000000000000000000000000000000000),((46775421964178349431813:ℚ)/216600000000000000000000)⟩
theorem valid10 : Valid eighth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound eighth nn0 nn1 Qcell ((8867:ℚ)/12800) ((4443:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4443:ℚ)/6400),((1781:ℚ)/2560),((-15:ℚ)/16),((-7:ℚ)/8),((7151215113:ℚ)/10000000000),((3609424453:ℚ)/5000000000),((-3481424453:ℚ)/3702500000),((-47818505791:ℚ)/55656250000),((9627690243:ℚ)/10000000000),((9633416507:ℚ)/10000000000),((2737309683:ℚ)/10000000000),((3453726541:ℚ)/10000000000),((1277490706651173242019337347877913403514101888718754316887:ℚ)/77401558525495800781250000000000000000000000000000000000000),((1197701092230841859753096573:ℚ)/5544960000000000000000000000)⟩
theorem valid11 : Valid eighth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound eighth nn0 nn1 Qcell ((4443:ℚ)/6400) ((1781:ℚ)/2560) :=
  cell_of_packet eighth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1781:ℚ)/2560),((2231:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((3583030469:ℚ)/5000000000),((7233694109:ℚ)/10000000000),((-20933082327:ℚ)/22262500000),((-23961213283:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((1203461281:ℚ)/1250000000),((551641531:ℚ)/2000000000),((106111143:ℚ)/312500000),((88511271582363934033154256630223105848583662960564696136561:ℚ)/5363162813250408363342285156250000000000000000000000000000000),((5254172700411871224222541:ℚ)/24320000000000000000000000)⟩
theorem valid12 : Valid eighth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound eighth nn0 nn1 Qcell ((1781:ℚ)/2560) ((2231:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2231:ℚ)/3200),((8943:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((1436181351:ℚ)/2000000000),((1449707861:ℚ)/2000000000),((-4195523583:ℚ)/4462000000),((-9605269457:ℚ)/11178750000),((961640533:ℚ)/1000000000),((9622019977:ℚ)/10000000000),((555749933:ℚ)/2000000000),((208525783:ℚ)/625000000),((31860650925734080811334952081840393591604267012631368868623:ℚ)/1930666854290461650000000000000000000000000000000000000000000),((47928066106204139477733917:ℚ)/221798400000000000000000000)⟩
theorem valid13 : Valid eighth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound eighth nn0 nn1 Qcell ((2231:ℚ)/3200) ((8943:ℚ)/12800) :=
  cell_of_packet eighth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((8943:ℚ)/12800),((4481:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((3597876281:ℚ)/5000000000),((453961531:ℚ)/625000000),((-437961531:ℚ)/465781250),((-24065133967:ℚ)/28006250000),((1922169193:ℚ)/2000000000),((1923281067:ℚ)/2000000000),((349868089:ℚ)/1250000000),((819060397:ℚ)/2500000000),((4185265984600996962218491192129177784254181381597764789:ℚ)/253633086646343183994293212890625000000000000000000000000),((99870993595749451877237279:ℚ)/462080000000000000000000000)⟩
theorem valid14 : Valid eighth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound eighth nn0 nn1 Qcell ((8943:ℚ)/12800) ((4481:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4481:ℚ)/6400),((8981:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7210598361:ℚ)/10000000000),((7278229681:ℚ)/10000000000),((-21066689043:ℚ)/22405000000),((-6890598361:ℚ)/8018750000),((4802670763:ℚ)/5000000000),((961084597:ℚ)/1000000000),((563760281:ℚ)/2000000000),((401873253:ℚ)/1250000000),((19092171622806077219646569371730881481940310972943723550589:ℚ)/1157092756413805070312500000000000000000000000000000000000000),((1198702187158104704998412957:ℚ)/5544960000000000000000000000)⟩
theorem valid15 : Valid eighth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound eighth nn0 nn1 Qcell ((4481:ℚ)/6400) ((8981:ℚ)/12800) :=
  cell_of_packet eighth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((8981:ℚ)/12800),((45:ℚ)/64),((-15:ℚ)/16),((-7:ℚ)/8),((7225444151:ℚ)/10000000000),((7293074859:ℚ)/10000000000),((-21111224577:ℚ)/22452500000),((-16112703019:ℚ)/18750000000),((599993229:ℚ)/625000000),((9605341531:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3152582549:ℚ)/10000000000),((500212617582211359221817493817718690374279767725541979:ℚ)/30317776512597656250000000000000000000000000000000000000),((399650814888530009978423039:ℚ)/1848320000000000000000000000)⟩
theorem valid16 : Valid eighth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound eighth nn0 nn1 Qcell ((8981:ℚ)/12800) ((45:ℚ)/64) :=
  cell_of_packet eighth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((1810072483:ℚ)/2500000000),((3661382599:ℚ)/5000000000),((-3533382599:ℚ)/3750000000),((-12110507381:ℚ)/14121875000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((123558461:ℚ)/400000000),((112183084982242690043373460040885835689855294128169936696633:ℚ)/6730673181152343750000000000000000000000000000000000000000000),((24988667852594522865886471:ℚ)/115520000000000000000000000)⟩
theorem valid17 : Valid eighth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((7269981469:ℚ)/10000000000),((7352455513:ℚ)/10000000000),((-21289366539:ℚ)/22595000000),((-48649870283:ℚ)/56725000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((369718847:ℚ)/1250000000),((1546360731538038962001501883727123297536885413109424513991293:ℚ)/92795315949060859179687500000000000000000000000000000000000000),((399985513109553262529110279:ℚ)/1848320000000000000000000000)⟩
theorem valid18 : Valid eighth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound eighth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((1824918243:ℚ)/2500000000),((1476429161:ℚ)/2000000000),((-4275687483:ℚ)/4538000000),((-1744918243:ℚ)/2034375000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((2754521:ℚ)/9765625),((164966955680267369794321518184254793427435497837712521909:ℚ)/9901373891250618000000000000000000000000000000000000000000),((75028562238210792404309333:ℚ)/346560000000000000000000000)⟩
theorem valid19 : Valid eighth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet eighth nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((3664682221:ℚ)/5000000000),((7411836073:ℚ)/10000000000),((-7155836073:ℚ)/7595000000),((-24532775547:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((1338344439:ℚ)/5000000000),((2562436537341977310844484989254979466274860435751220781:ℚ)/153827521699414062500000000000000000000000000000000000000),((100079785529623689594394599:ℚ)/462080000000000000000000000)⟩
theorem valid20 : Valid eighth packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound eighth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet eighth nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((7359055879:ℚ)/10000000000),((3735608271:ℚ)/5000000000),((-10822824813:ℚ)/11440000000),((-49273391153:ℚ)/57675000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1262381081:ℚ)/5000000000),((23497765272441644487948820195040829906880373595960851147891:ℚ)/1383409580581600000000000000000000000000000000000000000000000),((400654850524268030615856799:ℚ)/1848320000000000000000000000)⟩
theorem valid21 : Valid eighth packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet eighth nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((7244569:ℚ)/9765625),((7530596921:ℚ)/10000000000),((-7274596921:ℚ)/7690000000),((-388195864:ℚ)/454296875),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((2190222841:ℚ)/10000000000),((2610369316484286946648517727727412542990109532502774342967:ℚ)/153772422969630250000000000000000000000000000000000000000000),((391590261177370250860871:ℚ)/1805000000000000000000000)⟩
theorem valid22 : Valid eighth packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet eighth nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-15:ℚ)/16),((-7:ℚ)/8),((1495564261:ℚ)/2000000000),((382467871:ℚ)/500000000),((-1109003613:ℚ)/1163000000),((-3340316609:ℚ)/3940000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((56109901:ℚ)/312500000),((1679766509257911492463715493213284188987329491362551451:ℚ)/95387534255192187500000000000000000000000000000000000000),((16055159567686494121446519:ℚ)/73932800000000000000000000)⟩
theorem valid23 : Valid eighth packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound eighth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet eighth nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-15:ℚ)/16),((-7:ℚ)/8),((1519317247:ℚ)/2000000000),((1971719359:ℚ)/2500000000),((-1907719359:ℚ)/1970000000),((-10187220729:ℚ)/12200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((299737633:ℚ)/10000000000),((3347815337363324767014102943861050874250106132378638937:ℚ)/177802705831250000000000000000000000000000000000000000000),((16054813846705430160857551:ℚ)/73932800000000000000000000)⟩
theorem valid24 : Valid eighth packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet eighth nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((78341147:ℚ)/100000000),((8361913947:ℚ)/10000000000),((-24317741841:ℚ)/24400000000),((-175329343:ℚ)/216000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((349042774790239199269610722355043097087996808930595398287:ℚ)/16546914900000000000000000000000000000000000000000000000000),((27795713:ℚ)/128000000)⟩
theorem valid25 : Valid eighth packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound eighth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet eighth nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((8309166621:ℚ)/10000000000),((1282753163:ℚ)/1250000000),(-1:ℚ),((-55924166347:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((601127230776244159652632332089539723:ℚ)/24000000000000000000000000000000000000),((27795713:ℚ)/128000000)⟩
theorem valid26 : Valid eighth packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet eighth nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((408372999:ℚ)/400000000),((7031078011:ℚ)/5000000000),(-1:ℚ),((-2769010993:ℚ)/4416000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((273437498503578620277131:ℚ)/9750528000000000000000000),((27795713:ℚ)/128000000)⟩
theorem valid27 : Valid eighth packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound eighth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet eighth nn0 nn1 packet27 valid27
private theorem node1_3 :
    CellBound eighth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound eighth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound eighth nn0 nn1 Qcell ((267:ℚ)/400) ((2193:ℚ)/3200) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((2193:ℚ)/3200) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound eighth nn0 nn1 Qcell ((881:ℚ)/1280) ((8867:ℚ)/12800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound eighth nn0 nn1 Qcell ((2193:ℚ)/3200) ((8867:ℚ)/12800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound eighth nn0 nn1 Qcell ((8867:ℚ)/12800) ((1781:ℚ)/2560) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound eighth nn0 nn1 Qcell ((1781:ℚ)/2560) ((8943:ℚ)/12800) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound eighth nn0 nn1 Qcell ((8867:ℚ)/12800) ((8943:ℚ)/12800) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound eighth nn0 nn1 Qcell ((2193:ℚ)/3200) ((8943:ℚ)/12800) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((8943:ℚ)/12800) :=
  cell_join node0_7 node7_14
private theorem node15_17 :
    CellBound eighth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound eighth nn0 nn1 Qcell ((8943:ℚ)/12800) ((45:ℚ)/64) :=
  cell_join leaf14 node15_17
private theorem node17_19 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_join leaf17 leaf18
private theorem node19_21 :
    CellBound eighth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf19 leaf20
private theorem node17_21 :
    CellBound eighth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join node17_19 node19_21
private theorem node14_21 :
    CellBound eighth nn0 nn1 Qcell ((8943:ℚ)/12800) ((143:ℚ)/200) :=
  cell_join node14_17 node17_21
private theorem node22_24 :
    CellBound eighth nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf22 leaf23
private theorem node21_24 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf21 node22_24
private theorem node24_26 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf24 leaf25
private theorem node26_28 :
    CellBound eighth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf26 leaf27
private theorem node24_28 :
    CellBound eighth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node24_26 node26_28
private theorem node21_28 :
    CellBound eighth nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node21_24 node24_28
private theorem node14_28 :
    CellBound eighth nn0 nn1 Qcell ((8943:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node14_21 node21_28
private theorem node0_28 :
    CellBound eighth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_14 node14_28
theorem bound : CellBound eighth nn0 nn1 Qcell (31/50) (69/50) := node0_28
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27]
theorem packet_count : packets.length = 28 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450EighthGroupedC02
#check @N11Formalization.C450EighthGroupedC02.bound
#print axioms N11Formalization.C450EighthGroupedC02.valid0
#print axioms N11Formalization.C450EighthGroupedC02.valid1
#print axioms N11Formalization.C450EighthGroupedC02.valid2
#print axioms N11Formalization.C450EighthGroupedC02.valid3
#print axioms N11Formalization.C450EighthGroupedC02.valid4
#print axioms N11Formalization.C450EighthGroupedC02.valid5
#print axioms N11Formalization.C450EighthGroupedC02.valid6
#print axioms N11Formalization.C450EighthGroupedC02.valid7
#print axioms N11Formalization.C450EighthGroupedC02.valid8
#print axioms N11Formalization.C450EighthGroupedC02.valid9
#print axioms N11Formalization.C450EighthGroupedC02.valid10
#print axioms N11Formalization.C450EighthGroupedC02.valid11
#print axioms N11Formalization.C450EighthGroupedC02.valid12
#print axioms N11Formalization.C450EighthGroupedC02.valid13
#print axioms N11Formalization.C450EighthGroupedC02.valid14
#print axioms N11Formalization.C450EighthGroupedC02.valid15
#print axioms N11Formalization.C450EighthGroupedC02.valid16
#print axioms N11Formalization.C450EighthGroupedC02.valid17
#print axioms N11Formalization.C450EighthGroupedC02.valid18
#print axioms N11Formalization.C450EighthGroupedC02.valid19
#print axioms N11Formalization.C450EighthGroupedC02.valid20
#print axioms N11Formalization.C450EighthGroupedC02.valid21
#print axioms N11Formalization.C450EighthGroupedC02.valid22
#print axioms N11Formalization.C450EighthGroupedC02.valid23
#print axioms N11Formalization.C450EighthGroupedC02.valid24
#print axioms N11Formalization.C450EighthGroupedC02.valid25
#print axioms N11Formalization.C450EighthGroupedC02.valid26
#print axioms N11Formalization.C450EighthGroupedC02.valid27
#print axioms N11Formalization.C450EighthGroupedC02.bound
#print axioms N11Formalization.C450EighthGroupedC02.endpoint_checks
