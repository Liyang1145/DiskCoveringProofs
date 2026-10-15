import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC28
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((11:ℚ)/16),((3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((11:ℚ)/16),((3:ℚ)/4),((5148216351:ℚ)/10000000000),((5490039739:ℚ)/10000000000),((77110379861:ℚ)/103000000000),((21750119217:ℚ)/24800000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((8265781587:ℚ)/10000000000),((-135889999050302041410344692641020438069:ℚ)/392764544000000000000000000000000000000),((-7432333231152747120296720931:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((11:ℚ)/16),((3:ℚ)/4),((5388017421:ℚ)/10000000000),((716245509:ℚ)/1250000000),((79748191631:ℚ)/106800000000),((2808736527:ℚ)/3218750000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1565577061:ℚ)/2000000000),((-75671100205135909748032365378392709362524555519902197:ℚ)/217376730591058731079101562500000000000000000000000000),((-343269195236872555659882473:ℚ)/693120000000000000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((5627652527:ℚ)/10000000000),((365616359:ℚ)/625000000),((82384177797:ℚ)/108700000000),((475616359:ℚ)/556250000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7370111607:ℚ)/10000000000),((-425374836321689722278965310570014866417290240955916121:ℚ)/1169282994079589843750000000000000000000000000000000000),((-28386797770834348670733291:ℚ)/57760000000000000000000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((2873706689:ℚ)/5000000000),((5969719431:ℚ)/10000000000),((41850773579:ℚ)/55300000000),((23189158293:ℚ)/27175000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((356625621:ℚ)/500000000),((-56380430452904434612230216177441929347644570581527054939:ℚ)/154823112086486816406250000000000000000000000000000000000),((-21630037920287390401399990913:ℚ)/44359680000000000000000000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((5867139069:ℚ)/10000000000),((602963393:ℚ)/1000000000),((85018529759:ℚ)/111550000000),((2336890179:ℚ)/2765000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((6888272513:ℚ)/10000000000),((-976634643473070115018151512375314335139354307478448091:ℚ)/2631764181689453125000000000000000000000000000000000000),((-71811519644914656101917339:ℚ)/147865600000000000000000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((11:ℚ)/16),((3:ℚ)/4),((59269893:ℚ)/100000000),((1217907839:ℚ)/2000000000),((856768823:ℚ)/1125000000),((4709723517:ℚ)/5577500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1690857489:ℚ)/2500000000),((-14150277629689983758874248911904124952326748939975429:ℚ)/38124249084091186523437500000000000000000000000000000),((-286082134501568120895080731:ℚ)/591462400000000000000000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((598683141:ℚ)/1000000000),((6149435463:ℚ)/10000000000),((8633514551:ℚ)/11345000000),((7909435463:ℚ)/9375000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((6636631863:ℚ)/10000000000),((-10844370269124487442557366359984761909343687610264806899:ℚ)/29212474822998046875000000000000000000000000000000000000),((-21368150489256738796257861377:ℚ)/44359680000000000000000000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((3023332803:ℚ)/5000000000),((77616537:ℚ)/125000000),((43496660833:ℚ)/57200000000),((298849611:ℚ)/354531250),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3253880321:ℚ)/5000000000),((-7393536816279215985300448942555563896616648440522983:ℚ)/19913592917764186859130859375000000000000000000000000),((-3324910482771964417245377:ℚ)/6931200000000000000000000)⟩
theorem valid7 : Valid source34 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source34 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((6106492089:ℚ)/10000000000),((1567300477:ℚ)/2500000000),((87651412979:ℚ)/115350000000),((463223187:ℚ)/550000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((99635739:ℚ)/156250000),((-34796833232878948250433460027028450463663041509313:ℚ)/93707794189453125000000000000000000000000000000000),((-441458122404178665381791219:ℚ)/924160000000000000000000000)⟩
theorem valid8 : Valid source34 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((6166311051:ℚ)/10000000000),((158226813:ℚ)/250000000),((88309421561:ℚ)/116300000000),((202226813:ℚ)/240312500),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1248653963:ℚ)/2000000000),((-37463591539543057308387849641458892569582682594518763:ℚ)/100876223805809020996093750000000000000000000000000000),((-36530191889467809020657:ℚ)/76800000000000000000000)⟩
theorem valid9 : Valid source34 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source34 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((11:ℚ)/16),((3:ℚ)/4),((155653067:ℚ)/250000000),((6388935001:ℚ)/10000000000),((2224183737:ℚ)/2931250000),((24446805003:ℚ)/29075000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((95427363:ℚ)/156250000),((-3822845710209542639361966339185971217787925434043117109697:ℚ)/10292336821191406250000000000000000000000000000000000000000),((-7002991320180840351116469611:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid source34 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source34 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((1571481789:ℚ)/2500000000),((6448789551:ℚ)/10000000000),((22406299679:ℚ)/29550000000),((24626368653:ℚ)/29312500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2984378661:ℚ)/5000000000),((-8639468694711799773312967984180875219752672928078170287259:ℚ)/23257663734054565429687500000000000000000000000000000000000),((-20917395239586542408344571633:ℚ)/44359680000000000000000000000)⟩
theorem valid11 : Valid source34 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source34 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((11:ℚ)/16),((3:ℚ)/4),((1269144931:ℚ)/2000000000),((6508636363:ℚ)/10000000000),((18056594241:ℚ)/23830000000),((8268636363:ℚ)/9850000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((2913646903:ℚ)/5000000000),((-26841821337859485555160798030791956877789967123605244089:ℚ)/72251442968750000000000000000000000000000000000000000000),((-6941700887404713374877537859:ℚ)/14786560000000000000000000000)⟩
theorem valid12 : Valid source34 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((3202757673:ℚ)/5000000000),((6568475623:ℚ)/10000000000),((45470334403:ℚ)/60050000000),((24985426869:ℚ)/29787500000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((5682742957:ℚ)/10000000000),((-18427730023374221852833035798434692351763977697304561129173:ℚ)/49598118225973510742187500000000000000000000000000000000000),((-6910698739891842965946467819:ℚ)/14786560000000000000000000000)⟩
theorem valid13 : Valid source34 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source34 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((11:ℚ)/16),((3:ℚ)/4),((101020303:ℚ)/156250000),((6688132203:ℚ)/10000000000),((1431223333:ℚ)/1906250000),((25344396609:ℚ)/30025000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((221394377:ℚ)/400000000),((-3774200963306144407327755558202718523739502927218624421533:ℚ)/10319505826269531250000000000000000000000000000000000000000),((-20543941703195570898154345097:ℚ)/44359680000000000000000000000)⟩
theorem valid14 : Valid source34 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source34 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source34 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((11:ℚ)/16),((3:ℚ)/4),((6584848181:ℚ)/10000000000),((6807760669:ℚ)/10000000000),((30971109997:ℚ)/41300000000),((25703282007:ℚ)/30500000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((5227942383:ℚ)/10000000000),((-3828439265344266623702051408639329977283920677680645698181:ℚ)/10462405468750000000000000000000000000000000000000000000000),((-6784310539366736082642478771:ℚ)/14786560000000000000000000000)⟩
theorem valid15 : Valid source34 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((11:ℚ)/16),((3:ℚ)/4),((6704372231:ℚ)/10000000000),((6927362313:ℚ)/10000000000),((94228094541:ℚ)/125800000000),((1241051759:ℚ)/1475000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((196151759:ℚ)/400000000),((-58710234413973524892804668494966297660971156460762771:ℚ)/160367358398437500000000000000000000000000000000000000),((-20159065898693923425187766177:ℚ)/44359680000000000000000000000)⟩
theorem valid16 : Valid source34 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source34 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((11:ℚ)/16),((3:ℚ)/4),((6823872677:ℚ)/10000000000),((22395281:ℚ)/31250000),((10615844383:ℚ)/14400000000),((83685843:ℚ)/98281250),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2279354229:ℚ)/5000000000),((-256417194004993975970930001383348973265027133069:ℚ)/721610462665557861328125000000000000000000000000),((-178204777941089518211:ℚ)/400000000000000000000)⟩
theorem valid17 : Valid source34 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source34 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((11:ℚ)/16),((3:ℚ)/4),((3531403481:ℚ)/5000000000),((8122138637:ℚ)/10000000000),((49085438291:ℚ)/72400000000),((9882138637:ℚ)/10800000000),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((945595339:ℚ)/2500000000),((-78004598312935296035389617749221105481830931415049489523:ℚ)/267196725000000000000000000000000000000000000000000000000),((-438937809:ℚ)/1024000000)⟩
theorem valid18 : Valid source34 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((11:ℚ)/16),((3:ℚ)/4),((8017785519:ℚ)/10000000000),((1815341257:ℚ)/2000000000),((108675640709:ℚ)/160000000000),((6502023771:ℚ)/7240000000),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-179529964298715137455353510726084156289016841904154227:ℚ)/592974100000000000000000000000000000000000000000000000),((-438937809:ℚ)/1024000000)⟩
theorem valid19 : Valid source34 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source34 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((11:ℚ)/16),((3:ℚ)/4),((4485906041:ℚ)/5000000000),((3222165017:ℚ)/2500000000),((59584966451:ℚ)/110400000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-16616328196660957:ℚ)/110400000000000000),((-438937809:ℚ)/1024000000)⟩
theorem valid20 : Valid source34 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((2231:ℚ)/3200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source34 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source34 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source34 nn0 nn1 Qcell ((2231:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source34 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound source34 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound source34 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC28
#check @N11Formalization.C450Source34GroupedC28.bound
#print axioms N11Formalization.C450Source34GroupedC28.valid0
#print axioms N11Formalization.C450Source34GroupedC28.valid1
#print axioms N11Formalization.C450Source34GroupedC28.valid2
#print axioms N11Formalization.C450Source34GroupedC28.valid3
#print axioms N11Formalization.C450Source34GroupedC28.valid4
#print axioms N11Formalization.C450Source34GroupedC28.valid5
#print axioms N11Formalization.C450Source34GroupedC28.valid6
#print axioms N11Formalization.C450Source34GroupedC28.valid7
#print axioms N11Formalization.C450Source34GroupedC28.valid8
#print axioms N11Formalization.C450Source34GroupedC28.valid9
#print axioms N11Formalization.C450Source34GroupedC28.valid10
#print axioms N11Formalization.C450Source34GroupedC28.valid11
#print axioms N11Formalization.C450Source34GroupedC28.valid12
#print axioms N11Formalization.C450Source34GroupedC28.valid13
#print axioms N11Formalization.C450Source34GroupedC28.valid14
#print axioms N11Formalization.C450Source34GroupedC28.valid15
#print axioms N11Formalization.C450Source34GroupedC28.valid16
#print axioms N11Formalization.C450Source34GroupedC28.valid17
#print axioms N11Formalization.C450Source34GroupedC28.valid18
#print axioms N11Formalization.C450Source34GroupedC28.valid19
#print axioms N11Formalization.C450Source34GroupedC28.valid20
#print axioms N11Formalization.C450Source34GroupedC28.bound
#print axioms N11Formalization.C450Source34GroupedC28.endpoint_checks
