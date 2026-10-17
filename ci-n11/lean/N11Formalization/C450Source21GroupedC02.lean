import N11Formalization.C450Source21Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source21GroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source21Data
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((685407303:ℚ)/1000000000),((3531307241:ℚ)/5000000000),((-9377921723:ℚ)/9920000000),((-4157851121:ℚ)/5055000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4467598787:ℚ)/10000000000),((1378113145469068597957506614423584552744079:ℚ)/10393602290688000000000000000000000000000000),((568646602824553695890705647:ℚ)/739328000000000000000000000)⟩
theorem valid0 : Valid source21 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((54476787:ℚ)/78125000),((7122046653:ℚ)/10000000000),((-18934139959:ℚ)/20220000000),((-662675018:ℚ)/797265625),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((2045191001:ℚ)/5000000000),((3329958204822383360301132365463915588951266608679685511237:ℚ)/26532705619603125000000000000000000000000000000000000000000),((2280201293184460493394628983:ℚ)/2957312000000000000000000000)⟩
theorem valid1 : Valid source21 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source21 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((4101:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7032503709:ℚ)/10000000000),((7151762341:ℚ)/10000000000),((-1463329771:ℚ)/1570000000),((-42827525963:ℚ)/51262500000),((4940065779:ℚ)/5000000000),((1979272569:ℚ)/2000000000),((774947369:ℚ)/5000000000),((3888928057:ℚ)/10000000000),((662246896522786125973646436248018852466404773528754438393:ℚ)/5423719860207750000000000000000000000000000000000000000000),((2283010780578223152705659047:ℚ)/2957312000000000000000000000)⟩
theorem valid2 : Valid source21 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source21 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_of_packet source21 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((4101:ℚ)/6400),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((7062240499:ℚ)/10000000000),((897684721:ℚ)/1250000000),((-2389054163:ℚ)/2563125000),((-43035683493:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((9880131563:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((4730499:ℚ)/12500000),((11354968898160649940413652352998489981204221549428330749:ℚ)/93042759116021347045898437500000000000000000000000000000),((35715963009395562717492767:ℚ)/46208000000000000000000000)⟩
theorem valid3 : Valid source21 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source21 nn0 nn1 Qcell ((4101:ℚ)/6400) ((103:ℚ)/160) :=
  cell_of_packet source21 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((103:ℚ)/160),((8259:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7091976833:ℚ)/10000000000),((1439267077:ℚ)/2000000000),((-3831401231:ℚ)/4120000000),((-43243837831:ℚ)/51618750000),((9856320801:ℚ)/10000000000),((616511681:ℚ)/625000000),((1697201141:ℚ)/10000000000),((3677048627:ℚ)/10000000000),((4673444259528690691128528686609308264816388687558843511373:ℚ)/38820880160357812500000000000000000000000000000000000000000),((91489102818702001213333223:ℚ)/118292480000000000000000000)⟩
theorem valid4 : Valid source21 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source21 nn0 nn1 Qcell ((103:ℚ)/160) ((8259:ℚ)/12800) :=
  cell_of_packet source21 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((8259:ℚ)/12800),((4139:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((222088901:ℚ)/312500000),((7211192939:ℚ)/10000000000),((-19201578817:ℚ)/20647500000),((-1354622307:ℚ)/1616796875),((984852489:ℚ)/1000000000),((4928160403:ℚ)/5000000000),((1742751127:ℚ)/10000000000),((905559223:ℚ)/2500000000),((9453119686163258787974069930178403307730795049012838922208331:ℚ)/78540208246706707836914062500000000000000000000000000000000000),((2288633849690443492984160327:ℚ)/2957312000000000000000000000)⟩
theorem valid5 : Valid source21 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source21 nn0 nn1 Qcell ((8259:ℚ)/12800) ((4139:ℚ)/6400) :=
  cell_of_packet source21 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4139:ℚ)/6400),((8297:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((3560856359:ℚ)/5000000000),((7226050429:ℚ)/10000000000),((-19246151287:ℚ)/20695000000),((-21725994513:ℚ)/25928125000),((9840798677:ℚ)/10000000000),((1969704979:ℚ)/2000000000),((1786759881:ℚ)/10000000000),((1783310517:ℚ)/5000000000),((18355813357650382333744029966300309721560000342266337929940143:ℚ)/152538152161197574093750000000000000000000000000000000000000000),((2290040470170892390830962167:ℚ)/2957312000000000000000000000)⟩
theorem valid6 : Valid source21 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source21 nn0 nn1 Qcell ((4139:ℚ)/6400) ((8297:ℚ)/12800) :=
  cell_of_packet source21 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((8297:ℚ)/12800),((2079:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((3568290247:ℚ)/5000000000),((452556741:ℚ)/625000000),((-1205670223:ℚ)/1296406250),((-21778031729:ℚ)/25987500000),((4916570841:ℚ)/5000000000),((4920399341:ℚ)/5000000000),((1829340989:ℚ)/10000000000),((877540689:ℚ)/2500000000),((8028817266781167262952744029102893892705883865033586771:ℚ)/66733477892034924030303955078125000000000000000000000000),((8950966531246553469388647:ℚ)/11552000000000000000000000)⟩
theorem valid7 : Valid source21 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source21 nn0 nn1 Qcell ((8297:ℚ)/12800) ((2079:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2079:ℚ)/3200),((1667:ℚ)/2560),((-15:ℚ)/16),((-7:ℚ)/8),((44696551:ℚ)/62500000),((7255765221:ℚ)/10000000000),((-19335295663:ℚ)/20790000000),((-545751714:ℚ)/651171875),((4912776717:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((935297099:ℚ)/5000000000),((53950323:ℚ)/156250000),((27089596668321065252927154915356927766440279853851640508411:ℚ)/225206774442168750000000000000000000000000000000000000000000),((2292854735265433873362889767:ℚ)/2957312000000000000000000000)⟩
theorem valid8 : Valid source21 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source21 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1667:ℚ)/2560) :=
  cell_of_packet source21 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1667:ℚ)/2560),((4177:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7166315717:ℚ)/10000000000),((1817655631:ℚ)/2500000000),((-4844966893:ℚ)/5209375000),((-43764210019:ℚ)/52212500000),((4909016731:ℚ)/5000000000),((9825553439:ℚ)/10000000000),((382121547:ℚ)/2000000000),((135781997:ℚ)/400000000),((1853961879543429410422640207253895399080550497675558624219237:ℚ)/15415791662727513694763183593750000000000000000000000000000000),((143391398747843310922152607:ℚ)/184832000000000000000000000)⟩
theorem valid9 : Valid source21 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source21 nn0 nn1 Qcell ((1667:ℚ)/2560) ((4177:ℚ)/6400) :=
  cell_of_packet source21 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4177:ℚ)/6400),((16727:ℚ)/25600),((-15:ℚ)/16),((-7:ℚ)/8),((1436236633:ℚ)/2000000000),((454878197:ℚ)/625000000),((-1212634591:ℚ)/1305312500),((-8773656431:ℚ)/10454375000),((1962859787:ℚ)/2000000000),((9818033467:ℚ)/10000000000),((482543621:ℚ)/2500000000),((133412071:ℚ)/400000000),((464596604032182459012639434223634555866505590014082581690499:ℚ)/3889194133537570239448547363281250000000000000000000000000000),((8964712227844240097819783:ℚ)/11552000000000000000000000)⟩
theorem valid10 : Valid source21 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source21 nn0 nn1 Qcell ((4177:ℚ)/6400) ((16727:ℚ)/25600) :=
  cell_of_packet source21 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((16727:ℚ)/25600),((8373:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((449288553:ℚ)/625000000),((1457095953:ℚ)/2000000000),((-3884887859:ℚ)/4181750000),((-2745019871:ℚ)/3270703125),((4905290651:ℚ)/5000000000),((490714947:ℚ)/500000000),((194946007:ℚ)/1000000000),((3305294763:ℚ)/10000000000),((5174851156104112689487034751539554191794383480858839619:ℚ)/43323096891882407958984375000000000000000000000000000000),((91826814643797881552303583:ℚ)/118292480000000000000000000)⟩
theorem valid11 : Valid source21 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source21 nn0 nn1 Qcell ((16727:ℚ)/25600) ((8373:ℚ)/12800) :=
  cell_of_packet source21 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((8373:ℚ)/12800),((3353:ℚ)/5120),((-15:ℚ)/16),((-7:ℚ)/8),((1439210101:ℚ)/2000000000),((7292908363:ℚ)/10000000000),((-19446725089:ℚ)/20932500000),((-8794470707:ℚ)/10478125000),((2451720127:ℚ)/2500000000),((9810581307:ℚ)/10000000000),((123029563:ℚ)/625000000),((3275023107:ℚ)/10000000000),((10996458595234292393017105950189935598115313236399111675484303:ℚ)/92068779037317302636718750000000000000000000000000000000000000),((2296374487265431736656855303:ℚ)/2957312000000000000000000000)⟩
theorem valid12 : Valid source21 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source21 nn0 nn1 Qcell ((8373:ℚ)/12800) ((3353:ℚ)/5120) :=
  cell_of_packet source21 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((3353:ℚ)/5120),((1049:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((1440696827:ℚ)/2000000000),((1460067389:ℚ)/2000000000),((-3893802167:ℚ)/4191250000),((-8804877789:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((9806880513:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((1622239697:ℚ)/5000000000),((60473398187678495736644000034376498290452330575914042507703:ℚ)/506362683817856164550781250000000000000000000000000000000000),((91883147749770034607825527:ℚ)/118292480000000000000000000)⟩
theorem valid13 : Valid source21 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source21 nn0 nn1 Qcell ((3353:ℚ)/5120) ((1049:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1049:ℚ)/1600),((8411:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((3605458869:ℚ)/5000000000),((457199629:ℚ)/625000000),((-1219598887:ℚ)/1311250000),((-22038212083:ℚ)/26284375000),((9795878581:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((1011977397:ℚ)/5000000000),((160682793:ℚ)/500000000),((119815210775570763755831841752486088573128727998667313416887:ℚ)/996854530299972277832031250000000000000000000000000000000000),((8978466261363776031585367:ℚ)/11552000000000000000000000)⟩
theorem valid14 : Valid source21 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source21 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8411:ℚ)/12800) :=
  cell_of_packet source21 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((8411:ℚ)/12800),((843:ℚ)/1280),((-15:ℚ)/16),((-7:ℚ)/8),((1445156973:ℚ)/2000000000),((7330051123:ℚ)/10000000000),((-19558153369:ℚ)/21027500000),((-8836098811:ℚ)/10537500000),((978862711:ℚ)/1000000000),((4897939293:ℚ)/5000000000),((2059717253:ℚ)/10000000000),((3151136363:ℚ)/10000000000),((1240607787756848771166196980852519423509938762925660309808841:ℚ)/10323764764070425268554687500000000000000000000000000000000000),((2299896373680146149783889623:ℚ)/2957312000000000000000000000)⟩
theorem valid15 : Valid source21 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source21 nn0 nn1 Qcell ((8411:ℚ)/12800) ((843:ℚ)/1280) :=
  cell_of_packet source21 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((843:ℚ)/1280),((8449:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((3620325943:ℚ)/5000000000),((3672454061:ℚ)/5000000000),((-9801362183:ℚ)/10537500000),((-1302487153:ℚ)/1553125000),((4890720817:ℚ)/5000000000),((1957725423:ℚ)/2000000000),((83782417:ℚ)/400000000),((3087394549:ℚ)/10000000000),((1240168563039998503370610285210183737805090314887182244849:ℚ)/10322086852885253906250000000000000000000000000000000000000),((575326431513275423606818327:ℚ)/739328000000000000000000000)⟩
theorem valid16 : Valid source21 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source21 nn0 nn1 Qcell ((843:ℚ)/1280) ((8449:ℚ)/12800) :=
  cell_of_packet source21 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((8449:ℚ)/12800),((2117:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((3627759401:ℚ)/5000000000),((3679882531:ℚ)/5000000000),((-9823647593:ℚ)/10561250000),((-22194315807:ℚ)/26462500000),((9774321709:ℚ)/10000000000),((9781441639:ℚ)/10000000000),((425706267:ℚ)/2000000000),((604470601:ℚ)/2000000000),((233157485781912664815282866463062386813385839909923479889201:ℚ)/1940969814352590734863281250000000000000000000000000000000000),((575678855029670481214961207:ℚ)/739328000000000000000000000)⟩
theorem valid17 : Valid source21 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source21 nn0 nn1 Qcell ((8449:ℚ)/12800) ((2117:ℚ)/3200) :=
  cell_of_packet source21 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((2117:ℚ)/3200),((8487:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((3635192807:ℚ)/5000000000),((3687310971:ℚ)/5000000000),((-9845932913:ℚ)/10585000000),((-7415449883:ℚ)/8840625000),((9767266893:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((2161672951:ℚ)/10000000000),((147796293:ℚ)/500000000),((197908530337800351336002323019804167922584162651719336709153:ℚ)/1647843634008718164062500000000000000000000000000000000000000),((576031363944457440086497767:ℚ)/739328000000000000000000000)⟩
theorem valid18 : Valid source21 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source21 nn0 nn1 Qcell ((2117:ℚ)/3200) ((8487:ℚ)/12800) :=
  cell_of_packet source21 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((8487:ℚ)/12800),((4253:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((3642626161:ℚ)/5000000000),((1847369691:ℚ)/2500000000),((-4934109073:ℚ)/5304375000),((-22298383127:ℚ)/26581250000),((9760276751:ℚ)/10000000000),((4883633449:ℚ)/5000000000),((438804929:ℚ)/2000000000),((2888017429:ℚ)/10000000000),((56277907749253784113054294019494191437436086691175589054033:ℚ)/468674085417882271957397460937500000000000000000000000000000),((144095989576013975042241447:ℚ)/184832000000000000000000000)⟩
theorem valid19 : Valid source21 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source21 nn0 nn1 Qcell ((8487:ℚ)/12800) ((4253:ℚ)/6400) :=
  cell_of_packet source21 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((456257433:ℚ)/625000000),((927399029:ℚ)/1250000000),((-2478197087:ℚ)/2658125000),((-2793802031:ℚ)/3337500000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((1409260281:ℚ)/5000000000),((63586462235353015962740950709041829296248642324870593143:ℚ)/523008512594704914093017578125000000000000000000000000000),((36068087706632821861157767:ℚ)/46208000000000000000000000)⟩
theorem valid20 : Valid source21 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source21 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source21 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((3664925917:ℚ)/5000000000),((7448905471:ℚ)/10000000000),((-19914716413:ℚ)/21360000000),((-22454481419:ℚ)/26818750000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((534852613:ℚ)/2000000000),((19469965738231644840230121376559963386663638019201073740444811:ℚ)/160214844078172800000000000000000000000000000000000000000000000),((2311180760585876585340800767:ℚ)/2957312000000000000000000000)⟩
theorem valid21 : Valid source21 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source21 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-15:ℚ)/16),((-7:ℚ)/8),((7359584337:ℚ)/10000000000),((3739309241:ℚ)/5000000000),((-10001927723:ℚ)/10727500000),((-45117090359:ℚ)/53875000000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2521977101:ℚ)/10000000000),((174101163217615688269635097701496670863508404207208176871307:ℚ)/1433276985275305761718750000000000000000000000000000000000000),((578501318840829380512973647:ℚ)/739328000000000000000000000)⟩
theorem valid22 : Valid source21 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source21 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source21 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((3694658221:ℚ)/5000000000),((3769021917:ℚ)/5000000000),((-10091065751:ℚ)/10775000000),((-22662607547:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((236010833:ℚ)/1000000000),((1149234248610117301804090706904727546875646079408137634583631:ℚ)/9238276192663964843750000000000000000000000000000000000000000),((579914602092740421768562743:ℚ)/739328000000000000000000000)⟩
theorem valid23 : Valid source21 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source21 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source21 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-15:ℚ)/16),((-7:ℚ)/8),((186219487:ℚ)/250000000),((7656891941:ℚ)/10000000000),((-20538675823:ℚ)/21740000000),((-1143536409:ℚ)/1382500000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((15985503:ℚ)/80000000),((3259708973016510386024102633660699339265562528573439637783:ℚ)/25049140950696875000000000000000000000000000000000000000000),((805248689:ℚ)/1024000000)⟩
theorem valid24 : Valid source21 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source21 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source21 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((7567701009:ℚ)/10000000000),((7894578367:ℚ)/10000000000),((-21251735101:ℚ)/22120000000),((-46573907063:ℚ)/57200000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((922266871:ℚ)/10000000000),((27891045524528781538061826554499843737255701329908021365163:ℚ)/197610228415600000000000000000000000000000000000000000000000),((805248689:ℚ)/1024000000)⟩
theorem valid25 : Valid source21 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source21 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((7805526939:ℚ)/10000000000),((4422607319:ℚ)/5000000000),(-1:ℚ),((-48238688573:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((3755761115427905151385678812062497453:ℚ)/20995200000000000000000000000000000000),((805248689:ℚ)/1024000000)⟩
theorem valid26 : Valid source21 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source21 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source21 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((8756639201:ℚ)/10000000000),((10746124251:ℚ)/10000000000),(-1:ℚ),((-54896474407:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1534200461824949814697677654929437257:ℚ)/8000000000000000000000000000000000000),((805248689:ℚ)/1024000000)⟩
theorem valid27 : Valid source21 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source21 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((2131645791:ℚ)/2000000000),((7273595873:ℚ)/5000000000),(-1:ℚ),((-13641520537:ℚ)/22080000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((52749288753060661406960227:ℚ)/243763200000000000000000000),((805248689:ℚ)/1024000000)⟩
theorem valid28 : Valid source21 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source21 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source21 nn0 nn1 packet28 valid28
private theorem node1_3 :
    CellBound source21 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4101:ℚ)/6400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((4101:ℚ)/6400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source21 nn0 nn1 Qcell ((4101:ℚ)/6400) ((8259:ℚ)/12800) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source21 nn0 nn1 Qcell ((8259:ℚ)/12800) ((8297:ℚ)/12800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source21 nn0 nn1 Qcell ((4101:ℚ)/6400) ((8297:ℚ)/12800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((8297:ℚ)/12800) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source21 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source21 nn0 nn1 Qcell ((8297:ℚ)/12800) ((4177:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source21 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8373:ℚ)/12800) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source21 nn0 nn1 Qcell ((8373:ℚ)/12800) ((1049:ℚ)/1600) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source21 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source21 nn0 nn1 Qcell ((8297:ℚ)/12800) ((1049:ℚ)/1600) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_7 node7_14
private theorem node15_17 :
    CellBound source21 nn0 nn1 Qcell ((8411:ℚ)/12800) ((8449:ℚ)/12800) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source21 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8449:ℚ)/12800) :=
  cell_join leaf14 node15_17
private theorem node17_19 :
    CellBound source21 nn0 nn1 Qcell ((8449:ℚ)/12800) ((8487:ℚ)/12800) :=
  cell_join leaf17 leaf18
private theorem node19_21 :
    CellBound source21 nn0 nn1 Qcell ((8487:ℚ)/12800) ((267:ℚ)/400) :=
  cell_join leaf19 leaf20
private theorem node17_21 :
    CellBound source21 nn0 nn1 Qcell ((8449:ℚ)/12800) ((267:ℚ)/400) :=
  cell_join node17_19 node19_21
private theorem node14_21 :
    CellBound source21 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join node14_17 node17_21
private theorem node21_23 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_join leaf21 leaf22
private theorem node23_25 :
    CellBound source21 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join leaf23 leaf24
private theorem node21_25 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join node21_23 node23_25
private theorem node25_27 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf25 leaf26
private theorem node27_29 :
    CellBound source21 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf27 leaf28
private theorem node25_29 :
    CellBound source21 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node25_27 node27_29
private theorem node21_29 :
    CellBound source21 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node21_25 node25_29
private theorem node14_29 :
    CellBound source21 nn0 nn1 Qcell ((1049:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node14_21 node21_29
private theorem node0_29 :
    CellBound source21 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_14 node14_29
theorem bound : CellBound source21 nn0 nn1 Qcell (31/50) (69/50) := node0_29
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28]
theorem packet_count : packets.length = 29 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source21GroupedC02
#check @N11Formalization.C450Source21GroupedC02.bound
#print axioms N11Formalization.C450Source21GroupedC02.valid0
#print axioms N11Formalization.C450Source21GroupedC02.valid1
#print axioms N11Formalization.C450Source21GroupedC02.valid2
#print axioms N11Formalization.C450Source21GroupedC02.valid3
#print axioms N11Formalization.C450Source21GroupedC02.valid4
#print axioms N11Formalization.C450Source21GroupedC02.valid5
#print axioms N11Formalization.C450Source21GroupedC02.valid6
#print axioms N11Formalization.C450Source21GroupedC02.valid7
#print axioms N11Formalization.C450Source21GroupedC02.valid8
#print axioms N11Formalization.C450Source21GroupedC02.valid9
#print axioms N11Formalization.C450Source21GroupedC02.valid10
#print axioms N11Formalization.C450Source21GroupedC02.valid11
#print axioms N11Formalization.C450Source21GroupedC02.valid12
#print axioms N11Formalization.C450Source21GroupedC02.valid13
#print axioms N11Formalization.C450Source21GroupedC02.valid14
#print axioms N11Formalization.C450Source21GroupedC02.valid15
#print axioms N11Formalization.C450Source21GroupedC02.valid16
#print axioms N11Formalization.C450Source21GroupedC02.valid17
#print axioms N11Formalization.C450Source21GroupedC02.valid18
#print axioms N11Formalization.C450Source21GroupedC02.valid19
#print axioms N11Formalization.C450Source21GroupedC02.valid20
#print axioms N11Formalization.C450Source21GroupedC02.valid21
#print axioms N11Formalization.C450Source21GroupedC02.valid22
#print axioms N11Formalization.C450Source21GroupedC02.valid23
#print axioms N11Formalization.C450Source21GroupedC02.valid24
#print axioms N11Formalization.C450Source21GroupedC02.valid25
#print axioms N11Formalization.C450Source21GroupedC02.valid26
#print axioms N11Formalization.C450Source21GroupedC02.valid27
#print axioms N11Formalization.C450Source21GroupedC02.valid28
#print axioms N11Formalization.C450Source21GroupedC02.bound
#print axioms N11Formalization.C450Source21GroupedC02.endpoint_checks
