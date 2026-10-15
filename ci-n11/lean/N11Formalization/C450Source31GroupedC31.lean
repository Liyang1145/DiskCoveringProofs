import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC31
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((7:ℚ)/8),((15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((7:ℚ)/8),((15:ℚ)/16),((5060921513:ℚ)/10000000000),((1349489519:ℚ)/2500000000),((44706450591:ℚ)/51500000000),(1:ℚ),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((842082413:ℚ)/1000000000),((-4570809553931719650081875806190169339:ℚ)/13261250000000000000000000000000000000),((-925159724643333532858870197:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((5298942031:ℚ)/10000000000),((1127266891:ℚ)/2000000000),((46372594217:ℚ)/53400000000),(1:ℚ),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((399635683:ℚ)/500000000),((-823840116110283875271516449233161727:ℚ)/2376300000000000000000000000000000000),((-911276594881890779163383493:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((1107385079:ℚ)/2000000000),((2877749773:ℚ)/5000000000),((9607695553:ℚ)/10870000000),((3517749773:ℚ)/3560000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7546040663:ℚ)/10000000000),((-120535054583855812763802289246318898175721834608016426960799:ℚ)/333187806544400000000000000000000000000000000000000000000000),((-36188477796887789877110133:ℚ)/73932800000000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((5655904367:ℚ)/10000000000),((2937325151:ℚ)/5000000000),((48871330569:ℚ)/55300000000),((10731975453:ℚ)/10870000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((91432881:ℚ)/125000000),((-7949182534239264175610920839844742720635797076221977635713:ℚ)/21917998331859765625000000000000000000000000000000000000000),((-897800229500630767167949957:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((5774875449:ℚ)/10000000000),((1186844107:ℚ)/2000000000),((49704128143:ℚ)/55775000000),((4328532321:ℚ)/4424000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3538554253:ℚ)/5000000000),((-20389790225869021090490522737405579312497324701178032103163:ℚ)/54970341217769600000000000000000000000000000000000000000000),((-894538342667578798015049813:ℚ)/1848320000000000000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((7:ℚ)/8),((15:ℚ)/16),((5834358159:ℚ)/10000000000),((93652929:ℚ)/156250000),((50120507113:ℚ)/56250000000),((340958787:ℚ)/348593750),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((434740859:ℚ)/625000000),((-44053890959861483964306153435309451834042062659:ℚ)/118669533729553222656250000000000000000000000000),((-891089891568695335697699653:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((1473459761:ℚ)/2500000000),((3026675573:ℚ)/5000000000),((12634218327:ℚ)/14181250000),((1222225191:ℚ)/1250000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1708203807:ℚ)/2500000000),((-23349076379274292964497051042442306881820607069156935838597:ℚ)/62846203613281250000000000000000000000000000000000000000000),((-55477725398196466999561573:ℚ)/115520000000000000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((744164769:ℚ)/1250000000),((764113961:ℚ)/1250000000),((6369153383:ℚ)/7150000000),((2772341883:ℚ)/2836250000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((1341578413:ℚ)/2000000000),((-43367799671096584052845410945900485197953334285612664161:ℚ)/116639489525361816406250000000000000000000000000000000000),((-13815616905924238100922693:ℚ)/28880000000000000000000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((3006397763:ℚ)/5000000000),((154311729:ℚ)/250000000),((25684784341:ℚ)/28837500000),((558935187:ℚ)/572000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((6580974183:ℚ)/10000000000),((-193028308029497883800627008483931132951427728387393958067:ℚ)/518778592718100000000000000000000000000000000000000000000),((-220189378398045300591405197:ℚ)/462080000000000000000000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((6072271209:ℚ)/10000000000),((6232023637:ℚ)/10000000000),((51785898463:ℚ)/58150000000),((7512023637:ℚ)/7690000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((6451941093:ℚ)/10000000000),((-57256023966129225606262783343892114559997091680898967748911:ℚ)/153772422969630250000000000000000000000000000000000000000000),((-877317696598789505303180853:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((4671:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((6131745243:ℚ)/10000000000),((195681243:ℚ)/312500000),((52202216701:ℚ)/58387500000),((707043729:ℚ)/726875000),((148605427:ℚ)/156250000),((4759921809:ℚ)/5000000000),((98156347:ℚ)/312500000),((316033023:ℚ)/500000000),((-1641076045524062382111562173582870427729158511465373951041:ℚ)/4364130232002643203735351562500000000000000000000000000000),((-875700096357483909495348637:ℚ)/1848320000000000000000000000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((4671:ℚ)/6400) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4671:ℚ)/6400),((469:ℚ)/640),((7:ℚ)/8),((15:ℚ)/16),((1232296331:ℚ)/2000000000),((6291575193:ℚ)/10000000000),((10482074317:ℚ)/11725000000),((7571575193:ℚ)/7785000000),((9501845013:ℚ)/10000000000),((9510747333:ℚ)/10000000000),((792422551:ℚ)/2500000000),((1250826461:ℚ)/2000000000),((-9036203483343449983631970442284323935082428436097568161713:ℚ)/24023583471874218750000000000000000000000000000000000000000),((-34959280858219290800319293:ℚ)/73932800000000000000000000)⟩
theorem valid11 : Valid source31 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source31 nn0 nn1 Qcell ((4671:ℚ)/6400) ((469:ℚ)/640) :=
  cell_of_packet source31 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((469:ℚ)/640),((4709:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((6191217669:ℚ)/10000000000),((3160674949:ℚ)/5000000000),((52618523683:ℚ)/58862500000),((11402024847:ℚ)/11725000000),((9493134321:ℚ)/10000000000),((4750922509:ℚ)/5000000000),((1598759513:ℚ)/5000000000),((773373299:ℚ)/1250000000),((-3001792301076636202878371873812091652067498339141339334203243:ℚ)/7978438854944995117187500000000000000000000000000000000000000),((-872264482137416431994835293:ℚ)/1848320000000000000000000000)⟩
theorem valid12 : Valid source31 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source31 nn0 nn1 Qcell ((469:ℚ)/640) ((4709:ℚ)/6400) :=
  cell_of_packet source31 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4709:ℚ)/6400),((591:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((6220953291:ℚ)/10000000000),((3175561949:ℚ)/5000000000),((52826673037:ℚ)/59100000000),((11446685847:ℚ)/11772500000),((4742306471:ℚ)/5000000000),((4746567163:ℚ)/5000000000),((806129637:ℚ)/2500000000),((382450127:ℚ)/625000000),((-111700315916535772334064914045693507239188382722235530872783:ℚ)/296810889471728100585937500000000000000000000000000000000000),((-870547477976416338708497853:ℚ)/1848320000000000000000000000)⟩
theorem valid13 : Valid source31 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source31 nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((250027541:ℚ)/400000000),((3205334911:ℚ)/5000000000),((2121392787:ℚ)/2383000000),((3845334911:ℚ)/3940000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((756344677:ℚ)/1250000000),((-809832696134879384681048888377552185355700128221001127217477:ℚ)/2170784777799850000000000000000000000000000000000000000000000),((-1387217775170142064745853:ℚ)/2957312000000000000000000)⟩
theorem valid14 : Valid source31 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((788769731:ℚ)/1250000000),((647021303:ℚ)/1000000000),((6681388117:ℚ)/7506250000),((2325063909:ℚ)/2383000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2955897017:ℚ)/5000000000),((-2846110015699253419007863828304401722747271615101835332127:ℚ)/7624619518642455859375000000000000000000000000000000000000),((-13493435224279757301654693:ℚ)/28880000000000000000000000)⟩
theorem valid15 : Valid source31 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source31 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((1592406419:ℚ)/2500000000),((3264876793:ℚ)/5000000000),((4488948311:ℚ)/5043750000),((11714630379:ℚ)/12010000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((2884947881:ℚ)/5000000000),((-877833646667997314112568569889399587800976650757277218253291:ℚ)/2350362526724268750000000000000000000000000000000000000000000),((-53759420595957095247265293:ℚ)/115520000000000000000000000)⟩
theorem valid16 : Valid source31 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source31 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source31 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/8),((15:ℚ)/16),((1607273011:ℚ)/2500000000),((3294645777:ℚ)/5000000000),((13570911077:ℚ)/15250000000),((3934645777:ℚ)/4035000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((5624837533:ℚ)/10000000000),((-21145456328484143308715303136208670396916087792082568537:ℚ)/56585680147656250000000000000000000000000000000000000000),((-53545233193137305277338573:ℚ)/115520000000000000000000000)⟩
theorem valid17 : Valid source31 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source31 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source31 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((1297711397:ℚ)/2000000000),((3354179981:ℚ)/5000000000),((10939979779:ℚ)/12390000000),((11982539943:ℚ)/12200000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1369091313:ℚ)/2500000000),((-177813474680054054004463357671220138487558337159823376819949:ℚ)/483949027362500000000000000000000000000000000000000000000000),((-33986392303992385690901917:ℚ)/73932800000000000000000000)⟩
theorem valid18 : Valid source31 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((6607482721:ℚ)/10000000000),((3413709357:ℚ)/5000000000),((55532379047:ℚ)/62900000000),((4053709357:ℚ)/4130000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2583991187:ℚ)/5000000000),((-8940756703970580224370524694783666935219263721585795033:ℚ)/24301521569891357421875000000000000000000000000000000000),((-842816701798471648587968933:ℚ)/1848320000000000000000000000)⟩
theorem valid19 : Valid source31 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source31 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/8),((15:ℚ)/16),((105100049:ℚ)/156250000),((7065508959:ℚ)/10000000000),((293566781:ℚ)/337500000),((25036526877:ℚ)/25160000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((4841883749:ℚ)/10000000000),((-8609967049755355128947991546959100716196868665011328780613:ℚ)/24189015970800000000000000000000000000000000000000000000000),((-3237130774624017482822783:ℚ)/7220000000000000000000000)⟩
theorem valid20 : Valid source31 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source31 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((6964228947:ℚ)/10000000000),((2004389791:ℚ)/2500000000),((58029602629:ℚ)/72400000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((2059698519:ℚ)/5000000000),((-8369347471339036797731557203749395349:ℚ)/26208800000000000000000000000000000000),((-796942322332821672363185517:ℚ)/1848320000000000000000000000)⟩
theorem valid21 : Valid source31 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((7:ℚ)/8),((15:ℚ)/16),((3957680443:ℚ)/5000000000),((22423047:ℚ)/25000000),((32343763101:ℚ)/40000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-2589433190587852386578896899330678549:ℚ)/8000000000000000000000000000000000000),((-27684413:ℚ)/64000000)⟩
theorem valid22 : Valid source31 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source31 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/8),((15:ℚ)/16),((8866277443:ℚ)/10000000000),((12773568637:ℚ)/10000000000),((71343942101:ℚ)/110400000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-156580522534386711526763201:ℚ)/677120000000000000000000000),((-27684413:ℚ)/64000000)⟩
theorem valid23 : Valid source31 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet23 valid23
private theorem node1_3 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source31 nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source31 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_6 node6_12
private theorem node13_15 :
    CellBound source31 nn0 nn1 Qcell ((4709:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source31 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf12 node13_15
private theorem node16_18 :
    CellBound source31 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source31 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf15 node16_18
private theorem node12_18 :
    CellBound source31 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node12_15 node15_18
private theorem node19_21 :
    CellBound source31 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf18 node19_21
private theorem node22_24 :
    CellBound source31 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf22 leaf23
private theorem node21_24 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf21 node22_24
private theorem node18_24 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node18_21 node21_24
private theorem node12_24 :
    CellBound source31 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node12_18 node18_24
private theorem node0_24 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_12 node12_24
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_24
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23]
theorem packet_count : packets.length = 24 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC31
#check @N11Formalization.C450Source31GroupedC31.bound
#print axioms N11Formalization.C450Source31GroupedC31.valid0
#print axioms N11Formalization.C450Source31GroupedC31.valid1
#print axioms N11Formalization.C450Source31GroupedC31.valid2
#print axioms N11Formalization.C450Source31GroupedC31.valid3
#print axioms N11Formalization.C450Source31GroupedC31.valid4
#print axioms N11Formalization.C450Source31GroupedC31.valid5
#print axioms N11Formalization.C450Source31GroupedC31.valid6
#print axioms N11Formalization.C450Source31GroupedC31.valid7
#print axioms N11Formalization.C450Source31GroupedC31.valid8
#print axioms N11Formalization.C450Source31GroupedC31.valid9
#print axioms N11Formalization.C450Source31GroupedC31.valid10
#print axioms N11Formalization.C450Source31GroupedC31.valid11
#print axioms N11Formalization.C450Source31GroupedC31.valid12
#print axioms N11Formalization.C450Source31GroupedC31.valid13
#print axioms N11Formalization.C450Source31GroupedC31.valid14
#print axioms N11Formalization.C450Source31GroupedC31.valid15
#print axioms N11Formalization.C450Source31GroupedC31.valid16
#print axioms N11Formalization.C450Source31GroupedC31.valid17
#print axioms N11Formalization.C450Source31GroupedC31.valid18
#print axioms N11Formalization.C450Source31GroupedC31.valid19
#print axioms N11Formalization.C450Source31GroupedC31.valid20
#print axioms N11Formalization.C450Source31GroupedC31.valid21
#print axioms N11Formalization.C450Source31GroupedC31.valid22
#print axioms N11Formalization.C450Source31GroupedC31.valid23
#print axioms N11Formalization.C450Source31GroupedC31.bound
#print axioms N11Formalization.C450Source31GroupedC31.endpoint_checks
