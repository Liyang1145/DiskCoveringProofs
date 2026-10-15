import N11Formalization.C450Source34Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source34GroupedC32
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source34Data
def Qcell : RatInterval := ⟨((15:ℚ)/16),(1:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((15:ℚ)/16),(1:ℚ),((2439999999:ℚ)/5000000000),((2611035903:ℚ)/5000000000),((9367999997:ℚ)/10300000000),(1:ℚ),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((4367775171:ℚ)/5000000000),((-3400643274542579:ℚ)/10300000000000000),((-421743392709737966164280331:ℚ)/739328000000000000000000000)⟩
theorem valid0 : Valid source34 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source34 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((15:ℚ)/16),(1:ℚ),((2558749999:ℚ)/5000000000),((2730060999:ℚ)/5000000000),((9724249997:ℚ)/10680000000),(1:ℚ),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((4160292749:ℚ)/5000000000),((-8713374776803051849099609:ℚ)/26074218750000000000000000),((-416998453566029757131780331:ℚ)/739328000000000000000000000)⟩
theorem valid1 : Valid source34 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source34 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((2677499999:ℚ)/5000000000),((5579132621:ℚ)/10000000000),((10080499997:ℚ)/10870000000),(1:ℚ),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1577859233:ℚ)/2000000000),((-28158041600579675340232879853:ℚ)/81525000000000000000000000000),((-416017551248505424539280331:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source34 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((15:ℚ)/16),(1:ℚ),((5473749997:ℚ)/10000000000),((5698134261:ℚ)/10000000000),((2931035713:ℚ)/3160000000),(1:ℚ),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((3833310739:ℚ)/5000000000),((-128431304298666696724591349:ℚ)/370312500000000000000000000),((-1655005713717446359231022979:ℚ)/2957312000000000000000000000)⟩
theorem valid3 : Valid source34 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source34 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((2796249999:ℚ)/5000000000),((359851991:ℚ)/625000000),((453771739:ℚ)/485000000),(1:ℚ),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3719337287:ℚ)/5000000000),((-853544713086482782622436889:ℚ)/2425000000000000000000000000),((-413336662646960229826780331:ℚ)/739328000000000000000000000)⟩
theorem valid4 : Valid source34 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((15:ℚ)/16),(1:ℚ),((2825937499:ℚ)/5000000000),((46537019:ℚ)/80000000),((10525812497:ℚ)/11250000000),(1:ℚ),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((114415067:ℚ)/156250000),((-79327614176254030781163977:ℚ)/225000000000000000000000000),((-412230170703206717202405331:ℚ)/739328000000000000000000000)⟩
theorem valid5 : Valid source34 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source34 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source34 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((2855624999:ℚ)/5000000000),((5876620869:ℚ)/10000000000),((10614874997:ℚ)/11345000000),(1:ℚ),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((7204934523:ℚ)/10000000000),((-20031486600891531479668890213:ℚ)/56725000000000000000000000000),((-411131285655874917015530331:ℚ)/739328000000000000000000000)⟩
theorem valid6 : Valid source34 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((2885312499:ℚ)/5000000000),((5906366873:ℚ)/10000000000),((10703937497:ℚ)/11392500000),(1:ℚ),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((3542853533:ℚ)/5000000000),((-231477045626793621006414787:ℚ)/651000000000000000000000000),((-410950395474378947666155331:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid source34 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source34 nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet source34 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((15:ℚ)/16),(1:ℚ),((2900156249:ℚ)/5000000000),((593611239:ℚ)/1000000000),((10748468747:ℚ)/11440000000),(1:ℚ),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((1405093607:ℚ)/2000000000),((-318020093589804002561436031:ℚ)/893750000000000000000000000),((-410407592400487354755530331:ℚ)/739328000000000000000000000)⟩
theorem valid8 : Valid source34 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source34 nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((15:ℚ)/16),(1:ℚ),((2914999999:ℚ)/5000000000),((238634297:ℚ)/400000000),((10792999997:ℚ)/11487500000),(1:ℚ),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((1392959463:ℚ)/2000000000),((-6135641308376317904918901701:ℚ)/17231250000000000000000000000),((-409866690308507102274280331:ℚ)/739328000000000000000000000)⟩
theorem valid9 : Valid source34 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet source34 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((2929843749:ℚ)/5000000000),((1199120397:ℚ)/2000000000),((10837531247:ℚ)/11535000000),(1:ℚ),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((6903683209:ℚ)/10000000000),((-5137699328286304564234563659:ℚ)/14418750000000000000000000000),((-409327688984196597902405331:ℚ)/739328000000000000000000000)⟩
theorem valid10 : Valid source34 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source34 nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2307:ℚ)/3200),((4633:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((2944687499:ℚ)/5000000000),((1506336519:ℚ)/2500000000),((10882062497:ℚ)/11582500000),(1:ℚ),((1905827251:ℚ)/2000000000),((1907725537:ℚ)/2000000000),((3080928657:ℚ)/10000000000),((1710528379:ℚ)/2500000000),((-1651941242781174091401542089:ℚ)/4633000000000000000000000000),((-408790588243920191079905331:ℚ)/739328000000000000000000000)⟩
theorem valid11 : Valid source34 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source34 nn0 nn1 Qcell ((2307:ℚ)/3200) ((4633:ℚ)/6400) :=
  cell_of_packet source34 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4633:ℚ)/6400),((1163:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((2959531249:ℚ)/5000000000),((6055089703:ℚ)/10000000000),((10926593747:ℚ)/11630000000),(1:ℚ),((9519843613:ℚ)/10000000000),((476456813:ℚ)/500000000),((622285377:ℚ)/2000000000),((6780075507:ℚ)/10000000000),((-25934428788707214567252179:ℚ)/72687500000000000000000000),((-408255387934648173006780331:ℚ)/739328000000000000000000000)⟩
theorem valid12 : Valid source34 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source34 nn0 nn1 Qcell ((4633:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1163:ℚ)/1600),((9323:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((2974374999:ℚ)/5000000000),((1213992269:ℚ)/2000000000),((10971124997:ℚ)/11653750000),(1:ℚ),((2378817769:ℚ)/2500000000),((4759921809:ℚ)/5000000000),((156316407:ℚ)/500000000),((1679388971:ℚ)/2500000000),((-62572301995284633170060939473:ℚ)/174806250000000000000000000000),((-408177244961989160643030331:ℚ)/739328000000000000000000000)⟩
theorem valid13 : Valid source34 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((9323:ℚ)/12800) :=
  cell_of_packet source34 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((9323:ℚ)/12800),((4671:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((1490898437:ℚ)/2500000000),((760604109:ℚ)/1250000000),((5496695311:ℚ)/5838750000),(1:ℚ),((148605427:ℚ)/156250000),((9515271081:ℚ)/10000000000),((98156347:ℚ)/312500000),((133722223:ℚ)/200000000),((-41812786099369523070480815167:ℚ)/116775000000000000000000000000),((-101977826006767987860542739:ℚ)/184832000000000000000000000)⟩
theorem valid14 : Valid source34 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source34 nn0 nn1 Qcell ((9323:ℚ)/12800) ((4671:ℚ)/6400) :=
  cell_of_packet source34 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4671:ℚ)/6400),((9361:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((2989218749:ℚ)/5000000000),((6099704287:ℚ)/10000000000),((11015656247:ℚ)/11701250000),(1:ℚ),((1188284009:ℚ)/1250000000),((9510747333:ℚ)/10000000000),((157772791:ℚ)/500000000),((415908797:ℚ)/625000000),((-251463659658189115018912026059:ℚ)/702075000000000000000000000000),((-407645838077482072388655331:ℚ)/739328000000000000000000000)⟩
theorem valid15 : Valid source34 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source34 nn0 nn1 Qcell ((4671:ℚ)/6400) ((9361:ℚ)/12800) :=
  cell_of_packet source34 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((9361:ℚ)/12800),((469:ℚ)/640),((15:ℚ)/16),(1:ℚ),((187290039:ℚ)/312500000),((6114575589:ℚ)/10000000000),((689870117:ℚ)/732812500),(1:ℚ),((9501845013:ℚ)/10000000000),((9506272077:ℚ)/10000000000),((792422551:ℚ)/2500000000),((3311421427:ℚ)/5000000000),((-1800357414840676400964225953:ℚ)/5025000000000000000000000000),((-1591331434155568223603451:ℚ)/2888000000000000000000000)⟩
theorem valid16 : Valid source34 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source34 nn0 nn1 Qcell ((9361:ℚ)/12800) ((469:ℚ)/640) :=
  cell_of_packet source34 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((469:ℚ)/640),((9399:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((3004062499:ℚ)/5000000000),((306472339:ℚ)/500000000),((11060187497:ℚ)/11748750000),(1:ℚ),((474873293:ℚ)/500000000),((4750922509:ℚ)/5000000000),((636742009:ℚ)/2000000000),((823876947:ℚ)/1250000000),((-21052987730044808320766335583:ℚ)/58743750000000000000000000000),((-407116331164890246483655331:ℚ)/739328000000000000000000000)⟩
theorem valid17 : Valid source34 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source34 nn0 nn1 Qcell ((469:ℚ)/640) ((9399:ℚ)/12800) :=
  cell_of_packet source34 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((9399:ℚ)/12800),((4709:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((1505742187:ℚ)/2500000000),((307215893:ℚ)/500000000),((5541226561:ℚ)/5886250000),(1:ℚ),((9493134321:ℚ)/10000000000),((1899493173:ℚ)/2000000000),((1598759513:ℚ)/5000000000),((3279528497:ℚ)/5000000000),((-5064422091443279575438117831:ℚ)/14127000000000000000000000000),((-101713072535169104028042739:ℚ)/184832000000000000000000000)⟩
theorem valid18 : Valid source34 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source34 nn0 nn1 Qcell ((9399:ℚ)/12800) ((4709:ℚ)/6400) :=
  cell_of_packet source34 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((4709:ℚ)/6400),((9437:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((3018906249:ℚ)/5000000000),((6159188829:ℚ)/10000000000),((11104718747:ℚ)/11796250000),(1:ℚ),((948885011:ℚ)/1000000000),((4746567163:ℚ)/5000000000),((802780177:ℚ)/2500000000),((6526965139:ℚ)/10000000000),((-21150482868787340185916782021:ℚ)/58981250000000000000000000000),((-406588724071183974128030331:ℚ)/739328000000000000000000000)⟩
theorem valid19 : Valid source34 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source34 nn0 nn1 Qcell ((4709:ℚ)/6400) ((9437:ℚ)/12800) :=
  cell_of_packet source34 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((9437:ℚ)/12800),((591:ℚ)/800),((15:ℚ)/16),(1:ℚ),((756582031:ℚ)/1250000000),((771757461:ℚ)/1250000000),((2781746093:ℚ)/2955000000),(1:ℚ),((4742306471:ℚ)/5000000000),((1897770023:ℚ)/2000000000),((806129637:ℚ)/2500000000),((3247368997:ℚ)/5000000000),((-211991602630850836157347823:ℚ)/591000000000000000000000000),((-25395352057862936173202091:ℚ)/46208000000000000000000000)⟩
theorem valid20 : Valid source34 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source34 nn0 nn1 Qcell ((9437:ℚ)/12800) ((591:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((591:ℚ)/800),((379:ℚ)/512),((15:ℚ)/16),(1:ℚ),((3033749999:ℚ)/5000000000),((6188930439:ℚ)/10000000000),((11149249997:ℚ)/11843750000),(1:ℚ),((2370105633:ℚ)/2500000000),((9484612947:ℚ)/10000000000),((323771591:ℚ)/1000000000),((807796687:ℚ)/1250000000),((-10198939664602234293092334281:ℚ)/28425000000000000000000000000),((-406063016643333546521780331:ℚ)/739328000000000000000000000)⟩
theorem valid21 : Valid source34 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source34 nn0 nn1 Qcell ((591:ℚ)/800) ((379:ℚ)/512) :=
  cell_of_packet source34 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((379:ℚ)/512),((4747:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((1520585937:ℚ)/2500000000),((6203801081:ℚ)/10000000000),((5585757811:ℚ)/5933750000),(1:ℚ),((9476278601:ℚ)/10000000000),((9480422537:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((642986953:ℚ)/1000000000),((-42592750112817712524598741451:ℚ)/118675000000000000000000000000),((-101450218813592404784917739:ℚ)/184832000000000000000000000)⟩
theorem valid22 : Valid source34 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source34 nn0 nn1 Qcell ((379:ℚ)/512) ((4747:ℚ)/6400) :=
  cell_of_packet source34 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3048593749:ℚ)/5000000000),((6233542043:ℚ)/10000000000),((11193781247:ℚ)/11915000000),(1:ℚ),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((799652991:ℚ)/1250000000),((-5333309555747698597832362479:ℚ)/14893750000000000000000000000),((-405084085274994981584905331:ℚ)/739328000000000000000000000)⟩
theorem valid23 : Valid source34 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source34 nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((2383:ℚ)/3200),((957:ℚ)/1280),((15:ℚ)/16),(1:ℚ),((3063437499:ℚ)/5000000000),((6263282579:ℚ)/10000000000),((11238312497:ℚ)/11962500000),(1:ℚ),((75681297:ℚ)/80000000),((2367032267:ℚ)/2500000000),((1650403157:ℚ)/5000000000),((3165749441:ℚ)/5000000000),((-535754950729034169070227461:ℚ)/1495312500000000000000000000),((-404562183177620828437405331:ℚ)/739328000000000000000000000)⟩
theorem valid24 : Valid source34 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source34 nn0 nn1 Qcell ((2383:ℚ)/3200) ((957:ℚ)/1280) :=
  cell_of_packet source34 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((957:ℚ)/1280),((1201:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3078281249:ℚ)/5000000000),((3146511347:ℚ)/5000000000),((11282843747:ℚ)/12010000000),(1:ℚ),((4726187811:ℚ)/5000000000),((946016213:ℚ)/1000000000),((831186567:ℚ)/2500000000),((1566294979:ℚ)/2500000000),((-107634859449609024580723033:ℚ)/300250000000000000000000000),((-404042180195195568359280331:ℚ)/739328000000000000000000000)⟩
theorem valid25 : Valid source34 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source34 nn0 nn1 Qcell ((957:ℚ)/1280) ((1201:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((1201:ℚ)/1600),((4823:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3093124999:ℚ)/5000000000),((3161381197:ℚ)/5000000000),((11327374997:ℚ)/12057500000),(1:ℚ),((9444767421:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1673989387:ℚ)/5000000000),((1239649527:ℚ)/2000000000),((-6178160094678374850292449817:ℚ)/17225000000000000000000000000),((-403524076144083550790530331:ℚ)/739328000000000000000000000)⟩
theorem valid26 : Valid source34 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source34 nn0 nn1 Qcell ((1201:ℚ)/1600) ((4823:ℚ)/6400) :=
  cell_of_packet source34 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((4823:ℚ)/6400),((2421:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3107968749:ℚ)/5000000000),((6352501683:ℚ)/10000000000),((11371906247:ℚ)/12105000000),(1:ℚ),((4718667711:ℚ)/5000000000),((4722383713:ℚ)/5000000000),((674104879:ℚ)/2000000000),((383167601:ℚ)/625000000),((-5429990967121879968803496293:ℚ)/15131250000000000000000000000),((-403007870901861008691155331:ℚ)/739328000000000000000000000)⟩
theorem valid27 : Valid source34 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source34 nn0 nn1 Qcell ((4823:ℚ)/6400) ((2421:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((15:ℚ)/16),(1:ℚ),((3122812499:ℚ)/5000000000),((6411979049:ℚ)/10000000000),((11416437497:ℚ)/12200000000),(1:ℚ),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((3031230167:ℚ)/5000000000),((-544826606949967768737013333:ℚ)/1525000000000000000000000000),((-401583390036769483181155331:ℚ)/739328000000000000000000000)⟩
theorem valid28 : Valid source34 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source34 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source34 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((6304999997:ℚ)/10000000000),((1617863707:ℚ)/2500000000),((23010999991:ℚ)/24590000000),(1:ℚ),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((118479197:ℚ)/200000000),((-5496258941276732370263636267:ℚ)/15368750000000000000000000000),((-1602241985416394809188522979:ℚ)/2957312000000000000000000000)⟩
theorem valid29 : Valid source34 packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source34 nn0 nn1 packet29 valid29
def packet30 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3182187499:ℚ)/5000000000),((3265464529:ℚ)/5000000000),((1656366071:ℚ)/1770000000),(1:ℚ),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((5782548443:ℚ)/10000000000),((-1584019370588510164049379121:ℚ)/4425000000000000000000000000),((-399545195026408843034905331:ℚ)/739328000000000000000000000)⟩
theorem valid30 : Valid source34 packet30 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf30 :
    CellBound source34 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source34 nn0 nn1 packet30 valid30
def packet31 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3211874999:ℚ)/5000000000),((6649873011:ℚ)/10000000000),((11683624997:ℚ)/12580000000),(1:ℚ),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2819002137:ℚ)/5000000000),((-1362366897373377527411727:ℚ)/3839111328125000000000000),((-396717311725993556258030331:ℚ)/739328000000000000000000000)⟩
theorem valid31 : Valid source34 packet31 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf31 :
    CellBound source34 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source34 nn0 nn1 packet31 valid31
def packet32 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((15:ℚ)/16),(1:ℚ),((3271249999:ℚ)/5000000000),((860967977:ℚ)/1250000000),((11861749997:ℚ)/12960000000),(1:ℚ),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2669241301:ℚ)/5000000000),((-706536823242078515697501577:ℚ)/2025000000000000000000000000),((-391084703275541965776780331:ℚ)/739328000000000000000000000)⟩
theorem valid32 : Valid source34 packet32 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf32 :
    CellBound source34 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source34 nn0 nn1 packet32 valid32
def packet33 : Packet := ⟨((81:ℚ)/100),((343:ℚ)/400),((15:ℚ)/16),(1:ℚ),((3389999999:ℚ)/5000000000),((294536947:ℚ)/400000000),((1745428571:ℚ)/1960000000),(1:ℚ),((57977633:ℚ)/62500000),((2332870371:ℚ)/2500000000),((1913736159:ℚ)/5000000000),((4688129407:ℚ)/10000000000),((-11087190334944360544108877:ℚ)/32812500000000000000000000),((-379911915354824187824280331:ℚ)/739328000000000000000000000)⟩
theorem valid33 : Valid source34 packet33 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf33 :
    CellBound source34 nn0 nn1 Qcell ((81:ℚ)/100) ((343:ℚ)/400) :=
  cell_of_packet source34 nn0 nn1 packet33 valid33
def packet34 : Packet := ⟨((343:ℚ)/400),((181:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3627499999:ℚ)/5000000000),((783903203:ℚ)/1000000000),((12930499997:ℚ)/14480000000),(1:ℚ),((9252071821:ℚ)/10000000000),((1855284257:ℚ)/2000000000),((1946075537:ℚ)/5000000000),((1512322773:ℚ)/5000000000),((-61620043334732521191024933:ℚ)/181000000000000000000000000),((-379805114541264948599280331:ℚ)/739328000000000000000000000)⟩
theorem valid34 : Valid source34 packet34 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf34 :
    CellBound source34 nn0 nn1 Qcell ((343:ℚ)/400) ((181:ℚ)/200) :=
  cell_of_packet source34 nn0 nn1 packet34 valid34
def packet35 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((15:ℚ)/16),(1:ℚ),((3864999999:ℚ)/5000000000),((8790075077:ℚ)/10000000000),((13642999997:ℚ)/16000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-2005151557975315234511657:ℚ)/6250000000000000000000000),((-533641637:ℚ)/1024000000)⟩
theorem valid35 : Valid source34 packet35 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf35 :
    CellBound source34 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source34 nn0 nn1 packet35 valid35
def packet36 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((15:ℚ)/16),(1:ℚ),((4339999999:ℚ)/5000000000),((3148202431:ℚ)/2500000000),((15067999997:ℚ)/22080000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-4854046754542579:ℚ)/22080000000000000),((-533641637:ℚ)/1024000000)⟩
theorem valid36 : Valid source34 packet36 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf36 :
    CellBound source34 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source34 nn0 nn1 packet36 valid36
private theorem node0_2 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source34 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf4 leaf5
private theorem node7_9 :
    CellBound source34 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source34 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf6 node7_9
private theorem node4_9 :
    CellBound source34 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join node4_6 node6_9
private theorem node0_9 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_4 node4_9
private theorem node9_11 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source34 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join node9_11 node11_13
private theorem node13_15 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((4671:ℚ)/6400) :=
  cell_join leaf13 leaf14
private theorem node16_18 :
    CellBound source34 nn0 nn1 Qcell ((9361:ℚ)/12800) ((9399:ℚ)/12800) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source34 nn0 nn1 Qcell ((4671:ℚ)/6400) ((9399:ℚ)/12800) :=
  cell_join leaf15 node16_18
private theorem node13_18 :
    CellBound source34 nn0 nn1 Qcell ((1163:ℚ)/1600) ((9399:ℚ)/12800) :=
  cell_join node13_15 node15_18
private theorem node9_18 :
    CellBound source34 nn0 nn1 Qcell ((143:ℚ)/200) ((9399:ℚ)/12800) :=
  cell_join node9_13 node13_18
private theorem node0_18 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((9399:ℚ)/12800) :=
  cell_join node0_9 node9_18
private theorem node18_20 :
    CellBound source34 nn0 nn1 Qcell ((9399:ℚ)/12800) ((9437:ℚ)/12800) :=
  cell_join leaf18 leaf19
private theorem node20_22 :
    CellBound source34 nn0 nn1 Qcell ((9437:ℚ)/12800) ((379:ℚ)/512) :=
  cell_join leaf20 leaf21
private theorem node18_22 :
    CellBound source34 nn0 nn1 Qcell ((9399:ℚ)/12800) ((379:ℚ)/512) :=
  cell_join node18_20 node20_22
private theorem node22_24 :
    CellBound source34 nn0 nn1 Qcell ((379:ℚ)/512) ((2383:ℚ)/3200) :=
  cell_join leaf22 leaf23
private theorem node25_27 :
    CellBound source34 nn0 nn1 Qcell ((957:ℚ)/1280) ((4823:ℚ)/6400) :=
  cell_join leaf25 leaf26
private theorem node24_27 :
    CellBound source34 nn0 nn1 Qcell ((2383:ℚ)/3200) ((4823:ℚ)/6400) :=
  cell_join leaf24 node25_27
private theorem node22_27 :
    CellBound source34 nn0 nn1 Qcell ((379:ℚ)/512) ((4823:ℚ)/6400) :=
  cell_join node22_24 node24_27
private theorem node18_27 :
    CellBound source34 nn0 nn1 Qcell ((9399:ℚ)/12800) ((4823:ℚ)/6400) :=
  cell_join node18_22 node22_27
private theorem node27_29 :
    CellBound source34 nn0 nn1 Qcell ((4823:ℚ)/6400) ((61:ℚ)/80) :=
  cell_join leaf27 leaf28
private theorem node30_32 :
    CellBound source34 nn0 nn1 Qcell ((2459:ℚ)/3200) ((629:ℚ)/800) :=
  cell_join leaf30 leaf31
private theorem node29_32 :
    CellBound source34 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf29 node30_32
private theorem node27_32 :
    CellBound source34 nn0 nn1 Qcell ((4823:ℚ)/6400) ((629:ℚ)/800) :=
  cell_join node27_29 node29_32
private theorem node32_34 :
    CellBound source34 nn0 nn1 Qcell ((629:ℚ)/800) ((343:ℚ)/400) :=
  cell_join leaf32 leaf33
private theorem node35_37 :
    CellBound source34 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf35 leaf36
private theorem node34_37 :
    CellBound source34 nn0 nn1 Qcell ((343:ℚ)/400) ((69:ℚ)/50) :=
  cell_join leaf34 node35_37
private theorem node32_37 :
    CellBound source34 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node32_34 node34_37
private theorem node27_37 :
    CellBound source34 nn0 nn1 Qcell ((4823:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node27_32 node32_37
private theorem node18_37 :
    CellBound source34 nn0 nn1 Qcell ((9399:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node18_27 node27_37
private theorem node0_37 :
    CellBound source34 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_18 node18_37
theorem bound : CellBound source34 nn0 nn1 Qcell (31/50) (69/50) := node0_37
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29,packet30,packet31,packet32,packet33,packet34,packet35,packet36]
theorem packet_count : packets.length = 37 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source34GroupedC32
#check @N11Formalization.C450Source34GroupedC32.bound
#print axioms N11Formalization.C450Source34GroupedC32.valid0
#print axioms N11Formalization.C450Source34GroupedC32.valid1
#print axioms N11Formalization.C450Source34GroupedC32.valid2
#print axioms N11Formalization.C450Source34GroupedC32.valid3
#print axioms N11Formalization.C450Source34GroupedC32.valid4
#print axioms N11Formalization.C450Source34GroupedC32.valid5
#print axioms N11Formalization.C450Source34GroupedC32.valid6
#print axioms N11Formalization.C450Source34GroupedC32.valid7
#print axioms N11Formalization.C450Source34GroupedC32.valid8
#print axioms N11Formalization.C450Source34GroupedC32.valid9
#print axioms N11Formalization.C450Source34GroupedC32.valid10
#print axioms N11Formalization.C450Source34GroupedC32.valid11
#print axioms N11Formalization.C450Source34GroupedC32.valid12
#print axioms N11Formalization.C450Source34GroupedC32.valid13
#print axioms N11Formalization.C450Source34GroupedC32.valid14
#print axioms N11Formalization.C450Source34GroupedC32.valid15
#print axioms N11Formalization.C450Source34GroupedC32.valid16
#print axioms N11Formalization.C450Source34GroupedC32.valid17
#print axioms N11Formalization.C450Source34GroupedC32.valid18
#print axioms N11Formalization.C450Source34GroupedC32.valid19
#print axioms N11Formalization.C450Source34GroupedC32.valid20
#print axioms N11Formalization.C450Source34GroupedC32.valid21
#print axioms N11Formalization.C450Source34GroupedC32.valid22
#print axioms N11Formalization.C450Source34GroupedC32.valid23
#print axioms N11Formalization.C450Source34GroupedC32.valid24
#print axioms N11Formalization.C450Source34GroupedC32.valid25
#print axioms N11Formalization.C450Source34GroupedC32.valid26
#print axioms N11Formalization.C450Source34GroupedC32.valid27
#print axioms N11Formalization.C450Source34GroupedC32.valid28
#print axioms N11Formalization.C450Source34GroupedC32.valid29
#print axioms N11Formalization.C450Source34GroupedC32.valid30
#print axioms N11Formalization.C450Source34GroupedC32.valid31
#print axioms N11Formalization.C450Source34GroupedC32.valid32
#print axioms N11Formalization.C450Source34GroupedC32.valid33
#print axioms N11Formalization.C450Source34GroupedC32.valid34
#print axioms N11Formalization.C450Source34GroupedC32.valid35
#print axioms N11Formalization.C450Source34GroupedC32.valid36
#print axioms N11Formalization.C450Source34GroupedC32.bound
#print axioms N11Formalization.C450Source34GroupedC32.endpoint_checks
