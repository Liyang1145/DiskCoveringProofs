import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC32
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((15:ℚ)/16),(1:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((15:ℚ)/16),(1:ℚ),((2539999999:ℚ)/5000000000),((5414020251:ℚ)/10000000000),((9347999997:ℚ)/10300000000),(1:ℚ),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((524195269:ℚ)/625000000),((-210177976909742123722028306811654799:ℚ)/530450000000000000000000000000000000),((-334444713609573947643640659:ℚ)/739328000000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((15:ℚ)/16),(1:ℚ),((2658749999:ℚ)/5000000000),((1412977887:ℚ)/2500000000),((3234749999:ℚ)/3560000000),(1:ℚ),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7958593453:ℚ)/10000000000),((-12593503344450985258332202173099601:ℚ)/31684000000000000000000000000000000),((-328641433292698980551140659:ℚ)/739328000000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((2777499999:ℚ)/5000000000),((5770846913:ℚ)/10000000000),((10060499997:ℚ)/10870000000),(1:ℚ),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1877814369:ℚ)/2500000000),((-724747221111413681903832398048135273:ℚ)/1772353500000000000000000000000000000),((-326966602375586192938640659:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((15:ℚ)/16),(1:ℚ),((2836874999:ℚ)/5000000000),((1177955179:ℚ)/2000000000),((10238624997:ℚ)/11060000000),(1:ℚ),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((113740747:ℚ)/156250000),((-13408512139231919834121730681150843:ℚ)/32765250000000000000000000000000000),((-324155369469670905077390659:ℚ)/739328000000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((2896249999:ℚ)/5000000000),((1189847619:ℚ)/2000000000),((10416749997:ℚ)/11155000000),(1:ℚ),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((7041361799:ℚ)/10000000000),((-64496875667184014657928628056765127:ℚ)/155542531250000000000000000000000000),((-323382313278402609446140659:ℚ)/739328000000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((15:ℚ)/16),(1:ℚ),((2925937499:ℚ)/5000000000),((3004349409:ℚ)/5000000000),((3501937499:ℚ)/3750000000),(1:ℚ),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1729952383:ℚ)/2500000000),((-607539921732267497543822265529153:ℚ)/1464843750000000000000000000000000),((-321999285148091157316765659:ℚ)/739328000000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((2955624999:ℚ)/5000000000),((6068158103:ℚ)/10000000000),((10594874997:ℚ)/11345000000),(1:ℚ),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((6796447439:ℚ)/10000000000),((-13348207910336896258641436279634323:ℚ)/32177256250000000000000000000000000),((-320622723055912608444890659:ℚ)/739328000000000000000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((15:ℚ)/16),(1:ℚ),((2985312499:ℚ)/5000000000),((1225523197:ℚ)/2000000000),((10683937497:ℚ)/11440000000),(1:ℚ),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((6671172527:ℚ)/10000000000),((-271508232763407881833989449254925009:ℚ)/654368000000000000000000000000000000),((-319252625817377900430515659:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3014999999:ℚ)/5000000000),((2474829:ℚ)/4000000),((3590999999:ℚ)/3845000000),(1:ℚ),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1635968081:ℚ)/2500000000),((-143796595585987813193646927938231:ℚ)/346500585937500000000000000000000),((-317888992214155426233640659:ℚ)/739328000000000000000000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3044687499:ℚ)/5000000000),((6246527679:ℚ)/10000000000),((10862062497:ℚ)/11630000000),(1:ℚ),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((6414423613:ℚ)/10000000000),((-280707843779657720368292649722831057:ℚ)/676284500000000000000000000000000000),((-316531821197126302014265659:ℚ)/739328000000000000000000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((4671:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3074374999:ℚ)/5000000000),((6276254779:ℚ)/10000000000),((3650374999:ℚ)/3892500000),(1:ℚ),((148605427:ℚ)/156250000),((4759921809:ℚ)/5000000000),((98156347:ℚ)/312500000),((6282690929:ℚ)/10000000000),((-3954667914278477458061083193873461:ℚ)/9469722656250000000000000000000000),((-316187141393269835292390659:ℚ)/739328000000000000000000000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((4671:ℚ)/6400) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4671:ℚ)/6400),((469:ℚ)/640),((15:ℚ)/16),(1:ℚ),((3089218749:ℚ)/5000000000),((6305981557:ℚ)/10000000000),((10995656247:ℚ)/11725000000),(1:ℚ),((9501845013:ℚ)/10000000000),((9510747333:ℚ)/10000000000),((792422551:ℚ)/2500000000),((6215921983:ℚ)/10000000000),((-861222250622658392979865823904291971:ℚ)/2062134375000000000000000000000000000),((-315514198548964745613015659:ℚ)/739328000000000000000000000)⟩
theorem valid11 : Valid source29 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source29 nn0 nn1 Qcell ((4671:ℚ)/6400) ((469:ℚ)/640) :=
  cell_of_packet source29 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3104062499:ℚ)/5000000000),((1273086833:ℚ)/2000000000),((3680062499:ℚ)/3940000000),(1:ℚ),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3074262389:ℚ)/5000000000),((-16114223557729574110443365051522491:ℚ)/38809000000000000000000000000000000),((-313836862319062032468015659:ℚ)/739328000000000000000000000)⟩
theorem valid12 : Valid source29 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source29 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3133749999:ℚ)/5000000000),((1606221383:ℚ)/2500000000),((11129249997:ℚ)/11915000000),(1:ℚ),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1202351903:ℚ)/2000000000),((-884357426143607031610389414006773321:ℚ)/2129508375000000000000000000000000000),((-312499072427474208741140659:ℚ)/739328000000000000000000000)⟩
theorem valid13 : Valid source29 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3163437499:ℚ)/5000000000),((6484335689:ℚ)/10000000000),((11218312497:ℚ)/12010000000),(1:ℚ),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2936105393:ℚ)/5000000000),((-149776356128505595871007932687581679:ℚ)/360600250000000000000000000000000000),((-311167740857919110351765659:ℚ)/739328000000000000000000000)⟩
theorem valid14 : Valid source29 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source29 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3193124999:ℚ)/5000000000),((817973083:ℚ)/1250000000),((3769124999:ℚ)/4035000000),(1:ℚ),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((2864836211:ℚ)/5000000000),((-5636235667855262687765864988266677:ℚ)/13567687500000000000000000000000000),((-309842866662805487379890659:ℚ)/739328000000000000000000000)⟩
theorem valid15 : Valid source29 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source29 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((15:ℚ)/16),(1:ℚ),((3222812499:ℚ)/5000000000),((1320646497:ℚ)/2000000000),((11396437497:ℚ)/12200000000),(1:ℚ),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((697989081:ℚ)/1250000000),((-309197841157664676928282295344631789:ℚ)/744200000000000000000000000000000000),((-308524448894542089905515659:ℚ)/739328000000000000000000000)⟩
theorem valid16 : Valid source29 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source29 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source29 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3252499999:ℚ)/5000000000),((6722124771:ℚ)/10000000000),((3828499999:ℚ)/4130000000),(1:ℚ),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1358667347:ℚ)/2500000000),((-35046206281044006103424297274513063:ℚ)/85284500000000000000000000000000000),((-305200696538468985768640659:ℚ)/739328000000000000000000000)⟩
theorem valid17 : Valid source29 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3311874999:ℚ)/5000000000),((427563297:ℚ)/625000000),((11663624997:ℚ)/12580000000),(1:ℚ),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((5124495983:ℚ)/10000000000),((-162656060347175748655379209073332627:ℚ)/395641000000000000000000000000000000),((-302596207132445232547390659:ℚ)/739328000000000000000000000)⟩
theorem valid18 : Valid source29 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source29 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((15:ℚ)/16),(1:ℚ),((3371249999:ℚ)/5000000000),((1415755311:ℚ)/2000000000),((3947249999:ℚ)/4320000000),(1:ℚ),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((1199046113:ℚ)/2500000000),((-37570993361193935578962658609439459:ℚ)/93312000000000000000000000000000000),((-295994326903984628996140659:ℚ)/739328000000000000000000000)⟩
theorem valid19 : Valid source29 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source29 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3489999999:ℚ)/5000000000),((8029693113:ℚ)/10000000000),((12197999997:ℚ)/14480000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((1016814367:ℚ)/2500000000),((-1127250318565623430146351113106915707:ℚ)/3145056000000000000000000000000000000),((-281321111446488200183640659:ℚ)/739328000000000000000000000)⟩
theorem valid20 : Valid source29 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((15:ℚ)/16),(1:ℚ),((3964999999:ℚ)/5000000000),((224510883:ℚ)/250000000),((13622999997:ℚ)/16000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-466338811936700614441503218957899129:ℚ)/1280000000000000000000000000000000000),((-401036893:ℚ)/1024000000)⟩
theorem valid21 : Valid source29 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source29 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((15:ℚ)/16),(1:ℚ),((4439999999:ℚ)/5000000000),((6391190763:ℚ)/5000000000),((5015999999:ℚ)/7360000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-6977926427850430288059621:ℚ)/27084800000000000000000000),((-401036893:ℚ)/1024000000)⟩
theorem valid22 : Valid source29 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet22 valid22
private theorem node0_2 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((2231:ℚ)/3200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source29 nn0 nn1 Qcell ((2231:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source29 nn0 nn1 Qcell ((2307:ℚ)/3200) ((4671:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((4671:ℚ)/6400) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source29 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4671:ℚ)/6400) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((4671:ℚ)/6400) :=
  cell_join node0_5 node5_11
private theorem node12_14 :
    CellBound source29 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source29 nn0 nn1 Qcell ((4671:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_join leaf11 node12_14
private theorem node15_17 :
    CellBound source29 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source29 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf14 node15_17
private theorem node11_17 :
    CellBound source29 nn0 nn1 Qcell ((4671:ℚ)/6400) ((61:ℚ)/80) :=
  cell_join node11_14 node14_17
private theorem node18_20 :
    CellBound source29 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf17 node18_20
private theorem node21_23 :
    CellBound source29 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf20 node21_23
private theorem node17_23 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node17_20 node20_23
private theorem node11_23 :
    CellBound source29 nn0 nn1 Qcell ((4671:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node11_17 node17_23
private theorem node0_23 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_23
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_23
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22]
theorem packet_count : packets.length = 23 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC32
#check @N11Formalization.C450Source29GroupedC32.bound
#print axioms N11Formalization.C450Source29GroupedC32.valid0
#print axioms N11Formalization.C450Source29GroupedC32.valid1
#print axioms N11Formalization.C450Source29GroupedC32.valid2
#print axioms N11Formalization.C450Source29GroupedC32.valid3
#print axioms N11Formalization.C450Source29GroupedC32.valid4
#print axioms N11Formalization.C450Source29GroupedC32.valid5
#print axioms N11Formalization.C450Source29GroupedC32.valid6
#print axioms N11Formalization.C450Source29GroupedC32.valid7
#print axioms N11Formalization.C450Source29GroupedC32.valid8
#print axioms N11Formalization.C450Source29GroupedC32.valid9
#print axioms N11Formalization.C450Source29GroupedC32.valid10
#print axioms N11Formalization.C450Source29GroupedC32.valid11
#print axioms N11Formalization.C450Source29GroupedC32.valid12
#print axioms N11Formalization.C450Source29GroupedC32.valid13
#print axioms N11Formalization.C450Source29GroupedC32.valid14
#print axioms N11Formalization.C450Source29GroupedC32.valid15
#print axioms N11Formalization.C450Source29GroupedC32.valid16
#print axioms N11Formalization.C450Source29GroupedC32.valid17
#print axioms N11Formalization.C450Source29GroupedC32.valid18
#print axioms N11Formalization.C450Source29GroupedC32.valid19
#print axioms N11Formalization.C450Source29GroupedC32.valid20
#print axioms N11Formalization.C450Source29GroupedC32.valid21
#print axioms N11Formalization.C450Source29GroupedC32.valid22
#print axioms N11Formalization.C450Source29GroupedC32.bound
#print axioms N11Formalization.C450Source29GroupedC32.endpoint_checks
