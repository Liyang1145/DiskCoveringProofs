import N11Formalization.C450Source22Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source22GroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source22Data
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((3388689041:ℚ)/5000000000),((6982246649:ℚ)/10000000000),((-77969206437:ℚ)/99200000000),((-2828689041:ℚ)/4212500000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((146742471:ℚ)/312500000),((1808602170114063834077324300990568520014449525604145278471821:ℚ)/11175916441600000000000000000000000000000000000000000000000000),((1056760398860868099037028737:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid source22 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((1379310947:ℚ)/2000000000),((7041799081:ℚ)/10000000000),((-78743388053:ℚ)/101100000000),((-3465932841:ℚ)/5102500000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((2168210819:ℚ)/5000000000),((1315746494181229817259176590735914641001823999633800814681619:ℚ)/8407551093211740234375000000000000000000000000000000000000000),((8905558332146419304180947:ℚ)/15564800000000000000000000)⟩
theorem valid1 : Valid source22 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source22 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((434758567:ℚ)/625000000),((284053929:ℚ)/400000000),((-3180701077:ℚ)/4082000000),((-1094275701:ℚ)/1609375000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((1036477221:ℚ)/2500000000),((1058908858035446102677254754559258777384756289785206730897:ℚ)/6764952116766675000000000000000000000000000000000000000000),((16541545651231317015563853:ℚ)/28880000000000000000000000)⟩
theorem valid2 : Valid source22 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source22 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source22 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((3507857783:ℚ)/5000000000),((891390199:ℚ)/1250000000),((-9988072587:ℚ)/12875000000),((-8843573349:ℚ)/12934375000),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((1973389423:ℚ)/5000000000),((175925156525769533731652923369696511357401922041919168121061:ℚ)/1142569397117126464843750000000000000000000000000000000000000),((1059038526638612229589189553:ℚ)/1848320000000000000000000000)⟩
theorem valid3 : Valid source22 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source22 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source22 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4139:ℚ)/6400),((2079:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((1761375851:ℚ)/2500000000),((1790223543:ℚ)/2500000000),((-20072906059:ℚ)/25868750000),((-1481375851:ℚ)/2165625000),((4916570841:ℚ)/5000000000),((1969704979:ℚ)/2000000000),((1829340989:ℚ)/10000000000),((480445597:ℚ)/1250000000),((12990378808178124075684989667554570439499704256012196593241:ℚ)/84351363206806755065917968750000000000000000000000000000000),((264899433533187300009002777:ℚ)/462080000000000000000000000)⟩
theorem valid4 : Valid source22 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source22 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((88441129:ℚ)/125000000),((3595332987:ℚ)/5000000000),((-40339328831:ℚ)/51975000000),((-223323387:ℚ)/326328125),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((373765017:ℚ)/1000000000),((26799161058970779418419164189606723679697659314503020431380123:ℚ)/173984191658576916503906250000000000000000000000000000000000000),((662597598228077775693657:ℚ)/1155200000000000000000000)⟩
theorem valid5 : Valid source22 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source22 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source22 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((888134541:ℚ)/1250000000),((722043701:ℚ)/1000000000),((-8106568113:ℚ)/10442500000),((-2244403623:ℚ)/3278125000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3628798023:ℚ)/10000000000),((150815147234427165691033565487766081002815480697487028609311:ℚ)/978936357801348059082031250000000000000000000000000000000000),((198883836753565407316897211:ℚ)/346560000000000000000000000)⟩
theorem valid6 : Valid source22 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source22 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1049:ℚ)/1600),((8411:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((7134861439:ℚ)/10000000000),((7235322243:ℚ)/10000000000),((-81259189159:ℚ)/104900000000),((-18044584317:ℚ)/26284375000),((9795878581:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((1011977397:ℚ)/5000000000),((439591877:ℚ)/1250000000),((38999472431472842631563905964174479484263002028113487897958113993:ℚ)/255194759756792903125000000000000000000000000000000000000000000000),((4243600477798031422853630817:ℚ)/7393280000000000000000000000)⟩
theorem valid7 : Valid source22 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source22 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8411:ℚ)/12800) :=
  cell_of_packet source22 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((8411:ℚ)/12800),((843:ℚ)/1280),((-13:ℚ)/16),((-3:ℚ)/4),((3574876831:ℚ)/5000000000),((7250207289:ℚ)/10000000000),((-81452694757:ℚ)/105137500000),((-3014876831:ℚ)/4390625000),((978862711:ℚ)/1000000000),((4897939293:ℚ)/5000000000),((2059717253:ℚ)/10000000000),((3459402103:ℚ)/10000000000),((438299649461429792315763201795353290076122254415827895887731:ℚ)/2867712434464007019042968750000000000000000000000000000000000),((1061178257655448879550334497:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source22 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source22 nn0 nn1 Qcell ((8411:ℚ)/12800) ((843:ℚ)/1280) :=
  cell_of_packet source22 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((843:ℚ)/1280),((8449:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((3582322833:ℚ)/5000000000),((1816273037:ℚ)/2500000000),((-6803849827:ℚ)/8781250000),((-9066968499:ℚ)/13201562500),((4890720817:ℚ)/5000000000),((1957725423:ℚ)/2000000000),((83782417:ℚ)/400000000),((1700571603:ℚ)/5000000000),((48507185482154289641265065882279820668713422914943136230611:ℚ)/317338462997412681579589843750000000000000000000000000000000),((167598347356231236535191761:ℚ)/291840000000000000000000000)⟩
theorem valid9 : Valid source22 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source22 nn0 nn1 Qcell ((843:ℚ)/1280) ((8449:ℚ)/12800) :=
  cell_of_packet source22 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8449:ℚ)/12800),((2117:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((1794884363:ℚ)/2500000000),((7279976823:ℚ)/10000000000),((-81839698699:ℚ)/105612500000),((-4544653089:ℚ)/6615625000),((9774321709:ℚ)/10000000000),((9781441639:ℚ)/10000000000),((425706267:ℚ)/2000000000),((835477457:ℚ)/2500000000),((12424306925086039890308758361642964290098672052039573809424279:ℚ)/81272135083729168701171875000000000000000000000000000000000000),((265433486582123926492645913:ℚ)/462080000000000000000000000)⟩
theorem valid10 : Valid source22 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source22 nn0 nn1 Qcell ((8449:ℚ)/12800) ((2117:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2117:ℚ)/3200),((8487:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((7194429021:ℚ)/10000000000),((7294861313:ℚ)/10000000000),((-82033197069:ℚ)/105850000000),((-6074429021:ℚ)/8840625000),((9767266893:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((2161672951:ℚ)/10000000000),((328164913:ℚ)/1000000000),((503875153721424216468666477986093485734973843102209233041518163:ℚ)/3295687268017436328125000000000000000000000000000000000000000000),((670744103273595892242364409:ℚ)/1167360000000000000000000000)⟩
theorem valid11 : Valid source22 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source22 nn0 nn1 Qcell ((2117:ℚ)/3200) ((8487:ℚ)/12800) :=
  cell_of_packet source22 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((8487:ℚ)/12800),((4253:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((3604660187:ℚ)/5000000000),((365487281:ℚ)/500000000),((-4111334653:ℚ)/5304375000),((-9133980561:ℚ)/13290625000),((9760276751:ℚ)/10000000000),((4883633449:ℚ)/5000000000),((438804929:ℚ)/2000000000),((3220303367:ℚ)/10000000000),((10487236073739388465857244653150960107825813607577089700937:ℚ)/68586451524568137359619140625000000000000000000000000000000),((1062288851538835597326064313:ℚ)/1848320000000000000000000000)⟩
theorem valid12 : Valid source22 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source22 nn0 nn1 Qcell ((8487:ℚ)/12800) ((4253:ℚ)/6400) :=
  cell_of_packet source22 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((1444842303:ℚ)/2000000000),((7339513691:ℚ)/10000000000),((-82613677983:ℚ)/106325000000),((-1220842303:ℚ)/1780000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((49340769:ℚ)/156250000),((1146721555434351424974342079586042014730544366001630114438729:ℚ)/7438343290235803222656250000000000000000000000000000000000000),((510209526956782766318530979:ℚ)/887193600000000000000000000)⟩
theorem valid13 : Valid source22 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source22 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source22 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((181349829:ℚ)/250000000),((3684640523:ℚ)/5000000000),((-41500326799:ℚ)/53400000000),((-460049487:ℚ)/670468750),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((1514544929:ℚ)/5000000000),((3015513782636045566915033100523959171278952079376454879649239:ℚ)/19557476083761328125000000000000000000000000000000000000000000),((7976176770763273056538571:ℚ)/13862400000000000000000000)⟩
theorem valid14 : Valid source22 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source22 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-13:ℚ)/16),((-3:ℚ)/4),((7283773967:ℚ)/10000000000),((3699523847:ℚ)/5000000000),((-5956258573:ℚ)/7662500000),((-18491321901:ℚ)/26937500000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((361854947:ℚ)/1250000000),((471965479159047615939675328824544912049380723652352179297:ℚ)/3060534743293547630310058593750000000000000000000000000000),((4256172699886529661459423553:ℚ)/7393280000000000000000000000)⟩
theorem valid15 : Valid source22 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source22 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source22 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((1828388487:ℚ)/2500000000),((3729289453:ℚ)/5000000000),((-42080762889:ℚ)/53875000000),((-4645165461:ℚ)/6793750000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2754249019:ℚ)/10000000000),((90457938893086947422050727036332209774435439099630662070693847:ℚ)/577392262041497802734375000000000000000000000000000000000000000),((42052747658955943137616481:ℚ)/72960000000000000000000000)⟩
theorem valid16 : Valid source22 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source22 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source22 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((7373111473:ℚ)/10000000000),((3759053701:ℚ)/5000000000),((-42467698113:ℚ)/54350000000),((-6253111473:ℚ)/9137500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((489926433:ℚ)/2000000000),((10501170883795632175288618331730108445258373817181879682283879:ℚ)/67022933061385058593750000000000000000000000000000000000000000),((4265752826087595268428848833:ℚ)/7393280000000000000000000000)⟩
theorem valid17 : Valid source22 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source22 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source22 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((3716332911:ℚ)/5000000000),((30310533:ℚ)/40000000),((-342836929:ℚ)/438600000),((-9468998733:ℚ)/13825000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1051164331:ℚ)/5000000000),((84604939375476612049395291984169695258616885521516227:ℚ)/539944854739639453125000000000000000000000000000000000),((168558475647936506990046929:ℚ)/291840000000000000000000000)⟩
theorem valid18 : Valid source22 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source22 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source22 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((299688683:ℚ)/400000000),((7815711499:ℚ)/10000000000),((-88804249487:ℚ)/110600000000),((-764666049:ℚ)/1144000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((337231227:ℚ)/2000000000),((1134898968764965198214443215693997569238933283394163754967213:ℚ)/6650344225525000000000000000000000000000000000000000000000000),((6833329671503844485763353:ℚ)/11829248000000000000000000)⟩
theorem valid19 : Valid source22 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source22 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source22 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((3865196347:ℚ)/5000000000),((876768437:ℚ)/1000000000),((-10117989681:ℚ)/11440000000),((-3305196347:ℚ)/5400000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((63172154007977712306353948382867393130470189350363958109:ℚ)/284232920400000000000000000000000000000000000000000000000),((59113643:ℚ)/102400000)⟩
theorem valid20 : Valid source22 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source22 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((8682697567:ℚ)/10000000000),((10670503119:ℚ)/10000000000),((-125916540547:ℚ)/129600000000),((-22688092701:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((350526197409761899419250678331768520605976414158049226103:ℚ)/1275458400000000000000000000000000000000000000000000000000),((59113643:ℚ)/102400000)⟩
theorem valid21 : Valid source22 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source22 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((1323248773:ℚ)/1250000000),((7236904543:ℚ)/5000000000),(-1:ℚ),((-1183248773:ℚ)/2300000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((831148939029121842261281:ℚ)/2645000000000000000000000),((59113643:ℚ)/102400000)⟩
theorem valid22 : Valid source22 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source22 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source22 nn0 nn1 packet22 valid22
private theorem node0_2 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source22 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source22 nn0 nn1 Qcell ((2041:ℚ)/3200) ((2079:ℚ)/3200) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source22 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8411:ℚ)/12800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source22 nn0 nn1 Qcell ((2079:ℚ)/3200) ((8411:ℚ)/12800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source22 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source22 nn0 nn1 Qcell ((8411:ℚ)/12800) ((2117:ℚ)/3200) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source22 nn0 nn1 Qcell ((2079:ℚ)/3200) ((2117:ℚ)/3200) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join node0_5 node5_11
private theorem node12_14 :
    CellBound source22 nn0 nn1 Qcell ((8487:ℚ)/12800) ((267:ℚ)/400) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound source22 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf11 node12_14
private theorem node15_17 :
    CellBound source22 nn0 nn1 Qcell ((4291:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source22 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf14 node15_17
private theorem node11_17 :
    CellBound source22 nn0 nn1 Qcell ((2117:ℚ)/3200) ((1087:ℚ)/1600) :=
  cell_join node11_14 node14_17
private theorem node18_20 :
    CellBound source22 nn0 nn1 Qcell ((2193:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound source22 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf17 node18_20
private theorem node21_23 :
    CellBound source22 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound source22 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf20 node21_23
private theorem node17_23 :
    CellBound source22 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node17_20 node20_23
private theorem node11_23 :
    CellBound source22 nn0 nn1 Qcell ((2117:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node11_17 node17_23
private theorem node0_23 :
    CellBound source22 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_23
theorem bound : CellBound source22 nn0 nn1 Qcell (31/50) (69/50) := node0_23
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22]
theorem packet_count : packets.length = 23 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source22GroupedC04
#check @N11Formalization.C450Source22GroupedC04.bound
#print axioms N11Formalization.C450Source22GroupedC04.valid0
#print axioms N11Formalization.C450Source22GroupedC04.valid1
#print axioms N11Formalization.C450Source22GroupedC04.valid2
#print axioms N11Formalization.C450Source22GroupedC04.valid3
#print axioms N11Formalization.C450Source22GroupedC04.valid4
#print axioms N11Formalization.C450Source22GroupedC04.valid5
#print axioms N11Formalization.C450Source22GroupedC04.valid6
#print axioms N11Formalization.C450Source22GroupedC04.valid7
#print axioms N11Formalization.C450Source22GroupedC04.valid8
#print axioms N11Formalization.C450Source22GroupedC04.valid9
#print axioms N11Formalization.C450Source22GroupedC04.valid10
#print axioms N11Formalization.C450Source22GroupedC04.valid11
#print axioms N11Formalization.C450Source22GroupedC04.valid12
#print axioms N11Formalization.C450Source22GroupedC04.valid13
#print axioms N11Formalization.C450Source22GroupedC04.valid14
#print axioms N11Formalization.C450Source22GroupedC04.valid15
#print axioms N11Formalization.C450Source22GroupedC04.valid16
#print axioms N11Formalization.C450Source22GroupedC04.valid17
#print axioms N11Formalization.C450Source22GroupedC04.valid18
#print axioms N11Formalization.C450Source22GroupedC04.valid19
#print axioms N11Formalization.C450Source22GroupedC04.valid20
#print axioms N11Formalization.C450Source22GroupedC04.valid21
#print axioms N11Formalization.C450Source22GroupedC04.valid22
#print axioms N11Formalization.C450Source22GroupedC04.bound
#print axioms N11Formalization.C450Source22GroupedC04.endpoint_checks
