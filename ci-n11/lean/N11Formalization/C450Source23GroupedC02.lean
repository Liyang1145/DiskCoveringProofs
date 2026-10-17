import N11Formalization.C450Source23Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source23GroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source23Data
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((2003:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((6921648929:ℚ)/10000000000),((7076879751:ℚ)/10000000000),((-18542639253:ℚ)/19840000000),((-41411542503:ℚ)/50075000000),((398569427:ℚ)/400000000),(1:ℚ),((845998389:ℚ)/10000000000),((851431989:ℚ)/2000000000),((52918954051190452956729208980895394196172803:ℚ)/244780564723712000000000000000000000000000000),((305901147503412281427654621:ℚ)/369664000000000000000000000)⟩
theorem valid0 : Valid source23 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((2003:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((2003:ℚ)/3200),((1011:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((6981150843:ℚ)/10000000000),((446020329:ℚ)/625000000),((-1170060987:ℚ)/1251875000),((-41828055901:ℚ)/50550000000),((9929701407:ℚ)/10000000000),((62276473:ℚ)/62500000),((18538009:ℚ)/156250000),((4063428027:ℚ)/10000000000),((93993068224184200847211217555454765646134929674541413:ℚ)/435183820625478267669677734375000000000000000000000000),((1198541744990656687349661:ℚ)/1444000000000000000000000)⟩
theorem valid1 : Valid source23 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source23 nn0 nn1 Qcell ((2003:ℚ)/3200) ((1011:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1011:ℚ)/1600),((4063:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((1408130073:ℚ)/2000000000),((3583023763:ℚ)/5000000000),((-3135023763:ℚ)/3370000000),((-8448910511:ℚ)/10157500000),((4956442379:ℚ)/5000000000),((2482425353:ℚ)/2500000000),((1320924081:ℚ)/10000000000),((1930279493:ℚ)/5000000000),((13036217415615764883461064490321246352050192271339605411611:ℚ)/61699748053579785156250000000000000000000000000000000000000),((76822489780708973856832949:ℚ)/92416000000000000000000000)⟩
theorem valid2 : Valid source23 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source23 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4063:ℚ)/6400) :=
  cell_of_packet source23 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((4063:ℚ)/6400),((2041:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((28281597:ℚ)/40000000),((7195769463:ℚ)/10000000000),((-18899308389:ℚ)/20315000000),((-169811179:ℚ)/204100000),((247409071:ℚ)/250000000),((9912884763:ℚ)/10000000000),((1440948769:ℚ)/10000000000),((3755236637:ℚ)/10000000000),((4011906162525252988276232674224342333860614727456581205901:ℚ)/18994194875695117187500000000000000000000000000000000000000),((307753566784535952661345149:ℚ)/369664000000000000000000000)⟩
theorem valid3 : Valid source23 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source23 nn0 nn1 Qcell ((4063:ℚ)/6400) ((2041:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2041:ℚ)/3200),((4101:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((3550073781:ℚ)/5000000000),((180637277:ℚ)/250000000),((-474711831:ℚ)/510250000),((-21330516467:ℚ)/25631250000),((4940065779:ℚ)/5000000000),((1979272569:ℚ)/2000000000),((774947369:ℚ)/5000000000),((1823512079:ℚ)/5000000000),((252008985982999558315763785032951877646763348434211459:ℚ)/1193500854655090820312500000000000000000000000000000000),((192635943606013185274709:ℚ)/231040000000000000000000)⟩
theorem valid4 : Valid source23 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source23 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_of_packet source23 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4101:ℚ)/6400),((8221:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((1782473827:ℚ)/2500000000),((724035177:ℚ)/1000000000),((-634435177:ℚ)/683500000),((-10717316789:ℚ)/12845312500),((4936061823:ℚ)/5000000000),((9880131563:ℚ)/10000000000),((320187229:ℚ)/2000000000),((3535655661:ℚ)/10000000000),((7043182385408072868542724592624764776785914531005926189721:ℚ)/33719791387831012304687500000000000000000000000000000000000),((3084496070284296633813309:ℚ)/3696640000000000000000000)⟩
theorem valid5 : Valid source23 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source23 nn0 nn1 Qcell ((4101:ℚ)/6400) ((8221:ℚ)/12800) :=
  cell_of_packet source23 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((8221:ℚ)/12800),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((1786192243:ℚ)/2500000000),((3627606191:ℚ)/5000000000),((-9538818573:ℚ)/10276250000),((-10743345701:ℚ)/12875000000),((9864186891:ℚ)/10000000000),((9872123651:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((3478693349:ℚ)/10000000000),((3756904250083256347965650289937642386269194826298062016909:ℚ)/17988645325095669555664062500000000000000000000000000000000),((77170447036308314857538701:ℚ)/92416000000000000000000000)⟩
theorem valid6 : Valid source23 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source23 nn0 nn1 Qcell ((8221:ℚ)/12800) ((103:ℚ)/160) :=
  cell_of_packet source23 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((103:ℚ)/160),((8259:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7159642497:ℚ)/10000000000),((7270072917:ℚ)/10000000000),((-19122218751:ℚ)/20600000000),((-43077497479:ℚ)/51618750000),((9856320801:ℚ)/10000000000),((616511681:ℚ)/625000000),((1697201141:ℚ)/10000000000),((3420822367:ℚ)/10000000000),((84444959507591912653984052744147891154010400812346479625247:ℚ)/404384168337060546875000000000000000000000000000000000000000),((308914053134324764874688069:ℚ)/369664000000000000000000000)⟩
theorem valid7 : Valid source23 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source23 nn0 nn1 Qcell ((103:ℚ)/160) ((8259:ℚ)/12800) :=
  cell_of_packet source23 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((8259:ℚ)/12800),((4139:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((1434903177:ℚ)/2000000000),((3642466687:ℚ)/5000000000),((-3194466687:ℚ)/3441250000),((-8636322239:ℚ)/10347500000),((984852489:ℚ)/1000000000),((4928160403:ℚ)/5000000000),((1742751127:ℚ)/10000000000),((84049893:ℚ)/250000000),((56941298995567266637009028323293221312213637284709395268351:ℚ)/272709056412176068878173828125000000000000000000000000000000),((214090306079462249361509:ℚ)/256000000000000000000000)⟩
theorem valid8 : Valid source23 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source23 nn0 nn1 Qcell ((8259:ℚ)/12800) ((4139:ℚ)/6400) :=
  cell_of_packet source23 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4139:ℚ)/6400),((8297:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7189389137:ℚ)/10000000000),((3649896877:ℚ)/5000000000),((-9605690631:ℚ)/10347500000),((-43285723959:ℚ)/51856250000),((9840798677:ℚ)/10000000000),((1969704979:ℚ)/2000000000),((1786759881:ℚ)/10000000000),((3302162263:ℚ)/10000000000),((995187319614065693644921446247115526250240341836908976049087:ℚ)/4766817255037424190429687500000000000000000000000000000000000),((77344708673198443254061109:ℚ)/92416000000000000000000000)⟩
theorem valid9 : Valid source23 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source23 nn0 nn1 Qcell ((4139:ℚ)/6400) ((8297:ℚ)/12800) :=
  cell_of_packet source23 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8297:ℚ)/12800),((2079:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((7204262253:ℚ)/10000000000),((3657327029:ℚ)/5000000000),((-9627981087:ℚ)/10371250000),((-43389835771:ℚ)/51975000000),((4916570841:ℚ)/5000000000),((4920399341:ℚ)/5000000000),((1829340989:ℚ)/10000000000),((810316543:ℚ)/2500000000),((231144282816838518073076137453752000238057538679315427339:ℚ)/1107281410949320220947265625000000000000000000000000000000),((77402837822700717486880261:ℚ)/92416000000000000000000000)⟩
theorem valid10 : Valid source23 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source23 nn0 nn1 Qcell ((8297:ℚ)/12800) ((2079:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2079:ℚ)/3200),((1667:ℚ)/2560),((-15:ℚ)/16),((-7:ℚ)/8),((3609567617:ℚ)/5000000000),((7329514287:ℚ)/10000000000),((-6433514287:ℚ)/6930000000),((-21746973319:ℚ)/26046875000),((4912776717:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((935297099:ℚ)/5000000000),((1589623157:ℚ)/5000000000),((39567559410337160355970369530382406601395443533225431153:ℚ)/189567991954687500000000000000000000000000000000000000000),((309843951787120935117355149:ℚ)/369664000000000000000000000)⟩
theorem valid11 : Valid source23 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source23 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1667:ℚ)/2560) :=
  cell_of_packet source23 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1667:ℚ)/2560),((4177:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((3617004041:ℚ)/5000000000),((7344374441:ℚ)/10000000000),((-19345123323:ℚ)/20837500000),((-21799028287:ℚ)/26106250000),((4909016731:ℚ)/5000000000),((9825553439:ℚ)/10000000000),((382121547:ℚ)/2000000000),((311603551:ℚ)/1000000000),((51476553400574285031438988917753787293321392355278909904469059:ℚ)/246652666603640219116210937500000000000000000000000000000000000),((310076636180459892049152701:ℚ)/369664000000000000000000000)⟩
theorem valid12 : Valid source23 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source23 nn0 nn1 Qcell ((1667:ℚ)/2560) ((4177:ℚ)/6400) :=
  cell_of_packet source23 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4177:ℚ)/6400),((8373:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7248880797:ℚ)/10000000000),((183980863:ℚ)/250000000),((-484742589:ℚ)/522125000),((-43702165579:ℚ)/52331250000),((4905290651:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((194946007:ℚ)/1000000000),((1525779841:ℚ)/5000000000),((361523459951011585649574389686725991952685398105813572413:ℚ)/1732459791152126077270507812500000000000000000000000000000),((193943377793457294229549:ℚ)/231040000000000000000000)⟩
theorem valid13 : Valid source23 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source23 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8373:ℚ)/12800) :=
  cell_of_packet source23 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((8373:ℚ)/12800),((1049:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((363187669:ℚ)/500000000),((294963781:ℚ)/400000000),((-259123781:ℚ)/279100000),((-2190313683:ℚ)/2622500000),((4901598247:ℚ)/5000000000),((9810581307:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3732171:ℚ)/12500000),((7799626135844885041367836368844996320491862737271631877:ℚ)/37380965279637610937500000000000000000000000000000000000),((496867610669953273023781:ℚ)/591462400000000000000000)⟩
theorem valid14 : Valid source23 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source23 nn0 nn1 Qcell ((8373:ℚ)/12800) ((1049:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1049:ℚ)/1600),((8411:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((909828229:ℚ)/1250000000),((923619307:ℚ)/1250000000),((-2434857921:ℚ)/2622500000),((-5488797603:ℚ)/6571093750),((9795878581:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((1011977397:ℚ)/5000000000),((729618911:ℚ)/2500000000),((2461209480177746425123593692942482688528731422253947392697:ℚ)/11797095033135766601562500000000000000000000000000000000000),((4855862387136818495322629:ℚ)/5776000000000000000000000)⟩
theorem valid15 : Valid source23 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source23 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8411:ℚ)/12800) :=
  cell_of_packet source23 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((8411:ℚ)/12800),((843:ℚ)/1280),((-15:ℚ)/16),((-7:ℚ)/8),((3646749077:ℚ)/5000000000),((1480762863:ℚ)/2000000000),((-3904688589:ℚ)/4205500000),((-22007243539:ℚ)/26343750000),((978862711:ℚ)/1000000000),((4897939293:ℚ)/5000000000),((2059717253:ℚ)/10000000000),((712418573:ℚ)/2500000000),((478574534452901122566527459173384718596478489674453463373:ℚ)/2294169947571205615234375000000000000000000000000000000000),((12440328512949425304801549:ℚ)/14786560000000000000000000)⟩
theorem valid16 : Valid source23 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source23 nn0 nn1 Qcell ((8411:ℚ)/12800) ((843:ℚ)/1280) :=
  cell_of_packet source23 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((7308370347:ℚ)/10000000000),((3716766907:ℚ)/5000000000),((-3268766907:ℚ)/3512500000),((-44118592429:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((69480457:ℚ)/250000000),((2557720699498720741163445320255489252677762547992813141899:ℚ)/12138659580230590820312500000000000000000000000000000000000),((77868626170623142361877029:ℚ)/92416000000000000000000000)⟩
theorem valid17 : Valid source23 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source23 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source23 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7338114349:ℚ)/10000000000),((7463253027:ℚ)/10000000000),((-19701759081:ℚ)/21170000000),((-44326800443:ℚ)/53162500000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((658201877:ℚ)/2500000000),((14121199934444801078646482756753890340799231920004371169971793:ℚ)/67036815295923639453125000000000000000000000000000000000000000),((311941132313531132399522709:ℚ)/369664000000000000000000000)⟩
theorem valid18 : Valid source23 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source23 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source23 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((1473571569:ℚ)/2000000000),((3746485979:ℚ)/5000000000),((-9895457937:ℚ)/10632500000),((-8907000983:ℚ)/10680000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((2477974953:ℚ)/10000000000),((195804054390602862490497112288425515535044834147163603369:ℚ)/929792911279475402832031250000000000000000000000000000000),((78102023942475385189093861:ℚ)/92416000000000000000000000)⟩
theorem valid19 : Valid source23 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source23 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source23 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-15:ℚ)/16),((-7:ℚ)/8),((7397600841:ℚ)/10000000000),((7552408987:ℚ)/10000000000),((-6656408987:ℚ)/7120000000),((-44743205887:ℚ)/53875000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1156514611:ℚ)/5000000000),((22492545933040474455617650447976683219039250266068499987811:ℚ)/104764597127200000000000000000000000000000000000000000000000),((313343030324531302649838949:ℚ)/369664000000000000000000000)⟩
theorem valid20 : Valid source23 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source23 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((7457085361:ℚ)/10000000000),((7611844929:ℚ)/10000000000),((-20147534787:ℚ)/21550000000),((-45159597527:ℚ)/54350000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((388471779:ℚ)/2000000000),((3963769950014842785045876814738932669766940166174220820527971:ℚ)/18476552385327929687500000000000000000000000000000000000000000),((108757829:ℚ)/128000000)⟩
theorem valid21 : Valid source23 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source23 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source23 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-15:ℚ)/16),((-7:ℚ)/8),((3758283981:ℚ)/5000000000),((7730713669:ℚ)/10000000000),((-20504141007:ℚ)/21740000000),((-22787987867:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1483107851:ℚ)/10000000000),((9751862191604334051368231798621900613958628715284614331553:ℚ)/43835996663719531250000000000000000000000000000000000000000),((108757829:ℚ)/128000000)⟩
theorem valid22 : Valid source23 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source23 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source23 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((1908881901:ℚ)/2500000000),((79684393:ℚ)/100000000),((-212173179:ℚ)/221200000),((-11602173307:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((69470516869693314472186534628801137915035650705541:ℚ)/292322823100000000000000000000000000000000000000000),((108757829:ℚ)/128000000)⟩
theorem valid23 : Valid source23 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source23 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((984178243:ℚ)/1250000000),((1114901169:ℚ)/1250000000),(-1:ℚ),((-667694189:ℚ)/900000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1366441139525772258047608248329:ℚ)/4687500000000000000000000000000),((108757829:ℚ)/128000000)⟩
theorem valid24 : Valid source23 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source23 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source23 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((8824785223:ℚ)/10000000000),((10820310153:ℚ)/10000000000),(-1:ℚ),((-54733496561:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((77875226988678169012982395483330567:ℚ)/250000000000000000000000000000000000),((108757829:ℚ)/128000000)⟩
theorem valid25 : Valid source23 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source23 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((5363363913:ℚ)/5000000000),((14621601939:ℚ)/10000000000),(-1:ℚ),((-34023547391:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1826219329026715186211333:ℚ)/5290000000000000000000000),((108757829:ℚ)/128000000)⟩
theorem valid26 : Valid source23 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source23 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source23 nn0 nn1 packet26 valid26
private theorem node1_3 :
    CellBound source23 nn0 nn1 Qcell ((2003:ℚ)/3200) ((4063:ℚ)/6400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((4063:ℚ)/6400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source23 nn0 nn1 Qcell ((2041:ℚ)/3200) ((8221:ℚ)/12800) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source23 nn0 nn1 Qcell ((4063:ℚ)/6400) ((8221:ℚ)/12800) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((8221:ℚ)/12800) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source23 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source23 nn0 nn1 Qcell ((8221:ℚ)/12800) ((4139:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source23 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source23 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source23 nn0 nn1 Qcell ((4139:ℚ)/6400) ((4177:ℚ)/6400) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source23 nn0 nn1 Qcell ((8221:ℚ)/12800) ((4177:ℚ)/6400) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((4177:ℚ)/6400) :=
  cell_join node0_6 node6_13
private theorem node14_16 :
    CellBound source23 nn0 nn1 Qcell ((8373:ℚ)/12800) ((8411:ℚ)/12800) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source23 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8411:ℚ)/12800) :=
  cell_join leaf13 node14_16
private theorem node16_18 :
    CellBound source23 nn0 nn1 Qcell ((8411:ℚ)/12800) ((2117:ℚ)/3200) :=
  cell_join leaf16 leaf17
private theorem node18_20 :
    CellBound source23 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf18 leaf19
private theorem node16_20 :
    CellBound source23 nn0 nn1 Qcell ((8411:ℚ)/12800) ((267:ℚ)/400) :=
  cell_join node16_18 node18_20
private theorem node13_20 :
    CellBound source23 nn0 nn1 Qcell ((4177:ℚ)/6400) ((267:ℚ)/400) :=
  cell_join node13_16 node16_20
private theorem node21_23 :
    CellBound source23 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf20 node21_23
private theorem node23_25 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf23 leaf24
private theorem node25_27 :
    CellBound source23 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf25 leaf26
private theorem node23_27 :
    CellBound source23 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node23_25 node25_27
private theorem node20_27 :
    CellBound source23 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node20_23 node23_27
private theorem node13_27 :
    CellBound source23 nn0 nn1 Qcell ((4177:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node13_20 node20_27
private theorem node0_27 :
    CellBound source23 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_13 node13_27
theorem bound : CellBound source23 nn0 nn1 Qcell (31/50) (69/50) := node0_27
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26]
theorem packet_count : packets.length = 27 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source23GroupedC02
#check @N11Formalization.C450Source23GroupedC02.bound
#print axioms N11Formalization.C450Source23GroupedC02.valid0
#print axioms N11Formalization.C450Source23GroupedC02.valid1
#print axioms N11Formalization.C450Source23GroupedC02.valid2
#print axioms N11Formalization.C450Source23GroupedC02.valid3
#print axioms N11Formalization.C450Source23GroupedC02.valid4
#print axioms N11Formalization.C450Source23GroupedC02.valid5
#print axioms N11Formalization.C450Source23GroupedC02.valid6
#print axioms N11Formalization.C450Source23GroupedC02.valid7
#print axioms N11Formalization.C450Source23GroupedC02.valid8
#print axioms N11Formalization.C450Source23GroupedC02.valid9
#print axioms N11Formalization.C450Source23GroupedC02.valid10
#print axioms N11Formalization.C450Source23GroupedC02.valid11
#print axioms N11Formalization.C450Source23GroupedC02.valid12
#print axioms N11Formalization.C450Source23GroupedC02.valid13
#print axioms N11Formalization.C450Source23GroupedC02.valid14
#print axioms N11Formalization.C450Source23GroupedC02.valid15
#print axioms N11Formalization.C450Source23GroupedC02.valid16
#print axioms N11Formalization.C450Source23GroupedC02.valid17
#print axioms N11Formalization.C450Source23GroupedC02.valid18
#print axioms N11Formalization.C450Source23GroupedC02.valid19
#print axioms N11Formalization.C450Source23GroupedC02.valid20
#print axioms N11Formalization.C450Source23GroupedC02.valid21
#print axioms N11Formalization.C450Source23GroupedC02.valid22
#print axioms N11Formalization.C450Source23GroupedC02.valid23
#print axioms N11Formalization.C450Source23GroupedC02.valid24
#print axioms N11Formalization.C450Source23GroupedC02.valid25
#print axioms N11Formalization.C450Source23GroupedC02.valid26
#print axioms N11Formalization.C450Source23GroupedC02.bound
#print axioms N11Formalization.C450Source23GroupedC02.endpoint_checks
