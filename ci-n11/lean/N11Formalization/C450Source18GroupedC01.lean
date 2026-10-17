import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC01
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨(-1:ℚ),((-15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((3397999353:ℚ)/5000000000),((3499375001:ℚ)/5000000000),(-1:ℚ),((-9105998059:ℚ)/10110000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4641322321:ℚ)/10000000000),((14116054476847134590755475172861701:ℚ)/170353500000000000000000000000000000),((126025297840962751250151:ℚ)/180500000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((6914823951:ℚ)/10000000000),((3529062501:ℚ)/5000000000),(-1:ℚ),((-18568471853:ℚ)/20410000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((2139426701:ℚ)/5000000000),((24827018853995346220152603937879:ℚ)/308112500000000000000000000000000),((126325374906889685625151:ℚ)/180500000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),(-1:ℚ),((-15:ℚ)/16),((3487117761:ℚ)/5000000000),((7117500003:ℚ)/10000000000),(-1:ℚ),((-9373353283:ℚ)/10300000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((510798473:ℚ)/1250000000),((128005424312859472857001807609766273:ℚ)/1591350000000000000000000000000000000),((506502872579477845001359:ℚ)/722000000000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7033646417:ℚ)/10000000000),((7147187503:ℚ)/10000000000),(-1:ℚ),((-18924939251:ℚ)/20695000000),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((3884960669:ℚ)/10000000000),((16989042567421740094193108957425801:ℚ)/214141512500000000000000000000000000),((507103958295813335626359:ℚ)/722000000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4139:ℚ)/6400),((2079:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((7063351617:ℚ)/10000000000),((3588437501:ℚ)/5000000000),(-1:ℚ),((-1728550441:ℚ)/1890000000),((4916570841:ℚ)/5000000000),((1969704979:ℚ)/2000000000),((1829340989:ℚ)/10000000000),((378044023:ℚ)/1000000000),((11237434651569824194939302988703:ℚ)/141750000000000000000000000000000),((126926327539720116875151:ℚ)/180500000000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2079:ℚ)/3200),((1667:ℚ)/2560),(-1:ℚ),((-15:ℚ)/16),((443316041:ℚ)/625000000),((224741211:ℚ)/312500000),(-1:ℚ),((-1193948123:ℚ)/1302343750),((4912776717:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((935297099:ℚ)/5000000000),((918273527:ℚ)/2500000000),((42733338857526124394394764733832211:ℚ)/542751757812500000000000000000000000),((496099693274572162171:ℚ)/705078125000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1667:ℚ)/2560) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1667:ℚ)/2560),((4177:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((1421581823:ℚ)/2000000000),((3603281251:ℚ)/5000000000),(-1:ℚ),((-3829545469:ℚ)/4177000000),((4909016731:ℚ)/5000000000),((9825553439:ℚ)/10000000000),((382121547:ℚ)/2000000000),((904570733:ℚ)/2500000000),((3433090828214309731524628709318419:ℚ)/43618322500000000000000000000000000),((127076732052297841875151:ℚ)/180500000000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((1667:ℚ)/2560) ((4177:ℚ)/6400) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4177:ℚ)/6400),((8373:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((3561380767:ℚ)/5000000000),((1805351563:ℚ)/2500000000),(-1:ℚ),((-9596142301:ℚ)/10466250000),((4905290651:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((194946007:ℚ)/1000000000),((4453333:ℚ)/12500000),((43094377802754088702618177527375593:ℚ)/547711945312500000000000000000000000),((31787989815435555488319:ℚ)/45125000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8373:ℚ)/12800) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((8373:ℚ)/12800),((1049:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((3568806957:ℚ)/5000000000),((3618125001:ℚ)/5000000000),(-1:ℚ),((-9618420871:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((9810581307:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3506206121:ℚ)/10000000000),((64913349209048516239715690051890429:ℚ)/825300750000000000000000000000000000),((127227203106623613750151:ℚ)/180500000000000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((8373:ℚ)/12800) ((1049:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1049:ℚ)/1600),((8411:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((447029141:ℚ)/625000000),((906386719:ℚ)/1250000000),(-1:ℚ),((-1205087423:ℚ)/1314218750),((9795878581:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((1011977397:ℚ)/5000000000),((344886059:ℚ)/1000000000),((43457200297167054401323815767704899:ℚ)/552694695312500000000000000000000000),((7956403974183876079111:ℚ)/11281250000000000000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8411:ℚ)/12800) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8411:ℚ)/12800),((16841:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((3583659279:ℚ)/5000000000),((7258515627:ℚ)/10000000000),(-1:ℚ),((-9662977837:ℚ)/10525625000),((9792244569:ℚ)/10000000000),((4897939293:ℚ)/5000000000),((2041954043:ℚ)/10000000000),((678116967:ℚ)/2000000000),((32556259538421274917615955416836243:ℚ)/415457931152343750000000000000000000),((509360400261560393672479:ℚ)/722000000000000000000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell ((8411:ℚ)/12800) ((16841:ℚ)/25600) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((16841:ℚ)/25600),((843:ℚ)/1280),(-1:ℚ),((-15:ℚ)/16),((3587372347:ℚ)/5000000000),((3632968751:ℚ)/5000000000),(-1:ℚ),((-9674117041:ℚ)/10537500000),((978862711:ℚ)/1000000000),((4896122287:ℚ)/5000000000),((2059717253:ℚ)/10000000000),((3361083013:ℚ)/10000000000),((4349937593237731261081190716099319:ℚ)/55519453125000000000000000000000000),((127377740702697432500151:ℚ)/180500000000000000000000)⟩
theorem valid11 : Valid source18 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source18 nn0 nn1 Qcell ((16841:ℚ)/25600) ((843:ℚ)/1280) :=
  cell_of_packet source18 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((843:ℚ)/1280),((16879:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((7182170821:ℚ)/10000000000),((7273359377:ℚ)/10000000000),(-1:ℚ),((-19370512463:ℚ)/21098750000),((9785026151:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((2077250707:ℚ)/10000000000),((3331329969:ℚ)/10000000000),((261543102660449910245386928885876119:ℚ)/3338679386718750000000000000000000000),((509661541995456078047479:ℚ)/722000000000000000000000)⟩
theorem valid12 : Valid source18 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source18 nn0 nn1 Qcell ((843:ℚ)/1280) ((16879:ℚ)/25600) :=
  cell_of_packet source18 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((16879:ℚ)/25600),((8449:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7189596939:ℚ)/10000000000),((1820195313:ℚ)/2500000000),(-1:ℚ),((-1140752401:ℚ)/1242500000),((4890720817:ℚ)/5000000000),((2446256539:ℚ)/2500000000),((83782417:ℚ)/400000000),((3301318903:ℚ)/10000000000),((302295983348670957838218549114953:ℚ)/3859515625000000000000000000000000),((31863258613472464863319:ℚ)/45125000000000000000000)⟩
theorem valid13 : Valid source18 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source18 nn0 nn1 Qcell ((16879:ℚ)/25600) ((8449:ℚ)/12800) :=
  cell_of_packet source18 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((8449:ℚ)/12800),((16917:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((7197023047:ℚ)/10000000000),((7288203127:ℚ)/10000000000),(-1:ℚ),((-19415069141:ℚ)/21146250000),((1955574701:ℚ)/2000000000),((9781441639:ℚ)/10000000000),((105582607:ℚ)/500000000),((327104271:ℚ)/1000000000),((8754626676762422815973179224359551:ℚ)/111790972265625000000000000000000000),((509962750271099809297479:ℚ)/722000000000000000000000)⟩
theorem valid14 : Valid source18 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source18 nn0 nn1 Qcell ((8449:ℚ)/12800) ((16917:ℚ)/25600) :=
  cell_of_packet source18 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((16917:ℚ)/25600),((2117:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((1440889829:ℚ)/2000000000),((7295625003:ℚ)/10000000000),(-1:ℚ),((-3887469487:ℚ)/4234000000),((9774321709:ℚ)/10000000000),((977787351:ℚ)/1000000000),((425706267:ℚ)/2000000000),((810123487:ℚ)/2500000000),((21055012069759830985158245772301967:ℚ)/268901340000000000000000000000000000),((510113379382373601251359:ℚ)/722000000000000000000000)⟩
theorem valid15 : Valid source18 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source18 nn0 nn1 Qcell ((16917:ℚ)/25600) ((2117:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((2117:ℚ)/3200),((8487:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((3605937617:ℚ)/5000000000),((7310468753:ℚ)/10000000000),(-1:ℚ),((-9729812851:ℚ)/10608750000),((9767266893:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((2161672951:ℚ)/10000000000),((401208103:ℚ)/1250000000),((4909799367010467214984212601146193:ℚ)/62525320312500000000000000000000000),((510414687470643885626359:ℚ)/722000000000000000000000)⟩
theorem valid16 : Valid source18 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source18 nn0 nn1 Qcell ((2117:ℚ)/3200) ((8487:ℚ)/12800) :=
  cell_of_packet source18 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((8487:ℚ)/12800),((4253:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7226727383:ℚ)/10000000000),((7325312503:ℚ)/10000000000),(-1:ℚ),((-19504182149:ℚ)/21265000000),((9760276751:ℚ)/10000000000),((4883633449:ℚ)/5000000000),((438804929:ℚ)/2000000000),((3147132429:ℚ)/10000000000),((177488227502875515840976250214904159:ℚ)/2261001125000000000000000000000000000),((510716062100662216876359:ℚ)/722000000000000000000000)⟩
theorem valid17 : Valid source18 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source18 nn0 nn1 Qcell ((8487:ℚ)/12800) ((4253:ℚ)/6400) :=
  cell_of_packet source18 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((4253:ℚ)/6400),((341:ℚ)/512),(-1:ℚ),((-15:ℚ)/16),((1448315899:ℚ)/2000000000),((7340156253:ℚ)/10000000000),(-1:ℚ),((-3909747697:ℚ)/4262500000),((195067017:ℚ)/200000000),((2440069189:ℚ)/2500000000),((1112811311:ℚ)/5000000000),((3083375211:ℚ)/10000000000),((142580367896939099173066219388577:ℚ)/1816890625000000000000000000000000),((511017503272428595001359:ℚ)/722000000000000000000000)⟩
theorem valid18 : Valid source18 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source18 nn0 nn1 Qcell ((4253:ℚ)/6400) ((341:ℚ)/512) :=
  cell_of_packet source18 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((341:ℚ)/512),((267:ℚ)/400),(-1:ℚ),((-15:ℚ)/16),((725643157:ℚ)/1000000000),((3677500001:ℚ)/5000000000),(-1:ℚ),((-1959329471:ℚ)/2136000000),((4873244381:ℚ)/5000000000),((1950670171:ℚ)/2000000000),((2256500263:ℚ)/10000000000),((1509157741:ℚ)/5000000000),((894822370653655508696983347962389:ℚ)/11406240000000000000000000000000000),((127829752741407170000151:ℚ)/180500000000000000000000)⟩
theorem valid19 : Valid source18 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source18 nn0 nn1 Qcell ((341:ℚ)/512) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((267:ℚ)/400),((8563:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7271283607:ℚ)/10000000000),((921230469:ℚ)/1250000000),(-1:ℚ),((-19637850821:ℚ)/21407500000),((9739690061:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((1143344217:ℚ)/5000000000),((1475933527:ℚ)/5000000000),((539115810607067809605522691307616827:ℚ)/6874215843750000000000000000000000000),((7994071644076354204111:ℚ)/11281250000000000000000)⟩
theorem valid20 : Valid source18 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((8563:ℚ)/12800) :=
  cell_of_packet source18 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((8563:ℚ)/12800),((4291:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((910766951:ℚ)/1250000000),((3692343751:ℚ)/5000000000),(-1:ℚ),((-2460300853:ℚ)/2681875000),((1216619291:ℚ)/1250000000),((4869845033:ℚ)/5000000000),((1158107867:ℚ)/5000000000),((1441966927:ℚ)/5000000000),((2819497621058532529198073921671843:ℚ)/35962267578125000000000000000000000),((127980556504473176250151:ℚ)/180500000000000000000000)⟩
theorem valid21 : Valid source18 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source18 nn0 nn1 Qcell ((8563:ℚ)/12800) ((4291:ℚ)/6400) :=
  cell_of_packet source18 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),(-1:ℚ),((-15:ℚ)/16),((1825246893:ℚ)/2500000000),((3707187501:ℚ)/5000000000),(-1:ℚ),((-4931740679:ℚ)/5387500000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2814408299:ℚ)/10000000000),((8581278882335590014480339905001893:ℚ)/108844335937500000000000000000000000),((128131426809287229375151:ℚ)/180500000000000000000000)⟩
theorem valid22 : Valid source18 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source18 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source18 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7330691391:ℚ)/10000000000),((3722031251:ℚ)/5000000000),(-1:ℚ),((-19816074173:ℚ)/21645000000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((667519859:ℚ)/2500000000),((46141773197937631492964833232641373:ℚ)/585632531250000000000000000000000000),((128282363655849329375151:ℚ)/180500000000000000000000)⟩
theorem valid23 : Valid source18 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source18 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source18 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((1840098767:ℚ)/2500000000),((3736875001:ℚ)/5000000000),(-1:ℚ),((-4976296301:ℚ)/5435000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1258849277:ℚ)/5000000000),((34888882514866730564217979033097213:ℚ)/443088375000000000000000000000000000),((128433367044159476250151:ℚ)/180500000000000000000000)⟩
theorem valid24 : Valid source18 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source18 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((3695049301:ℚ)/5000000000),((7533125003:ℚ)/10000000000),(-1:ℚ),((-9997147903:ℚ)/10965000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((235570291:ℚ)/1000000000),((23922594301543930680649665826118399:ℚ)/300578062500000000000000000000000000),((514942293804463776251359:ℚ)/722000000000000000000000)⟩
theorem valid25 : Valid source18 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),(-1:ℚ),((-15:ℚ)/16),((3724752627:ℚ)/5000000000),((3796250001:ℚ)/5000000000),(-1:ℚ),((-1440893983:ℚ)/1580000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((498342759:ℚ)/2500000000),((124013759097735822501432432118803:ℚ)/1560250000000000000000000000000000),((129038046014880532500151:ℚ)/180500000000000000000000)⟩
theorem valid26 : Valid source18 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source18 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),(-1:ℚ),((-15:ℚ)/16),((7508911363:ℚ)/10000000000),((7830000003:ℚ)/10000000000),(-1:ℚ),((-20350734089:ℚ)/22880000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((309959549:ℚ)/2000000000),((220820152170129074198641223376108309:ℚ)/2617472000000000000000000000000000000),((22347:ℚ)/31250)⟩
theorem valid27 : Valid source18 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),(-1:ℚ),((-15:ℚ)/16),((121039541:ℚ)/156250000),((8780000003:ℚ)/10000000000),(-1:ℚ),((-329118623:ℚ)/405000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((81493532495027277093520130076719:ℚ)/820125000000000000000000000000000),((22347:ℚ)/31250)⟩
theorem valid28 : Valid source18 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(-1:ℚ),((-15:ℚ)/16),((869693769:ℚ)/1000000000),((5340000001:ℚ)/5000000000),(-1:ℚ),((-2391481307:ℚ)/3200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((16825909924726964897507030849089703:ℚ)/153600000000000000000000000000000000),((22347:ℚ)/31250)⟩
theorem valid29 : Valid source18 packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet29 valid29
def packet30 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(-1:ℚ),((-15:ℚ)/16),((1059751969:ℚ)/1000000000),((14480000003:ℚ)/10000000000),(-1:ℚ),((-2961655907:ℚ)/4416000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1231065635502736455934241:ℚ)/9750528000000000000000000),((22347:ℚ)/31250)⟩
theorem valid30 : Valid source18 packet30 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf30 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet30 valid30
private theorem node1_3 :
    CellBound source18 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source18 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source18 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source18 nn0 nn1 Qcell ((103:ℚ)/160) ((4177:ℚ)/6400) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((4177:ℚ)/6400) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source18 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source18 nn0 nn1 Qcell ((1049:ℚ)/1600) ((16841:ℚ)/25600) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source18 nn0 nn1 Qcell ((4177:ℚ)/6400) ((16841:ℚ)/25600) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source18 nn0 nn1 Qcell ((16841:ℚ)/25600) ((16879:ℚ)/25600) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source18 nn0 nn1 Qcell ((16879:ℚ)/25600) ((16917:ℚ)/25600) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source18 nn0 nn1 Qcell ((16841:ℚ)/25600) ((16917:ℚ)/25600) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source18 nn0 nn1 Qcell ((4177:ℚ)/6400) ((16917:ℚ)/25600) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((16917:ℚ)/25600) :=
  cell_join node0_7 node7_15
private theorem node15_17 :
    CellBound source18 nn0 nn1 Qcell ((16917:ℚ)/25600) ((8487:ℚ)/12800) :=
  cell_join leaf15 leaf16
private theorem node17_19 :
    CellBound source18 nn0 nn1 Qcell ((8487:ℚ)/12800) ((341:ℚ)/512) :=
  cell_join leaf17 leaf18
private theorem node15_19 :
    CellBound source18 nn0 nn1 Qcell ((16917:ℚ)/25600) ((341:ℚ)/512) :=
  cell_join node15_17 node17_19
private theorem node19_21 :
    CellBound source18 nn0 nn1 Qcell ((341:ℚ)/512) ((8563:ℚ)/12800) :=
  cell_join leaf19 leaf20
private theorem node21_23 :
    CellBound source18 nn0 nn1 Qcell ((8563:ℚ)/12800) ((431:ℚ)/640) :=
  cell_join leaf21 leaf22
private theorem node19_23 :
    CellBound source18 nn0 nn1 Qcell ((341:ℚ)/512) ((431:ℚ)/640) :=
  cell_join node19_21 node21_23
private theorem node15_23 :
    CellBound source18 nn0 nn1 Qcell ((16917:ℚ)/25600) ((431:ℚ)/640) :=
  cell_join node15_19 node19_23
private theorem node23_25 :
    CellBound source18 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_join leaf23 leaf24
private theorem node25_27 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf25 leaf26
private theorem node23_27 :
    CellBound source18 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join node23_25 node25_27
private theorem node27_29 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf27 leaf28
private theorem node29_31 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf29 leaf30
private theorem node27_31 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node27_29 node29_31
private theorem node23_31 :
    CellBound source18 nn0 nn1 Qcell ((431:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node23_27 node27_31
private theorem node15_31 :
    CellBound source18 nn0 nn1 Qcell ((16917:ℚ)/25600) ((69:ℚ)/50) :=
  cell_join node15_23 node23_31
private theorem node0_31 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_15 node15_31
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_31
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29,packet30]
theorem packet_count : packets.length = 31 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC01
#check @N11Formalization.C450Source18GroupedC01.bound
#print axioms N11Formalization.C450Source18GroupedC01.valid0
#print axioms N11Formalization.C450Source18GroupedC01.valid1
#print axioms N11Formalization.C450Source18GroupedC01.valid2
#print axioms N11Formalization.C450Source18GroupedC01.valid3
#print axioms N11Formalization.C450Source18GroupedC01.valid4
#print axioms N11Formalization.C450Source18GroupedC01.valid5
#print axioms N11Formalization.C450Source18GroupedC01.valid6
#print axioms N11Formalization.C450Source18GroupedC01.valid7
#print axioms N11Formalization.C450Source18GroupedC01.valid8
#print axioms N11Formalization.C450Source18GroupedC01.valid9
#print axioms N11Formalization.C450Source18GroupedC01.valid10
#print axioms N11Formalization.C450Source18GroupedC01.valid11
#print axioms N11Formalization.C450Source18GroupedC01.valid12
#print axioms N11Formalization.C450Source18GroupedC01.valid13
#print axioms N11Formalization.C450Source18GroupedC01.valid14
#print axioms N11Formalization.C450Source18GroupedC01.valid15
#print axioms N11Formalization.C450Source18GroupedC01.valid16
#print axioms N11Formalization.C450Source18GroupedC01.valid17
#print axioms N11Formalization.C450Source18GroupedC01.valid18
#print axioms N11Formalization.C450Source18GroupedC01.valid19
#print axioms N11Formalization.C450Source18GroupedC01.valid20
#print axioms N11Formalization.C450Source18GroupedC01.valid21
#print axioms N11Formalization.C450Source18GroupedC01.valid22
#print axioms N11Formalization.C450Source18GroupedC01.valid23
#print axioms N11Formalization.C450Source18GroupedC01.valid24
#print axioms N11Formalization.C450Source18GroupedC01.valid25
#print axioms N11Formalization.C450Source18GroupedC01.valid26
#print axioms N11Formalization.C450Source18GroupedC01.valid27
#print axioms N11Formalization.C450Source18GroupedC01.valid28
#print axioms N11Formalization.C450Source18GroupedC01.valid29
#print axioms N11Formalization.C450Source18GroupedC01.valid30
#print axioms N11Formalization.C450Source18GroupedC01.bound
#print axioms N11Formalization.C450Source18GroupedC01.endpoint_checks
