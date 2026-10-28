import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((3276095889:ℚ)/5000000000),((6853304461:ℚ)/10000000000),((-44453131227:ℚ)/49600000000),((-38749246557:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1062673623:ℚ)/2000000000),((10708272453466841836568082866255686629492933:ℚ)/202273740160000000000000000000000000000000000),((1303916809297266826926052773:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((6789887773:ℚ)/10000000000),((13944261:ℚ)/20000000),((-90569827:ℚ)/103000000),((-80588541049:ℚ)/104900000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((291203273:ℚ)/625000000),((287240977042279149061013214615405262590259995184287:ℚ)/5871278728159179687500000000000000000000000000000000),((5227644359046701615573:ℚ)/14786560000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((172718261:ℚ)/250000000),((219735703:ℚ)/312500000),((-1428149921:ℚ)/1639062500),((-2053337393:ℚ)/2646250000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((2149067517:ℚ)/5000000000),((1160680950005734349889920291909912004125191630061333273421:ℚ)/24668246055107884407043457031250000000000000000000000000000),((3539453340511721141797:ℚ)/10000000000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((278726021:ℚ)/400000000),((1412249649:ℚ)/2000000000),((-9181747543:ℚ)/10585000000),((-3316238273:ℚ)/4253000000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((410649053:ℚ)/1000000000),((928050734340792922562120066351477230705359400426893293275589:ℚ)/20111044588777091835937500000000000000000000000000000000000000),((52366289488333521151327613:ℚ)/147865600000000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((874732533:ℚ)/1250000000),((886369229:ℚ)/1250000000),((-5764584603:ℚ)/6645312500),((-3470507643:ℚ)/4450000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((4007438067:ℚ)/10000000000),((1506510054444810175688877623708805228178571638143547667:ℚ)/32647223008408546447753906250000000000000000000000000000),((20467281821490881850173733:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((3513784903:ℚ)/5000000000),((7120659259:ℚ)/10000000000),((-15441538271:ℚ)/17800000000),((-41839203739:ℚ)/53637500000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((244125891:ℚ)/625000000),((17968929011654428678769206040046276265643642877626567902543453:ℚ)/389411079356670000000000000000000000000000000000000000000000000),((1310654877817828370527684053:ℚ)/3696640000000000000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-7:ℚ)/8),((-13:ℚ)/16),((441079947:ℚ)/625000000),((446897783:ℚ)/625000000),((-2908284481:ℚ)/3352343750),((-5254039311:ℚ)/6734375000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3802028857:ℚ)/10000000000),((605484235818712826641156425141125921811780497216814607129:ℚ)/13122042711871085464954376220703125000000000000000000000000),((5122670941348650196410157:ℚ)/14440000000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((431:ℚ)/640),((8639:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((3543494153:ℚ)/5000000000),((7165217103:ℚ)/10000000000),((-46636519721:ℚ)/53875000000),((-796706113:ℚ)/1018750000),((4856560387:ℚ)/5000000000),((9719670101:ℚ)/10000000000),((9604357:ℚ)/40000000),((923816283:ℚ)/2500000000),((364051270138246116397739779439771605811472016008126407883:ℚ)/7965251179809570312500000000000000000000000000000000000000),((1311778218284315877536097917:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((431:ℚ)/640) ((8639:ℚ)/12800) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((8639:ℚ)/12800),((4329:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7101842811:ℚ)/10000000000),((179501741:ℚ)/250000000),((-1168512187:ℚ)/1349843750),((-28214652181:ℚ)/36075000000),((2426658193:ℚ)/2500000000),((9713120779:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((728153023:ℚ)/2000000000),((292591541340030966137303645167593271743801900410508881977:ℚ)/6401668413049777178764343261718750000000000000000000000000),((820095428813859314510053:ℚ)/2310400000000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((8639:ℚ)/12800) ((4329:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4329:ℚ)/6400),((8677:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7116697269:ℚ)/10000000000),((3597461069:ℚ)/5000000000),((-7807409161:ℚ)/9018750000),((-84837064497:ℚ)/108462500000),((9700205687:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((306851119:ℚ)/1250000000),((3585474409:ℚ)/10000000000),((3155455991267294300337650595852517016017073072716030471021369:ℚ)/69038008210905762634277343750000000000000000000000000000000000),((328131791103382474409881893:ℚ)/924160000000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((4329:ℚ)/6400) ((8677:ℚ)/12800) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8677:ℚ)/12800),((1087:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((22286099:ℚ)/31250000),((3604887299:ℚ)/5000000000),((-23474211093:ℚ)/27115625000),((-265719287:ℚ)/339687500),((9693839119:ℚ)/10000000000),((2425051423:ℚ)/2500000000),((2480870833:ℚ)/10000000000),((3529355791:ℚ)/10000000000),((1345881684670453251515175786441335633150056186116386045208437:ℚ)/29446111929351275520324707031250000000000000000000000000000000),((328225413310876191390126213:ℚ)/924160000000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((8677:ℚ)/12800) ((1087:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1087:ℚ)/1600),((1743:ℚ)/2560),((-7:ℚ)/8),((-13:ℚ)/16),((1786601511:ℚ)/2500000000),((361231351:ℚ)/500000000),((-2352619457:ℚ)/2717500000),((-7101939881:ℚ)/9078125000),((9687532673:ℚ)/10000000000),((2423459781:ℚ)/2500000000),((2506424897:ℚ)/10000000000),((3472369059:ℚ)/10000000000),((55291279396543040332145222726021392154527599429683030119:ℚ)/1209686672874394531250000000000000000000000000000000000000),((3283190381480028543933613:ℚ)/9241600000000000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1743:ℚ)/2560) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1743:ℚ)/2560),((4367:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((3580630181:ℚ)/5000000000),((1447895881:ℚ)/2000000000),((-9431271167:ℚ)/10893750000),((-42708192353:ℚ)/54587500000),((2420321489:ℚ)/2500000000),((4843766339:ℚ)/5000000000),((2531487941:ℚ)/10000000000),((3414470679:ℚ)/10000000000),((29346458888243980963179146381252547518007772514754659805101:ℚ)/642047815746062107086181640625000000000000000000000000000000),((52546026499367104898146093:ℚ)/147865600000000000000000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((1743:ℚ)/2560) ((4367:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4367:ℚ)/6400),((8753:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((3588057317:ℚ)/5000000000),((7254331751:ℚ)/10000000000),((-47260322257:ℚ)/54587500000),((-42804745121:ℚ)/54706250000),((483754929:ℚ)/500000000),((9681285961:ℚ)/10000000000),((639018949:ℚ)/2500000000),((3355613397:ℚ)/10000000000),((5340198961322357022690893189952662959658295070158455294077499:ℚ)/116832790062085597540283203125000000000000000000000000000000000),((1314025182869484348043464013:ℚ)/3696640000000000000000000000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell ((4367:ℚ)/6400) ((8753:ℚ)/12800) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((8753:ℚ)/12800),((2193:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((7190968861:ℚ)/10000000000),((7269184061:ℚ)/10000000000),((-47364288427:ℚ)/54706250000),((-85802595193:ℚ)/109650000000),((4834485079:ℚ)/5000000000),((1935019717:ℚ)/2000000000),((2580203419:ℚ)/10000000000),((823936443:ℚ)/2500000000),((11246954604429345582111981000489216370349695606626452883891803:ℚ)/246058358526295736160278320312500000000000000000000000000000000),((1314399713823493397598618373:ℚ)/3696640000000000000000000000)⟩
theorem valid14 : Valid source13 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source13 nn0 nn1 Qcell ((8753:ℚ)/12800) ((2193:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((2193:ℚ)/3200),((8791:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((3602911521:ℚ)/5000000000),((7284036333:ℚ)/10000000000),((-47468254331:ℚ)/54825000000),((-42997849773:ℚ)/54943750000),((9662900309:ℚ)/10000000000),((9668970163:ℚ)/10000000000),((520776989:ℚ)/2000000000),((646962329:ℚ)/2000000000),((727651143434162646792442669294285434739267415050833908193663299:ℚ)/15919246008187086269531250000000000000000000000000000000000000000),((1314774255295684966692243557:ℚ)/3696640000000000000000000000)⟩
theorem valid15 : Valid source13 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source13 nn0 nn1 Qcell ((2193:ℚ)/3200) ((8791:ℚ)/12800) :=
  cell_of_packet source13 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((8791:ℚ)/12800),((881:ℚ)/1280),((-7:ℚ)/8),((-13:ℚ)/16),((7220677177:ℚ)/10000000000),((7298888569:ℚ)/10000000000),((-47572219983:ℚ)/54943750000),((-86188803301:ℚ)/110125000000),((4828444327:ℚ)/5000000000),((4831450157:ℚ)/5000000000),((2627133759:ℚ)/10000000000),((6345499:ℚ)/20000000),((1838912769079800893701694151393672032032010292486147236527847:ℚ)/40230620472502214889526367187500000000000000000000000000000000),((1315148807336408864587066893:ℚ)/3696640000000000000000000000)⟩
theorem valid16 : Valid source13 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source13 nn0 nn1 Qcell ((8791:ℚ)/12800) ((881:ℚ)/1280) :=
  cell_of_packet source13 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((881:ℚ)/1280),((8829:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((1808882817:ℚ)/2500000000),((228554399:ℚ)/312500000),((-1489880793:ℚ)/1720703125),((-7198492207:ℚ)/9196875000),((301591713:ℚ)/312500000),((9656888659:ℚ)/10000000000),((2649962557:ℚ)/10000000000),((77737293:ℚ)/250000000),((13131519972806091394658815373230560200705036532587512201:ℚ)/287281163355190510628744959831237792968750000000000000000),((1284690790937853435491613:ℚ)/3610000000000000000000000)⟩
theorem valid17 : Valid source13 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source13 nn0 nn1 Qcell ((881:ℚ)/1280) ((8829:ℚ)/12800) :=
  cell_of_packet source13 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((8829:ℚ)/12800),((553:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((3625192657:ℚ)/5000000000),((7328592931:ℚ)/10000000000),((-5308905613:ℚ)/6131250000),((-43287504541:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9650934821:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3044963723:ℚ)/10000000000),((13484401275033344131688315457993538063826706857324742961:ℚ)/294999034680368900299072265625000000000000000000000000000),((1315897943072678851181005893:ℚ)/3696640000000000000000000000)⟩
theorem valid18 : Valid source13 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source13 nn0 nn1 Qcell ((8829:ℚ)/12800) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7265239317:ℚ)/10000000000),((1839574287:ℚ)/2500000000),((-11997020009:ℚ)/13825000000),((-28922703707:ℚ)/37025000000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((2979082889:ℚ)/10000000000),((47743569155572608050610363831649150130274652284822458680303:ℚ)/1034945570114667968750000000000000000000000000000000000000000),((82290445066053032007852797:ℚ)/231040000000000000000000000)⟩
theorem valid19 : Valid source13 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((7294947189:ℚ)/10000000000),((7388001223:ℚ)/10000000000),((-16065336187:ℚ)/18512500000),((-87154313457:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1421442163:ℚ)/5000000000),((1820893473322968527334245142032926410641764551858389609397283:ℚ)/39473384789979006347656250000000000000000000000000000000000000),((1317396341363916356932398477:ℚ)/3696640000000000000000000000)⟩
theorem valid20 : Valid source13 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source13 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-7:ℚ)/8),((-13:ℚ)/16),((915581861:ℚ)/1250000000),((7447408953:ℚ)/10000000000),((-48611862671:ℚ)/55775000000),((-10942564193:ℚ)/14062500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2700019361:ℚ)/10000000000),((11955886937479750482389532330268614842781540246709677419:ℚ)/254603680839843750000000000000000000000000000000000000000),((1318894909095473320780664717:ℚ)/3696640000000000000000000000)⟩
theorem valid21 : Valid source13 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source13 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source13 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((7384069773:ℚ)/10000000000),((1501363227:ℚ)/2000000000),((-9805542589:ℚ)/11250000000),((-88312907049:ℚ)/113450000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((149340843:ℚ)/625000000),((430161741128775729976402817787546012596984620023122038808701:ℚ)/9162976486816406250000000000000000000000000000000000000000000),((52815745864614218953849877:ℚ)/147865600000000000000000000)⟩
theorem valid22 : Valid source13 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((744348399:ℚ)/1000000000),((7566222781:ℚ)/10000000000),((-49443559467:ℚ)/56725000000),((-8908529187:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((508248089:ℚ)/2500000000),((8758683401344916447688092122758324761677047515317733010083:ℚ)/186623183240578906250000000000000000000000000000000000000000),((1321892554221275960926847493:ℚ)/3696640000000000000000000000)⟩
theorem valid23 : Valid source13 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((1500579511:ℚ)/2000000000),((1950961069:ℚ)/2500000000),((-982825191:ℚ)/1100000000),((-17971533643:ℚ)/23640000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1600246087:ℚ)/10000000000),((7511249428667720644925744313631069037948178963409918351:ℚ)/145279065937500000000000000000000000000000000000000000000),((91602831:ℚ)/256000000)⟩
theorem valid24 : Valid source13 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-7:ℚ)/8),((-13:ℚ)/16),((7740545609:ℚ)/10000000000),((2010364549:ℚ)/2500000000),((-4397517281:ℚ)/4925000000),((-92947092917:ℚ)/122000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((85771459635812940880905169705258319081721650449295404603:ℚ)/1666900367167968750000000000000000000000000000000000000000),((91602831:ℚ)/256000000)⟩
theorem valid25 : Valid source13 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((498636527:ℚ)/625000000),((8516665983:ℚ)/10000000000),((-56096661881:ℚ)/61000000000),((-6002274851:ℚ)/8100000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((26546579349618101956743474604040738078035490358358722221441:ℚ)/465381981562500000000000000000000000000000000000000000000000),((91602831:ℚ)/256000000)⟩
theorem valid26 : Valid source13 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((2113359409:ℚ)/2500000000),((5208649819:ℚ)/5000000000),(-1:ℚ),((-25553672317:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((465586612086211177160476809507365927:ℚ)/6000000000000000000000000000000000000),((91602831:ℚ)/256000000)⟩
theorem valid27 : Valid source13 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((10354209769:ℚ)/10000000000),((7109021671:ℚ)/5000000000),(-1:ℚ),((-126924726997:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2086680271489067484010096799:ℚ)/24376320000000000000000000000),((91602831:ℚ)/256000000)⟩
theorem valid28 : Valid source13 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source13 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source13 nn0 nn1 packet28 valid28
private theorem node1_3 :
    CellBound source13 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source13 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source13 nn0 nn1 Qcell ((2117:ℚ)/3200) ((431:ℚ)/640) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source13 nn0 nn1 Qcell ((8639:ℚ)/12800) ((8677:ℚ)/12800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source13 nn0 nn1 Qcell ((431:ℚ)/640) ((8677:ℚ)/12800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source13 nn0 nn1 Qcell ((8677:ℚ)/12800) ((1743:ℚ)/2560) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source13 nn0 nn1 Qcell ((1743:ℚ)/2560) ((8753:ℚ)/12800) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source13 nn0 nn1 Qcell ((8677:ℚ)/12800) ((8753:ℚ)/12800) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source13 nn0 nn1 Qcell ((431:ℚ)/640) ((8753:ℚ)/12800) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((8753:ℚ)/12800) :=
  cell_join node0_7 node7_14
private theorem node15_17 :
    CellBound source13 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source13 nn0 nn1 Qcell ((8753:ℚ)/12800) ((881:ℚ)/1280) :=
  cell_join leaf14 node15_17
private theorem node17_19 :
    CellBound source13 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_join leaf17 leaf18
private theorem node19_21 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_join leaf19 leaf20
private theorem node17_21 :
    CellBound source13 nn0 nn1 Qcell ((881:ℚ)/1280) ((2231:ℚ)/3200) :=
  cell_join node17_19 node19_21
private theorem node14_21 :
    CellBound source13 nn0 nn1 Qcell ((8753:ℚ)/12800) ((2231:ℚ)/3200) :=
  cell_join node14_17 node17_21
private theorem node21_23 :
    CellBound source13 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf21 leaf22
private theorem node23_25 :
    CellBound source13 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf23 leaf24
private theorem node21_25 :
    CellBound source13 nn0 nn1 Qcell ((2231:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node21_23 node23_25
private theorem node25_27 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf25 leaf26
private theorem node27_29 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf27 leaf28
private theorem node25_29 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node25_27 node27_29
private theorem node21_29 :
    CellBound source13 nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node21_25 node25_29
private theorem node14_29 :
    CellBound source13 nn0 nn1 Qcell ((8753:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node14_21 node21_29
private theorem node0_29 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_14 node14_29
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_29
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28]
theorem packet_count : packets.length = 29 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC03
#check @N11Formalization.C450Source13GroupedC03.bound
#print axioms N11Formalization.C450Source13GroupedC03.valid0
#print axioms N11Formalization.C450Source13GroupedC03.valid1
#print axioms N11Formalization.C450Source13GroupedC03.valid2
#print axioms N11Formalization.C450Source13GroupedC03.valid3
#print axioms N11Formalization.C450Source13GroupedC03.valid4
#print axioms N11Formalization.C450Source13GroupedC03.valid5
#print axioms N11Formalization.C450Source13GroupedC03.valid6
#print axioms N11Formalization.C450Source13GroupedC03.valid7
#print axioms N11Formalization.C450Source13GroupedC03.valid8
#print axioms N11Formalization.C450Source13GroupedC03.valid9
#print axioms N11Formalization.C450Source13GroupedC03.valid10
#print axioms N11Formalization.C450Source13GroupedC03.valid11
#print axioms N11Formalization.C450Source13GroupedC03.valid12
#print axioms N11Formalization.C450Source13GroupedC03.valid13
#print axioms N11Formalization.C450Source13GroupedC03.valid14
#print axioms N11Formalization.C450Source13GroupedC03.valid15
#print axioms N11Formalization.C450Source13GroupedC03.valid16
#print axioms N11Formalization.C450Source13GroupedC03.valid17
#print axioms N11Formalization.C450Source13GroupedC03.valid18
#print axioms N11Formalization.C450Source13GroupedC03.valid19
#print axioms N11Formalization.C450Source13GroupedC03.valid20
#print axioms N11Formalization.C450Source13GroupedC03.valid21
#print axioms N11Formalization.C450Source13GroupedC03.valid22
#print axioms N11Formalization.C450Source13GroupedC03.valid23
#print axioms N11Formalization.C450Source13GroupedC03.valid24
#print axioms N11Formalization.C450Source13GroupedC03.valid25
#print axioms N11Formalization.C450Source13GroupedC03.valid26
#print axioms N11Formalization.C450Source13GroupedC03.valid27
#print axioms N11Formalization.C450Source13GroupedC03.valid28
#print axioms N11Formalization.C450Source13GroupedC03.bound
#print axioms N11Formalization.C450Source13GroupedC03.endpoint_checks
