import N11Formalization.C450Source13Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source13GroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source13Data
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((6581339643:ℚ)/10000000000),((6885332647:ℚ)/10000000000),((-19247997941:ℚ)/19840000000),((-42229377501:ℚ)/51500000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5237180861:ℚ)/10000000000),((91415863323233496620413635011515927460698911:ℚ)/1618189921280000000000000000000000000000000000),((9589344461849802839169661:ℚ)/24320000000000000000000000)⟩
theorem valid0 : Valid source13 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source13 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((170474369:ℚ)/250000000),((6944727461:ℚ)/10000000000),((-19426182383:ℚ)/20600000000),((-1097320583:ℚ)/1299375000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((2286662713:ℚ)/5000000000),((144159218263467257614398022232506222855412123929588109801:ℚ)/2928465675351562500000000000000000000000000000000000000000),((14254583451252650010697:ℚ)/36100000000000000000000)⟩
theorem valid1 : Valid source13 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source13 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((1375676399:ℚ)/2000000000),((1751030479:ℚ)/2500000000),((-445553767:ℚ)/472500000),((-8861734793:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((2196492203:ℚ)/5000000000),((339823241737968544694574387452081685262061866451911043:ℚ)/6909508146269531250000000000000000000000000000000000000),((384676281517419822169189:ℚ)/972800000000000000000000)⟩
theorem valid2 : Valid source13 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source13 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((1387557729:ℚ)/2000000000),((3531758011:ℚ)/5000000000),((-9891274033:ℚ)/10490000000),((-8944904103:ℚ)/10585000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((1051360347:ℚ)/2500000000),((317759636224587931268129423849473418041341167913441912277257:ℚ)/6466632693870201250000000000000000000000000000000000000000000),((7319351737045194990798431:ℚ)/18483200000000000000000000)⟩
theorem valid3 : Valid source13 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source13 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((6997194727:ℚ)/10000000000),((7093212947:ℚ)/10000000000),((-19871638841:ℚ)/21170000000),((-45140363089:ℚ)/53162500000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((4009682279:ℚ)/10000000000),((7725078064133598268705620204951537397154116419315342440161867:ℚ)/160888356710216734687500000000000000000000000000000000000000000),((183114818493025132202841839:ℚ)/462080000000000000000000000)⟩
theorem valid4 : Valid source13 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source13 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((7026897559:ℚ)/10000000000),((1780727447:ℚ)/2500000000),((-4990182341:ℚ)/5316250000),((-45348282913:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((1954168387:ℚ)/5000000000),((1805311600682017691728516006650820905766052276840031211:ℚ)/37609600905686645507812500000000000000000000000000000000),((183246093649792276483485071:ℚ)/462080000000000000000000000)⟩
theorem valid5 : Valid source13 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source13 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source13 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((1411320051:ℚ)/2000000000),((3576303273:ℚ)/5000000000),((-10024909819:ℚ)/10680000000),((-9111240357:ℚ)/10727500000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((951108801:ℚ)/2500000000),((4036382476492634378837891960378469988705486788793956159381257:ℚ)/84112793141040720000000000000000000000000000000000000000000000),((7335094694621061328655991:ℚ)/18483200000000000000000000)⟩
theorem valid6 : Valid source13 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source13 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4291:ℚ)/6400),((8601:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7086302817:ℚ)/10000000000),((3583727447:ℚ)/5000000000),((-1435311763:ℚ)/1532500000),((-15254706573:ℚ)/17918750000),((1215785143:ℚ)/1250000000),((9732954333:ℚ)/10000000000),((2345108749:ℚ)/10000000000),((1848880813:ℚ)/5000000000),((111985716959982118236995674780673872215559334519419975687:ℚ)/2360425214773769531250000000000000000000000000000000000000),((183442875634882352069487199:ℚ)/462080000000000000000000000)⟩
theorem valid7 : Valid source13 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source13 nn0 nn1 Qcell ((4291:ℚ)/6400) ((8601:ℚ)/12800) :=
  cell_of_packet source13 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((8601:ℚ)/12800),((431:ℚ)/640),((-15:ℚ)/16),((-7:ℚ)/8),((7101154047:ℚ)/10000000000),((3591151611:ℚ)/5000000000),((-10069454833:ℚ)/10751250000),((-45868078329:ℚ)/53875000000),((607479381:ℚ)/625000000),((9726281149:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((728661869:ℚ)/2000000000),((4562964243875907804523832806353134936008809103841816297531:ℚ)/96187841845295866699218750000000000000000000000000000000000),((183508511327632785842770719:ℚ)/462080000000000000000000000)⟩
theorem valid8 : Valid source13 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source13 nn0 nn1 Qcell ((8601:ℚ)/12800) ((431:ℚ)/640) :=
  cell_of_packet source13 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((431:ℚ)/640),((8639:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((1423201049:ℚ)/2000000000),((719715153:ℚ)/1000000000),((-2018345459:ℚ)/2155000000),((-9194407343:ℚ)/10798750000),((4856560387:ℚ)/5000000000),((9719670101:ℚ)/10000000000),((9604357:ℚ)/40000000),((1794034163:ℚ)/5000000000),((271689490233795859661638223380014927239005999479529165257:ℚ)/5727843984405781250000000000000000000000000000000000000000),((7342965866537545637455791:ℚ)/18483200000000000000000000)⟩
theorem valid9 : Valid source13 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source13 nn0 nn1 Qcell ((431:ℚ)/640) ((8639:ℚ)/12800) :=
  cell_of_packet source13 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8639:ℚ)/12800),((4329:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((713085641:ℚ)/1000000000),((3605999909:ℚ)/5000000000),((-10113999727:ℚ)/10798750000),((-4607599487:ℚ)/5411250000),((2426658193:ℚ)/2500000000),((9713120779:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((3532001503:ℚ)/10000000000),((1399079370557605024119790493520238646982451165339549054877327:ℚ)/29498888047333373239746093750000000000000000000000000000000000),((1836397816423103392543471:ℚ)/4620800000000000000000000)⟩
theorem valid10 : Valid source13 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source13 nn0 nn1 Qcell ((8639:ℚ)/12800) ((4329:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4329:ℚ)/6400),((8677:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((3572853771:ℚ)/5000000000),((3613424043:ℚ)/5000000000),((-10136272129:ℚ)/10822500000),((-23089976397:ℚ)/27115625000),((9700205687:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((306851119:ℚ)/1250000000),((1737534421:ℚ)/5000000000),((16972478706666796202804104702654461990076387666410078593304803:ℚ)/357893034565335473496093750000000000000000000000000000000000000),((45926354066062417894951431:ℚ)/115520000000000000000000000)⟩
theorem valid11 : Valid source13 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source13 nn0 nn1 Qcell ((4329:ℚ)/6400) ((8677:ℚ)/12800) :=
  cell_of_packet source13 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((8677:ℚ)/12800),((1087:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((3580279321:ℚ)/5000000000),((3620848167:ℚ)/5000000000),((-10158544501:ℚ)/10846250000),((-23141955247:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((2425051423:ℚ)/2500000000),((2480870833:ℚ)/10000000000),((3417227003:ℚ)/10000000000),((5585159267395627397923664446799896566001285207406906670349:ℚ)/117784447717405102081298828125000000000000000000000000000000),((45942762632312426782886031:ℚ)/115520000000000000000000000)⟩
theorem valid12 : Valid source13 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source13 nn0 nn1 Qcell ((8677:ℚ)/12800) ((1087:ℚ)/1600) :=
  cell_of_packet source13 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1087:ℚ)/1600),((1743:ℚ)/2560),((-15:ℚ)/16),((-7:ℚ)/8),((717540971:ℚ)/1000000000),((7256544563:ℚ)/10000000000),((-20361633689:ℚ)/21740000000),((-4638786797:ℚ)/5446875000),((9687532673:ℚ)/10000000000),((2423459781:ℚ)/2500000000),((2506424897:ℚ)/10000000000),((209901809:ℚ)/625000000),((16518432942541484619341607664320629253135744828271327212287:ℚ)/348389761787825625000000000000000000000000000000000000000000),((1838366844417412339439831:ℚ)/4620800000000000000000000)⟩
theorem valid13 : Valid source13 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source13 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1743:ℚ)/2560) :=
  cell_of_packet source13 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1743:ℚ)/2560),((4367:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((3595130373:ℚ)/5000000000),((1817848193:ℚ)/2500000000),((-5101544579:ℚ)/5446875000),((-23245912611:ℚ)/27293750000),((2420321489:ℚ)/2500000000),((4843766339:ℚ)/5000000000),((2531487941:ℚ)/10000000000),((1649311733:ℚ)/5000000000),((6522591203003784590684685375520642407502095287040773727037:ℚ)/137581674802727594375610351562500000000000000000000000000000),((45975579499324234249450439:ℚ)/115520000000000000000000000)⟩
theorem valid14 : Valid source13 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source13 nn0 nn1 Qcell ((1743:ℚ)/2560) ((4367:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4367:ℚ)/6400),((8753:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((28820447:ℚ)/40000000),((3643120481:ℚ)/5000000000),((-929578313:ℚ)/992500000),((-186383129:ℚ)/218825000),((483754929:ℚ)/500000000),((9681285961:ℚ)/10000000000),((639018949:ℚ)/2500000000),((80943867:ℚ)/250000000),((4438450164023978350434289533523196539711295372476915169217:ℚ)/93630084697889785156250000000000000000000000000000000000000),((2943487219205561669119:ℚ)/7393280000000000000000)⟩
theorem valid15 : Valid source13 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source13 nn0 nn1 Qcell ((4367:ℚ)/6400) ((8753:ℚ)/12800) :=
  cell_of_packet source13 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((8753:ℚ)/12800),((2193:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((7219962723:ℚ)/10000000000),((1825272283:ℚ)/2500000000),((-5123816849:ℚ)/5470625000),((-15566579687:ℚ)/18275000000),((4834485079:ℚ)/5000000000),((1935019717:ℚ)/2000000000),((2580203419:ℚ)/10000000000),((3175761373:ℚ)/10000000000),((207342409879115773728759114834948791590149991840101781129:ℚ)/4374370818245257531738281250000000000000000000000000000000),((184033584046457126968990039:ℚ)/462080000000000000000000000)⟩
theorem valid16 : Valid source13 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source13 nn0 nn1 Qcell ((8753:ℚ)/12800) ((2193:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2193:ℚ)/3200),((8791:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((226087927:ℚ)/312500000),((1828984321:ℚ)/2500000000),((-5134952963:ℚ)/5482500000),((-2925230978:ℚ)/3433984375),((9662900309:ℚ)/10000000000),((9668970163:ℚ)/10000000000),((520776989:ℚ)/2000000000),((3112576291:ℚ)/10000000000),((17546215043264793219109810039686579851478448197431420531969:ℚ)/370215023446211308593750000000000000000000000000000000000000),((719137564626930086824681:ℚ)/1805000000000000000000000)⟩
theorem valid17 : Valid source13 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source13 nn0 nn1 Qcell ((2193:ℚ)/3200) ((8791:ℚ)/12800) :=
  cell_of_packet source13 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((8791:ℚ)/12800),((881:ℚ)/1280),((-15:ℚ)/16),((-7:ℚ)/8),((3624832287:ℚ)/5000000000),((916348177:ℚ)/1250000000),((-2573044531:ℚ)/2747187500),((-23453826009:ℚ)/27531250000),((4828444327:ℚ)/5000000000),((4831450157:ℚ)/5000000000),((2627133759:ℚ)/10000000000),((3048125247:ℚ)/10000000000),((238316032414185739450915777115612403185293279089302793751:ℚ)/5028827559062776861190795898437500000000000000000000000000),((46041212171398333360925279:ℚ)/115520000000000000000000000)⟩
theorem valid18 : Valid source13 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source13 nn0 nn1 Qcell ((8791:ℚ)/12800) ((881:ℚ)/1280) :=
  cell_of_packet source13 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-15:ℚ)/16),((-7:ℚ)/8),((3632257727:ℚ)/5000000000),((58883853:ℚ)/80000000),((-165387559:ℚ)/176200000),((-23505804089:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2982326091:ℚ)/10000000000),((14308362020580774484921775127681642293061462157753537:ℚ)/298730762797670000000000000000000000000000000000000000),((46074060864102213146473839:ℚ)/115520000000000000000000000)⟩
theorem valid19 : Valid source13 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source13 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((45588857:ℚ)/62500000),((7390177759:ℚ)/10000000000),((-20762533277:ℚ)/22120000000),((-295121999:ℚ)/347109375),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((711576823:ℚ)/2500000000),((608971626336130648851720867324888467506142263646048643094793:ℚ)/12717411165569040000000000000000000000000000000000000000000000),((115267191138158292817819:ℚ)/288800000000000000000000)⟩
theorem valid20 : Valid source13 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source13 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source13 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((3661959333:ℚ)/5000000000),((7419873819:ℚ)/10000000000),((-20851621457:ℚ)/22215000000),((-23713715331:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((2703648749:ℚ)/10000000000),((3265397900218733820405391634703833001015564970986124259451473:ℚ)/68210008917083722968750000000000000000000000000000000000000000),((46139691696128044598572599:ℚ)/115520000000000000000000000)⟩
theorem valid21 : Valid source13 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source13 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source13 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-15:ℚ)/16),((-7:ℚ)/8),((1838405023:ℚ)/2500000000),((7479265723:ℚ)/10000000000),((-21029797169:ℚ)/22310000000),((-11908835161:ℚ)/14062500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1276618543:ℚ)/5000000000),((796221658206828118513923966056581529163562936352488661:ℚ)/16294635573750000000000000000000000000000000000000000000),((11551346943606423795445339:ℚ)/28880000000000000000000000)⟩
theorem valid22 : Valid source13 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source13 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source13 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((741302259:ℚ)/1000000000),((7598048687:ℚ)/10000000000),((-21386146061:ℚ)/22500000000),((-4805115813:ℚ)/5720000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2222783693:ℚ)/10000000000),((14792078339036167028319485736848424844963338991685414547941:ℚ)/291158613281250000000000000000000000000000000000000000000000),((1853471127656944088373671:ℚ)/4620800000000000000000000)⟩
theorem valid23 : Valid source13 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source13 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-15:ℚ)/16),((-7:ℚ)/8),((941478277:ℚ)/1250000000),((1958902859:ℚ)/2500000000),((-5524708577:ℚ)/5720000000),((-6110347939:ℚ)/7387500000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1340423649:ℚ)/10000000000),((1113847102322827802102188152828880081611330555068086032073:ℚ)/20427398903340000000000000000000000000000000000000000000000),((2896166780478997700764039:ℚ)/7220000000000000000000000)⟩
theorem valid24 : Valid source13 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source13 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source13 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-15:ℚ)/16),((-7:ℚ)/8),((7769428293:ℚ)/10000000000),((322926811:ℚ)/400000000),((-912460433:ℚ)/945600000),((-50545998051:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((638924385114246426428505107384523408406086235090506571:ℚ)/11798134105973760000000000000000000000000000000000000000),((51344611:ℚ)/128000000)⟩
theorem valid25 : Valid source13 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source13 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source13 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((8007024007:ℚ)/10000000000),((8548277597:ℚ)/10000000000),((-24236832791:ℚ)/24400000000),((-52209168049:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1811009158939473390173447567748639128180632769060699428271:ℚ)/29784446820000000000000000000000000000000000000000000000000),((51344611:ℚ)/128000000)⟩
theorem valid26 : Valid source13 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source13 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source13 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((8482198587:ℚ)/10000000000),((2089720981:ℚ)/2000000000),(-1:ℚ),((-55535390109:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1744398718271135886295220544574986983:ℚ)/24000000000000000000000000000000000000),((51344611:ℚ)/128000000)⟩
theorem valid27 : Valid source13 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source13 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source13 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((1038273099:ℚ)/1000000000),((1781123637:ℚ)/1250000000),(-1:ℚ),((-2294637231:ℚ)/3680000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((551425122978719704033271:ℚ)/6771200000000000000000000),((51344611:ℚ)/128000000)⟩
theorem valid28 : Valid source13 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source13 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source13 nn0 nn1 packet28 valid28
private theorem node1_3 :
    CellBound source13 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source13 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4253:ℚ)/6400) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source13 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4291:ℚ)/6400) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source13 nn0 nn1 Qcell ((1049:ℚ)/1600) ((4291:ℚ)/6400) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((4291:ℚ)/6400) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source13 nn0 nn1 Qcell ((8601:ℚ)/12800) ((8639:ℚ)/12800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source13 nn0 nn1 Qcell ((4291:ℚ)/6400) ((8639:ℚ)/12800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source13 nn0 nn1 Qcell ((8639:ℚ)/12800) ((8677:ℚ)/12800) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source13 nn0 nn1 Qcell ((8677:ℚ)/12800) ((1743:ℚ)/2560) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source13 nn0 nn1 Qcell ((8639:ℚ)/12800) ((1743:ℚ)/2560) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source13 nn0 nn1 Qcell ((4291:ℚ)/6400) ((1743:ℚ)/2560) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((1743:ℚ)/2560) :=
  cell_join node0_7 node7_14
private theorem node15_17 :
    CellBound source13 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source13 nn0 nn1 Qcell ((1743:ℚ)/2560) ((2193:ℚ)/3200) :=
  cell_join leaf14 node15_17
private theorem node17_19 :
    CellBound source13 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_join leaf17 leaf18
private theorem node19_21 :
    CellBound source13 nn0 nn1 Qcell ((881:ℚ)/1280) ((4443:ℚ)/6400) :=
  cell_join leaf19 leaf20
private theorem node17_21 :
    CellBound source13 nn0 nn1 Qcell ((2193:ℚ)/3200) ((4443:ℚ)/6400) :=
  cell_join node17_19 node19_21
private theorem node14_21 :
    CellBound source13 nn0 nn1 Qcell ((1743:ℚ)/2560) ((4443:ℚ)/6400) :=
  cell_join node14_17 node17_21
private theorem node21_23 :
    CellBound source13 nn0 nn1 Qcell ((4443:ℚ)/6400) ((45:ℚ)/64) :=
  cell_join leaf21 leaf22
private theorem node23_25 :
    CellBound source13 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf23 leaf24
private theorem node21_25 :
    CellBound source13 nn0 nn1 Qcell ((4443:ℚ)/6400) ((591:ℚ)/800) :=
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
    CellBound source13 nn0 nn1 Qcell ((4443:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node21_25 node25_29
private theorem node14_29 :
    CellBound source13 nn0 nn1 Qcell ((1743:ℚ)/2560) ((69:ℚ)/50) :=
  cell_join node14_21 node21_29
private theorem node0_29 :
    CellBound source13 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_14 node14_29
theorem bound : CellBound source13 nn0 nn1 Qcell (31/50) (69/50) := node0_29
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28]
theorem packet_count : packets.length = 29 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source13GroupedC02
#check @N11Formalization.C450Source13GroupedC02.bound
#print axioms N11Formalization.C450Source13GroupedC02.valid0
#print axioms N11Formalization.C450Source13GroupedC02.valid1
#print axioms N11Formalization.C450Source13GroupedC02.valid2
#print axioms N11Formalization.C450Source13GroupedC02.valid3
#print axioms N11Formalization.C450Source13GroupedC02.valid4
#print axioms N11Formalization.C450Source13GroupedC02.valid5
#print axioms N11Formalization.C450Source13GroupedC02.valid6
#print axioms N11Formalization.C450Source13GroupedC02.valid7
#print axioms N11Formalization.C450Source13GroupedC02.valid8
#print axioms N11Formalization.C450Source13GroupedC02.valid9
#print axioms N11Formalization.C450Source13GroupedC02.valid10
#print axioms N11Formalization.C450Source13GroupedC02.valid11
#print axioms N11Formalization.C450Source13GroupedC02.valid12
#print axioms N11Formalization.C450Source13GroupedC02.valid13
#print axioms N11Formalization.C450Source13GroupedC02.valid14
#print axioms N11Formalization.C450Source13GroupedC02.valid15
#print axioms N11Formalization.C450Source13GroupedC02.valid16
#print axioms N11Formalization.C450Source13GroupedC02.valid17
#print axioms N11Formalization.C450Source13GroupedC02.valid18
#print axioms N11Formalization.C450Source13GroupedC02.valid19
#print axioms N11Formalization.C450Source13GroupedC02.valid20
#print axioms N11Formalization.C450Source13GroupedC02.valid21
#print axioms N11Formalization.C450Source13GroupedC02.valid22
#print axioms N11Formalization.C450Source13GroupedC02.valid23
#print axioms N11Formalization.C450Source13GroupedC02.valid24
#print axioms N11Formalization.C450Source13GroupedC02.valid25
#print axioms N11Formalization.C450Source13GroupedC02.valid26
#print axioms N11Formalization.C450Source13GroupedC02.valid27
#print axioms N11Formalization.C450Source13GroupedC02.valid28
#print axioms N11Formalization.C450Source13GroupedC02.bound
#print axioms N11Formalization.C450Source13GroupedC02.endpoint_checks
