import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((6665531503:ℚ)/10000000000),((274352121:ℚ)/400000000),((-3156977573:ℚ)/3968000000),((-17276594509:ℚ)/25275000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((5011229897:ℚ)/10000000000),((14344952332209084911276073967490234059073317342761170587999:ℚ)/199557163981209600000000000000000000000000000000000000000000),((349066874439426335914182659:ℚ)/739328000000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((6784554031:ℚ)/10000000000),((697778307:ℚ)/1000000000),((-8047117991:ℚ)/10110000000),((-17633662093:ℚ)/25750000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((467484997:ℚ)/1000000000),((7386993846389367409590256649956255408103864318186923131511:ℚ)/102777770508553125000000000000000000000000000000000000000000),((349700689693900724902759811:ℚ)/739328000000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((862945809:ℚ)/1250000000),((703726993:ℚ)/1000000000),((-8124450909:ℚ)/10300000000),((-2248837427:ℚ)/3248437500),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((539301507:ℚ)/1250000000),((255562642774472406622039657922940768474672308499418082404687:ℚ)/3689866750942968750000000000000000000000000000000000000000000),((5468440108766875881847331:ℚ)/11552000000000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((6963069083:ℚ)/10000000000),((7096754759:ℚ)/10000000000),((-82017811867:ℚ)/103950000000),((-18169207249:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((2061603513:ℚ)/5000000000),((66904676217704305369010617610397145341479584456155928556557081:ℚ)/965638310981898339843750000000000000000000000000000000000000000),((350295929967141949081322539:ℚ)/739328000000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-13:ℚ)/16),((-3:ℚ)/4),((11236111:ℚ)/16000000),((1781624107:ℚ)/2500000000),((-20601113391:ℚ)/26225000000),((-29356333:ℚ)/42150000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((784651761:ℚ)/2000000000),((27250979508617929293993602710200443003398177148338159680037:ℚ)/400545319771094238281250000000000000000000000000000000000000),((4485566240869696900431:ℚ)/9463398400000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((440769917:ℚ)/625000000),((715623761:ℚ)/1000000000),((-8279108893:ℚ)/10537500000),((-39734819:ℚ)/57031250),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((477447253:ℚ)/1250000000),((442015946459238335871331856529452244901216118530606546733:ℚ)/6495121059576416015625000000000000000000000000000000000000),((1369501790232629972273539:ℚ)/2888000000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((1770516853:ℚ)/2500000000),((7185978311:ℚ)/10000000000),((-83177718043:ℚ)/105850000000),((-4631550559:ℚ)/6645312500),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((3713151107:ℚ)/10000000000),((4563319455872208151783077466980891718770100616724311618019551009:ℚ)/67036815295923639453125000000000000000000000000000000000000000000),((21921873226077967456077259:ℚ)/46208000000000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((7111815603:ℚ)/10000000000),((3607859269:ℚ)/5000000000),((-41782170497:ℚ)/53162500000),((-18615446809:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((1801867119:ℚ)/5000000000),((569783265263480089610932269061772861648078579736263174456531:ℚ)/8368136201515278625488281250000000000000000000000000000000000),((350907402561920780843807259:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((267:ℚ)/400),((8563:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((1785390813:ℚ)/2500000000),((289223539:ℚ)/400000000),((-1116768669:ℚ)/1424000000),((-4676172439:ℚ)/6689843750),((9739690061:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((1143344217:ℚ)/5000000000),((3491045759:ℚ)/10000000000),((44651097865580844266500654149082330442270273125687647874863:ℚ)/661655424908300800000000000000000000000000000000000000000000),((21936031594806440756050619:ℚ)/46208000000000000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((8563:ℚ)/12800) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((8563:ℚ)/12800),((4291:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7156436877:ℚ)/10000000000),((905682287:ℚ)/1250000000),((-10493869731:ℚ)/13379687500),((-18749310631:ℚ)/26818750000),((1216619291:ℚ)/1250000000),((4869845033:ℚ)/5000000000),((1158107867:ℚ)/5000000000),((3433374189:ℚ)/10000000000),((290684480631516989364730107633546894126898662424312625196461:ℚ)/4306802758434253002330660820007324218750000000000000000000000),((351055149637207679007738779:ℚ)/739328000000000000000000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((8563:ℚ)/12800) ((4291:ℚ)/6400) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4291:ℚ)/6400),((8601:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((224103449:ℚ)/312500000),((3630164001:ℚ)/5000000000),((-42072132013:ℚ)/53637500000),((-2349241388:ℚ)/3359765625),((1215785143:ℚ)/1250000000),((9732954333:ℚ)/10000000000),((2345108749:ℚ)/10000000000),((1687378697:ℚ)/5000000000),((12542520895577458297073647887927499426181444747086195658578693:ℚ)/185802807067226262760162353515625000000000000000000000000000000),((342904075376623033716701:ℚ)/722000000000000000000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell ((4291:ℚ)/6400) ((8601:ℚ)/12800) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((8601:ℚ)/12800),((431:ℚ)/640),((-13:ℚ)/16),((-3:ℚ)/4),((7186183727:ℚ)/10000000000),((7275197593:ℚ)/10000000000),((-28112522903:ℚ)/35837500000),((-18838551181:ℚ)/26937500000),((607479381:ℚ)/625000000),((9726281149:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1657572581:ℚ)/5000000000),((21139579196171275873796666539827501097509261054411034794943:ℚ)/313111464340155816078186035156250000000000000000000000000000),((351212376161508083304226179:ℚ)/739328000000000000000000000)⟩
theorem valid11 : Valid source18 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source18 nn0 nn1 Qcell ((8601:ℚ)/12800) ((431:ℚ)/640) :=
  cell_of_packet source18 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((1800264239:ℚ)/2500000000),((7304936433:ℚ)/10000000000),((-84724173629:ℚ)/107750000000),((-4720792717:ℚ)/6764062500),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((813620679:ℚ)/2500000000),((312003000383652054303749900843044196799040841808169922725197743:ℚ)/4578856648317965698242187500000000000000000000000000000000000000),((21961200093633904119435971:ℚ)/46208000000000000000000000)⟩
theorem valid12 : Valid source18 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source18 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source18 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((451925189:ℚ)/625000000),((916834353:ℚ)/1250000000),((-10638846589:ℚ)/13528125000),((-1185775567:ℚ)/1698437500),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1564880797:ℚ)/5000000000),((5613080389510853847466976470476317569082370501479834614273:ℚ)/82356703272536373138427734375000000000000000000000000000000),((1373188684778060314882571:ℚ)/2888000000000000000000000)⟩
theorem valid13 : Valid source18 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source18 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7260548579:ℚ)/10000000000),((7364412771:ℚ)/10000000000),((-85497366023:ℚ)/108700000000),((-48014221:ℚ)/68750000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((3000038909:ℚ)/10000000000),((2069206603698784403889568183446466425973936128546657734221:ℚ)/30353169113867187500000000000000000000000000000000000000000),((351693322911365753255188091:ℚ)/739328000000000000000000000)⟩
theorem valid14 : Valid source18 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source18 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((7290293627:ℚ)/10000000000),((184853757:ℚ)/250000000),((-2147098841:ℚ)/2729375000),((-19150880881:ℚ)/27412500000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((1432317319:ℚ)/5000000000),((5208962291412332577622550960842806173302079726628822910627:ℚ)/76393590350186135673522949218750000000000000000000000000000),((351850260358480588873740779:ℚ)/739328000000000000000000000)⟩
theorem valid15 : Valid source18 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source18 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((292801527:ℚ)/400000000),((1490724801:ℚ)/2000000000),((-17331422413:ℚ)/21930000000),((-769604581:ℚ)/1106000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((544540117:ℚ)/2000000000),((32787720151637739306194182741470908540797423514623354430453:ℚ)/472451747897184521484375000000000000000000000000000000000000),((563493742726507005087379:ℚ)/1182924800000000000000000)⟩
theorem valid16 : Valid source18 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source18 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-13:ℚ)/16),((-3:ℚ)/4),((1844881449:ℚ)/2500000000),((3786283221:ℚ)/5000000000),((-44101681873:ℚ)/55300000000),((-4854644347:ℚ)/7031250000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1207292841:ℚ)/5000000000),((151912696293897879200897659023395171982971104076898469:ℚ)/2116622351074218750000000000000000000000000000000000000),((22053123653623776861354451:ℚ)/46208000000000000000000000)⟩
theorem valid17 : Valid source18 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source18 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((3749247659:ℚ)/5000000000),((7691502471:ℚ)/10000000000),((-89749532123:ℚ)/112500000000),((-9887742977:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((818098879:ℚ)/5000000000),((6527604342330655146539896171951114310312212223842528019606209:ℚ)/90987066650390625000000000000000000000000000000000000000000000),((88233217263773466857293131:ℚ)/184832000000000000000000000)⟩
theorem valid18 : Valid source18 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((952182191:ℚ)/1250000000),((2160698489:ℚ)/2500000000),((-2320825487:ℚ)/2600000000),((-2516546573:ℚ)/4050000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((3083063726892330113117584121040849584234800655052649327:ℚ)/30030243750000000000000000000000000000000000000000000000),((122182713:ℚ)/256000000)⟩
theorem valid19 : Valid source18 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((4284465353:ℚ)/5000000000),((5272319863:ℚ)/5000000000),((-63420158219:ℚ)/64800000000),((-11493396059:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((20644018389326820390943423819753219354645835374121298451:ℚ)/159432300000000000000000000000000000000000000000000000000),((122182713:ℚ)/256000000)⟩
theorem valid20 : Valid source18 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((523551799:ℚ)/500000000),((14346805213:ℚ)/10000000000),(-1:ℚ),((-1434655397:ℚ)/2760000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((563505593593243123464881:ℚ)/3808800000000000000000000),((122182713:ℚ)/256000000)⟩
theorem valid21 : Valid source18 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet21 valid21
private theorem node0_2 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source18 nn0 nn1 Qcell ((2079:ℚ)/3200) ((843:ℚ)/1280) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source18 nn0 nn1 Qcell ((103:ℚ)/160) ((843:ℚ)/1280) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((843:ℚ)/1280) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound source18 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound source18 nn0 nn1 Qcell ((843:ℚ)/1280) ((267:ℚ)/400) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound source18 nn0 nn1 Qcell ((8563:ℚ)/12800) ((8601:ℚ)/12800) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((8601:ℚ)/12800) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound source18 nn0 nn1 Qcell ((843:ℚ)/1280) ((8601:ℚ)/12800) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((8601:ℚ)/12800) :=
  cell_join node0_5 node5_11
private theorem node11_13 :
    CellBound source18 nn0 nn1 Qcell ((8601:ℚ)/12800) ((4329:ℚ)/6400) :=
  cell_join leaf11 leaf12
private theorem node14_16 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source18 nn0 nn1 Qcell ((4329:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_join leaf13 node14_16
private theorem node11_16 :
    CellBound source18 nn0 nn1 Qcell ((8601:ℚ)/12800) ((2193:ℚ)/3200) :=
  cell_join node11_13 node13_16
private theorem node17_19 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source18 nn0 nn1 Qcell ((2193:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf16 node17_19
private theorem node20_22 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf20 leaf21
private theorem node19_22 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf19 node20_22
private theorem node16_22 :
    CellBound source18 nn0 nn1 Qcell ((2193:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node16_19 node19_22
private theorem node11_22 :
    CellBound source18 nn0 nn1 Qcell ((8601:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node11_16 node16_22
private theorem node0_22 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_22
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_22
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21]
theorem packet_count : packets.length = 22 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC04
#check @N11Formalization.C450Source18GroupedC04.bound
#print axioms N11Formalization.C450Source18GroupedC04.valid0
#print axioms N11Formalization.C450Source18GroupedC04.valid1
#print axioms N11Formalization.C450Source18GroupedC04.valid2
#print axioms N11Formalization.C450Source18GroupedC04.valid3
#print axioms N11Formalization.C450Source18GroupedC04.valid4
#print axioms N11Formalization.C450Source18GroupedC04.valid5
#print axioms N11Formalization.C450Source18GroupedC04.valid6
#print axioms N11Formalization.C450Source18GroupedC04.valid7
#print axioms N11Formalization.C450Source18GroupedC04.valid8
#print axioms N11Formalization.C450Source18GroupedC04.valid9
#print axioms N11Formalization.C450Source18GroupedC04.valid10
#print axioms N11Formalization.C450Source18GroupedC04.valid11
#print axioms N11Formalization.C450Source18GroupedC04.valid12
#print axioms N11Formalization.C450Source18GroupedC04.valid13
#print axioms N11Formalization.C450Source18GroupedC04.valid14
#print axioms N11Formalization.C450Source18GroupedC04.valid15
#print axioms N11Formalization.C450Source18GroupedC04.valid16
#print axioms N11Formalization.C450Source18GroupedC04.valid17
#print axioms N11Formalization.C450Source18GroupedC04.valid18
#print axioms N11Formalization.C450Source18GroupedC04.valid19
#print axioms N11Formalization.C450Source18GroupedC04.valid20
#print axioms N11Formalization.C450Source18GroupedC04.valid21
#print axioms N11Formalization.C450Source18GroupedC04.bound
#print axioms N11Formalization.C450Source18GroupedC04.endpoint_checks
