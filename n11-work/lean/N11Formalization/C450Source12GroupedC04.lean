import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((811794033:ℚ)/1250000000),((3394943889:ℚ)/5000000000),((-40934270557:ℚ)/49600000000),((-2215382099:ℚ)/3218750000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2730851173:ℚ)/5000000000),((20601442934975851747138999510086255953900253984262140242251:ℚ)/505684350400000000000000000000000000000000000000000000000000),((3306910225122657249834823:ℚ)/11552000000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((3366030403:ℚ)/5000000000),((1381746089:ℚ)/2000000000),((-16682699157:ℚ)/20600000000),((-9218091209:ℚ)/13112500000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4825866959:ℚ)/10000000000),((35882712791310477399275975019834276300910463404442961300171:ℚ)/939404596505468750000000000000000000000000000000000000000000),((529872875276071906195623:ℚ)/1848320000000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((1370181881:ℚ)/2000000000),((696815053:ℚ)/1000000000),((-8418595689:ℚ)/10490000000),((-3758545643:ℚ)/5292500000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4477223897:ℚ)/10000000000),((74777473526390140722839573658862374059190033406438736810943:ℚ)/2020822716834437890625000000000000000000000000000000000000000),((132564191938550080682367:ℚ)/462080000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((55282659:ℚ)/80000000),((7027569811:ℚ)/10000000000),((-84958407543:ℚ)/105850000000),((-151767977:ℚ)/213600000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((2146536959:ℚ)/5000000000),((1395164054402410010192263541348211088497026074107084057971:ℚ)/37700841009558105468750000000000000000000000000000000000000),((13266021057623956943203023:ℚ)/46208000000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-13:ℚ)/16),((-3:ℚ)/4),((6969754491:ℚ)/10000000000),((7086988311:ℚ)/10000000000),((-85730848043:ℚ)/106800000000),((-19149263473:ℚ)/26937500000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2050600299:ℚ)/5000000000),((4259590327910213148263341687739783842607898507221598057967:ℚ)/115097823992285156250000000000000000000000000000000000000000),((13275627476738008066994023:ℚ)/46208000000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((281167031:ℚ)/400000000),((3558348637:ℚ)/5000000000),((-43058532281:ℚ)/53875000000),((-773101093:ℚ)/1082250000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((3900460551:ℚ)/10000000000),((869063422190972166627001313291596060802858513029299108123509:ℚ)/23848211709989404678344726562500000000000000000000000000000000),((3320108098860513875650847:ℚ)/11552000000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((220590191:ℚ)/312500000),((7146406049:ℚ)/10000000000),((-86503278637:ℚ)/108225000000),((-606770573:ℚ)/849218750),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((3796327213:ℚ)/10000000000),((21344229077169404377573644189649544516113259018631587760709:ℚ)/585647667715814208984375000000000000000000000000000000000000),((13285238454086608055535863:ℚ)/46208000000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7088596249:ℚ)/10000000000),((7176114639:ℚ)/10000000000),((-86889490307:ℚ)/108700000000),((-19505788747:ℚ)/27293750000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((3689402813:ℚ)/10000000000),((21796450004759368585335794686757607429759070179321631283856461:ℚ)/597991578858436694335937500000000000000000000000000000000000000),((13290045653134941954012823:ℚ)/46208000000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4367:ℚ)/6400),((8753:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((7118306189:ℚ)/10000000000),((3595484433:ℚ)/5000000000),((-43541297629:ℚ)/54587500000),((-19594918567:ℚ)/27353125000),((483754929:ℚ)/500000000),((9681285961:ℚ)/10000000000),((639018949:ℚ)/2500000000),((715887347:ℚ)/2000000000),((440223366429362954749855708634864424134959549849602038155603:ℚ)/12170082298133916410446166992187500000000000000000000000000000),((3323112420131559976027207:ℚ)/11552000000000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((4367:ℚ)/6400) ((8753:ℚ)/12800) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((8753:ℚ)/12800),((2193:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((1426632217:ℚ)/2000000000),((7205823047:ℚ)/10000000000),((-87275699611:ℚ)/109412500000),((-3927896651:ℚ)/5482500000),((4834485079:ℚ)/5000000000),((1935019717:ℚ)/2000000000),((2580203419:ℚ)/10000000000),((1761612109:ℚ)/5000000000),((7417680150326063574717090729666620226466771936465099696098919:ℚ)/205048632105246446800231933593750000000000000000000000000000000),((13294853993050806286970567:ℚ)/46208000000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((8753:ℚ)/12800) ((2193:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2193:ℚ)/3200),((8791:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((3574007967:ℚ)/5000000000),((3610338591:ℚ)/5000000000),((-43734401683:ℚ)/54825000000),((-9842023901:ℚ)/13735937500),((9662900309:ℚ)/10000000000),((9668970163:ℚ)/10000000000),((520776989:ℚ)/2000000000),((3466138981:ℚ)/10000000000),((19997347367869341199156877193113375739290838712368762168031709:ℚ)/552751597506496051025390625000000000000000000000000000000000000),((3324314647676480741431303:ℚ)/11552000000000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((2193:ℚ)/3200) ((8791:ℚ)/12800) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((8791:ℚ)/12800),((881:ℚ)/1280),((-13:ℚ)/16),((-3:ℚ)/4),((3581435367:ℚ)/5000000000),((7235531273:ℚ)/10000000000),((-87661906549:ℚ)/109887500000),((-9864306101:ℚ)/13765625000),((4828444327:ℚ)/5000000000),((4831450157:ℚ)/5000000000),((2627133759:ℚ)/10000000000),((3408137113:ℚ)/10000000000),((3638897252535907011127324098754467345911105552870684739548923:ℚ)/100576551181255537223815917968750000000000000000000000000000000),((13299663473812692285850727:ℚ)/46208000000000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((8791:ℚ)/12800) ((881:ℚ)/1280) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((881:ℚ)/1280),((8829:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((7177725487:ℚ)/10000000000),((7250385319:ℚ)/10000000000),((-87855009147:ℚ)/110125000000),((-19773176461:ℚ)/27590625000),((301591713:ℚ)/312500000),((9656888659:ℚ)/10000000000),((2649962557:ℚ)/10000000000),((83729273:ℚ)/250000000),((159662014430857590034340398504140279099040347349116381590629:ℚ)/4412638669135726243257522583007812500000000000000000000000000),((13302068642206584372657543:ℚ)/46208000000000000000000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((881:ℚ)/1280) ((8829:ℚ)/12800) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((8829:ℚ)/12800),((553:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((224768131:ℚ)/312500000),((3632619661:ℚ)/5000000000),((-44024055593:ℚ)/55181250000),((-619304393:ℚ)/864062500),((1205629803:ℚ)/1250000000),((9650934821:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((822297119:ℚ)/2500000000),((77200574429269564910065868460643473597537334267909886413:ℚ)/2133475161527667939662933349609375000000000000000000000000),((3326118524052209865762623:ℚ)/11552000000000000000000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((8829:ℚ)/12800) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7207434851:ℚ)/10000000000),((3647473597:ℚ)/5000000000),((-44217156761:ℚ)/55300000000),((-19862304553:ℚ)/27768750000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3228133059:ℚ)/10000000000),((1320826358257680457566480114756855779969574886305514627884103:ℚ)/36223094954013378906250000000000000000000000000000000000000000),((3327321465054582550755167:ℚ)/11552000000000000000000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((7237144027:ℚ)/10000000000),((7324654893:ℚ)/10000000000),((-88820513609:ℚ)/111075000000),((-19951432081:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((38781857:ℚ)/125000000),((224917259919839126319160143227553664043458978339746738893149:ℚ)/6167716373434219741821289062500000000000000000000000000000000),((13314098766468360674380687:ℚ)/46208000000000000000000000)⟩
theorem valid15 : Valid source12 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source12 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((3633426509:ℚ)/5000000000),((367718121:ℚ)/500000000),((-4460335573:ℚ)/5577500000),((-10020279527:ℚ)/14003125000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((2971840491:ℚ)/10000000000),((1985288576988304647230635553203534103142305593590443009179:ℚ)/54436306504063025146484375000000000000000000000000000000000),((33297282037751385059983:ℚ)/115520000000000000000000)⟩
theorem valid16 : Valid source12 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source12 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-13:ℚ)/16),((-3:ℚ)/4),((1824140457:ℚ)/2500000000),((3692034889:ℚ)/5000000000),((-44796453557:ℚ)/56012500000),((-5032421371:ℚ)/7031250000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((2835299729:ℚ)/10000000000),((88021234305790758471222640158717469081158733379283611:ℚ)/2413334100750088691711425781250000000000000000000000000),((3330932001645226370908823:ℚ)/11552000000000000000000000)⟩
theorem valid17 : Valid source12 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source12 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source12 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((915783807:ℚ)/1250000000),((1488696799:ℚ)/2000000000),((-18073058387:ℚ)/22500000000),((-2527351421:ℚ)/3545312500),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((673009573:ℚ)/2500000000),((235522316533601333860606712362061390837585477328092763029:ℚ)/6363178115844726562500000000000000000000000000000000000000),((533334472772147352663863:ℚ)/1848320000000000000000000)⟩
theorem valid18 : Valid source12 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((7385687183:ℚ)/10000000000),((187572439:ℚ)/250000000),((-2278441707:ℚ)/2836250000),((-20397061549:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2380444991:ℚ)/10000000000),((13491099173383568284794577274648354952720823018059686307:ℚ)/364498404766755676269531250000000000000000000000000000000),((8339375129421906419523:ℚ)/28880000000000000000000)⟩
theorem valid19 : Valid source12 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((465318951:ℚ)/625000000),((7621722797:ℚ)/10000000000),((-92682396361:ℚ)/114400000000),((-1285956853:ℚ)/1817187500),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2022412743:ℚ)/10000000000),((2736797382705163449152948622973758306947474427339416790997373:ℚ)/71912577050600000000000000000000000000000000000000000000000000),((37004883:ℚ)/128000000)⟩
theorem valid20 : Valid source12 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((1890983317:ℚ)/2500000000),((3870272807:ℚ)/5000000000),((-47113546491:ℚ)/58150000000),((-5232949951:ℚ)/7387500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((487307957:ℚ)/5000000000),((85028781037583053831757593708029440717015311621063702382951:ℚ)/2235645334106066894531250000000000000000000000000000000000000),((37004883:ℚ)/128000000)⟩
theorem valid21 : Valid source12 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-13:ℚ)/16),((-3:ℚ)/4),((1536552149:ℚ)/2000000000),((7978184437:ℚ)/10000000000),((-32438799227:ℚ)/39400000000),((-4257656447:ℚ)/6100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((3555898109142576200592624326879668760591527168127474996669:ℚ)/88901352915625000000000000000000000000000000000000000000000),((37004883:ℚ)/128000000)⟩
theorem valid22 : Valid source12 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((7920408451:ℚ)/10000000000),((8453437641:ℚ)/10000000000),((-103494689333:ℚ)/122000000000),((-22001225353:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1110041615647614279989046433554534271704819527006278583837:ℚ)/25430709375000000000000000000000000000000000000000000000000),((37004883:ℚ)/128000000)⟩
theorem valid23 : Valid source12 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((8395677857:ℚ)/10000000000),((5177104887:ℚ)/5000000000),((-64102363531:ℚ)/64800000000),((-23427033571:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((142136429971676937262390664015489423765770580781055391:ℚ)/2214337500000000000000000000000000000000000000000000000),((37004883:ℚ)/128000000)⟩
theorem valid24 : Valid source12 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((2059299877:ℚ)/2000000000),((2831023193:ℚ)/2000000000),(-1:ℚ),((-5825899631:ℚ)/11040000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((72273115446582095940491:ℚ)/1015680000000000000000000),((37004883:ℚ)/128000000)⟩
theorem valid25 : Valid source12 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet25 valid25
private theorem node1_3 :
    CellBound source12 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((4329:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source12 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4329:ℚ)/6400) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((4329:ℚ)/6400) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source12 nn0 nn1 Qcell ((1087:ℚ)/1600) ((8753:ℚ)/12800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source12 nn0 nn1 Qcell ((4329:ℚ)/6400) ((8753:ℚ)/12800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source12 nn0 nn1 Qcell ((8753:ℚ)/12800) ((8791:ℚ)/12800) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source12 nn0 nn1 Qcell ((8791:ℚ)/12800) ((8829:ℚ)/12800) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source12 nn0 nn1 Qcell ((8753:ℚ)/12800) ((8829:ℚ)/12800) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source12 nn0 nn1 Qcell ((4329:ℚ)/6400) ((8829:ℚ)/12800) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((8829:ℚ)/12800) :=
  cell_join node0_6 node6_13
private theorem node14_16 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source12 nn0 nn1 Qcell ((8829:ℚ)/12800) ((2231:ℚ)/3200) :=
  cell_join leaf13 node14_16
private theorem node17_19 :
    CellBound source12 nn0 nn1 Qcell ((4481:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source12 nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf16 node17_19
private theorem node13_19 :
    CellBound source12 nn0 nn1 Qcell ((8829:ℚ)/12800) ((2269:ℚ)/3200) :=
  cell_join node13_16 node16_19
private theorem node20_22 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf20 leaf21
private theorem node19_22 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf19 node20_22
private theorem node22_24 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf22 leaf23
private theorem node24_26 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf24 leaf25
private theorem node22_26 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node22_24 node24_26
private theorem node19_26 :
    CellBound source12 nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node19_22 node22_26
private theorem node13_26 :
    CellBound source12 nn0 nn1 Qcell ((8829:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node13_19 node19_26
private theorem node0_26 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_13 node13_26
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_26
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25]
theorem packet_count : packets.length = 26 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC04
#check @N11Formalization.C450Source12GroupedC04.bound
#print axioms N11Formalization.C450Source12GroupedC04.valid0
#print axioms N11Formalization.C450Source12GroupedC04.valid1
#print axioms N11Formalization.C450Source12GroupedC04.valid2
#print axioms N11Formalization.C450Source12GroupedC04.valid3
#print axioms N11Formalization.C450Source12GroupedC04.valid4
#print axioms N11Formalization.C450Source12GroupedC04.valid5
#print axioms N11Formalization.C450Source12GroupedC04.valid6
#print axioms N11Formalization.C450Source12GroupedC04.valid7
#print axioms N11Formalization.C450Source12GroupedC04.valid8
#print axioms N11Formalization.C450Source12GroupedC04.valid9
#print axioms N11Formalization.C450Source12GroupedC04.valid10
#print axioms N11Formalization.C450Source12GroupedC04.valid11
#print axioms N11Formalization.C450Source12GroupedC04.valid12
#print axioms N11Formalization.C450Source12GroupedC04.valid13
#print axioms N11Formalization.C450Source12GroupedC04.valid14
#print axioms N11Formalization.C450Source12GroupedC04.valid15
#print axioms N11Formalization.C450Source12GroupedC04.valid16
#print axioms N11Formalization.C450Source12GroupedC04.valid17
#print axioms N11Formalization.C450Source12GroupedC04.valid18
#print axioms N11Formalization.C450Source12GroupedC04.valid19
#print axioms N11Formalization.C450Source12GroupedC04.valid20
#print axioms N11Formalization.C450Source12GroupedC04.valid21
#print axioms N11Formalization.C450Source12GroupedC04.valid22
#print axioms N11Formalization.C450Source12GroupedC04.valid23
#print axioms N11Formalization.C450Source12GroupedC04.valid24
#print axioms N11Formalization.C450Source12GroupedC04.valid25
#print axioms N11Formalization.C450Source12GroupedC04.bound
#print axioms N11Formalization.C450Source12GroupedC04.endpoint_checks
