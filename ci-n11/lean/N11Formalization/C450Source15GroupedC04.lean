import N11Formalization.C450Source15Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source15GroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source15Data
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((6580452323:ℚ)/10000000000),((1721054251:ℚ)/2500000000),((-20293705263:ℚ)/24800000000),((-17501356969:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5239514959:ℚ)/10000000000),((60152242126183045913517071884000413671649155948409450624577:ℚ)/1011368700800000000000000000000000000000000000000000000000000),((5543431435150981093211790927:ℚ)/14786560000000000000000000000)⟩
theorem valid0 : Valid source15 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source15 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((6818305081:ℚ)/10000000000),((3501558609:ℚ)/5000000000),((-41360261917:ℚ)/51500000000),((-18214915243:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4575320591:ℚ)/10000000000),((13045722897696174868188412244584711612708613050757446507386643:ℚ)/234851149126367187500000000000000000000000000000000000000000000),((5552236794297966007137023143:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid source15 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source15 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((216788183:ℚ)/312500000),((3531282649:ℚ)/5000000000),((-41746674437:ℚ)/52450000000),((-580364549:ℚ)/826953125),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((4207267743:ℚ)/10000000000),((2973443938993890263924231946394280497221449899909664147571171:ℚ)/55365005940669531250000000000000000000000000000000000000000000),((5426396154108633972461507:ℚ)/14440000000000000000000000)⟩
theorem valid2 : Valid source15 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source15 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((6996677993:ℚ)/10000000000),((443268053:ℚ)/625000000),((-5242484689:ℚ)/6615625000),((-18750033979:ℚ)/26581250000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((125356997:ℚ)/312500000),((1728694836837357451707044666647818538963177518063636892547759:ℚ)/32732819968712714576721191406250000000000000000000000000000000),((5558823643864213247085225287:ℚ)/14786560000000000000000000000)⟩
theorem valid3 : Valid source15 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source15 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((7026405517:ℚ)/10000000000),((7122012077:ℚ)/10000000000),((-84266157001:ℚ)/106325000000),((-18839216551:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((97750897:ℚ)/250000000),((7072308577027934672195908158495399726754561792906263430593791:ℚ)/133890179224244458007812500000000000000000000000000000000000000),((5561111497795106597556999407:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid source15 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source15 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source15 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((1764033171:ℚ)/2500000000),((1787933747:ℚ)/2500000000),((-21163138711:ℚ)/26700000000),((-4732099513:ℚ)/6704687500),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((761218333:ℚ)/2000000000),((200907413098021669150613631823836917176137227395825688548921:ℚ)/3802842571842480468750000000000000000000000000000000000000000),((347712432759985151925863983:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid source15 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source15 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-13:ℚ)/16),((-3:ℚ)/4),((14171719:ℚ)/20000000),((7181457587:ℚ)/10000000000),((-12148421233:ℚ)/15325000000),((-38035157:ℚ)/53875000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1849687647:ℚ)/5000000000),((862494635880865916939409231425497234057266641216521849583:ℚ)/16322851964232254028320312500000000000000000000000000000000),((22262743693737353314343:ℚ)/59146240000000000000000)⟩
theorem valid6 : Valid source15 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source15 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source15 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((431:ℚ)/640),((8639:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((444724123:ℚ)/625000000),((7196318771:ℚ)/10000000000),((-85232144023:ℚ)/107750000000),((-2388344738:ℚ)/3374609375),((4856560387:ℚ)/5000000000),((9719670101:ℚ)/10000000000),((9604357:ℚ)/40000000),((448704879:ℚ)/1250000000),((46902576191966027935836612479223445887346660234037121473489539:ℚ)/894975622563403320312500000000000000000000000000000000000000000),((21745238506848053401892327:ℚ)/57760000000000000000000000)⟩
theorem valid7 : Valid source15 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source15 nn0 nn1 Qcell ((431:ℚ)/640) ((8639:ℚ)/12800) :=
  cell_of_packet source15 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((8639:ℚ)/12800),((4329:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7130449073:ℚ)/10000000000),((3605589939:ℚ)/5000000000),((-805899419:ℚ)/1018750000),((-19151347219:ℚ)/27056250000),((2426658193:ℚ)/2500000000),((9713120779:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((3533550661:ℚ)/10000000000),((405666476976739519034330844624096524868658161142529988949:ℚ)/7739948510172557830810546875000000000000000000000000000000),((5567924190143900153894359927:ℚ)/14786560000000000000000000000)⟩
theorem valid8 : Valid source15 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source15 nn0 nn1 Qcell ((8639:ℚ)/12800) ((4329:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4329:ℚ)/6400),((8677:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((7145312093:ℚ)/10000000000),((1806510227:ℚ)/2500000000),((-1646510227:ℚ)/2081250000),((-19195936279:ℚ)/27115625000),((9700205687:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((306851119:ℚ)/1250000000),((3476596403:ℚ)/10000000000),((24707306615554269929032740428709600819489045188306719636573:ℚ)/471356451144099426269531250000000000000000000000000000000000),((5569067215842255113762459087:ℚ)/14786560000000000000000000000)⟩
theorem valid9 : Valid source15 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source15 nn0 nn1 Qcell ((4329:ℚ)/6400) ((8677:ℚ)/12800) :=
  cell_of_packet source15 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8677:ℚ)/12800),((1087:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((1790043757:ℚ)/2500000000),((7240901863:ℚ)/10000000000),((-85811724219:ℚ)/108462500000),((-4810131271:ℚ)/6793750000),((9693839119:ℚ)/10000000000),((2425051423:ℚ)/2500000000),((2480870833:ℚ)/10000000000),((3418732919:ℚ)/10000000000),((493967226830952380026122048967254595980453345086659378779798949:ℚ)/9422755817392408166503906250000000000000000000000000000000000000),((348138133438139936808346287:ℚ)/924160000000000000000000000)⟩
theorem valid10 : Valid source15 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source15 nn0 nn1 Qcell ((8677:ℚ)/12800) ((1087:ℚ)/1600) :=
  cell_of_packet source15 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1087:ℚ)/1600),((1743:ℚ)/2560),((-13:ℚ)/16),((-3:ℚ)/4),((179375947:ℚ)/250000000),((7255762743:ℚ)/10000000000),((-86004915659:ℚ)/108700000000),((-482127841:ℚ)/680859375),((9687532673:ℚ)/10000000000),((2423459781:ℚ)/2500000000),((2506424897:ℚ)/10000000000),((83997829:ℚ)/250000000),((182653999454319597640344794082512981144118198842921149061589923:ℚ)/3483897617878256250000000000000000000000000000000000000000000000),((3482095592276895945935167:ℚ)/9241600000000000000000000)⟩
theorem valid11 : Valid source15 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source15 nn0 nn1 Qcell ((1087:ℚ)/1600) ((1743:ℚ)/2560) :=
  cell_of_packet source15 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1743:ℚ)/2560),((4367:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((898737581:ℚ)/1250000000),((1817655887:ℚ)/2500000000),((-21549526531:ℚ)/27234375000),((-2416212743:ℚ)/3411718750),((2420321489:ℚ)/2500000000),((4843766339:ℚ)/5000000000),((2531487941:ℚ)/10000000000),((1650042967:ℚ)/5000000000),((876683662818075570285549255790121692193326398574544206454549:ℚ)/16719995201720367372035980224609375000000000000000000000000000),((87070244589775122716868143:ℚ)/231040000000000000000000000)⟩
theorem valid12 : Valid source15 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source15 nn0 nn1 Qcell ((1743:ℚ)/2560) ((4367:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((7204763333:ℚ)/10000000000),((7300344937:ℚ)/10000000000),((-86584484181:ℚ)/109175000000),((-19374289999:ℚ)/27412500000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((647839069:ℚ)/2000000000),((517005420128683054893140976803189122995021236641287616533309851:ℚ)/9778379564823825366210937500000000000000000000000000000000000000),((5574829655590484276539470207:ℚ)/14786560000000000000000000000)⟩
theorem valid13 : Valid source15 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source15 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-13:ℚ)/16),((-3:ℚ)/4),((7234488457:ℚ)/10000000000),((458129127:ℚ)/625000000),((-319745803:ℚ)/403125000),((-19463465371:ℚ)/27531250000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((1556986599:ℚ)/5000000000),((466807786310381831375241356603165885798290038396162253:ℚ)/8827719587373733520507812500000000000000000000000000000),((5577114523909472623211431687:ℚ)/14786560000000000000000000000)⟩
theorem valid14 : Valid source15 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source15 nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet source15 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((1452842651:ℚ)/2000000000),((3679893419:ℚ)/5000000000),((-43678614447:ℚ)/55062500000),((-3910527953:ℚ)/5530000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1491839527:ℚ)/5000000000),((37667677195781706212809467424492357677243780657983335561911:ℚ)/712229640001463890075683593750000000000000000000000000000000),((223175958679337938536403263:ℚ)/591462400000000000000000000)⟩
theorem valid15 : Valid source15 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source15 nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7293937733:ℚ)/10000000000),((46184421:ℚ)/62500000),((-548397473:ℚ)/691250000),((-19641813199:ℚ)/27768750000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((1423808077:ℚ)/5000000000),((179623392125715447603032024020244644388232728014882937069:ℚ)/3395915151938754272460937500000000000000000000000000000000),((5581682985206565686400545407:ℚ)/14786560000000000000000000000)⟩
theorem valid16 : Valid source15 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet source15 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((7323661893:ℚ)/10000000000),((7419227599:ℚ)/10000000000),((-29376652929:ℚ)/37025000000),((-19730985679:ℚ)/27887500000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((2704913457:ℚ)/10000000000),((5220421739037194219306780173432742130799515199959871594860359:ℚ)/98683461974947515869140625000000000000000000000000000000000000),((5583966578665332669386575487:ℚ)/14786560000000000000000000000)⟩
theorem valid17 : Valid source15 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source15 nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet source15 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-13:ℚ)/16),((-3:ℚ)/4),((7353385741:ℚ)/10000000000),((7478667247:ℚ)/10000000000),((-88902674211:ℚ)/111550000000),((-19820157223:ℚ)/28125000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2554457731:ℚ)/10000000000),((147536276987660616026580783089307422637057315875858217829:ℚ)/2744945934054565429687500000000000000000000000000000000000),((5588632421541795240779217903:ℚ)/14786560000000000000000000000)⟩
theorem valid18 : Valid source15 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source15 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source15 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((1482566503:ℚ)/2000000000),((7597543317:ℚ)/10000000000),((-90448063121:ℚ)/112500000000),((-307669193:ℚ)/440000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((2223917887:ℚ)/10000000000),((6628901587517226921405570202134098354243544983339718149071:ℚ)/119641113281250000000000000000000000000000000000000000000000),((223918505696628380528033767:ℚ)/591462400000000000000000000)⟩
theorem valid19 : Valid source15 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source15 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((143:ℚ)/200),((591:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((7531722479:ℚ)/10000000000),((97941041:ℚ)/125000000),((-89941041:ℚ)/110000000),((-20355167437:ℚ)/29550000000),((4742306471:ℚ)/5000000000),((4779108393:ℚ)/5000000000),((806129637:ℚ)/2500000000),((83840289:ℚ)/625000000),((14185369240932258694666087846479781848963792674537213:ℚ)/242131776562500000000000000000000000000000000000000000),((5597754254384286757234406583:ℚ)/14786560000000000000000000000)⟩
theorem valid20 : Valid source15 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source15 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_of_packet source15 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-13:ℚ)/16),((-3:ℚ)/4),((3884744443:ℚ)/5000000000),((504563017:ℚ)/625000000),((-2013106407:ℚ)/2462500000),((-10534233329:ℚ)/15250000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((20277924231719684287908639718151989330044625846426343337:ℚ)/347270909826660156250000000000000000000000000000000000000),((387639789:ℚ)/1024000000)⟩
theorem valid21 : Valid source15 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source15 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((800723867:ℚ)/1000000000),((68387349:ℚ)/80000000),((-822475537:ℚ)/976000000),((-2178171601:ℚ)/3240000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2442477123579306681328011253431332787680324458251132887:ℚ)/38124091929600000000000000000000000000000000000000000000),((387639789:ℚ)/1024000000)⟩
theorem valid22 : Valid source15 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source15 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source15 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((4241347117:ℚ)/5000000000),((1306208729:ℚ)/1250000000),((-5313571159:ℚ)/5400000000),((-11604041351:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1974486761831345851081050940894810511615918492414627:ℚ)/20503125000000000000000000000000000000000000000000000),((387639789:ℚ)/1024000000)⟩
theorem valid23 : Valid source15 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source15 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((10384083247:ℚ)/10000000000),((14251138049:ℚ)/10000000000),(-1:ℚ),((-28912249741:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((164940363993918154466372129:ℚ)/1523520000000000000000000000),((387639789:ℚ)/1024000000)⟩
theorem valid24 : Valid source15 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source15 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source15 nn0 nn1 packet24 valid24
private theorem node1_3 :
    CellBound source15 nn0 nn1 Qcell ((103:ℚ)/160) ((2117:ℚ)/3200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((2117:ℚ)/3200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source15 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4291:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source15 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4291:ℚ)/6400) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((4291:ℚ)/6400) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source15 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source15 nn0 nn1 Qcell ((4291:ℚ)/6400) ((4329:ℚ)/6400) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source15 nn0 nn1 Qcell ((8677:ℚ)/12800) ((1743:ℚ)/2560) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source15 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1743:ℚ)/2560) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source15 nn0 nn1 Qcell ((4291:ℚ)/6400) ((1743:ℚ)/2560) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((1743:ℚ)/2560) :=
  cell_join node0_6 node6_12
private theorem node13_15 :
    CellBound source15 nn0 nn1 Qcell ((4367:ℚ)/6400) ((881:ℚ)/1280) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source15 nn0 nn1 Qcell ((1743:ℚ)/2560) ((881:ℚ)/1280) :=
  cell_join leaf12 node13_15
private theorem node16_18 :
    CellBound source15 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source15 nn0 nn1 Qcell ((881:ℚ)/1280) ((2231:ℚ)/3200) :=
  cell_join leaf15 node16_18
private theorem node12_18 :
    CellBound source15 nn0 nn1 Qcell ((1743:ℚ)/2560) ((2231:ℚ)/3200) :=
  cell_join node12_15 node15_18
private theorem node19_21 :
    CellBound source15 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source15 nn0 nn1 Qcell ((2231:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf18 node19_21
private theorem node21_23 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf21 leaf22
private theorem node23_25 :
    CellBound source15 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf23 leaf24
private theorem node21_25 :
    CellBound source15 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node21_23 node23_25
private theorem node18_25 :
    CellBound source15 nn0 nn1 Qcell ((2231:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node18_21 node21_25
private theorem node12_25 :
    CellBound source15 nn0 nn1 Qcell ((1743:ℚ)/2560) ((69:ℚ)/50) :=
  cell_join node12_18 node18_25
private theorem node0_25 :
    CellBound source15 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_12 node12_25
theorem bound : CellBound source15 nn0 nn1 Qcell (31/50) (69/50) := node0_25
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24]
theorem packet_count : packets.length = 25 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source15GroupedC04
#check @N11Formalization.C450Source15GroupedC04.bound
#print axioms N11Formalization.C450Source15GroupedC04.valid0
#print axioms N11Formalization.C450Source15GroupedC04.valid1
#print axioms N11Formalization.C450Source15GroupedC04.valid2
#print axioms N11Formalization.C450Source15GroupedC04.valid3
#print axioms N11Formalization.C450Source15GroupedC04.valid4
#print axioms N11Formalization.C450Source15GroupedC04.valid5
#print axioms N11Formalization.C450Source15GroupedC04.valid6
#print axioms N11Formalization.C450Source15GroupedC04.valid7
#print axioms N11Formalization.C450Source15GroupedC04.valid8
#print axioms N11Formalization.C450Source15GroupedC04.valid9
#print axioms N11Formalization.C450Source15GroupedC04.valid10
#print axioms N11Formalization.C450Source15GroupedC04.valid11
#print axioms N11Formalization.C450Source15GroupedC04.valid12
#print axioms N11Formalization.C450Source15GroupedC04.valid13
#print axioms N11Formalization.C450Source15GroupedC04.valid14
#print axioms N11Formalization.C450Source15GroupedC04.valid15
#print axioms N11Formalization.C450Source15GroupedC04.valid16
#print axioms N11Formalization.C450Source15GroupedC04.valid17
#print axioms N11Formalization.C450Source15GroupedC04.valid18
#print axioms N11Formalization.C450Source15GroupedC04.valid19
#print axioms N11Formalization.C450Source15GroupedC04.valid20
#print axioms N11Formalization.C450Source15GroupedC04.valid21
#print axioms N11Formalization.C450Source15GroupedC04.valid22
#print axioms N11Formalization.C450Source15GroupedC04.valid23
#print axioms N11Formalization.C450Source15GroupedC04.valid24
#print axioms N11Formalization.C450Source15GroupedC04.bound
#print axioms N11Formalization.C450Source15GroupedC04.endpoint_checks
