import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC04
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨((-13:ℚ)/16),((-3:ℚ)/4)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-13:ℚ)/16),((-3:ℚ)/4),((6436386041:ℚ)/10000000000),((6726578219:ℚ)/10000000000),((-82325516847:ℚ)/99200000000),((-17869158123:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1121363041:ℚ)/2000000000),((1811786369589224635151926025129302272032214363952029748907197:ℚ)/64727596851200000000000000000000000000000000000000000000000000),((53522170122195700558194797:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((1334803889:ℚ)/2000000000),((1711347557:ℚ)/2500000000),((-20967518241:ℚ)/25750000000),((-3716411667:ℚ)/5245000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2493966421:ℚ)/5000000000),((770506441763478552311733970458597171929952509638012255831099:ℚ)/29356393640795898437500000000000000000000000000000000000000000),((3349457805017469203824373:ℚ)/14440000000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-13:ℚ)/16),((-3:ℚ)/4),((169820813:ℚ)/250000000),((6964200029:ℚ)/10000000000),((-85414600377:ℚ)/104900000000),((-157820813:ℚ)/222500000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((1162655051:ℚ)/2500000000),((374746178283851493026539610585767411195830818936252748262043:ℚ)/14286521657389062500000000000000000000000000000000000000000000),((53660644271481033414642557:ℚ)/231040000000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-13:ℚ)/16),((-3:ℚ)/4),((1727910837:ℚ)/2500000000),((7023604139:ℚ)/10000000000),((-28728951269:ℚ)/35600000000),((-4823732511:ℚ)/6734375000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2144463947:ℚ)/5000000000),((15610859468663092593095024269908319406237582347252330665797:ℚ)/613855061292187500000000000000000000000000000000000000000000),((53695365723541883389873517:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((3485523979:ℚ)/5000000000),((3541503869:ℚ)/5000000000),((-43479550297:ℚ)/53875000000),((-9736571937:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((409693001:ℚ)/1000000000),((29368421275937934070762342855725870934921024203270041499751987:ℚ)/1154784524082995605468750000000000000000000000000000000000000000),((13432532088618232559009197:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((7030452049:ℚ)/10000000000),((889088669:ℚ)/1250000000),((-10918152697:ℚ)/13587500000),((-19651356147:ℚ)/27293750000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((389604163:ℚ)/1000000000),((468055948306407657193490598009320735109283528318106181442867:ℚ)/18687236839326146697998046875000000000000000000000000000000000),((839805079926076115366497:ℚ)/3610000000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((1412030781:ℚ)/2000000000),((3571205421:ℚ)/5000000000),((-43865670473:ℚ)/54587500000),((-30605367:ℚ)/42500000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((379182321:ℚ)/1000000000),((1839899531935676591431323438029296607821351177196918550803:ℚ)/73450961216452026367187500000000000000000000000000000000000),((13441233043145912315865357:ℚ)/57760000000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-13:ℚ)/16),((-3:ℚ)/4),((1772463909:ℚ)/2500000000),((7172112213:ℚ)/10000000000),((-88117458769:ℚ)/109650000000),((-4957391727:ℚ)/6882812500),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((1842402531:ℚ)/5000000000),((40053150179371587699518755108140727567207238089212308886647611:ℚ)/1598813294571128320312500000000000000000000000000000000000000000),((53782349529220346814557613:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((1779889311:ℚ)/2500000000),((7201813463:ℚ)/10000000000),((-88503575019:ℚ)/110125000000),((-4979667933:ℚ)/6912500000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3574735251:ℚ)/10000000000),((142754445042063311150576781452859009511094684673037540715727:ℚ)/5697837120011711120605468750000000000000000000000000000000000),((53799777183880452641272613:ℚ)/231040000000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((553:ℚ)/800),((8867:ℚ)/12800),((-13:ℚ)/16),((-3:ℚ)/4),((7149258731:ℚ)/10000000000),((1443332809:ℚ)/2000000000),((-17739326517:ℚ)/22120000000),((-20007776193:ℚ)/27709375000),((2409799777:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((673601917:ℚ)/2500000000),((865330537:ℚ)/2500000000),((1180851119136917749305651122889388195458215884418192203649489:ℚ)/47486567626066975000000000000000000000000000000000000000000000),((2152339794972963108236837:ℚ)/9241600000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((8867:ℚ)/12800) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8867:ℚ)/12800),((4443:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((716410943:ℚ)/1000000000),((1807878649:ℚ)/2500000000),((-22222422437:ℚ)/27709375000),((-668410943:ℚ)/925625000),((4816708251:ℚ)/5000000000),((9639199113:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((850814409:ℚ)/2500000000),((5439818161233968369514374122110886648180676687538022803878309:ℚ)/218741702621332174730300903320312500000000000000000000000000000),((3363575946174149693811277:ℚ)/14440000000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((8867:ℚ)/12800) ((4443:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4443:ℚ)/6400),((1781:ℚ)/2560),((-13:ℚ)/16),((-3:ℚ)/4),((7178960099:ℚ)/10000000000),((7246365119:ℚ)/10000000000),((-29694248849:ℚ)/37025000000),((-1545913869:ℚ)/2140625000),((9627690243:ℚ)/10000000000),((9633416507:ℚ)/10000000000),((2737309683:ℚ)/10000000000),((3344225103:ℚ)/10000000000),((444230501558768491477329919732558381307744973794589923478137:ℚ)/17861898121268261718750000000000000000000000000000000000000000),((53825937979013561076714197:ℚ)/231040000000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((4443:ℚ)/6400) ((1781:ℚ)/2560) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1781:ℚ)/2560),((2231:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((3596905369:ℚ)/5000000000),((7261215613:ℚ)/10000000000),((-89275802969:ℚ)/111312500000),((-10070716107:ℚ)/13943750000),((2405504993:ℚ)/2500000000),((1203461281:ℚ)/1250000000),((551641531:ℚ)/2000000000),((656834457:ℚ)/2000000000),((66695920597810182162280972731242164845330941708702416458500291:ℚ)/2681581406625204181671142578125000000000000000000000000000000000),((53834663394403275386324413:ℚ)/231040000000000000000000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((1781:ℚ)/2560) ((2231:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((1802165337:ℚ)/2500000000),((1822729129:ℚ)/2500000000),((-22415478677:ℚ)/27887500000),((-5046496011:ℚ)/7001562500),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((20144013:ℚ)/62500000),((2728417323683303786172236802042345151409082133139687872820367:ℚ)/108872613008126050292968750000000000000000000000000000000000000),((3365757621986598655338157:ℚ)/14440000000000000000000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-13:ℚ)/16),((-3:ℚ)/4),((90479531:ℚ)/125000000),((1464123461:ℚ)/2000000000),((-18009604993:ℚ)/22405000000),((-84479531:ℚ)/117187500),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((774323239:ℚ)/2500000000),((6881790807090811420543106044184389210499821037564467:ℚ)/274583791018676757812500000000000000000000000000000000),((2154783632432556427547917:ℚ)/9241600000000000000000000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-13:ℚ)/16),((-3:ℚ)/4),((3634031749:ℚ)/5000000000),((3675158991:ℚ)/5000000000),((-45217066883:ℚ)/56250000000),((-10182095247:ℚ)/14121875000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((2966396513:ℚ)/10000000000),((189788765198412447272066733555990942953586907417238917276953011:ℚ)/7572007328796386718750000000000000000000000000000000000000000000),((13471767493136562236252037:ℚ)/57760000000000000000000000)⟩
theorem valid15 : Valid tenth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-13:ℚ)/16),((-3:ℚ)/4),((7297764401:ℚ)/10000000000),((7380018549:ℚ)/10000000000),((-90820241137:ℚ)/112975000000),((-20453293203:ℚ)/28362500000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((2829637917:ℚ)/10000000000),((2907548407094112595919419950172208848410420847693358651732747:ℚ)/115994144936326073974609375000000000000000000000000000000000000),((53904559438043363464861677:ℚ)/231040000000000000000000000)⟩
theorem valid16 : Valid tenth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound tenth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-13:ℚ)/16),((-3:ℚ)/4),((7327465193:ℚ)/10000000000),((1859854839:ℚ)/2500000000),((-22898112907:ℚ)/28362500000),((-20542395579:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((2686121289:ℚ)/10000000000),((74162431095583675613219856645850238519441690810175181937257:ℚ)/2915987238134045410156250000000000000000000000000000000000000),((3371223080102519143842717:ℚ)/14440000000000000000000000)⟩
theorem valid17 : Valid tenth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-13:ℚ)/16),((-3:ℚ)/4),((1846716611:ℚ)/2500000000),((3779109853:ℚ)/5000000000),((-46568428089:ℚ)/57200000000),((-5180149833:ℚ)/7268750000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((474771143:ℚ)/2000000000),((3760972296333392505256919493665973500891107932989416018671929:ℚ)/143825154101200000000000000000000000000000000000000000000000000),((13502428160514593969066093:ℚ)/57760000000000000000000000)⟩
theorem valid18 : Valid tenth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-13:ℚ)/16),((-3:ℚ)/4),((7505667659:ℚ)/10000000000),((1919254609:ℚ)/2500000000),((-23670309917:ℚ)/29075000000),((-7025667659:ℚ)/9850000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((788603589:ℚ)/5000000000),((38949317223969471858259666988988261583100738866750311893727:ℚ)/1490430222737377929687500000000000000000000000000000000000000),((29935967:ℚ)/128000000)⟩
theorem valid19 : Valid tenth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-13:ℚ)/16),((-3:ℚ)/4),((3812233613:ℚ)/5000000000),((7914611341:ℚ)/10000000000),((-97769947433:ℚ)/118200000000),((-10716700839:ℚ)/15250000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((51901619764838474436772960355990556159158621675950640155061:ℚ)/1888789399650000000000000000000000000000000000000000000000000),((29935967:ℚ)/128000000)⟩
theorem valid20 : Valid tenth packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-13:ℚ)/16),((-3:ℚ)/4),((3931030863:ℚ)/5000000000),((2097445199:ℚ)/2500000000),((-25986787587:ℚ)/30500000000),((-1230343621:ℚ)/1800000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((430622067584675180677441772394014452264279154226764221433:ℚ)/14363641406250000000000000000000000000000000000000000000000),((29935967:ℚ)/128000000)⟩
theorem valid21 : Valid tenth packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-13:ℚ)/16),((-3:ℚ)/4),((8337234093:ℚ)/10000000000),((2572574393:ℚ)/2500000000),((-10721155703:ℚ)/10800000000),((-23571702279:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((64982499494094743436373836838919430707503094726753711:ℚ)/1476225000000000000000000000000000000000000000000000000),((29935967:ℚ)/128000000)⟩
theorem valid22 : Valid tenth packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-13:ℚ)/16),((-3:ℚ)/4),((10237759747:ℚ)/10000000000),((7045452061:ℚ)/5000000000),(-1:ℚ),((-9757759747:ℚ)/18400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((4106611596441778352105807:ℚ)/84640000000000000000000000),((29935967:ℚ)/128000000)⟩
theorem valid23 : Valid tenth packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet23 valid23
private theorem node1_3 :
    CellBound tenth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound tenth nn0 nn1 Qcell ((431:ℚ)/640) ((4367:ℚ)/6400) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((4367:ℚ)/6400) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((4367:ℚ)/6400) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound tenth nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound tenth nn0 nn1 Qcell ((4367:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound tenth nn0 nn1 Qcell ((8867:ℚ)/12800) ((1781:ℚ)/2560) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((1781:ℚ)/2560) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound tenth nn0 nn1 Qcell ((4367:ℚ)/6400) ((1781:ℚ)/2560) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((1781:ℚ)/2560) :=
  cell_join node0_6 node6_12
private theorem node13_15 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound tenth nn0 nn1 Qcell ((1781:ℚ)/2560) ((45:ℚ)/64) :=
  cell_join leaf12 node13_15
private theorem node16_18 :
    CellBound tenth nn0 nn1 Qcell ((4519:ℚ)/6400) ((143:ℚ)/200) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf15 node16_18
private theorem node12_18 :
    CellBound tenth nn0 nn1 Qcell ((1781:ℚ)/2560) ((143:ℚ)/200) :=
  cell_join node12_15 node15_18
private theorem node19_21 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf18 node19_21
private theorem node22_24 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf22 leaf23
private theorem node21_24 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf21 node22_24
private theorem node18_24 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node18_21 node21_24
private theorem node12_24 :
    CellBound tenth nn0 nn1 Qcell ((1781:ℚ)/2560) ((69:ℚ)/50) :=
  cell_join node12_18 node18_24
private theorem node0_24 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_12 node12_24
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_24
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23]
theorem packet_count : packets.length = 24 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC04
#check @N11Formalization.C450TenthGroupedC04.bound
#print axioms N11Formalization.C450TenthGroupedC04.valid0
#print axioms N11Formalization.C450TenthGroupedC04.valid1
#print axioms N11Formalization.C450TenthGroupedC04.valid2
#print axioms N11Formalization.C450TenthGroupedC04.valid3
#print axioms N11Formalization.C450TenthGroupedC04.valid4
#print axioms N11Formalization.C450TenthGroupedC04.valid5
#print axioms N11Formalization.C450TenthGroupedC04.valid6
#print axioms N11Formalization.C450TenthGroupedC04.valid7
#print axioms N11Formalization.C450TenthGroupedC04.valid8
#print axioms N11Formalization.C450TenthGroupedC04.valid9
#print axioms N11Formalization.C450TenthGroupedC04.valid10
#print axioms N11Formalization.C450TenthGroupedC04.valid11
#print axioms N11Formalization.C450TenthGroupedC04.valid12
#print axioms N11Formalization.C450TenthGroupedC04.valid13
#print axioms N11Formalization.C450TenthGroupedC04.valid14
#print axioms N11Formalization.C450TenthGroupedC04.valid15
#print axioms N11Formalization.C450TenthGroupedC04.valid16
#print axioms N11Formalization.C450TenthGroupedC04.valid17
#print axioms N11Formalization.C450TenthGroupedC04.valid18
#print axioms N11Formalization.C450TenthGroupedC04.valid19
#print axioms N11Formalization.C450TenthGroupedC04.valid20
#print axioms N11Formalization.C450TenthGroupedC04.valid21
#print axioms N11Formalization.C450TenthGroupedC04.valid22
#print axioms N11Formalization.C450TenthGroupedC04.valid23
#print axioms N11Formalization.C450TenthGroupedC04.bound
#print axioms N11Formalization.C450TenthGroupedC04.endpoint_checks
