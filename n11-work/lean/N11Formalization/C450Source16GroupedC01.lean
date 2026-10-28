import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC01
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨(-1:ℚ),((-15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((6721936741:ℚ)/10000000000),((3459375001:ℚ)/5000000000),(-1:ℚ),((-6081936741:ℚ)/6740000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4854493683:ℚ)/10000000000),((1957138245799193269108858533480379:ℚ)/28392250000000000000000000000000000),((111192699926524835416741:ℚ)/190000000000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((6840744337:ℚ)/10000000000),((3489062501:ℚ)/5000000000),(-1:ℚ),((-18602233011:ℚ)/20410000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((2254010361:ℚ)/5000000000),((2584333395739645434617759120643:ℚ)/38514062500000000000000000000000),((111427446426366488541741:ℚ)/190000000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),(-1:ℚ),((-15:ℚ)/16),((690014733:ℚ)/1000000000),((7037500003:ℚ)/10000000000),(-1:ℚ),((-1878044199:ℚ)/2060000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((1081289431:ℚ)/2500000000),((533156182721562696384794606803901:ℚ)/7956750000000000000000000000000000),((23507857675196485526351:ℚ)/40000000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((6959549807:ℚ)/10000000000),((3548437501:ℚ)/5000000000),(-1:ℚ),((-6319549807:ℚ)/6930000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((4134747091:ℚ)/10000000000),((15940605700450799374794856991291:ℚ)/238218750000000000000000000000000),((111897332507104482291741:ℚ)/190000000000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((7018951781:ℚ)/10000000000),((3563281251:ℚ)/5000000000),(-1:ℚ),((-19136855343:ℚ)/20885000000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((983922453:ℚ)/2500000000),((9002413741034995077544976740747703:ℚ)/136307257812500000000000000000000000),((336044657757526121875223:ℚ)/570000000000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((881081573:ℚ)/1250000000),((3578125001:ℚ)/5000000000),(-1:ℚ),((-2403244719:ℚ)/2622500000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((191624939:ℚ)/500000000),((141864378425974508191424883468929:ℚ)/2149220703125000000000000000000000),((112132472088000822916741:ℚ)/190000000000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1049:ℚ)/1600),((8411:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((3539176633:ℚ)/5000000000),((896386719:ℚ)/1250000000),(-1:ℚ),((-9657529899:ℚ)/10513750000),((9795878581:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((1011977397:ℚ)/5000000000),((931649173:ℚ)/2500000000),((1132663080452875522762747467102893:ℚ)/17271709228515625000000000000000000),((21035864523036844946303:ℚ)/35625000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8411:ℚ)/12800) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((8411:ℚ)/12800),((843:ℚ)/1280),(-1:ℚ),((-15:ℚ)/16),((7093203563:ℚ)/10000000000),((3592968751:ℚ)/5000000000),(-1:ℚ),((-6453203563:ℚ)/7025000000),((978862711:ℚ)/1000000000),((4897939293:ℚ)/5000000000),((2059717253:ℚ)/10000000000),((229534737:ℚ)/625000000),((606662288075186628846306529369049:ℚ)/9253242187500000000000000000000000),((112250091013580829166741:ℚ)/190000000000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((8411:ℚ)/12800) ((843:ℚ)/1280) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((843:ℚ)/1280),((8449:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7108053829:ℚ)/10000000000),((1800195313:ℚ)/2500000000),(-1:ℚ),((-19404161487:ℚ)/21122500000),((4890720817:ℚ)/5000000000),((1957725423:ℚ)/2000000000),((83782417:ℚ)/400000000),((3617744981:ℚ)/10000000000),((27415970381391779492412303872016553:ℚ)/418275005859375000000000000000000000),((28077228190038447819029:ℚ)/47500000000000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((843:ℚ)/1280) ((8449:ℚ)/12800) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((8449:ℚ)/12800),((2117:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((7122904067:ℚ)/10000000000),((7215625003:ℚ)/10000000000),(-1:ℚ),((-19448712201:ℚ)/21170000000),((9774321709:ℚ)/10000000000),((9781441639:ℚ)/10000000000),((425706267:ℚ)/2000000000),((712425729:ℚ)/2000000000),((18354944064046317288413875855192633:ℚ)/280105562500000000000000000000000000),((23656366884185041776351:ℚ)/40000000000000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((8449:ℚ)/12800) ((2117:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2117:ℚ)/3200),((8487:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((285510171:ℚ)/400000000),((7230468753:ℚ)/10000000000),(-1:ℚ),((-259910171:ℚ)/282900000),((9767266893:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((2161672951:ℚ)/10000000000),((3505668393:ℚ)/10000000000),((1092311706577426800768305526107:ℚ)/16673418750000000000000000000000),((71006261573576678454053:ℚ)/120000000000000000000000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((2117:ℚ)/3200) ((8487:ℚ)/12800) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((8487:ℚ)/12800),((16993:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((1430520891:ℚ)/2000000000),((1809472657:ℚ)/2500000000),(-1:ℚ),((-3907562673:ℚ)/4248250000),((1952752753:ℚ)/2000000000),((4883633449:ℚ)/5000000000),((435589041:ℚ)/2000000000),((3448322701:ℚ)/10000000000),((147318559023311487249958607767769:ℚ)/2255953507812500000000000000000000),((1479684249450669432311:ℚ)/2500000000000000000000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell ((8487:ℚ)/12800) ((16993:ℚ)/25600) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((16993:ℚ)/25600),((4253:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((3580014767:ℚ)/5000000000),((7245312503:ℚ)/10000000000),(-1:ℚ),((-9780044301:ℚ)/10632500000),((9760276751:ℚ)/10000000000),((976376377:ℚ)/1000000000),((438804929:ℚ)/2000000000),((3419303903:ℚ)/10000000000),((4613453822025586660791749580571787:ℚ)/70656285156250000000000000000000000),((23681142555572457401351:ℚ)/40000000000000000000000)⟩
theorem valid12 : Valid source16 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source16 nn0 nn1 Qcell ((16993:ℚ)/25600) ((4253:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4253:ℚ)/6400),((17031:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((3583727303:ℚ)/5000000000),((3626367189:ℚ)/5000000000),(-1:ℚ),((-3263727303:ℚ)/3548125000),((9756805797:ℚ)/10000000000),((2440069189:ℚ)/2500000000),((2209915701:ℚ)/10000000000),((3390046577:ℚ)/10000000000),((513690472367001322022448999733501:ℚ)/7868244384765625000000000000000000),((17765503163208099203357:ℚ)/30000000000000000000000)⟩
theorem valid13 : Valid source16 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source16 nn0 nn1 Qcell ((4253:ℚ)/6400) ((17031:ℚ)/25600) :=
  cell_of_packet source16 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((17031:ℚ)/25600),((341:ℚ)/512),(-1:ℚ),((-15:ℚ)/16),((717487967:ℚ)/1000000000),((7260156253:ℚ)/10000000000),(-1:ℚ),((-5749161:ℚ)/6250000),((195067017:ℚ)/200000000),((4878402901:ℚ)/5000000000),((1112811311:ℚ)/5000000000),((3360544489:ℚ)/10000000000),((31874416337792106019795659:ℚ)/488281250000000000000000000),((23693532977325735526351:ℚ)/40000000000000000000000)⟩
theorem valid14 : Valid source16 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source16 nn0 nn1 Qcell ((17031:ℚ)/25600) ((341:ℚ)/512) :=
  cell_of_packet source16 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((341:ℚ)/512),((17069:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((897788091:ℚ)/1250000000),((7267578127:ℚ)/10000000000),(-1:ℚ),((-2453364273:ℚ)/2667031250),((609369491:ℚ)/625000000),((1950670171:ℚ)/2000000000),((4482299:ℚ)/20000000),((1665395559:ℚ)/5000000000),((18571079347731072568727635495281907:ℚ)/284522227539062500000000000000000000),((450294847843766129557589:ℚ)/760000000000000000000000)⟩
theorem valid15 : Valid source16 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source16 nn0 nn1 Qcell ((341:ℚ)/512) ((17069:ℚ)/25600) :=
  cell_of_packet source16 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((17069:ℚ)/25600),((267:ℚ)/400),(-1:ℚ),((-15:ℚ)/16),((3594864889:ℚ)/5000000000),((3637500001:ℚ)/5000000000),(-1:ℚ),((-3274864889:ℚ)/3560000000),((4873244381:ℚ)/5000000000),((9749911861:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((3300779671:ℚ)/10000000000),((258475832838633722806450822500937:ℚ)/3960500000000000000000000000000000),((112603144330848191666741:ℚ)/190000000000000000000000)⟩
theorem valid16 : Valid source16 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source16 nn0 nn1 Qcell ((17069:ℚ)/25600) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((267:ℚ)/400),((17107:ℚ)/25600),(-1:ℚ),((-15:ℚ)/16),((3598577411:ℚ)/5000000000),((7282421877:ℚ)/10000000000),(-1:ℚ),((-9835732233:ℚ)/10691875000),((4871540757:ℚ)/5000000000),((9746488767:ℚ)/10000000000),((283959837:ℚ)/1250000000),((130820121:ℚ)/400000000),((55948460590042554568541832937699649:ℚ)/857371432617187500000000000000000000),((1351590944976624129297767:ℚ)/2280000000000000000000000)⟩
theorem valid17 : Valid source16 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((17107:ℚ)/25600) :=
  cell_of_packet source16 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((17107:ℚ)/25600),((8563:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((3602289929:ℚ)/5000000000),((911230469:ℚ)/1250000000),(-1:ℚ),((-9846869787:ℚ)/10703750000),((9739690061:ℚ)/10000000000),((9743081519:ℚ)/10000000000),((1143344217:ℚ)/5000000000),((1619976873:ℚ)/5000000000),((1168047503199085016459662732285977:ℚ)/17901603759765625000000000000000000),((7041375950784561857101:ℚ)/11875000000000000000000)⟩
theorem valid18 : Valid source16 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source16 nn0 nn1 Qcell ((17107:ℚ)/25600) ((8563:ℚ)/12800) :=
  cell_of_packet source16 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((8563:ℚ)/12800),((4291:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((901500611:ℚ)/1250000000),((3652343751:ℚ)/5000000000),(-1:ℚ),((-2464501833:ℚ)/2681875000),((1216619291:ℚ)/1250000000),((4869845033:ℚ)/5000000000),((1158107867:ℚ)/5000000000),((3209124031:ℚ)/10000000000),((294134703979165272348454618886379:ℚ)/4495283447265625000000000000000000),((338162682850339281250223:ℚ)/570000000000000000000000)⟩
theorem valid19 : Valid source16 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source16 nn0 nn1 Qcell ((8563:ℚ)/12800) ((4291:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((4291:ℚ)/6400),((8601:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((289074197:ℚ)/400000000),((1829882813:ℚ)/2500000000),(-1:ℚ),((-263474197:ℚ)/286700000),((1215785143:ℚ)/1250000000),((9732954333:ℚ)/10000000000),((2345108749:ℚ)/10000000000),((786647559:ℚ)/2500000000),((53627089971290399517152327677:ℚ)/819782812500000000000000000000),((28194945385882125944029:ℚ)/47500000000000000000000)⟩
theorem valid20 : Valid source16 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source16 nn0 nn1 Qcell ((4291:ℚ)/6400) ((8601:ℚ)/12800) :=
  cell_of_packet source16 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((8601:ℚ)/12800),((431:ℚ)/640),(-1:ℚ),((-15:ℚ)/16),((1448340987:ℚ)/2000000000),((3667187501:ℚ)/5000000000),(-1:ℚ),((-3961022961:ℚ)/4310000000),((607479381:ℚ)/625000000),((9726281149:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3082831289:ℚ)/10000000000),((47456656494154463695391419287837:ℚ)/725628906250000000000000000000000),((112838676992799219791741:ℚ)/190000000000000000000000)⟩
theorem valid21 : Valid source16 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source16 nn0 nn1 Qcell ((8601:ℚ)/12800) ((431:ℚ)/640) :=
  cell_of_packet source16 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((431:ℚ)/640),((8639:ℚ)/12800),(-1:ℚ),((-15:ℚ)/16),((7256554917:ℚ)/10000000000),((114831543:ℚ)/156250000),(-1:ℚ),((-19849664751:ℚ)/21597500000),((4856560387:ℚ)/5000000000),((9719670101:ℚ)/10000000000),((9604357:ℚ)/40000000),((3017769469:ℚ)/10000000000),((58472273544044606023839360822863:ℚ)/894271484375000000000000000000000),((330754630755640356827:ℚ)/556640625000000000000)⟩
theorem valid22 : Valid source16 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source16 nn0 nn1 Qcell ((431:ℚ)/640) ((8639:ℚ)/12800) :=
  cell_of_packet source16 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((8639:ℚ)/12800),((4329:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((908925609:ℚ)/1250000000),((3682031251:ℚ)/5000000000),(-1:ℚ),((-828925609:ℚ)/901875000),((2426658193:ℚ)/2500000000),((9713120779:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((2951318537:ℚ)/10000000000),((132926700731134101675498161818811:ℚ)/2033446289062500000000000000000000),((112956492458906569791741:ℚ)/190000000000000000000000)⟩
theorem valid23 : Valid source16 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source16 nn0 nn1 Qcell ((8639:ℚ)/12800) ((4329:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),(-1:ℚ),((-15:ℚ)/16),((18215637:ℚ)/25000000),((3696875001:ℚ)/5000000000),(-1:ℚ),((-49846911:ℚ)/54350000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((144169119:ℚ)/500000000),((182024130240665047486098298597:ℚ)/2769302343750000000000000000000),((339223022045305431250223:ℚ)/570000000000000000000000)⟩
theorem valid24 : Valid source16 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source16 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),(-1:ℚ),((-15:ℚ)/16),((3657977287:ℚ)/5000000000),((7423437503:ℚ)/10000000000),(-1:ℚ),((-10013931861:ℚ)/10917500000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((274261023:ℚ)/1000000000),((3670576168726291865902430076518159:ℚ)/55871159179687500000000000000000000),((23829941403232888651351:ℚ)/40000000000000000000000)⟩
theorem valid25 : Valid source16 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source16 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source16 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),(-1:ℚ),((-15:ℚ)/16),((3672827121:ℚ)/5000000000),((3726562501:ℚ)/5000000000),(-1:ℚ),((-3352827121:ℚ)/3655000000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((2594413209:ℚ)/10000000000),((274133980796479205804542957035843:ℚ)/4174695312500000000000000000000000),((113310135397755963541741:ℚ)/190000000000000000000000)⟩
theorem valid26 : Valid source16 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source16 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),(-1:ℚ),((-15:ℚ)/16),((7375353803:ℚ)/10000000000),((3756250001:ℚ)/5000000000),(-1:ℚ),((-20206061409:ℚ)/22120000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2437436711:ℚ)/10000000000),((362387242843710691554549912184313:ℚ)/5460875000000000000000000000000000),((113546061140761679166741:ℚ)/190000000000000000000000)⟩
theorem valid27 : Valid source16 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source16 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),(-1:ℚ),((-15:ℚ)/16),((929344077:ℚ)/1250000000),((7631250003:ℚ)/10000000000),(-1:ℚ),((-849344077:ℚ)/937500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((2089130467:ℚ)/10000000000),((3098769853395022411304571579581:ℚ)/45776367187500000000000000000000),((299721:ℚ)/500000)⟩
theorem valid28 : Valid source16 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source16 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),(-1:ℚ),((-15:ℚ)/16),((3776774517:ℚ)/5000000000),((7750000003:ℚ)/10000000000),(-1:ℚ),((-10370323551:ℚ)/11440000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((276545779:ℚ)/2500000000),((5523697158486047585484212152149897:ℚ)/81796000000000000000000000000000000),((299721:ℚ)/500000)⟩
theorem valid29 : Valid source16 packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet29 valid29
def packet30 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),(-1:ℚ),((-15:ℚ)/16),((767234391:ℚ)/1000000000),((8700000003:ℚ)/10000000000),(-1:ℚ),((-703234391:ℚ)/864000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((38591704788633544395634507621163:ℚ)/466560000000000000000000000000000),((299721:ℚ)/500000)⟩
theorem valid30 : Valid source16 packet30 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf30 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet30 valid30
def packet31 : Packet := ⟨((81:ℚ)/100),(1:ℚ),(-1:ℚ),((-15:ℚ)/16),((4311327761:ℚ)/5000000000),((5300000001:ℚ)/5000000000),(-1:ℚ),((-11973983283:ℚ)/16000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((43765463193035640122870086713780419:ℚ)/480000000000000000000000000000000000),((299721:ℚ)/500000)⟩
theorem valid31 : Valid source16 packet31 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf31 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet31 valid31
def packet32 : Packet := ⟨(1:ℚ),((69:ℚ)/50),(-1:ℚ),((-15:ℚ)/16),((10523101067:ℚ)/10000000000),((14400000003:ℚ)/10000000000),(-1:ℚ),((-9883101067:ℚ)/14720000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1415937139664593313292293:ℚ)/13542400000000000000000000),((299721:ℚ)/500000)⟩
theorem valid32 : Valid source16 packet32 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf32 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet32 valid32
private theorem node0_2 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source16 nn0 nn1 Qcell ((2041:ℚ)/3200) ((2079:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source16 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source16 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source16 nn0 nn1 Qcell ((2079:ℚ)/3200) ((843:ℚ)/1280) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((843:ℚ)/1280) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source16 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source16 nn0 nn1 Qcell ((2117:ℚ)/3200) ((16993:ℚ)/25600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source16 nn0 nn1 Qcell ((843:ℚ)/1280) ((16993:ℚ)/25600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source16 nn0 nn1 Qcell ((16993:ℚ)/25600) ((17031:ℚ)/25600) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound source16 nn0 nn1 Qcell ((17031:ℚ)/25600) ((17069:ℚ)/25600) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound source16 nn0 nn1 Qcell ((16993:ℚ)/25600) ((17069:ℚ)/25600) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound source16 nn0 nn1 Qcell ((843:ℚ)/1280) ((17069:ℚ)/25600) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((17069:ℚ)/25600) :=
  cell_join node0_8 node8_16
private theorem node16_18 :
    CellBound source16 nn0 nn1 Qcell ((17069:ℚ)/25600) ((17107:ℚ)/25600) :=
  cell_join leaf16 leaf17
private theorem node18_20 :
    CellBound source16 nn0 nn1 Qcell ((17107:ℚ)/25600) ((4291:ℚ)/6400) :=
  cell_join leaf18 leaf19
private theorem node16_20 :
    CellBound source16 nn0 nn1 Qcell ((17069:ℚ)/25600) ((4291:ℚ)/6400) :=
  cell_join node16_18 node18_20
private theorem node20_22 :
    CellBound source16 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_join leaf20 leaf21
private theorem node22_24 :
    CellBound source16 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_join leaf22 leaf23
private theorem node20_24 :
    CellBound source16 nn0 nn1 Qcell ((4291:ℚ)/6400) ((4329:ℚ)/6400) :=
  cell_join node20_22 node22_24
private theorem node16_24 :
    CellBound source16 nn0 nn1 Qcell ((17069:ℚ)/25600) ((4329:ℚ)/6400) :=
  cell_join node16_20 node20_24
private theorem node24_26 :
    CellBound source16 nn0 nn1 Qcell ((4329:ℚ)/6400) ((4367:ℚ)/6400) :=
  cell_join leaf24 leaf25
private theorem node26_28 :
    CellBound source16 nn0 nn1 Qcell ((4367:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join leaf26 leaf27
private theorem node24_28 :
    CellBound source16 nn0 nn1 Qcell ((4329:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join node24_26 node26_28
private theorem node28_30 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf28 leaf29
private theorem node31_33 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf31 leaf32
private theorem node30_33 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf30 node31_33
private theorem node28_33 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node28_30 node30_33
private theorem node24_33 :
    CellBound source16 nn0 nn1 Qcell ((4329:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node24_28 node28_33
private theorem node16_33 :
    CellBound source16 nn0 nn1 Qcell ((17069:ℚ)/25600) ((69:ℚ)/50) :=
  cell_join node16_24 node24_33
private theorem node0_33 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_16 node16_33
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_33
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29,packet30,packet31,packet32]
theorem packet_count : packets.length = 33 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC01
#check @N11Formalization.C450Source16GroupedC01.bound
#print axioms N11Formalization.C450Source16GroupedC01.valid0
#print axioms N11Formalization.C450Source16GroupedC01.valid1
#print axioms N11Formalization.C450Source16GroupedC01.valid2
#print axioms N11Formalization.C450Source16GroupedC01.valid3
#print axioms N11Formalization.C450Source16GroupedC01.valid4
#print axioms N11Formalization.C450Source16GroupedC01.valid5
#print axioms N11Formalization.C450Source16GroupedC01.valid6
#print axioms N11Formalization.C450Source16GroupedC01.valid7
#print axioms N11Formalization.C450Source16GroupedC01.valid8
#print axioms N11Formalization.C450Source16GroupedC01.valid9
#print axioms N11Formalization.C450Source16GroupedC01.valid10
#print axioms N11Formalization.C450Source16GroupedC01.valid11
#print axioms N11Formalization.C450Source16GroupedC01.valid12
#print axioms N11Formalization.C450Source16GroupedC01.valid13
#print axioms N11Formalization.C450Source16GroupedC01.valid14
#print axioms N11Formalization.C450Source16GroupedC01.valid15
#print axioms N11Formalization.C450Source16GroupedC01.valid16
#print axioms N11Formalization.C450Source16GroupedC01.valid17
#print axioms N11Formalization.C450Source16GroupedC01.valid18
#print axioms N11Formalization.C450Source16GroupedC01.valid19
#print axioms N11Formalization.C450Source16GroupedC01.valid20
#print axioms N11Formalization.C450Source16GroupedC01.valid21
#print axioms N11Formalization.C450Source16GroupedC01.valid22
#print axioms N11Formalization.C450Source16GroupedC01.valid23
#print axioms N11Formalization.C450Source16GroupedC01.valid24
#print axioms N11Formalization.C450Source16GroupedC01.valid25
#print axioms N11Formalization.C450Source16GroupedC01.valid26
#print axioms N11Formalization.C450Source16GroupedC01.valid27
#print axioms N11Formalization.C450Source16GroupedC01.valid28
#print axioms N11Formalization.C450Source16GroupedC01.valid29
#print axioms N11Formalization.C450Source16GroupedC01.valid30
#print axioms N11Formalization.C450Source16GroupedC01.valid31
#print axioms N11Formalization.C450Source16GroupedC01.valid32
#print axioms N11Formalization.C450Source16GroupedC01.bound
#print axioms N11Formalization.C450Source16GroupedC01.endpoint_checks
