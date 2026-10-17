import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((3376126611:ℚ)/5000000000),((3475908843:ℚ)/5000000000),((-9403726529:ℚ)/9920000000),((-20912886277:ℚ)/25275000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((149009329:ℚ)/312500000),((10734541343086781443205042945013840332840999:ℚ)/129920028633600000000000000000000000000000000),((22875203581025127438203901:ℚ)/36966400000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((6871148987:ℚ)/10000000000),((876404247:ℚ)/1250000000),((-2373212741:ℚ)/2527500000),((-42658042909:ℚ)/51025000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((1103827143:ℚ)/2500000000),((6082592616968730163249896977864820162894279641715190223:ℚ)/77732535994931030273437500000000000000000000000000000000),((1432500947519130747647541:ℚ)/2310400000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((693059483:ℚ)/1000000000),((7070649503:ℚ)/10000000000),((-19163948509:ℚ)/20410000000),((-4307416381:ℚ)/5150000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((4228566869:ℚ)/10000000000),((203333681780357363032025261540947285559377201593293328593:ℚ)/2601904660294875000000000000000000000000000000000000000000),((91859410203281677551637541:ℚ)/147865600000000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((1747509841:ℚ)/2500000000),((1775089247:ℚ)/2500000000),((-4813267741:ℚ)/5150000000),((-10872568887:ℚ)/12934375000),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((2016867897:ℚ)/5000000000),((2173142450807783715769022469113916393872523187339515054343:ℚ)/28564234927928161621093750000000000000000000000000000000000),((5746820232682486506757541:ℚ)/9241600000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4139:ℚ)/6400),((2079:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((7019761151:ℚ)/10000000000),((7130064289:ℚ)/10000000000),((-19342192867:ℚ)/20695000000),((-43698328057:ℚ)/51975000000),((4916570841:ℚ)/5000000000),((1969704979:ℚ)/2000000000),((1829340989:ℚ)/10000000000),((3932911837:ℚ)/10000000000),((5780171235947322781082455324160213004287539337765752784983:ℚ)/76010700412917703125000000000000000000000000000000000000000),((92038863072673272469963429:ℚ)/147865600000000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((55074083:ℚ)/78125000),((715977141:ℚ)/1000000000),((-1943131423:ℚ)/2079000000),((-1372074324:ℚ)/1631640625),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((1914788509:ℚ)/5000000000),((161212852662236747170976378974658146869251090280680645851:ℚ)/2120950145933128125000000000000000000000000000000000000000),((921286282641403288587069:ℚ)/1478656000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4177:ℚ)/6400),((8373:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((1769800947:ℚ)/2500000000),((896828113:ℚ)/1250000000),((-2434484339:ℚ)/2610625000),((-11028606629:ℚ)/13082812500),((4905290651:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((194946007:ℚ)/1000000000),((3723521803:ℚ)/10000000000),((292389433209623128486418672001861542649192735708329485860977:ℚ)/3898034530092283673858642578125000000000000000000000000000000),((1440211258646705073355781:ℚ)/2310400000000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8373:ℚ)/12800) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((8373:ℚ)/12800),((1049:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((1418812851:ℚ)/2000000000),((3594739177:ℚ)/5000000000),((-9760217531:ℚ)/10466250000),((-8843689957:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((9810581307:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((1834700209:ℚ)/5000000000),((887019540731751674450639446989748759574934699787460950191811:ℚ)/11827571045510337835693359375000000000000000000000000000000000),((23054604826477587145431221:ℚ)/36966400000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((8373:ℚ)/12800) ((1049:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1049:ℚ)/1600),((8411:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7108924647:ℚ)/10000000000),((7204331759:ℚ)/10000000000),((-19564995277:ℚ)/20980000000),((-44322472529:ℚ)/52568750000),((9795878581:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((1011977397:ℚ)/5000000000),((722901247:ℚ)/2000000000),((153081089266224513269234165868124472066623367160455818525068399:ℚ)/2041558078054343225000000000000000000000000000000000000000000000),((92263324518621931957476869:ℚ)/147865600000000000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8411:ℚ)/12800) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((8411:ℚ)/12800),((843:ℚ)/1280),((-15:ℚ)/16),((-7:ℚ)/8),((7123784963:ℚ)/10000000000),((7219185121:ℚ)/10000000000),((-19609555363:ℚ)/21027500000),((-44426494741:ℚ)/52687500000),((978862711:ℚ)/1000000000),((4897939293:ℚ)/5000000000),((2059717253:ℚ)/10000000000),((1779401717:ℚ)/5000000000),((386981887572380146636647684525076436458993862239209476507521:ℚ)/5161882382035212634277343750000000000000000000000000000000000),((92308236197511709008598309:ℚ)/147865600000000000000000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((8411:ℚ)/12800) ((843:ℚ)/1280) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((843:ℚ)/1280),((8449:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((1784661301:ℚ)/2500000000),((180850961:ℚ)/250000000),((-491352883:ℚ)/526875000),((-11132629107:ℚ)/13201562500),((4890720817:ℚ)/5000000000),((1957725423:ℚ)/2000000000),((83782417:ℚ)/400000000),((437781671:ℚ)/1250000000),((293474565067099758369118458157079716339340989203250168067:ℚ)/3915296569385037872314453125000000000000000000000000000000),((57720721464076495415429:ℚ)/92416000000000000000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell ((843:ℚ)/1280) ((8449:ℚ)/12800) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((8449:ℚ)/12800),((2117:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((7153505371:ℚ)/10000000000),((1812222929:ℚ)/2500000000),((-4924668787:ℚ)/5280625000),((-44634537597:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((9781441639:ℚ)/10000000000),((425706267:ℚ)/2000000000),((3444814243:ℚ)/10000000000),((9091350598431198235472544068732360231092195930182978726753:ℚ)/121310613397036920928955078125000000000000000000000000000000),((5774879934599793501323909:ℚ)/9241600000000000000000000)⟩
theorem valid11 : Valid source18 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source18 nn0 nn1 Qcell ((8449:ℚ)/12800) ((2117:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2117:ℚ)/3200),((8487:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((896045683:ℚ)/1250000000),((7263744949:ℚ)/10000000000),((-19743234847:ℚ)/21170000000),((-5592319781:ℚ)/6630468750),((9767266893:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((2161672951:ℚ)/10000000000),((846610189:ℚ)/2500000000),((4445006889402475940841110389978750290172130905894035028737701:ℚ)/59322370824313853906250000000000000000000000000000000000000000),((92443010030677332339372349:ℚ)/147865600000000000000000000)⟩
theorem valid12 : Valid source18 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source18 nn0 nn1 Qcell ((2117:ℚ)/3200) ((8487:ℚ)/12800) :=
  cell_of_packet source18 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((8487:ℚ)/12800),((4253:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((1795806371:ℚ)/2500000000),((363929907:ℚ)/500000000),((-989389721:ℚ)/1060875000),((-11210644597:ℚ)/13290625000),((9760276751:ℚ)/10000000000),((4883633449:ℚ)/5000000000),((438804929:ℚ)/2000000000),((1663541829:ℚ)/5000000000),((421338339411669509672290666492418173664081778256099008769:ℚ)/5624089025014587263488769531250000000000000000000000000000),((231219868941831710873901:ℚ)/369664000000000000000000)⟩
theorem valid13 : Valid source18 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source18 nn0 nn1 Qcell ((8487:ℚ)/12800) ((4253:ℚ)/6400) :=
  cell_of_packet source18 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4253:ℚ)/6400),((341:ℚ)/512),((-15:ℚ)/16),((-7:ℚ)/8),((7198085431:ℚ)/10000000000),((7293451289:ℚ)/10000000000),((-19832353867:ℚ)/21265000000),((-44946598017:ℚ)/53281250000),((195067017:ℚ)/200000000),((2440069189:ℚ)/2500000000),((1112811311:ℚ)/5000000000),((1633344633:ℚ)/5000000000),((16358335852101859263090095706590609634873857710407475618809:ℚ)/218391111256636645507812500000000000000000000000000000000000),((92532891591706797882977429:ℚ)/147865600000000000000000000)⟩
theorem valid14 : Valid source18 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source18 nn0 nn1 Qcell ((4253:ℚ)/6400) ((341:ℚ)/512) :=
  cell_of_packet source18 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((341:ℚ)/512),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((3606472653:ℚ)/5000000000),((1827076099:ℚ)/2500000000),((-14572517:ℚ)/15625000),((-22525308571:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((1950670171:ℚ)/2000000000),((2256500263:ℚ)/10000000000),((3205198871:ℚ)/10000000000),((39777976028912257314439620656221196297942910569:ℚ)/531144440174102783203125000000000000000000000000),((5786115129721482433067149:ℚ)/9241600000000000000000000)⟩
theorem valid15 : Valid source18 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source18 nn0 nn1 Qcell ((341:ℚ)/512) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((267:ℚ)/400),((8563:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7227805109:ℚ)/10000000000),((7323157461:ℚ)/10000000000),((-19921472383:ℚ)/21360000000),((-45154635763:ℚ)/53518750000),((9739690061:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((1143344217:ℚ)/5000000000),((314254807:ℚ)/1000000000),((501629807989296285317100940355556564166157575469914373618194943:ℚ)/6699261177196545600000000000000000000000000000000000000000000000),((92622799028187493635522429:ℚ)/147865600000000000000000000)⟩
theorem valid16 : Valid source18 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((8563:ℚ)/12800) :=
  cell_of_packet source18 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((8563:ℚ)/12800),((4291:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((181066621:ℚ)/250000000),((1467602097:ℚ)/2000000000),((-3993206291:ℚ)/4281500000),((-1131466347:ℚ)/1340937500),((1216619291:ℚ)/1250000000),((4869845033:ℚ)/5000000000),((1158107867:ℚ)/5000000000),((96208311:ℚ)/312500000),((84523644169226025757422857800640954497397705088268055978377:ℚ)/1129002502306988819042968750000000000000000000000000000000000),((3706710498104384556867141:ℚ)/5914624000000000000000000)⟩
theorem valid17 : Valid source18 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source18 nn0 nn1 Qcell ((8563:ℚ)/12800) ((4291:ℚ)/6400) :=
  cell_of_packet source18 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((4291:ℚ)/6400),((8601:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7257524501:ℚ)/10000000000),((1838215867:ℚ)/2500000000),((-714663943:ℚ)/766250000),((-45362671507:ℚ)/53756250000),((1215785143:ℚ)/1250000000),((9732954333:ℚ)/10000000000),((2345108749:ℚ)/10000000000),((301347413:ℚ)/1000000000),((165642663713288480955109406834821963420943309183889609187:ℚ)/2212898638850408935546875000000000000000000000000000000000),((5794545771797216154688861:ℚ)/9241600000000000000000000)⟩
theorem valid18 : Valid source18 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source18 nn0 nn1 Qcell ((4291:ℚ)/6400) ((8601:ℚ)/12800) :=
  cell_of_packet source18 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((8601:ℚ)/12800),((431:ℚ)/640),((-15:ℚ)/16),((-7:ℚ)/8),((7272384091:ℚ)/10000000000),((736771641:ℚ)/1000000000),((-2005514923:ℚ)/2150250000),((-45466688637:ℚ)/53875000000),((607479381:ℚ)/625000000),((9726281149:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((184180351:ℚ)/625000000),((143975542463851012843887767914236319162017045909853140347:ℚ)/1923756836905917333984375000000000000000000000000000000000),((927577087165704061338069:ℚ)/1478656000000000000000000)⟩
theorem valid19 : Valid source18 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source18 nn0 nn1 Qcell ((8601:ℚ)/12800) ((431:ℚ)/640) :=
  cell_of_packet source18 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7287243611:ℚ)/10000000000),((7397422173:ℚ)/10000000000),((-20144266519:ℚ)/21550000000),((-45570705277:ℚ)/54112500000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((1439401707:ℚ)/5000000000),((44397432020383704876244265304492921229802680733935395637223117:ℚ)/586093650984699609375000000000000000000000000000000000000000000),((92847680873047570682796621:ℚ)/147865600000000000000000000)⟩
theorem valid20 : Valid source18 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source18 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source18 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((1829240611:ℚ)/2500000000),((7427127777:ℚ)/10000000000),((-20233383331:ℚ)/21645000000),((-11444684277:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2737709469:ℚ)/10000000000),((8505900523899974523745382271038744015512237481835849404209139:ℚ)/112331907849234891796875000000000000000000000000000000000000000),((92937678930699800244886821:ℚ)/147865600000000000000000000)⟩
theorem valid21 : Valid source18 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source18 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((3673340501:ℚ)/5000000000),((7486538513:ℚ)/10000000000),((-20411615539:ℚ)/21740000000),((-10484899:ℚ)/12500000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((323642719:ℚ)/1250000000),((466653927870667406694665316319640841022959311135458811:ℚ)/6020463295312500000000000000000000000000000000000000000),((93117752762994320610725381:ℚ)/147865600000000000000000000)⟩
theorem valid22 : Valid source18 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source18 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-15:ℚ)/16),((-7:ℚ)/8),((7406117311:ℚ)/10000000000),((3772974317:ℚ)/5000000000),((-605583703:ℚ)/645000000),((-46402821177:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((2263629461:ℚ)/10000000000),((65966531830881391765982439655004779262623462374707281:ℚ)/851947695703125000000000000000000000000000000000000000),((23324482564657525920894061:ℚ)/36966400000000000000000000)⟩
theorem valid23 : Valid source18 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source18 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-15:ℚ)/16),((-7:ℚ)/8),((1866388141:ℚ)/2500000000),((7664767097:ℚ)/10000000000),((-20946301291:ℚ)/22120000000),((-3901572329:ℚ)/4687500000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((235470661:ℚ)/1250000000),((14842768559089483562938875491024281621166302882534523:ℚ)/183485400000000000000000000000000000000000000000000000),((161810851:ℚ)/256000000)⟩
theorem valid24 : Valid source18 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source18 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((3792210007:ℚ)/5000000000),((7783583283:ℚ)/10000000000),((-21302749849:ℚ)/22500000000),((-23825470049:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((80052697:ℚ)/1250000000),((58711010896628013182930985986065214432728060756824197680723:ℚ)/727896533203125000000000000000000000000000000000000000000000),((161810851:ℚ)/256000000)⟩
theorem valid25 : Valid source18 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((1925820889:ℚ)/2500000000),((436702143:ℚ)/500000000),(-1:ℚ),((-4040248741:ℚ)/5400000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((16140658447310395031364801671573591:ℚ)/145800000000000000000000000000000000),((161810851:ℚ)/256000000)⟩
theorem valid26 : Valid source18 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((4327035951:ℚ)/5000000000),((10634699923:ℚ)/10000000000),(-1:ℚ),((-27569251657:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((713365008670242932019913184581521233:ℚ)/6000000000000000000000000000000000000),((161810851:ℚ)/256000000)⟩
theorem valid27 : Valid source18 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((2111039769:ℚ)/2000000000),((7217735547:ℚ)/5000000000),(-1:ℚ),((-13689278383:ℚ)/22080000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((32702437416788651320636601:ℚ)/243763200000000000000000000),((161810851:ℚ)/256000000)⟩
theorem valid28 : Valid source18 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet28 valid28
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
    CellBound source18 nn0 nn1 Qcell ((2079:ℚ)/3200) ((8373:ℚ)/12800) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source18 nn0 nn1 Qcell ((103:ℚ)/160) ((8373:ℚ)/12800) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((8373:ℚ)/12800) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source18 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source18 nn0 nn1 Qcell ((8373:ℚ)/12800) ((843:ℚ)/1280) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source18 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source18 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source18 nn0 nn1 Qcell ((843:ℚ)/1280) ((4253:ℚ)/6400) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source18 nn0 nn1 Qcell ((8373:ℚ)/12800) ((4253:ℚ)/6400) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((4253:ℚ)/6400) :=
  cell_join node0_7 node7_14
private theorem node15_17 :
    CellBound source18 nn0 nn1 Qcell ((341:ℚ)/512) ((8563:ℚ)/12800) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source18 nn0 nn1 Qcell ((4253:ℚ)/6400) ((8563:ℚ)/12800) :=
  cell_join leaf14 node15_17
private theorem node17_19 :
    CellBound source18 nn0 nn1 Qcell ((8563:ℚ)/12800) ((8601:ℚ)/12800) :=
  cell_join leaf17 leaf18
private theorem node19_21 :
    CellBound source18 nn0 nn1 Qcell ((8601:ℚ)/12800) ((4329:ℚ)/6400) :=
  cell_join leaf19 leaf20
private theorem node17_21 :
    CellBound source18 nn0 nn1 Qcell ((8563:ℚ)/12800) ((4329:ℚ)/6400) :=
  cell_join node17_19 node19_21
private theorem node14_21 :
    CellBound source18 nn0 nn1 Qcell ((4253:ℚ)/6400) ((4329:ℚ)/6400) :=
  cell_join node14_17 node17_21
private theorem node21_23 :
    CellBound source18 nn0 nn1 Qcell ((4329:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_join leaf21 leaf22
private theorem node23_25 :
    CellBound source18 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf23 leaf24
private theorem node21_25 :
    CellBound source18 nn0 nn1 Qcell ((4329:ℚ)/6400) ((45:ℚ)/64) :=
  cell_join node21_23 node23_25
private theorem node25_27 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((81:ℚ)/100) :=
  cell_join leaf25 leaf26
private theorem node27_29 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf27 leaf28
private theorem node25_29 :
    CellBound source18 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node25_27 node27_29
private theorem node21_29 :
    CellBound source18 nn0 nn1 Qcell ((4329:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node21_25 node25_29
private theorem node14_29 :
    CellBound source18 nn0 nn1 Qcell ((4253:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node14_21 node21_29
private theorem node0_29 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_14 node14_29
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_29
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28]
theorem packet_count : packets.length = 29 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC02
#check @N11Formalization.C450Source18GroupedC02.bound
#print axioms N11Formalization.C450Source18GroupedC02.valid0
#print axioms N11Formalization.C450Source18GroupedC02.valid1
#print axioms N11Formalization.C450Source18GroupedC02.valid2
#print axioms N11Formalization.C450Source18GroupedC02.valid3
#print axioms N11Formalization.C450Source18GroupedC02.valid4
#print axioms N11Formalization.C450Source18GroupedC02.valid5
#print axioms N11Formalization.C450Source18GroupedC02.valid6
#print axioms N11Formalization.C450Source18GroupedC02.valid7
#print axioms N11Formalization.C450Source18GroupedC02.valid8
#print axioms N11Formalization.C450Source18GroupedC02.valid9
#print axioms N11Formalization.C450Source18GroupedC02.valid10
#print axioms N11Formalization.C450Source18GroupedC02.valid11
#print axioms N11Formalization.C450Source18GroupedC02.valid12
#print axioms N11Formalization.C450Source18GroupedC02.valid13
#print axioms N11Formalization.C450Source18GroupedC02.valid14
#print axioms N11Formalization.C450Source18GroupedC02.valid15
#print axioms N11Formalization.C450Source18GroupedC02.valid16
#print axioms N11Formalization.C450Source18GroupedC02.valid17
#print axioms N11Formalization.C450Source18GroupedC02.valid18
#print axioms N11Formalization.C450Source18GroupedC02.valid19
#print axioms N11Formalization.C450Source18GroupedC02.valid20
#print axioms N11Formalization.C450Source18GroupedC02.valid21
#print axioms N11Formalization.C450Source18GroupedC02.valid22
#print axioms N11Formalization.C450Source18GroupedC02.valid23
#print axioms N11Formalization.C450Source18GroupedC02.valid24
#print axioms N11Formalization.C450Source18GroupedC02.valid25
#print axioms N11Formalization.C450Source18GroupedC02.valid26
#print axioms N11Formalization.C450Source18GroupedC02.valid27
#print axioms N11Formalization.C450Source18GroupedC02.valid28
#print axioms N11Formalization.C450Source18GroupedC02.bound
#print axioms N11Formalization.C450Source18GroupedC02.endpoint_checks
