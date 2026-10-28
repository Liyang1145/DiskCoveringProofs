import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((6786253909:ℚ)/10000000000),((6988780689:ℚ)/10000000000),((-18790342067:ℚ)/19840000000),((-41743777363:ℚ)/50550000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4669884211:ℚ)/10000000000),((12769334580215330609496902623068082667274459:ℚ)/138581363875840000000000000000000000000000000),((992583501692964250138898223:ℚ)/1478656000000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((6905168503:ℚ)/10000000000),((1409640397:ℚ)/2000000000),((-3793721191:ℚ)/4044000000),((-42576179521:ℚ)/51025000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((53867107:ℚ)/125000000),((55482142803808698947216714825142818426277485805507335093:ℚ)/636784934870475000000000000000000000000000000000000000000),((39786634058698739580422567:ℚ)/59146240000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((870577937:ℚ)/1250000000),((7107622427:ℚ)/10000000000),((-19146867281:ℚ)/20410000000),((-5374045559:ℚ)/6437500000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((4118100243:ℚ)/10000000000),((452766861535544511016804407284511563305740332765946227477:ℚ)/5203809320589750000000000000000000000000000000000000000000),((996749688597248092808999927:ℚ)/1478656000000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7024077011:ℚ)/10000000000),((3568666167:ℚ)/5000000000),((-9617998501:ℚ)/10300000000),((-43408539077:ℚ)/51737500000),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((979516783:ℚ)/2500000000),((38681288501020309686226621954249333634567953632481596892903:ℚ)/457027758846850585937500000000000000000000000000000000000000),((249448041279816417501486207:ℚ)/369664000000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((4139:ℚ)/6400),((2079:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((7053803227:ℚ)/10000000000),((1791760509:ℚ)/2500000000),((-4831281527:ℚ)/5173750000),((-43616622589:ℚ)/51975000000),((4916570841:ℚ)/5000000000),((1969704979:ℚ)/2000000000),((1829340989:ℚ)/10000000000),((3814334023:ℚ)/10000000000),((66980043953127053067433350911116681283636728007504594041:ℚ)/791778129301226074218750000000000000000000000000000000000),((62427188359634039306760903:ℚ)/92416000000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2079:ℚ)/3200),((1667:ℚ)/2560),((-15:ℚ)/16),((-7:ℚ)/8),((7083529089:ℚ)/10000000000),((7181896811:ℚ)/10000000000),((-19369690433:ℚ)/20790000000),((-43824703623:ℚ)/52093750000),((4912776717:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((935297099:ℚ)/5000000000),((3707846941:ℚ)/10000000000),((56374298617199110796289496470223454815423073749358062371541:ℚ)/675620323326506250000000000000000000000000000000000000000000),((2768300769091906519695743:ℚ)/4096000000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1667:ℚ)/2560) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1667:ℚ)/2560),((4177:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((443649493:ℚ)/625000000),((449796971:ℚ)/625000000),((-1213390913:ℚ)/1302343750),((-2745546451:ℚ)/3263281250),((4909016731:ℚ)/5000000000),((9825553439:ℚ)/10000000000),((382121547:ℚ)/2000000000),((1826747749:ℚ)/5000000000),((10047247707086704992445627965027993211240965024250724694737:ℚ)/120435872365058700740337371826171875000000000000000000000000),((3905774353903884934661783:ℚ)/5776000000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((1667:ℚ)/2560) ((4177:ℚ)/6400) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4177:ℚ)/6400),((8373:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((35566273:ℚ)/50000000),((7211606211:ℚ)/10000000000),((-19458818633:ℚ)/20885000000),((-220163911:ℚ)/261656250),((4905290651:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((194946007:ℚ)/1000000000),((719672179:ℚ)/2000000000),((110975997191900600934682781858787923628694134632879964520631137:ℚ)/1330529119604832827343750000000000000000000000000000000000000000),((1000399984624835978664631623:ℚ)/1478656000000000000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8373:ℚ)/12800) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((8373:ℚ)/12800),((1049:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((3564058613:ℚ)/5000000000),((7226460837:ℚ)/10000000000),((-19503382511:ℚ)/20932500000),((-22068410291:ℚ)/26225000000),((4901598247:ℚ)/5000000000),((9810581307:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3542406499:ℚ)/10000000000),((15780990710900731854447050011634720966822970447518875890097991:ℚ)/189241136728165405371093750000000000000000000000000000000000000),((1000921827752678243322877047:ℚ)/1478656000000000000000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((8373:ℚ)/12800) ((1049:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1049:ℚ)/1600),((8411:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7142979767:ℚ)/10000000000),((7241315413:ℚ)/10000000000),((-19547946239:ℚ)/20980000000),((-44240858369:ℚ)/52568750000),((9795878581:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((1011977397:ℚ)/5000000000),((871398191:ℚ)/2500000000),((340427868816298766778707189084055958531495234981745846435764437:ℚ)/4083116156108686450000000000000000000000000000000000000000000000),((1001443763946843391705937047:ℚ)/1478656000000000000000000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8411:ℚ)/12800) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((8411:ℚ)/12800),((843:ℚ)/1280),((-15:ℚ)/16),((-7:ℚ)/8),((7157842223:ℚ)/10000000000),((7256169941:ℚ)/10000000000),((-19592509823:ℚ)/21027500000),((-44344895561:ℚ)/52687500000),((978862711:ℚ)/1000000000),((4897939293:ℚ)/5000000000),((2059717253:ℚ)/10000000000),((107121153:ℚ)/312500000),((95619005375367116228078834818237914387575497224070973711469:ℚ)/1147084973785602807617187500000000000000000000000000000000000),((1001965793276665846832158103:ℚ)/1478656000000000000000000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell ((8411:ℚ)/12800) ((843:ℚ)/1280) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((843:ℚ)/1280),((8449:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((3586352297:ℚ)/5000000000),((363551221:ℚ)/500000000),((-981853663:ℚ)/1053750000),((-313020649:ℚ)/371875000),((4890720817:ℚ)/5000000000),((1957725423:ℚ)/2000000000),((83782417:ℚ)/400000000),((421151559:ℚ)/1250000000),((1035696332211751176703073693873413246726212956437954927:ℚ)/12427047234707519531250000000000000000000000000000000000),((2506219789265185131869783:ℚ)/3696640000000000000000000)⟩
theorem valid11 : Valid source19 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source19 nn0 nn1 Qcell ((843:ℚ)/1280) ((8449:ℚ)/12800) :=
  cell_of_packet source19 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((8449:ℚ)/12800),((2117:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((7187566881:ℚ)/10000000000),((145717577:ℚ)/200000000),((-393632731:ℚ)/422450000),((-44552968167:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((9781441639:ℚ)/10000000000),((425706267:ℚ)/2000000000),((3309548979:ℚ)/10000000000),((10350937684442790456272544250734543443908810878892752281:ℚ)/124222068118565807031250000000000000000000000000000000000),((401204052493651862457727:ℚ)/591462400000000000000000)⟩
theorem valid12 : Valid source19 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source19 nn0 nn1 Qcell ((8449:ℚ)/12800) ((2117:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2117:ℚ)/3200),((8487:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((1440485817:ℚ)/2000000000),((7300733233:ℚ)/10000000000),((-19726199699:ℚ)/21170000000),((-2977133573:ℚ)/3536250000),((9767266893:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((2161672951:ℚ)/10000000000),((406103913:ℚ)/1250000000),((3294770840621556632693775348756370727466404543835565504748411:ℚ)/39548247216209235937500000000000000000000000000000000000000000),((1003532439930224539465511407:ℚ)/1478656000000000000000000000)⟩
theorem valid13 : Valid source19 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source19 nn0 nn1 Qcell ((2117:ℚ)/3200) ((8487:ℚ)/12800) :=
  cell_of_packet source19 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((8487:ℚ)/12800),((4253:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((3608645603:ℚ)/5000000000),((7315587569:ℚ)/10000000000),((-19770762707:ℚ)/21217500000),((-22380519221:ℚ)/26581250000),((9760276751:ℚ)/10000000000),((4883633449:ℚ)/5000000000),((438804929:ℚ)/2000000000),((318699913:ℚ)/1000000000),((7495278188852546241420187672279436621357852182685080178242427:ℚ)/89985424400233396215820312500000000000000000000000000000000000),((1004054841793458655354437743:ℚ)/1478656000000000000000000000)⟩
theorem valid14 : Valid source19 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source19 nn0 nn1 Qcell ((8487:ℚ)/12800) ((4253:ℚ)/6400) :=
  cell_of_packet source19 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4253:ℚ)/6400),((341:ℚ)/512),((-15:ℚ)/16),((-7:ℚ)/8),((1808038311:ℚ)/2500000000),((7330441857:ℚ)/10000000000),((-19815325571:ℚ)/21265000000),((-11216268177:ℚ)/13320312500),((195067017:ℚ)/200000000),((2440069189:ℚ)/2500000000),((1112811311:ℚ)/5000000000),((312398621:ℚ)/1000000000),((36374641946986073957935964053759044218980563752124252298393:ℚ)/436782222513273291015625000000000000000000000000000000000000),((1004577336787754076404177487:ℚ)/1478656000000000000000000000)⟩
theorem valid15 : Valid source19 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source19 nn0 nn1 Qcell ((4253:ℚ)/6400) ((341:ℚ)/512) :=
  cell_of_packet source19 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((341:ℚ)/512),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((3623507601:ℚ)/5000000000),((3672648049:ℚ)/5000000000),((-9929944147:ℚ)/10656250000),((-7494851069:ℚ)/8900000000),((4873244381:ℚ)/5000000000),((1950670171:ℚ)/2000000000),((2256500263:ℚ)/10000000000),((382464939:ℚ)/1250000000),((18138153129269656409994524402819964501488861781967746099:ℚ)/217841459892272949218750000000000000000000000000000000000),((251274981236843969335838063:ℚ)/369664000000000000000000000)⟩
theorem valid16 : Valid source19 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source19 nn0 nn1 Qcell ((341:ℚ)/512) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((267:ℚ)/400),((8563:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((3630938539:ℚ)/5000000000),((1840037573:ℚ)/2500000000),((-4976112719:ℚ)/5340000000),((-22536569773:ℚ)/26759375000),((9739690061:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((1143344217:ℚ)/5000000000),((18713239:ℚ)/62500000),((17428048850421483937038235288686798314077743247049763409941191:ℚ)/209351911787392050000000000000000000000000000000000000000000000),((62851412891964001213679927:ℚ)/92416000000000000000000000)⟩
theorem valid17 : Valid source19 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((8563:ℚ)/12800) :=
  cell_of_packet source19 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((8563:ℚ)/12800),((4291:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7276738873:ℚ)/10000000000),((7375004441:ℚ)/10000000000),((-19949013323:ℚ)/21407500000),((-45177172111:ℚ)/53637500000),((1216619291:ℚ)/1250000000),((4869845033:ℚ)/5000000000),((1158107867:ℚ)/5000000000),((2927092587:ℚ)/10000000000),((23492358356772239572914373178303086000483453087952789532794089:ℚ)/282250625576747204760742187500000000000000000000000000000000000),((1006145380829392531921435103:ℚ)/1478656000000000000000000000)⟩
theorem valid18 : Valid source19 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source19 nn0 nn1 Qcell ((8563:ℚ)/12800) ((4291:ℚ)/6400) :=
  cell_of_packet source19 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-15:ℚ)/16),((-7:ℚ)/8),((1822900147:ℚ)/2500000000),((37023563:ℚ)/50000000),((-100190689:ℚ)/107275000),((-11320301029:ℚ)/13468750000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((1429271141:ℚ)/5000000000),((362383787967435643813230653116122672140558349965110489:ℚ)/4299830955825917285156250000000000000000000000000000000),((25179780237570113484247:ℚ)/36966400000000000000000)⟩
theorem valid19 : Valid source19 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source19 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source19 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7321323781:ℚ)/10000000000),((7434420577:ℚ)/10000000000),((-20127261731:ℚ)/21550000000),((-45489266467:ℚ)/54112500000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((2716403151:ℚ)/10000000000),((32915655641300760395555069222388901808220873099781765697467451:ℚ)/390729100656466406250000000000000000000000000000000000000000000),((1008237411031009994880963727:ℚ)/1478656000000000000000000000)⟩
theorem valid20 : Valid source19 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source19 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source19 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((367552333:ℚ)/500000000),((59713027:ℚ)/80000000),((-161731081:ℚ)/173160000),((-2284866331:ℚ)/2717500000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((641652499:ℚ)/2500000000),((9685940421278202803695251416360242528323410668647588649:ℚ)/115027873637616529200000000000000000000000000000000000000),((64594175072815647901127:ℚ)/94633984000000000000000)⟩
theorem valid21 : Valid source19 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source19 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((7380769229:ℚ)/10000000000),((1880885861:ℚ)/2500000000),((-5098657583:ℚ)/5435000000),((-45905384603:ℚ)/54825000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((240773397:ℚ)/1000000000),((8671045154722237200747249762637972945626666113981373953503:ℚ)/100534399592077587890625000000000000000000000000000000000000),((63211140853874218863564023:ℚ)/92416000000000000000000000)⟩
theorem valid22 : Valid source19 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-15:ℚ)/16),((-7:ℚ)/8),((3720106727:ℚ)/5000000000),((7582957823:ℚ)/10000000000),((-20572873469:ℚ)/21930000000),((-23160747089:ℚ)/27650000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((205419733:ℚ)/1000000000),((5769676332159338003684708898248692905112605964374579129307:ℚ)/66969904463831250000000000000000000000000000000000000000000),((1013474014461038679100526927:ℚ)/1478656000000000000000000000)⟩
theorem valid23 : Valid source19 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source19 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((937457061:ℚ)/1250000000),((3910304397:ℚ)/5000000000),((-10642913191:ℚ)/11060000000),((-5842199427:ℚ)/7150000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((65071653:ℚ)/400000000),((2425205293809634884302827176046854696156969450541319220051:ℚ)/24701278551950000000000000000000000000000000000000000000000),((351134153:ℚ)/512000000)⟩
theorem valid24 : Valid source19 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((1547483461:ℚ)/2000000000),((350844963:ℚ)/400000000),(-1:ℚ),((-9680384227:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((6961586527120880731048017102870341:ℚ)/55987200000000000000000000000000000),((351134153:ℚ)/512000000)⟩
theorem valid25 : Valid source19 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((4344153709:ℚ)/5000000000),((266796519:ℚ)/250000000),(-1:ℚ),((-27529075963:ℚ)/40000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((160149881067569421577554426929141041:ℚ)/1200000000000000000000000000000000000),((351134153:ℚ)/512000000)⟩
theorem valid26 : Valid source19 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((10589579779:ℚ)/10000000000),((14472725359:ℚ)/10000000000),(-1:ℚ),((-68367058453:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((61297477189784085591652259:ℚ)/406272000000000000000000000),((351134153:ℚ)/512000000)⟩
theorem valid27 : Valid source19 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet27 valid27
private theorem node1_3 :
    CellBound source19 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source19 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source19 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source19 nn0 nn1 Qcell ((103:ℚ)/160) ((4177:ℚ)/6400) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((4177:ℚ)/6400) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source19 nn0 nn1 Qcell ((8373:ℚ)/12800) ((8411:ℚ)/12800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source19 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8411:ℚ)/12800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source19 nn0 nn1 Qcell ((8411:ℚ)/12800) ((8449:ℚ)/12800) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source19 nn0 nn1 Qcell ((8449:ℚ)/12800) ((8487:ℚ)/12800) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source19 nn0 nn1 Qcell ((8411:ℚ)/12800) ((8487:ℚ)/12800) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source19 nn0 nn1 Qcell ((4177:ℚ)/6400) ((8487:ℚ)/12800) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((8487:ℚ)/12800) :=
  cell_join node0_7 node7_14
private theorem node15_17 :
    CellBound source19 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source19 nn0 nn1 Qcell ((8487:ℚ)/12800) ((267:ℚ)/400) :=
  cell_join leaf14 node15_17
private theorem node17_19 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_join leaf17 leaf18
private theorem node19_21 :
    CellBound source19 nn0 nn1 Qcell ((4291:ℚ)/6400) ((4329:ℚ)/6400) :=
  cell_join leaf19 leaf20
private theorem node17_21 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((4329:ℚ)/6400) :=
  cell_join node17_19 node19_21
private theorem node14_21 :
    CellBound source19 nn0 nn1 Qcell ((8487:ℚ)/12800) ((4329:ℚ)/6400) :=
  cell_join node14_17 node17_21
private theorem node22_24 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf22 leaf23
private theorem node21_24 :
    CellBound source19 nn0 nn1 Qcell ((4329:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join leaf21 node22_24
private theorem node24_26 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf24 leaf25
private theorem node26_28 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf26 leaf27
private theorem node24_28 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node24_26 node26_28
private theorem node21_28 :
    CellBound source19 nn0 nn1 Qcell ((4329:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node21_24 node24_28
private theorem node14_28 :
    CellBound source19 nn0 nn1 Qcell ((8487:ℚ)/12800) ((69:ℚ)/50) :=
  cell_join node14_21 node21_28
private theorem node0_28 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_14 node14_28
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_28
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27]
theorem packet_count : packets.length = 28 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC02
#check @N11Formalization.C450Source19GroupedC02.bound
#print axioms N11Formalization.C450Source19GroupedC02.valid0
#print axioms N11Formalization.C450Source19GroupedC02.valid1
#print axioms N11Formalization.C450Source19GroupedC02.valid2
#print axioms N11Formalization.C450Source19GroupedC02.valid3
#print axioms N11Formalization.C450Source19GroupedC02.valid4
#print axioms N11Formalization.C450Source19GroupedC02.valid5
#print axioms N11Formalization.C450Source19GroupedC02.valid6
#print axioms N11Formalization.C450Source19GroupedC02.valid7
#print axioms N11Formalization.C450Source19GroupedC02.valid8
#print axioms N11Formalization.C450Source19GroupedC02.valid9
#print axioms N11Formalization.C450Source19GroupedC02.valid10
#print axioms N11Formalization.C450Source19GroupedC02.valid11
#print axioms N11Formalization.C450Source19GroupedC02.valid12
#print axioms N11Formalization.C450Source19GroupedC02.valid13
#print axioms N11Formalization.C450Source19GroupedC02.valid14
#print axioms N11Formalization.C450Source19GroupedC02.valid15
#print axioms N11Formalization.C450Source19GroupedC02.valid16
#print axioms N11Formalization.C450Source19GroupedC02.valid17
#print axioms N11Formalization.C450Source19GroupedC02.valid18
#print axioms N11Formalization.C450Source19GroupedC02.valid19
#print axioms N11Formalization.C450Source19GroupedC02.valid20
#print axioms N11Formalization.C450Source19GroupedC02.valid21
#print axioms N11Formalization.C450Source19GroupedC02.valid22
#print axioms N11Formalization.C450Source19GroupedC02.valid23
#print axioms N11Formalization.C450Source19GroupedC02.valid24
#print axioms N11Formalization.C450Source19GroupedC02.valid25
#print axioms N11Formalization.C450Source19GroupedC02.valid26
#print axioms N11Formalization.C450Source19GroupedC02.valid27
#print axioms N11Formalization.C450Source19GroupedC02.bound
#print axioms N11Formalization.C450Source19GroupedC02.endpoint_checks
