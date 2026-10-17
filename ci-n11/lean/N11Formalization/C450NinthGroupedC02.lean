import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC02
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((-15:ℚ)/16),((-7:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-15:ℚ)/16),((-7:ℚ)/8),((3221758983:ℚ)/5000000000),((842067103:ℚ)/1250000000),((-2414201309:ℚ)/2480000000),((-21272312881:ℚ)/25750000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2794571587:ℚ)/5000000000),((89153529575766904988204289096048101297011:ℚ)/3160527190000000000000000000000000000000000),((343430588275668647946280673:ℚ)/1386240000000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((1336214531:ℚ)/2000000000),((428456517:ℚ)/625000000),((-1229369551:ℚ)/1287500000),((-8841501717:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((4968497667:ℚ)/10000000000),((1467938846819048772026840379122357856286481757700589707:ℚ)/57336706329679489135742187500000000000000000000000000000),((18353109559309766445763859:ℚ)/73932800000000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-15:ℚ)/16),((-7:ℚ)/8),((6799848513:ℚ)/10000000000),((6974071099:ℚ)/10000000000),((-20026213297:ℚ)/20980000000),((-45038939591:ℚ)/53400000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((925998717:ℚ)/2000000000),((105025199238133709284782027614414636200776600930908741045489:ℚ)/4114518237328050000000000000000000000000000000000000000000000),((1379280681239831025523446833:ℚ)/5544960000000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-15:ℚ)/16),((-7:ℚ)/8),((6918623451:ℚ)/10000000000),((703345429:ℚ)/1000000000),((-2020436287:ℚ)/2136000000),((-45870364157:ℚ)/53875000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((4266789317:ℚ)/10000000000),((826660101074334632924713533203964170599051840398928768157:ℚ)/33943729469212800000000000000000000000000000000000000000000),((1380659398193005026432011657:ℚ)/5544960000000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((697801059:ℚ)/1000000000),((7063145831:ℚ)/10000000000),((-20293437493:ℚ)/21550000000),((-4628607413:ℚ)/5411250000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((4073869213:ℚ)/10000000000),((2144958012131439147761363606304019033795922041565142585941513:ℚ)/90168253997646093750000000000000000000000000000000000000000000),((13813485000315618656884217:ℚ)/55449600000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((87596301:ℚ)/125000000),((3546418669:ℚ)/5000000000),((-10191256007:ℚ)/10822500000),((-581174107:ℚ)/679375000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((794820883:ℚ)/2000000000),((667863649634585571217730190174676362747117185793146094026773:ℚ)/28082976962308722949218750000000000000000000000000000000000000),((215944921813677945801557:ℚ)/866400000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7037397517:ℚ)/10000000000),((7122528809:ℚ)/10000000000),((-20471586427:ℚ)/21740000000),((-46701782619:ℚ)/54587500000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((774382007:ℚ)/2000000000),((5459490144578232456486345069977658978744102038356724236907777:ℚ)/229628766281639690625000000000000000000000000000000000000000000),((24258709750314504156361889:ℚ)/97280000000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((7067090903:ℚ)/10000000000),((3576110123:ℚ)/5000000000),((-10280330369:ℚ)/10917500000),((-46909636321:ℚ)/54825000000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((14715187:ℚ)/39062500),((4971572343512526755179395081674414664737730291007461175811:ℚ)/209163199247568457031250000000000000000000000000000000000000),((461148456186676835508120171:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2193:ℚ)/3200),((8791:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7096784237:ℚ)/10000000000),((223970811:ℚ)/312500000),((-643912433:ℚ)/685312500),((-47117489659:ℚ)/54943750000),((9662900309:ℚ)/10000000000),((9668970163:ℚ)/10000000000),((520776989:ℚ)/2000000000),((914852911:ℚ)/2500000000),((84947997712605692230805359006130883311273193517328808887:ℚ)/3615381088341907310485839843750000000000000000000000000000),((461263242145543585946274611:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((2193:ℚ)/3200) ((8791:ℚ)/12800) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((8791:ℚ)/12800),((881:ℚ)/1280),((-15:ℚ)/16),((-7:ℚ)/8),((1422326177:ℚ)/2000000000),((7181911649:ℚ)/10000000000),((-20649734947:ℚ)/21977500000),((-9444283239:ℚ)/11012500000),((4828444327:ℚ)/5000000000),((4831450157:ℚ)/5000000000),((2627133759:ℚ)/10000000000),((3604423437:ℚ)/10000000000),((302456533990136284857494617137360157185623051478136849744339:ℚ)/12873798551200708764648437500000000000000000000000000000000000),((18455188601104426350950651:ℚ)/73932800000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((8791:ℚ)/12800) ((881:ℚ)/1280) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((881:ℚ)/1280),((8829:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((7126477521:ℚ)/10000000000),((3598378669:ℚ)/5000000000),((-10347136007:ℚ)/11012500000),((-47325342647:ℚ)/55181250000),((301591713:ℚ)/312500000),((9656888659:ℚ)/10000000000),((2649962557:ℚ)/10000000000),((3548621059:ℚ)/10000000000),((5095106744979200309774700486778403420863394545296521668175437:ℚ)/216890015865359216308593750000000000000000000000000000000000000),((1384488552898781602151737937:ℚ)/5544960000000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((881:ℚ)/1280) ((8829:ℚ)/12800) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((8829:ℚ)/12800),((553:ℚ)/800),((-15:ℚ)/16),((-7:ℚ)/8),((1428264829:ℚ)/2000000000),((3605801509:ℚ)/5000000000),((-10369404527:ℚ)/11036250000),((-9485853803:ℚ)/11060000000),((1205629803:ℚ)/1250000000),((9650934821:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((436495677:ℚ)/1250000000),((8621211187756895468269449155858130297888757979544218055457:ℚ)/367025998987927770996093750000000000000000000000000000000000),((18464505998141675895708179:ℚ)/73932800000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((8829:ℚ)/12800) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((553:ℚ)/800),((8867:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((1789042689:ℚ)/2500000000),((7226448691:ℚ)/10000000000),((-2969049439:ℚ)/3160000000),((-11883298823:ℚ)/13854687500),((2409799777:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((673601917:ℚ)/2500000000),((3434414223:ℚ)/10000000000),((364186735995784783666214405456554254787428667641089257743247:ℚ)/15505818000348400000000000000000000000000000000000000000000000),((86574208501030943693042897:ℚ)/346560000000000000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((8867:ℚ)/12800) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((8867:ℚ)/12800),((4443:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((1434203471:ℚ)/2000000000),((1448258871:ℚ)/2000000000),((-4165576613:ℚ)/4433500000),((-3175808099:ℚ)/3702500000),((4816708251:ℚ)/5000000000),((9639199113:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3375921611:ℚ)/10000000000),((84166489451950238072212266236185083686682975920428332354103:ℚ)/3583864055747906350781250000000000000000000000000000000000000),((18473822817577493594591579:ℚ)/73932800000000000000000000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((8867:ℚ)/12800) ((4443:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4443:ℚ)/6400),((1781:ℚ)/2560),((-15:ℚ)/16),((-7:ℚ)/8),((7185863941:ℚ)/10000000000),((7256140011:ℚ)/10000000000),((-20872420033:ℚ)/22215000000),((-47741047587:ℚ)/55656250000),((9627690243:ℚ)/10000000000),((9633416507:ℚ)/10000000000),((2737309683:ℚ)/10000000000),((829109427:ℚ)/2500000000),((392599406296385644514235091206796274272732157772034865206357:ℚ)/16718736641507092968750000000000000000000000000000000000000000),((461962025263442996368364739:ℚ)/1848320000000000000000000000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell ((4443:ℚ)/6400) ((1781:ℚ)/2560) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1781:ℚ)/2560),((2231:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((1800177629:ℚ)/2500000000),((3635492829:ℚ)/5000000000),((-10458478487:ℚ)/11131250000),((-520054061:ℚ)/606250000),((2405504993:ℚ)/2500000000),((1203461281:ℚ)/1250000000),((551641531:ℚ)/2000000000),((3255908109:ℚ)/10000000000),((29756390434516445247484447866748405420810768304332351239:ℚ)/1267287999350285530090332031250000000000000000000000000000),((1519994988385963627207041:ℚ)/6080000000000000000000000)⟩
theorem valid15 : Valid ninth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound ninth nn0 nn1 Qcell ((1781:ℚ)/2560) ((2231:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((2231:ℚ)/3200),((8943:ℚ)/12800),((-15:ℚ)/16),((-7:ℚ)/8),((3607778539:ℚ)/5000000000),((3642915649:ℚ)/5000000000),((-10480746947:ℚ)/11155000000),((-23974449773:ℚ)/27946875000),((961640533:ℚ)/1000000000),((9622019977:ℚ)/10000000000),((555749933:ℚ)/2000000000),((3194273311:ℚ)/10000000000),((708257663927348748684490657826685355452284475536644120227277:ℚ)/30166669598288463281250000000000000000000000000000000000000000),((6081512158858778579791921:ℚ)/24320000000000000000000000)⟩
theorem valid16 : Valid ninth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((8943:ℚ)/12800) :=
  cell_of_packet ninth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((8943:ℚ)/12800),((4481:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7230403629:ℚ)/10000000000),((730067693:ℚ)/1000000000),((-2100603079:ℚ)/2235750000),((-48052825403:ℚ)/56012500000),((1922169193:ℚ)/2000000000),((1923281067:ℚ)/2000000000),((349868089:ℚ)/1250000000),((1565733989:ℚ)/5000000000),((3950972589156509259246253450805068622283357531265527122141:ℚ)/168298741910354312425781250000000000000000000000000000000000),((1386934104201187006467757337:ℚ)/5544960000000000000000000000)⟩
theorem valid17 : Valid ninth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound ninth nn0 nn1 Qcell ((8943:ℚ)/12800) ((4481:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-15:ℚ)/16),((-7:ℚ)/8),((7245250167:ℚ)/10000000000),((7330368169:ℚ)/10000000000),((-21095104507:ℚ)/22405000000),((-48156751169:ℚ)/56250000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((3067420151:ℚ)/10000000000),((450416119711376164597545987714269152768247219228213513:ℚ)/18979231635210937500000000000000000000000000000000000000),((1387637934942520509196175873:ℚ)/5544960000000000000000000000)⟩
theorem valid18 : Valid ninth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound ninth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-15:ℚ)/16),((-7:ℚ)/8),((7274943209:ℚ)/10000000000),((3680029689:ℚ)/5000000000),((-10592089067:ℚ)/11250000000),((-48364602463:ℚ)/56487500000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((183454363:ℚ)/625000000),((4311715897775187363382965211626919937667793865284538354317451:ℚ)/181728175891113281250000000000000000000000000000000000000000000),((462778848132327135239842539:ℚ)/1848320000000000000000000000)⟩
theorem valid19 : Valid ninth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((1460927241:ℚ)/2000000000),((1477950111:ℚ)/2000000000),((-4254650333:ℚ)/4519000000),((-9714490687:ℚ)/11345000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((1398535481:ℚ)/5000000000),((17609124095398039850773689339975496473858074674233050635309:ℚ)/742362527592486873437500000000000000000000000000000000000000),((55561404421234871360348417:ℚ)/221798400000000000000000000)⟩
theorem valid20 : Valid ninth packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound ninth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-15:ℚ)/16),((-7:ℚ)/8),((3667164577:ℚ)/5000000000),((7449132817:ℚ)/10000000000),((-21451398451:ℚ)/22690000000),((-2217286549:ℚ)/2600000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((331484691:ℚ)/1250000000),((919565135105484788911142268546410771470997851736534071:ℚ)/37965301104250000000000000000000000000000000000000000000),((115870220818801292900829051:ℚ)/462080000000000000000000000)⟩
theorem valid21 : Valid ninth packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-15:ℚ)/16),((-7:ℚ)/8),((7393714917:ℚ)/10000000000),((93856437:ℚ)/125000000),((-270369311:ℚ)/286000000),((-49196004419:ℚ)/57675000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2335228429:ℚ)/10000000000),((1569573821863379647008496811857626065172208516929627949:ℚ)/64847324089762500000000000000000000000000000000000000000),((1391839564274102957225348873:ℚ)/5544960000000000000000000000)⟩
theorem valid22 : Valid ninth packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-15:ℚ)/16),((-7:ℚ)/8),((7453100503:ℚ)/10000000000),((3783948493:ℚ)/5000000000),((-10903845479:ℚ)/11535000000),((-49611703521:ℚ)/58150000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1969338559:ℚ)/10000000000),((4184290799131399893040453979283460298776169050672786357141:ℚ)/172993975840834031250000000000000000000000000000000000000000),((464412101901208805143934571:ℚ)/1848320000000000000000000000)⟩
theorem valid23 : Valid ninth packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-15:ℚ)/16),((-7:ℚ)/8),((1502497183:ℚ)/2000000000),((7686660699:ℚ)/10000000000),((-22163982097:ℚ)/23260000000),((-10005480281:ℚ)/11820000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((759512297:ℚ)/5000000000),((172706665862852356829983030098352120912373784598593759138161:ℚ)/6867902466373837500000000000000000000000000000000000000000000),((18586419478592868522829691:ℚ)/73932800000000000000000000)⟩
theorem valid24 : Valid ninth packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-15:ℚ)/16),((-7:ℚ)/8),((3815628119:ℚ)/5000000000),((1981046711:ℚ)/2500000000),((-5719140133:ℚ)/5910000000),((-25429396833:ℚ)/30500000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),(0:ℚ),((388743115970529199232446082459719825226355381971467827623:ℚ)/14402019172331250000000000000000000000000000000000000000000),((32177967:ℚ)/128000000)⟩
theorem valid25 : Valid ninth packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-15:ℚ)/16),((-7:ℚ)/8),((983599373:ℚ)/1250000000),((4199617267:ℚ)/5000000000),((-12150851801:ℚ)/12200000000),((-243155393:ℚ)/300000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((777004769419166577192029390526889019484771236249559697:ℚ)/25535362500000000000000000000000000000000000000000000000),((32177967:ℚ)/128000000)⟩
theorem valid26 : Valid ninth packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-15:ℚ)/16),((-7:ℚ)/8),((8343865659:ℚ)/10000000000),((10299379983:ℚ)/10000000000),(-1:ℚ),((-55847059613:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((436048474326548818498022528884090283:ℚ)/12000000000000000000000000000000000000),((32177967:ℚ)/128000000)⟩
theorem valid27 : Valid ninth packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-15:ℚ)/16),((-7:ℚ)/8),((2048816241:ℚ)/2000000000),((5507637:ℚ)/3906250),(-1:ℚ),((-13829713687:ℚ)/22080000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((4982782295799915691106891:ℚ)/121881600000000000000000000),((32177967:ℚ)/128000000)⟩
theorem valid28 : Valid ninth packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet28 valid28
private theorem node1_3 :
    CellBound ninth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((4329:ℚ)/6400) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound ninth nn0 nn1 Qcell ((4329:ℚ)/6400) ((4367:ℚ)/6400) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((4367:ℚ)/6400) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((4367:ℚ)/6400) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound ninth nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound ninth nn0 nn1 Qcell ((4367:ℚ)/6400) ((881:ℚ)/1280) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound ninth nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound ninth nn0 nn1 Qcell ((881:ℚ)/1280) ((4443:ℚ)/6400) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound ninth nn0 nn1 Qcell ((4367:ℚ)/6400) ((4443:ℚ)/6400) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((4443:ℚ)/6400) :=
  cell_join node0_7 node7_14
private theorem node15_17 :
    CellBound ninth nn0 nn1 Qcell ((1781:ℚ)/2560) ((8943:ℚ)/12800) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound ninth nn0 nn1 Qcell ((4443:ℚ)/6400) ((8943:ℚ)/12800) :=
  cell_join leaf14 node15_17
private theorem node17_19 :
    CellBound ninth nn0 nn1 Qcell ((8943:ℚ)/12800) ((45:ℚ)/64) :=
  cell_join leaf17 leaf18
private theorem node19_21 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_join leaf19 leaf20
private theorem node17_21 :
    CellBound ninth nn0 nn1 Qcell ((8943:ℚ)/12800) ((2269:ℚ)/3200) :=
  cell_join node17_19 node19_21
private theorem node14_21 :
    CellBound ninth nn0 nn1 Qcell ((4443:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_join node14_17 node17_21
private theorem node21_23 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf21 leaf22
private theorem node23_25 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join leaf23 leaf24
private theorem node21_25 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((591:ℚ)/800) :=
  cell_join node21_23 node23_25
private theorem node25_27 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf25 leaf26
private theorem node27_29 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf27 leaf28
private theorem node25_29 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node25_27 node27_29
private theorem node21_29 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node21_25 node25_29
private theorem node14_29 :
    CellBound ninth nn0 nn1 Qcell ((4443:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node14_21 node21_29
private theorem node0_29 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_14 node14_29
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_29
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28]
theorem packet_count : packets.length = 29 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC02
#check @N11Formalization.C450NinthGroupedC02.bound
#print axioms N11Formalization.C450NinthGroupedC02.valid0
#print axioms N11Formalization.C450NinthGroupedC02.valid1
#print axioms N11Formalization.C450NinthGroupedC02.valid2
#print axioms N11Formalization.C450NinthGroupedC02.valid3
#print axioms N11Formalization.C450NinthGroupedC02.valid4
#print axioms N11Formalization.C450NinthGroupedC02.valid5
#print axioms N11Formalization.C450NinthGroupedC02.valid6
#print axioms N11Formalization.C450NinthGroupedC02.valid7
#print axioms N11Formalization.C450NinthGroupedC02.valid8
#print axioms N11Formalization.C450NinthGroupedC02.valid9
#print axioms N11Formalization.C450NinthGroupedC02.valid10
#print axioms N11Formalization.C450NinthGroupedC02.valid11
#print axioms N11Formalization.C450NinthGroupedC02.valid12
#print axioms N11Formalization.C450NinthGroupedC02.valid13
#print axioms N11Formalization.C450NinthGroupedC02.valid14
#print axioms N11Formalization.C450NinthGroupedC02.valid15
#print axioms N11Formalization.C450NinthGroupedC02.valid16
#print axioms N11Formalization.C450NinthGroupedC02.valid17
#print axioms N11Formalization.C450NinthGroupedC02.valid18
#print axioms N11Formalization.C450NinthGroupedC02.valid19
#print axioms N11Formalization.C450NinthGroupedC02.valid20
#print axioms N11Formalization.C450NinthGroupedC02.valid21
#print axioms N11Formalization.C450NinthGroupedC02.valid22
#print axioms N11Formalization.C450NinthGroupedC02.valid23
#print axioms N11Formalization.C450NinthGroupedC02.valid24
#print axioms N11Formalization.C450NinthGroupedC02.valid25
#print axioms N11Formalization.C450NinthGroupedC02.valid26
#print axioms N11Formalization.C450NinthGroupedC02.valid27
#print axioms N11Formalization.C450NinthGroupedC02.valid28
#print axioms N11Formalization.C450NinthGroupedC02.bound
#print axioms N11Formalization.C450NinthGroupedC02.endpoint_checks
