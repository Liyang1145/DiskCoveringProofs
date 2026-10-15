import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC05
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((-3:ℚ)/4),((-11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((3323901947:ℚ)/5000000000),((53443577:ℚ)/78125000),((-139080731:ℚ)/193750000),((-30802921417:ℚ)/50550000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((5059570649:ℚ)/10000000000),((1168360671561477631871967542868407424871957919238001219:ℚ)/15487674311828613281250000000000000000000000000000000000),((12456746589324211056327803:ℚ)/28880000000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((103:ℚ)/160),((-3:ℚ)/4),((-11:ℚ)/16),((3383462597:ℚ)/5000000000),((6959860301:ℚ)/10000000000),((-18159580903:ℚ)/25275000000),((-31458088567:ℚ)/51500000000),((9864186891:ℚ)/10000000000),((2482425353:ℚ)/2500000000),((1649979683:ℚ)/10000000000),((4726063221:ℚ)/10000000000),((242568634236070387819905187534862540304961419422881116763087:ℚ)/3211805328392285156250000000000000000000000000000000000000000),((12461230460163781820539003:ℚ)/28880000000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((1377206547:ℚ)/2000000000),((7019396947:ℚ)/10000000000),((-18338190841:ℚ)/25750000000),((-4281757339:ℚ)/6930000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((873850987:ℚ)/2000000000),((312587355100625887949090180464325932040773187825211564085129:ℚ)/4270679109887695312500000000000000000000000000000000000000000),((1993509215256629950538603:ℚ)/4620800000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((3472790791:ℚ)/5000000000),((3539465327:ℚ)/5000000000),((-9258395981:ℚ)/12993750000),((-32440698701:ℚ)/52450000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((4180254251:ℚ)/10000000000),((276332855359290301654469047494153868592476607879064565436047:ℚ)/3772024652273040390014648437500000000000000000000000000000000),((12461553301640720193833027:ℚ)/28880000000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1049:ℚ)/1600),((843:ℚ)/1280),((-3:ℚ)/4),((-11:ℚ)/16),((7005127267:ℚ)/10000000000),((710869643:ℚ)/1000000000),((-1860608929:ℚ)/2622500000),((-65536399937:ℚ)/105375000000),((978862711:ℚ)/1000000000),((9803196499:ℚ)/10000000000),((2059717253:ℚ)/10000000000),((1991427833:ℚ)/5000000000),((19263880062434557147361099647239966559543973628818196001:ℚ)/267030213180729492187500000000000000000000000000000000000),((49842272266147251051517963:ℚ)/115520000000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((1049:ℚ)/1600) ((843:ℚ)/1280) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((843:ℚ)/1280),((2117:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((140697979:ℚ)/200000000),((7138461501:ℚ)/10000000000),((-18695384503:ℚ)/26343750000),((-1317277769:ℚ)/2117000000),((9774321709:ℚ)/10000000000),((1957725423:ℚ)/2000000000),((425706267:ℚ)/2000000000),((1940303777:ℚ)/5000000000),((12320803194092032373670719966404239732491264372770687113390703:ℚ)/170699900346992683410644531250000000000000000000000000000000000),((19938556994243260573947:ℚ)/46208000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((843:ℚ)/1280) ((2117:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((4253:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((56517359:ℚ)/80000000),((57345807:ℚ)/80000000),((-150277421:ℚ)/211700000),((-529530949:ℚ)/850600000),((9760276751:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((438804929:ℚ)/2000000000),((943934521:ℚ)/2500000000),((77456163914323566636116481436237708730131586185687962687:ℚ)/1072589044734778231250000000000000000000000000000000000000),((3190430592020821169427:ℚ)/7393280000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((2117:ℚ)/3200) ((4253:ℚ)/6400) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4253:ℚ)/6400),((267:ℚ)/400),((-3:ℚ)/4),((-11:ℚ)/16),((7094440051:ℚ)/10000000000),((1799497391:ℚ)/2500000000),((-4718492173:ℚ)/6645312500),((-66518840561:ℚ)/106800000000),((4873244381:ℚ)/5000000000),((2440069189:ℚ)/2500000000),((2256500263:ℚ)/10000000000),((3668021903:ℚ)/10000000000),((100765434375416058764999099539678216332666903675149267713559:ℚ)/1394689366919213104248046875000000000000000000000000000000000),((49854528815401911704154667:ℚ)/115520000000000000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((4253:ℚ)/6400) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((267:ℚ)/400),((4291:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7124209489:ℚ)/10000000000),((289110103:ℚ)/400000000),((-758530309:ℚ)/1068000000),((-66846304379:ℚ)/107275000000),((1216619291:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1158107867:ℚ)/5000000000),((3557199869:ℚ)/10000000000),((158332867116579874318615931979858230681551737570512020447:ℚ)/2190437321381268750000000000000000000000000000000000000000),((49858544933278806795983507:ℚ)/115520000000000000000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-3:ℚ)/4),((-11:ℚ)/16),((3576989099:ℚ)/5000000000),((3628757459:ℚ)/5000000000),((-9526272377:ℚ)/13409375000),((-33586880089:ℚ)/53875000000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((3442971529:ℚ)/10000000000),((37957939295475526375844292819162077570598508842966994261457:ℚ)/524881708474843418598175048828125000000000000000000000000000),((12465631589535709040431067:ℚ)/28880000000000000000000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((1795936547:ℚ)/2500000000),((3643638301:ℚ)/5000000000),((-9570914903:ℚ)/13468750000),((-16875302017:ℚ)/27056250000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((3324985261:ℚ)/10000000000),((431353020372479790445429553837228386019033493758395592753503:ℚ)/5962052927497351169586181640625000000000000000000000000000000),((3116654568340345093078603:ℚ)/7220000000000000000000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-3:ℚ)/4),((-11:ℚ)/16),((7213513469:ℚ)/10000000000),((3658518817:ℚ)/5000000000),((-9615556451:ℚ)/13528125000),((-67828648159:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((640565039:ℚ)/2000000000),((5961105051898375007874311402552727378763588023752623663661:ℚ)/82356703272536373138427734375000000000000000000000000000000),((49870385141766347862099787:ℚ)/115520000000000000000000000)⟩
theorem valid11 : Valid source19 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source19 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1087:ℚ)/1600),((4367:ℚ)/6400),((-3:ℚ)/4),((-11:ℚ)/16),((7243280049:ℚ)/10000000000),((293871921:ℚ)/400000000),((-772815763:ℚ)/1087000000),((-68156080539:ℚ)/109175000000),((2420321489:ℚ)/2500000000),((2423459781:ℚ)/2500000000),((2531487941:ℚ)/10000000000),((3075993491:ℚ)/10000000000),((692833291246662454492268436069808610902489441589882250009:ℚ)/9567865261734987109375000000000000000000000000000000000000),((49874262507855074905581267:ℚ)/115520000000000000000000000)⟩
theorem valid12 : Valid source19 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((4367:ℚ)/6400) :=
  cell_of_packet source19 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4367:ℚ)/6400),((2193:ℚ)/3200),((-3:ℚ)/4),((-11:ℚ)/16),((7273045939:ℚ)/10000000000),((3688278891:ℚ)/5000000000),((-9704836673:ℚ)/13646875000),((-68483505329:ℚ)/109650000000),((4834485079:ℚ)/5000000000),((9681285961:ℚ)/10000000000),((2580203419:ℚ)/10000000000),((1471942881:ℚ)/5000000000),((230589968284630113697590420959567474569378519321365254661169:ℚ)/3183066264591088986396789550781250000000000000000000000000000),((49878105193920888616513707:ℚ)/115520000000000000000000000)⟩
theorem valid13 : Valid source19 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source19 nn0 nn1 Qcell ((4367:ℚ)/6400) ((2193:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/4),((-11:ℚ)/16),((7302811147:ℚ)/10000000000),((3718037713:ℚ)/5000000000),((-227770073:ℚ)/318750000),((-68810922617:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((87679881:ℚ)/312500000),((6831754623499005557093111087879758917553346905038375271:ℚ)/92847907239532470703125000000000000000000000000000000000),((49894195416605740349589403:ℚ)/115520000000000000000000000)⟩
theorem valid14 : Valid source19 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source19 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-3:ℚ)/4),((-11:ℚ)/16),((7362339553:ℚ)/10000000000),((7555103463:ℚ)/10000000000),((-19945310389:ℚ)/27650000000),((-69465735083:ℚ)/112500000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1253703809:ℚ)/5000000000),((1056258076515987613986152809918908758555243681722923629:ℚ)/13934430477905273437500000000000000000000000000000000000),((49926269613753490471810803:ℚ)/115520000000000000000000000)⟩
theorem valid15 : Valid source19 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source19 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-3:ℚ)/4),((-11:ℚ)/16),((7481388563:ℚ)/10000000000),((7674122233:ℚ)/10000000000),((-20302366699:ℚ)/28125000000),((-5444251861:ℚ)/8800000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1769041157:ℚ)/10000000000),((1275834305377632792222716300776400486852302125839728507897:ℚ)/16824531555175781250000000000000000000000000000000000000000),((49910282362034140125340523:ℚ)/115520000000000000000000000)⟩
theorem valid16 : Valid source19 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-3:ℚ)/4),((-11:ℚ)/16),((1520085521:ℚ)/2000000000),((8625987883:ℚ)/10000000000),((-23157963649:ℚ)/28600000000),((-14416940731:ℚ)/25920000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((853507984440956093907086514374860077476818352800827759311:ℚ)/8199026550000000000000000000000000000000000000000000000000),((3453971:ℚ)/8000000)⟩
theorem valid17 : Valid source19 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/4),((-11:ℚ)/16),((8552433903:ℚ)/10000000000),((2105730713:ℚ)/2000000000),((-5773192139:ℚ)/6480000000),((-82556772933:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((40964974064346295886694858956114241395986689939357131:ℚ)/318864600000000000000000000000000000000000000000000000),((3453971:ℚ)/8000000)⟩
theorem valid18 : Valid source19 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/4),((-11:ℚ)/16),((653456273:ℚ)/625000000),((14331780163:ℚ)/10000000000),(-1:ℚ),((-6468019003:ℚ)/13800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((1099687481574403700373059:ℚ)/6348000000000000000000000),((3453971:ℚ)/8000000)⟩
theorem valid19 : Valid source19 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet19 valid19
private theorem node0_2 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source19 nn0 nn1 Qcell ((2079:ℚ)/3200) ((843:ℚ)/1280) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source19 nn0 nn1 Qcell ((103:ℚ)/160) ((843:ℚ)/1280) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((843:ℚ)/1280) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source19 nn0 nn1 Qcell ((843:ℚ)/1280) ((4253:ℚ)/6400) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source19 nn0 nn1 Qcell ((4253:ℚ)/6400) ((431:ℚ)/640) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source19 nn0 nn1 Qcell ((843:ℚ)/1280) ((431:ℚ)/640) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((431:ℚ)/640) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source19 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source19 nn0 nn1 Qcell ((4367:ℚ)/6400) ((553:ℚ)/800) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source19 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join node10_12 node12_15
private theorem node15_17 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf15 leaf16
private theorem node18_20 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf17 node18_20
private theorem node15_20 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node15_17 node17_20
private theorem node10_20 :
    CellBound source19 nn0 nn1 Qcell ((431:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node10_15 node15_20
private theorem node0_20 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_20
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_20
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19]
theorem packet_count : packets.length = 20 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC05
#check @N11Formalization.C450Source19GroupedC05.bound
#print axioms N11Formalization.C450Source19GroupedC05.valid0
#print axioms N11Formalization.C450Source19GroupedC05.valid1
#print axioms N11Formalization.C450Source19GroupedC05.valid2
#print axioms N11Formalization.C450Source19GroupedC05.valid3
#print axioms N11Formalization.C450Source19GroupedC05.valid4
#print axioms N11Formalization.C450Source19GroupedC05.valid5
#print axioms N11Formalization.C450Source19GroupedC05.valid6
#print axioms N11Formalization.C450Source19GroupedC05.valid7
#print axioms N11Formalization.C450Source19GroupedC05.valid8
#print axioms N11Formalization.C450Source19GroupedC05.valid9
#print axioms N11Formalization.C450Source19GroupedC05.valid10
#print axioms N11Formalization.C450Source19GroupedC05.valid11
#print axioms N11Formalization.C450Source19GroupedC05.valid12
#print axioms N11Formalization.C450Source19GroupedC05.valid13
#print axioms N11Formalization.C450Source19GroupedC05.valid14
#print axioms N11Formalization.C450Source19GroupedC05.valid15
#print axioms N11Formalization.C450Source19GroupedC05.valid16
#print axioms N11Formalization.C450Source19GroupedC05.valid17
#print axioms N11Formalization.C450Source19GroupedC05.valid18
#print axioms N11Formalization.C450Source19GroupedC05.valid19
#print axioms N11Formalization.C450Source19GroupedC05.bound
#print axioms N11Formalization.C450Source19GroupedC05.endpoint_checks
