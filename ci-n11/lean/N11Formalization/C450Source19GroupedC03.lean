import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((842476767:ℚ)/1250000000),((3469564217:ℚ)/5000000000),((-695708049:ℚ)/800000000),((-3170732657:ℚ)/4212500000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((1200959377:ℚ)/2500000000),((6132985570841869746867623868457099029:ℚ)/72684160000000000000000000000000000000),((375354605588754961713691:ℚ)/640000000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((342940151:ℚ)/500000000),((6998593137:ℚ)/10000000000),((-43550151959:ℚ)/50550000000),((-3882221963:ℚ)/5102500000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((4453171937:ℚ)/10000000000),((1001495912968204731084562377622913990002472491909644088693:ℚ)/12437205759188964843750000000000000000000000000000000000000),((1628577294522248614174548713:ℚ)/2772480000000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((6918294117:ℚ)/10000000000),((3529028091:ℚ)/5000000000),((-21983196637:ℚ)/25512500000),((-78417823521:ℚ)/103000000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((2133918139:ℚ)/5000000000),((265912348154462593273928924703876516452918630194826099286493:ℚ)/3303199275764978027343750000000000000000000000000000000000000),((407779672273335462811815137:ℚ)/693120000000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((1395556613:ℚ)/2000000000),((3558758807:ℚ)/5000000000),((-22191311649:ℚ)/25750000000),((-15838235969:ℚ)/20790000000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((203731237:ℚ)/500000000),((49099764558124452472627892126915057437837704510074802957943:ℚ)/610097015698242187500000000000000000000000000000000000000000),((136138361418369097160899891:ℚ)/231040000000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((281490797:ℚ)/400000000),((357362387:ℚ)/500000000),((-247726301:ℚ)/288750000),((-3198580361:ℚ)/4177000000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((484044329:ℚ)/1250000000),((4693643877975110366821515684276840110956870049969497277:ℚ)/59665360651089477539062500000000000000000000000000000000),((1362442713850149202832571:ℚ)/2310400000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((706701259:ℚ)/1000000000),((3588488739:ℚ)/5000000000),((-22399421173:ℚ)/26106250000),((-8035116367:ℚ)/10490000000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((3767367977:ℚ)/10000000000),((2406533065009538795828948771921195549536233567634865775306239:ℚ)/30591761181292126846313476562500000000000000000000000000000000),((409050560050287467555884817:ℚ)/693120000000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1049:ℚ)/1600),((8411:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((3548377377:ℚ)/5000000000),((1797960551:ℚ)/2500000000),((-11225723857:ℚ)/13112500000),((-40368905901:ℚ)/52568750000),((9795878581:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((1011977397:ℚ)/5000000000),((457440007:ℚ)/1250000000),((77534578843167161655643970967936457703718139006859860483387179:ℚ)/996854530299972277832031250000000000000000000000000000000000000),((34100786585218589398354259:ℚ)/57760000000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8411:ℚ)/12800) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((8411:ℚ)/12800),((843:ℚ)/1280),((-7:ℚ)/8),((-13:ℚ)/16),((142232513:ℚ)/200000000),((3603353417:ℚ)/5000000000),((-22503473919:ℚ)/26284375000),((-1618622669:ℚ)/2107500000),((978862711:ℚ)/1000000000),((4897939293:ℚ)/5000000000),((2059717253:ℚ)/10000000000),((3604442967:ℚ)/10000000000),((20911491924819267744430013844649792457024333486142999665231:ℚ)/268848040731000658035278320312500000000000000000000000000000),((136456107334726594844097651:ℚ)/231040000000000000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((8411:ℚ)/12800) ((843:ℚ)/1280) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((843:ℚ)/1280),((8449:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7126496423:ℚ)/10000000000),((7221571371:ℚ)/10000000000),((-45110999597:ℚ)/52687500000),((-81124453499:ℚ)/105612500000),((4890720817:ℚ)/5000000000),((1957725423:ℚ)/2000000000),((83782417:ℚ)/400000000),((3548549479:ℚ)/10000000000),((1268953425945042027916380533842689391183401205428202539883559111:ℚ)/16313735705770991134643554687500000000000000000000000000000000000),((1638108836107710201498777857:ℚ)/2772480000000000000000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((843:ℚ)/1280) ((8449:ℚ)/12800) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((8449:ℚ)/12800),((2117:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((285654683:ℚ)/400000000),((1447287163:ℚ)/2000000000),((-531941773:ℚ)/621250000),((-3252710879:ℚ)/4234000000),((9774321709:ℚ)/10000000000),((9781441639:ℚ)/10000000000),((425706267:ℚ)/2000000000),((698360063:ℚ)/2000000000),((74632656394113187041842147483028413620485700820042094177:ℚ)/959451218167370605468750000000000000000000000000000000000),((21849925338174499291069771:ℚ)/36966400000000000000000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((8449:ℚ)/12800) ((2117:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2117:ℚ)/3200),((8487:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((1431247521:ℚ)/2000000000),((1450260033:ℚ)/2000000000),((-9063820231:ℚ)/10585000000),((-5434072591:ℚ)/7072500000),((9767266893:ℚ)/10000000000),((4887160857:ℚ)/5000000000),((2161672951:ℚ)/10000000000),((3434152997:ℚ)/10000000000),((1538213477016691501298378538633969383566831459262527387965199:ℚ)/19774123608104617968750000000000000000000000000000000000000000),((65575199229588538330953353:ℚ)/110899200000000000000000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell ((2117:ℚ)/3200) ((8487:ℚ)/12800) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((8487:ℚ)/12800),((4253:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((1434221603:ℚ)/2000000000),((908270553:ℚ)/1250000000),((-5677893871:ℚ)/6630468750),((-16340880839:ℚ)/21265000000),((9760276751:ℚ)/10000000000),((4883633449:ℚ)/5000000000),((438804929:ℚ)/2000000000),((3375561437:ℚ)/10000000000),((83366337631659994139292085382527946046949992184627341052351:ℚ)/1071663305071377146244049072265625000000000000000000000000000),((25625243396335755587596793:ℚ)/43320000000000000000000000)⟩
theorem valid11 : Valid source19 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source19 nn0 nn1 Qcell ((8487:ℚ)/12800) ((4253:ℚ)/6400) :=
  cell_of_packet source19 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4253:ℚ)/6400),((341:ℚ)/512),((-7:ℚ)/8),((-13:ℚ)/16),((3592989153:ℚ)/5000000000),((728102859:ℚ)/1000000000),((-4552720013:ℚ)/5316250000),((-40948858989:ℚ)/53281250000),((195067017:ℚ)/200000000),((2440069189:ℚ)/2500000000),((1112811311:ℚ)/5000000000),((3315975511:ℚ)/10000000000),((10193684725814597686873237925085996357726704611424143997:ℚ)/131034666753981987304687500000000000000000000000000000000),((16406511901545180597574337:ℚ)/27724800000000000000000000)⟩
theorem valid12 : Valid source19 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source19 nn0 nn1 Qcell ((4253:ℚ)/6400) ((341:ℚ)/512) :=
  cell_of_packet source19 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((341:ℚ)/512),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((3600424239:ℚ)/5000000000),((3647946333:ℚ)/5000000000),((-22815624331:ℚ)/26640625000),((-153728521:ℚ)/200000000),((4873244381:ℚ)/5000000000),((1950670171:ℚ)/2000000000),((2256500263:ℚ)/10000000000),((65106811:ℚ)/200000000),((18386560304708354203379610218067810668354869908300976229:ℚ)/236343270540237426757812500000000000000000000000000000000),((410321704808678721390759953:ℚ)/693120000000000000000000000)⟩
theorem valid13 : Valid source19 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source19 nn0 nn1 Qcell ((341:ℚ)/512) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((267:ℚ)/400),((8563:ℚ)/12800),((-7:ℚ)/8),((-13:ℚ)/16),((7215718533:ℚ)/10000000000),((7310756651:ℚ)/10000000000),((-45735296557:ℚ)/53400000000),((-82284340929:ℚ)/107037500000),((9739690061:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((1143344217:ℚ)/5000000000),((399199591:ℚ)/1250000000),((1809687423936355273961684523749439713652530849940109755193503197:ℚ)/23261323531932450000000000000000000000000000000000000000000000000),((547307488187649401038534059:ℚ)/924160000000000000000000000)⟩
theorem valid14 : Valid source19 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((8563:ℚ)/12800) :=
  cell_of_packet source19 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((8563:ℚ)/12800),((4291:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((723058847:ℚ)/1000000000),((7325620547:ℚ)/10000000000),((-45839343829:ℚ)/53518750000),((-8247765011:ℚ)/10727500000),((1216619291:ℚ)/1250000000),((4869845033:ℚ)/5000000000),((1158107867:ℚ)/5000000000),((3130678371:ℚ)/10000000000),((21444485944274854125548564860403310170407895603994406644577327:ℚ)/275635376539792192149162292480468750000000000000000000000000000),((547519375408126812784869531:ℚ)/924160000000000000000000000)⟩
theorem valid15 : Valid source19 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source19 nn0 nn1 Qcell ((8563:ℚ)/12800) ((4291:ℚ)/6400) :=
  cell_of_packet source19 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((4291:ℚ)/6400),((431:ℚ)/640),((-7:ℚ)/8),((-13:ℚ)/16),((7245458291:ℚ)/10000000000),((7355348071:ℚ)/10000000000),((-46047436497:ℚ)/53637500000),((-82670957783:ℚ)/107750000000),((607479381:ℚ)/625000000),((9732954333:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((191657069:ℚ)/625000000),((55050646032778097317909283598417068682473604892581218939379:ℚ)/699842277966457891464233398437500000000000000000000000000000),((547943166167541919613595219:ℚ)/924160000000000000000000000)⟩
theorem valid16 : Valid source19 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source19 nn0 nn1 Qcell ((4291:ℚ)/6400) ((431:ℚ)/640) :=
  cell_of_packet source19 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((431:ℚ)/640),((4329:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((1818799397:ℚ)/2500000000),((7385075243:ℚ)/10000000000),((-46255526701:ℚ)/53875000000),((-20764392161:ℚ)/27056250000),((2426658193:ℚ)/2500000000),((9719670101:ℚ)/10000000000),((2428221417:ℚ)/10000000000),((366764093:ℚ)/1250000000),((30014444784182220071217161054355780744026752324839200575352189:ℚ)/381571387359830474853515625000000000000000000000000000000000000),((548366978760135519822642091:ℚ)/924160000000000000000000000)⟩
theorem valid17 : Valid source19 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source19 nn0 nn1 Qcell ((431:ℚ)/640) ((4329:ℚ)/6400) :=
  cell_of_packet source19 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((4329:ℚ)/6400),((1087:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((1826234107:ℚ)/2500000000),((1853700517:ℚ)/2500000000),((-3871967873:ℚ)/4509375000),((-20861043391:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9706632777:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2795639721:ℚ)/10000000000),((479856063255385149749964818739993855035275400278630034149:ℚ)/6100496538706398010253906250000000000000000000000000000000),((34299425828515266289610251:ℚ)/57760000000000000000000000)⟩
theorem valid18 : Valid source19 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source19 nn0 nn1 Qcell ((4329:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((7334674819:ℚ)/10000000000),((7474254693:ℚ)/10000000000),((-46879782851:ℚ)/54350000000),((-83830772647:ℚ)/109650000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((2650141609:ℚ)/10000000000),((32307399427502277790036104200195112878662894362507122343094739:ℚ)/402137598368310351562500000000000000000000000000000000000000000),((1648915644550213567357696673:ℚ)/2772480000000000000000000000)⟩
theorem valid19 : Valid source19 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source19 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((295766011:ℚ)/400000000),((3766852991:ℚ)/5000000000),((-7882656979:ℚ)/9137500000),((-3384158143:ℚ)/4424000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((583187917:ℚ)/2500000000),((784250762062553326046088986005798758689742478604036898343:ℚ)/9764627726049613952636718750000000000000000000000000000000),((137621592863752219777144579:ℚ)/231040000000000000000000000)⟩
theorem valid20 : Valid source19 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source19 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-7:ℚ)/8),((-13:ℚ)/16),((931703:ℚ)/1250000),((478287793:ℚ)/625000000),((-3008014551:ℚ)/3456250000),((-10672139:ℚ)/14062500),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((393163011:ℚ)/2000000000),((27725691620846232325547137261891104061916859944961371:ℚ)/331772154235839843750000000000000000000000000000000000),((7637561:ℚ)/12800000)⟩
theorem valid21 : Valid source19 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source19 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((7572566437:ℚ)/10000000000),((1554299689:ℚ)/2000000000),((-9792097823:ℚ)/11250000000),((-7902123971:ℚ)/10400000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((849923889:ℚ)/10000000000),((125498748830016552038451797855365894069503114768705448789:ℚ)/1503918457031250000000000000000000000000000000000000000000),((7637561:ℚ)/12800000)⟩
theorem valid22 : Valid source19 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((3845751233:ℚ)/5000000000),((8722496527:ℚ)/10000000000),((-55617475689:ℚ)/57200000000),((-44234766029:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((27115555701683909134166219211598470018348883737010677579787:ℚ)/213174690300000000000000000000000000000000000000000000000000),((7637561:ℚ)/12800000)⟩
theorem valid23 : Valid source19 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((8642793951:ℚ)/10000000000),((2655980789:ℚ)/2500000000),(-1:ℚ),((-100836321363:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((2749372065017629015337853706361696641:ℚ)/19200000000000000000000000000000000000),((7637561:ℚ)/12800000)⟩
theorem valid24 : Valid source19 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((10544639721:ℚ)/10000000000),((7212798563:ℚ)/5000000000),(-1:ℚ),((-41853438791:ℚ)/73600000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((86174078256689320606679393:ℚ)/541696000000000000000000000),((7637561:ℚ)/12800000)⟩
theorem valid25 : Valid source19 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet25 valid25
private theorem node1_3 :
    CellBound source19 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source19 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source19 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source19 nn0 nn1 Qcell ((8411:ℚ)/12800) ((8449:ℚ)/12800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source19 nn0 nn1 Qcell ((1049:ℚ)/1600) ((8449:ℚ)/12800) :=
  cell_join leaf6 node7_9
private theorem node9_11 :
    CellBound source19 nn0 nn1 Qcell ((8449:ℚ)/12800) ((8487:ℚ)/12800) :=
  cell_join leaf9 leaf10
private theorem node11_13 :
    CellBound source19 nn0 nn1 Qcell ((8487:ℚ)/12800) ((341:ℚ)/512) :=
  cell_join leaf11 leaf12
private theorem node9_13 :
    CellBound source19 nn0 nn1 Qcell ((8449:ℚ)/12800) ((341:ℚ)/512) :=
  cell_join node9_11 node11_13
private theorem node6_13 :
    CellBound source19 nn0 nn1 Qcell ((1049:ℚ)/1600) ((341:ℚ)/512) :=
  cell_join node6_9 node9_13
private theorem node0_13 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((341:ℚ)/512) :=
  cell_join node0_6 node6_13
private theorem node14_16 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((4291:ℚ)/6400) :=
  cell_join leaf14 leaf15
private theorem node13_16 :
    CellBound source19 nn0 nn1 Qcell ((341:ℚ)/512) ((4291:ℚ)/6400) :=
  cell_join leaf13 node14_16
private theorem node17_19 :
    CellBound source19 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_join leaf17 leaf18
private theorem node16_19 :
    CellBound source19 nn0 nn1 Qcell ((4291:ℚ)/6400) ((1087:ℚ)/1600) :=
  cell_join leaf16 node17_19
private theorem node13_19 :
    CellBound source19 nn0 nn1 Qcell ((341:ℚ)/512) ((1087:ℚ)/1600) :=
  cell_join node13_16 node16_19
private theorem node20_22 :
    CellBound source19 nn0 nn1 Qcell ((2193:ℚ)/3200) ((45:ℚ)/64) :=
  cell_join leaf20 leaf21
private theorem node19_22 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf19 node20_22
private theorem node22_24 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((81:ℚ)/100) :=
  cell_join leaf22 leaf23
private theorem node24_26 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf24 leaf25
private theorem node22_26 :
    CellBound source19 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node22_24 node24_26
private theorem node19_26 :
    CellBound source19 nn0 nn1 Qcell ((1087:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node19_22 node22_26
private theorem node13_26 :
    CellBound source19 nn0 nn1 Qcell ((341:ℚ)/512) ((69:ℚ)/50) :=
  cell_join node13_19 node19_26
private theorem node0_26 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_13 node13_26
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_26
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25]
theorem packet_count : packets.length = 26 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC03
#check @N11Formalization.C450Source19GroupedC03.bound
#print axioms N11Formalization.C450Source19GroupedC03.valid0
#print axioms N11Formalization.C450Source19GroupedC03.valid1
#print axioms N11Formalization.C450Source19GroupedC03.valid2
#print axioms N11Formalization.C450Source19GroupedC03.valid3
#print axioms N11Formalization.C450Source19GroupedC03.valid4
#print axioms N11Formalization.C450Source19GroupedC03.valid5
#print axioms N11Formalization.C450Source19GroupedC03.valid6
#print axioms N11Formalization.C450Source19GroupedC03.valid7
#print axioms N11Formalization.C450Source19GroupedC03.valid8
#print axioms N11Formalization.C450Source19GroupedC03.valid9
#print axioms N11Formalization.C450Source19GroupedC03.valid10
#print axioms N11Formalization.C450Source19GroupedC03.valid11
#print axioms N11Formalization.C450Source19GroupedC03.valid12
#print axioms N11Formalization.C450Source19GroupedC03.valid13
#print axioms N11Formalization.C450Source19GroupedC03.valid14
#print axioms N11Formalization.C450Source19GroupedC03.valid15
#print axioms N11Formalization.C450Source19GroupedC03.valid16
#print axioms N11Formalization.C450Source19GroupedC03.valid17
#print axioms N11Formalization.C450Source19GroupedC03.valid18
#print axioms N11Formalization.C450Source19GroupedC03.valid19
#print axioms N11Formalization.C450Source19GroupedC03.valid20
#print axioms N11Formalization.C450Source19GroupedC03.valid21
#print axioms N11Formalization.C450Source19GroupedC03.valid22
#print axioms N11Formalization.C450Source19GroupedC03.valid23
#print axioms N11Formalization.C450Source19GroupedC03.valid24
#print axioms N11Formalization.C450Source19GroupedC03.valid25
#print axioms N11Formalization.C450Source19GroupedC03.bound
#print axioms N11Formalization.C450Source19GroupedC03.endpoint_checks
