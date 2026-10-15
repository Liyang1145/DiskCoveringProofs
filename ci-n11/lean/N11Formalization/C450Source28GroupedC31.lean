import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC31
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨((7:ℚ)/8),((15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((7:ℚ)/8),((15:ℚ)/16),((517609889:ℚ)/1000000000),((5507780479:ℚ)/10000000000),((43255041:ℚ)/50000000),(1:ℚ),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((8215793207:ℚ)/10000000000),((-173245318335925078986301693179:ℚ)/390625000000000000000000000000),((-7308408284160429228934383:ℚ)/18483200000000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((2707010123:ℚ)/5000000000),((718248019:ℚ)/1250000000),((23109070861:ℚ)/26700000000),(1:ℚ),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7779253227:ℚ)/10000000000),((-205961911414035693182104825446371341211565811039441279:ℚ)/464701245117187500000000000000000000000000000000000000),((-9387382969891272616450893:ℚ)/24320000000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((5651911543:ℚ)/10000000000),((5865067461:ℚ)/10000000000),((47883380801:ℚ)/54350000000),((7017067461:ℚ)/7120000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7322492363:ℚ)/10000000000),((-462126733469374055467505368061598019716528345088580961059:ℚ)/1003410549218750000000000000000000000000000000000000000000),((-705004848811557286824898527:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((1442711727:ℚ)/2500000000),((1184920953:ℚ)/2000000000),((12178982089:ℚ)/13706250000),((4245962859:ℚ)/4348000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((7085258361:ℚ)/10000000000),((-629041447565043803807189963517784334226896503449522217:ℚ)/1341080100631713867187500000000000000000000000000000000),((-43799695755192573989457167:ℚ)/115520000000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((364394511:ℚ)/625000000),((5984139271:ℚ)/10000000000),((3070761577:ℚ)/3456250000),((7136139271:ℚ)/7310000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((6964157:ℚ)/10000000),((-5669484484441383104873003705638201617535790164075129:ℚ)/12095859789848327636718750000000000000000000000000000),((-2720538623290299125855783:ℚ)/7220000000000000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((588977589:ℚ)/1000000000),((755458881:ℚ)/1250000000),((4954843123:ℚ)/5577500000),((2698376643:ℚ)/2765000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((6841278921:ℚ)/10000000000),((-31745183446177379747006685280154495627730629793405377:ℚ)/67776442816162109375000000000000000000000000000000000),((-6921221953600307169728183:ℚ)/18483200000000000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((7:ℚ)/8),((15:ℚ)/16),((594923809:ℚ)/1000000000),((762900021:ℚ)/1250000000),((4996466663:ℚ)/5625000000),((2720700063:ℚ)/2788750000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3358261949:ℚ)/5000000000),((-6101405475419883503059907297597460916232758427895239:ℚ)/13035535812377929687500000000000000000000000000000000),((-6877880500564670230446063:ℚ)/18483200000000000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((6008698813:ℚ)/10000000000),((766620469:ℚ)/1250000000),((50380891691:ℚ)/56487500000),((910620469:ℚ)/937500000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((1317956521:ℚ)/2000000000),((-531874220032725021685276510495298230148085404363176588841:ℚ)/1126515263171386718750000000000000000000000000000000000000),((-685689635694232921908085287:ℚ)/1848320000000000000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((6038428633:ℚ)/10000000000),((6162726697:ℚ)/10000000000),((50589000431:ℚ)/56725000000),((21944180091:ℚ)/22595000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((6525630159:ℚ)/10000000000),((-1346023204866083643901946298742894268818731479887722021:ℚ)/2851960719970703125000000000000000000000000000000000000),((-683523863272394667287318847:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((3034079049:ℚ)/5000000000),((619248901:ℚ)/1000000000),((25398553343:ℚ)/28481250000),((2203346703:ℚ)/2269000000),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((3230467699:ℚ)/5000000000),((-7569432626411542866065147874935790891571225252935781253:ℚ)/16044073603820800781250000000000000000000000000000000000),((-8965243094017944344090117:ℚ)/24320000000000000000000000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((6097887213:ℚ)/10000000000),((6222250699:ℚ)/10000000000),((51005210491:ℚ)/57200000000),((7374250699:ℚ)/7595000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((1598920381:ℚ)/2500000000),((-551644069837172487850337906464283963753555466514308087089:ℚ)/1169682800000000000000000000000000000000000000000000000000),((-679193470712163285292348487:ℚ)/1848320000000000000000000000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((919:ℚ)/1280),((7:ℚ)/8),((15:ℚ)/16),((306380799:ℚ)/500000000),((6252011773:ℚ)/10000000000),((2560665593:ℚ)/2871875000),((22212035319:ℚ)/22880000000),((9548320353:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((1508511599:ℚ)/5000000000),((3164925453:ℚ)/5000000000),((-209379109592429311213144279391504246360212790600088641:ℚ)/444117484474182128906250000000000000000000000000000000),((-1692572123224885865794223:ℚ)/4620800000000000000000000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((919:ℚ)/1280) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((919:ℚ)/1280),((2307:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((3078672203:ℚ)/5000000000),((3140886119:ℚ)/5000000000),((25710705421:ℚ)/28837500000),((11150658357:ℚ)/11487500000),((59616423:ℚ)/62500000),((4774160179:ℚ)/5000000000),((762368323:ℚ)/2500000000),((391464063:ℚ)/625000000),((-8277832990462466735222280244569722493694281056697133:ℚ)/17564432777881622314453125000000000000000000000000000),((-168716152608237353455002807:ℚ)/462080000000000000000000000)⟩
theorem valid12 : Valid source28 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source28 nn0 nn1 Qcell ((919:ℚ)/1280) ((2307:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((2307:ℚ)/3200),((4633:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((1237414499:ℚ)/2000000000),((6311532103:ℚ)/10000000000),((10325901493:ℚ)/11582500000),((7463532103:ℚ)/7690000000),((1905827251:ℚ)/2000000000),((1907725537:ℚ)/2000000000),((3080928657:ℚ)/10000000000),((309819217:ℚ)/500000000),((-183011724304627613139102270051901064646462642652742783:ℚ)/388460563035156250000000000000000000000000000000000000),((-26908030138535579061874023:ℚ)/73932800000000000000000000)⟩
theorem valid13 : Valid source28 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source28 nn0 nn1 Qcell ((2307:ℚ)/3200) ((4633:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((4633:ℚ)/6400),((1163:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((6216800249:ℚ)/10000000000),((50730331:ℚ)/80000000),((51837601743:ℚ)/58150000000),((179838993:ℚ)/185320000),((9519843613:ℚ)/10000000000),((476456813:ℚ)/500000000),((622285377:ℚ)/2000000000),((6128708383:ℚ)/10000000000),((-578779259979824739260522419986995895134259743980800701877:ℚ)/1228935739843750000000000000000000000000000000000000000000),((-670537277849079421470817023:ℚ)/1848320000000000000000000000)⟩
theorem valid14 : Valid source28 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source28 nn0 nn1 Qcell ((4633:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1163:ℚ)/1600),((4671:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((3123263837:ℚ)/5000000000),((318552503:ℚ)/500000000),((26022846859:ℚ)/29193750000),((1128457509:ℚ)/1163000000),((148605427:ℚ)/156250000),((4759921809:ℚ)/5000000000),((98156347:ℚ)/312500000),((12120751:ℚ)/20000000),((-17874242547373059705619928348753761690701755797572929:ℚ)/37965552401170134544372558593750000000000000000000000),((-167093545785631773625818087:ℚ)/462080000000000000000000000)⟩
theorem valid15 : Valid source28 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((4671:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((4671:ℚ)/6400),((469:ℚ)/640),((7:ℚ)/8),((15:ℚ)/16),((3138127387:ℚ)/5000000000),((6400808167:ℚ)/10000000000),((26126891709:ℚ)/29312500000),((7552808167:ℚ)/7785000000),((9501845013:ℚ)/10000000000),((9510747333:ℚ)/10000000000),((792422551:ℚ)/2500000000),((5991362863:ℚ)/10000000000),((-74085455940230701500360358997594746463561715088620563319:ℚ)/157412275695800781250000000000000000000000000000000000000),((-166552867166629755831177687:ℚ)/462080000000000000000000000)⟩
theorem valid16 : Valid source28 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source28 nn0 nn1 Qcell ((4671:ℚ)/6400) ((469:ℚ)/640) :=
  cell_of_packet source28 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((469:ℚ)/640),((4709:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((394123847:ℚ)/625000000),((3215282851:ℚ)/5000000000),((3278866929:ℚ)/3678906250),((11373848553:ℚ)/11725000000),((9493134321:ℚ)/10000000000),((4750922509:ℚ)/5000000000),((1598759513:ℚ)/5000000000),((5921646353:ℚ)/10000000000),((-4306359955834878345918497933121030158359356930927009:ℚ)/9152869339287281036376953125000000000000000000000000),((-2593941929557862414695407:ℚ)/7220000000000000000000000)⟩
theorem valid17 : Valid source28 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source28 nn0 nn1 Qcell ((469:ℚ)/640) ((4709:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((4709:ℚ)/6400),((591:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((6335708013:ℚ)/10000000000),((403770167:ℚ)/625000000),((52669956091:ℚ)/59100000000),((1427310501:ℚ)/1471562500),((4742306471:ℚ)/5000000000),((4746567163:ℚ)/5000000000),((806129637:ℚ)/2500000000),((5851200451:ℚ)/10000000000),((-5618659501801091132192160338714832981433095663543367867:ℚ)/11945895312500000000000000000000000000000000000000000000),((-661887178519077269385666887:ℚ)/1848320000000000000000000000)⟩
theorem valid18 : Valid source28 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source28 nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((7:ℚ)/8),((15:ℚ)/16),((79567927:ℚ)/125000000),((1622519771:ℚ)/2500000000),((660975489:ℚ)/741718750),((1910519771:ℚ)/1970000000),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((1444999533:ℚ)/2500000000),((-599576989854119087017731653589495568680839611605693:ℚ)/1275169142758846282958984375000000000000000000000000),((-103082125280366388117567:ℚ)/288800000000000000000000)⟩
theorem valid19 : Valid source28 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((1598789999:ℚ)/2500000000),((1303966989:ℚ)/2000000000),((13271529993:ℚ)/14893750000),((4603100967:ℚ)/4747000000),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((570801073:ℚ)/1000000000),((-9705874962450500884145229210254681100233162138826763227:ℚ)/20648675364685058593750000000000000000000000000000000000),((-41097775203986525225851023:ℚ)/115520000000000000000000000)⟩
theorem valid20 : Valid source28 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source28 nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((6424885527:ℚ)/10000000000),((3289672519:ℚ)/5000000000),((53294198689:ℚ)/60050000000),((11597017557:ℚ)/11915000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((5635207789:ℚ)/10000000000),((-472842005031864487317530281214215318980203811223416073393:ℚ)/1015033359960937500000000000000000000000000000000000000000),((-653170006606041299579796767:ℚ)/1848320000000000000000000000)⟩
theorem valid21 : Valid source28 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source28 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((1621083921:ℚ)/2500000000),((1659713251:ℚ)/2500000000),((13427587447:ℚ)/15131250000),((5843139753:ℚ)/6005000000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((685877951:ℚ)/1250000000),((-7561010449145533391931745552296393876262113161278132831:ℚ)/16239240029525756835937500000000000000000000000000000000),((-40553098478802557708918543:ℚ)/115520000000000000000000000)⟩
theorem valid22 : Valid source28 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source28 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/8),((15:ℚ)/16),((6543784659:ℚ)/10000000000),((6698358893:ℚ)/10000000000),((54126492613:ℚ)/61000000000),((7850358893:ℚ)/8070000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2667579889:ℚ)/5000000000),((-1980572592272320001816207085083864927962181373699251881429:ℚ)/4255893750000000000000000000000000000000000000000000000000),((-644530647946219543305835463:ℚ)/1848320000000000000000000000)⟩
theorem valid23 : Valid source28 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source28 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source28 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((41270203:ℚ)/62500000),((1704341157:ℚ)/2500000000),((340891421:ℚ)/387187500),((5977023471:ℚ)/6100000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((323705597:ℚ)/625000000),((-165943301618453377745131475257262379174754101429731:ℚ)/362780555534362792968750000000000000000000000000000),((-24833853302020063251807:ℚ)/72200000000000000000000)⟩
theorem valid24 : Valid source28 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((3361062383:ℚ)/5000000000),((1387272523:ℚ)/2000000000),((27687436681:ℚ)/31450000000),((1617672523:ℚ)/1652000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((4853963441:ℚ)/10000000000),((-66659292597433154170919118030497517597206533995122406913:ℚ)/145815345117187500000000000000000000000000000000000000000),((-156779140209700987595288847:ℚ)/462080000000000000000000000)⟩
theorem valid25 : Valid source28 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source28 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/8),((15:ℚ)/16),((6841012747:ℚ)/10000000000),((717433671:ℚ)/1000000000),((56207089229:ℚ)/64800000000),((2497901013:ℚ)/2516000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((70425157:ℚ)/156250000),((-250877170691145525642834723052716756494089921619491433477:ℚ)/566870400000000000000000000000000000000000000000000000000),((-609560790601266543006897207:ℚ)/1848320000000000000000000000)⟩
theorem valid26 : Valid source28 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source28 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((141575531:ℚ)/200000000),((1015747953:ℚ)/1250000000),((1157428717:ℚ)/1448000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((3725066697:ℚ)/10000000000),((-1319843683189593086216696849204394839810878181322181:ℚ)/3557844600000000000000000000000000000000000000000000),((-231296043944297496986103:ℚ)/739328000000000000000000)⟩
theorem valid27 : Valid source28 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((7:ℚ)/8),((15:ℚ)/16),((2007423277:ℚ)/2500000000),((56733231:ℚ)/62500000),((16131962939:ℚ)/20000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-4730871580686411812275838134095480340569348759943517961:ℚ)/12500000000000000000000000000000000000000000000000000000),((-40145541:ℚ)/128000000)⟩
theorem valid28 : Valid source28 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source28 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/8),((15:ℚ)/16),((1796087063:ℚ)/2000000000),((12880812161:ℚ)/10000000000),((14236609441:ℚ)/22080000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-596079258451112298441803544193597097:ℚ)/2691145728000000000000000000000000000),((-40145541:ℚ)/128000000)⟩
theorem valid29 : Valid source28 packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet29 valid29
private theorem node1_3 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source28 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source28 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((1163:ℚ)/1600) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_7 node7_15
private theorem node16_18 :
    CellBound source28 nn0 nn1 Qcell ((4671:ℚ)/6400) ((4709:ℚ)/6400) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((4709:ℚ)/6400) :=
  cell_join leaf15 node16_18
private theorem node18_20 :
    CellBound source28 nn0 nn1 Qcell ((4709:ℚ)/6400) ((4747:ℚ)/6400) :=
  cell_join leaf18 leaf19
private theorem node20_22 :
    CellBound source28 nn0 nn1 Qcell ((4747:ℚ)/6400) ((1201:ℚ)/1600) :=
  cell_join leaf20 leaf21
private theorem node18_22 :
    CellBound source28 nn0 nn1 Qcell ((4709:ℚ)/6400) ((1201:ℚ)/1600) :=
  cell_join node18_20 node20_22
private theorem node15_22 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join node15_18 node18_22
private theorem node22_24 :
    CellBound source28 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf22 leaf23
private theorem node24_26 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf24 leaf25
private theorem node22_26 :
    CellBound source28 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join node22_24 node24_26
private theorem node26_28 :
    CellBound source28 nn0 nn1 Qcell ((629:ℚ)/800) ((181:ℚ)/200) :=
  cell_join leaf26 leaf27
private theorem node28_30 :
    CellBound source28 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf28 leaf29
private theorem node26_30 :
    CellBound source28 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node26_28 node28_30
private theorem node22_30 :
    CellBound source28 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node22_26 node26_30
private theorem node15_30 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node15_22 node22_30
private theorem node0_30 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_15 node15_30
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_30
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29]
theorem packet_count : packets.length = 30 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC31
#check @N11Formalization.C450Source28GroupedC31.bound
#print axioms N11Formalization.C450Source28GroupedC31.valid0
#print axioms N11Formalization.C450Source28GroupedC31.valid1
#print axioms N11Formalization.C450Source28GroupedC31.valid2
#print axioms N11Formalization.C450Source28GroupedC31.valid3
#print axioms N11Formalization.C450Source28GroupedC31.valid4
#print axioms N11Formalization.C450Source28GroupedC31.valid5
#print axioms N11Formalization.C450Source28GroupedC31.valid6
#print axioms N11Formalization.C450Source28GroupedC31.valid7
#print axioms N11Formalization.C450Source28GroupedC31.valid8
#print axioms N11Formalization.C450Source28GroupedC31.valid9
#print axioms N11Formalization.C450Source28GroupedC31.valid10
#print axioms N11Formalization.C450Source28GroupedC31.valid11
#print axioms N11Formalization.C450Source28GroupedC31.valid12
#print axioms N11Formalization.C450Source28GroupedC31.valid13
#print axioms N11Formalization.C450Source28GroupedC31.valid14
#print axioms N11Formalization.C450Source28GroupedC31.valid15
#print axioms N11Formalization.C450Source28GroupedC31.valid16
#print axioms N11Formalization.C450Source28GroupedC31.valid17
#print axioms N11Formalization.C450Source28GroupedC31.valid18
#print axioms N11Formalization.C450Source28GroupedC31.valid19
#print axioms N11Formalization.C450Source28GroupedC31.valid20
#print axioms N11Formalization.C450Source28GroupedC31.valid21
#print axioms N11Formalization.C450Source28GroupedC31.valid22
#print axioms N11Formalization.C450Source28GroupedC31.valid23
#print axioms N11Formalization.C450Source28GroupedC31.valid24
#print axioms N11Formalization.C450Source28GroupedC31.valid25
#print axioms N11Formalization.C450Source28GroupedC31.valid26
#print axioms N11Formalization.C450Source28GroupedC31.valid27
#print axioms N11Formalization.C450Source28GroupedC31.valid28
#print axioms N11Formalization.C450Source28GroupedC31.valid29
#print axioms N11Formalization.C450Source28GroupedC31.bound
#print axioms N11Formalization.C450Source28GroupedC31.endpoint_checks
