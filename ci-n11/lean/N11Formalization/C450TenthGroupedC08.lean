import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC08
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨((-9:ℚ)/16),((-1:ℚ)/2)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-9:ℚ)/16),((-1:ℚ)/2),((794225419:ℚ)/1250000000),((6633115253:ℚ)/10000000000),((-54578037277:ℚ)/99200000000),((-704225419:ℚ)/1609375000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((5807949087:ℚ)/10000000000),((60902218083728716174354307952741641063384586822572677:ℚ)/2422895693778991699218750000000000000000000000000000000),((1952481774446785552617877:ℚ)/14440000000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-9:ℚ)/16),((-1:ℚ)/2),((6591532183:ℚ)/10000000000),((429428779:ℚ)/625000000),((-3544859011:ℚ)/6437500000),((-5871532183:ℚ)/13350000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((5210301343:ℚ)/10000000000),((9605750320923063295445270691707411221470512731082267011:ℚ)/382913825976562500000000000000000000000000000000000000000),((973011519515414506461019:ℚ)/7220000000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((6829244707:ℚ)/10000000000),((6989726631:ℚ)/10000000000),((-57787539679:ℚ)/106800000000),((-6109244707:ℚ)/13587500000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((567828289:ℚ)/1250000000),((1144790698880797762169262011374844920660475019846646379:ℚ)/47034869494628906250000000000000000000000000000000000000),((102028646508095134021257:ℚ)/760000000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((694809539:ℚ)/1000000000),((7049158203:ℚ)/10000000000),((-58322423827:ℚ)/108700000000),((-622809539:ℚ)/1370625000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4172098993:ℚ)/10000000000),((34966335465331905996457159112412467365085979688298381:ℚ)/1457754069386672973632812500000000000000000000000000000),((1934812012581605619240977:ℚ)/14440000000000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((3503759711:ℚ)/5000000000),((3554294401:ℚ)/5000000000),((-29428649609:ℚ)/54825000000),((-3143759711:ℚ)/6912500000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3974732149:ℚ)/10000000000),((80800360546183521619996688142503078105146633522430937:ℚ)/3368408954811096191406250000000000000000000000000000000),((30206608505130368452433:ℚ)/225625000000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((706694261:ℚ)/1000000000),((27883999:ℚ)/39062500),((-32993713:ℚ)/61718750),((-634694261:ℚ)/1388437500),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((3767618259:ℚ)/10000000000),((23607730119776668334560670957274277149414335968502327:ℚ)/991168238389921188354492187500000000000000000000000000),((482840228676332235615877:ℚ)/3610000000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((3548326947:ℚ)/5000000000),((1792004613:ℚ)/2500000000),((-14848041517:ℚ)/27768750000),((-3188326947:ℚ)/6971875000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((1829945453:ℚ)/5000000000),((14009400318944889779597525479038818615027432453740901651:ℚ)/588145967641031742095947265625000000000000000000000000000),((482642321090495845741003:ℚ)/3610000000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((445397811:ℚ)/625000000),((7197732929:ℚ)/10000000000),((-59659596361:ℚ)/111550000000),((-800795622:ℚ)/1750390625),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((3549047227:ℚ)/10000000000),((142506728341594491987465518257339123564461160199496059:ℚ)/5982387087526053190231323242187500000000000000000000000),((1929778812267413617633773:ℚ)/14440000000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-9:ℚ)/16),((-1:ℚ)/2),((3578037929:ℚ)/5000000000),((3613723589:ℚ)/5000000000),((-29963512301:ℚ)/56012500000),((-3218037929:ℚ)/7031250000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((3434785023:ℚ)/10000000000),((2717816049472045938576900525661843285751876586186468337:ℚ)/114086398389190435409545898437500000000000000000000000000),((241123687293883631837269:ℚ)/1805000000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((3592893271:ℚ)/5000000000),((7257161201:ℚ)/10000000000),((-60194450809:ℚ)/112500000000),((-3232893271:ℚ)/7060937500),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((132670019:ℚ)/400000000),((471758854066149751018418140706835004644315387212041081:ℚ)/19802026110434532165527343750000000000000000000000000000),((1928201342533387137035353:ℚ)/14440000000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((721549703:ℚ)/1000000000),((3643437501:ℚ)/5000000000),((-30230937509:ℚ)/56487500000),((-649549703:ℚ)/1418125000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((3194524909:ℚ)/10000000000),((4797770972799808127397718899673256154667028468506867:ℚ)/201375163961681365966796875000000000000000000000000000),((120463396547134329902507:ℚ)/902500000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-9:ℚ)/16),((-1:ℚ)/2),((3622603663:ℚ)/5000000000),((914573573:ℚ)/1250000000),((-7591162157:ℚ)/14181250000),((-3262603663:ℚ)/7120312500),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((766901707:ℚ)/2500000000),((5808287620809506910620381428835996733573912005400896657:ℚ)/243776805850911140441894531250000000000000000000000000000),((481657126218057029587267:ℚ)/3610000000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-9:ℚ)/16),((-1:ℚ)/2),((909364679:ℚ)/1250000000),((7346301949:ℚ)/10000000000),((-60996717541:ℚ)/113925000000),((-819364679:ℚ)/1787500000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((366923379:ℚ)/1250000000),((553701864376464612934451265737892190517454654238232039:ℚ)/23238021936035156250000000000000000000000000000000000000),((101360201200491699549287:ℚ)/760000000000000000000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-9:ℚ)/16),((-1:ℚ)/2),((146092547:ℚ)/200000000),((7405728039:ℚ)/10000000000),((-61531552351:ℚ)/114400000000),((-131692547:ℚ)/288375000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((1398556583:ℚ)/5000000000),((5478043936367145099682573814658492444160051883:ℚ)/228337626112461090087890625000000000000000000000),((1925347101995182551382713:ℚ)/14440000000000000000000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-9:ℚ)/16),((-1:ℚ)/2),((7364046631:ℚ)/10000000000),((7465153293:ℚ)/10000000000),((-62066379637:ℚ)/115350000000),((-6644046631:ℚ)/14537500000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((624584731:ℚ)/2500000000),((1062788652220383353955310240974993935030048654904595375423:ℚ)/44299292997180175781250000000000000000000000000000000000000),((1923785828259649158327147:ℚ)/14440000000000000000000000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-9:ℚ)/16),((-1:ℚ)/2),((7423465187:ℚ)/10000000000),((3792000687:ℚ)/5000000000),((-31568006183:ℚ)/58150000000),((-6703465187:ℚ)/14775000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2159571787:ℚ)/10000000000),((5276251128850094715959243963542449049136793141898737817:ℚ)/217079316381835937500000000000000000000000000000000000000),((961407726200355798375889:ℚ)/7220000000000000000000000)⟩
theorem valid15 : Valid tenth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-9:ℚ)/16),((-1:ℚ)/2),((3771150099:ℚ)/5000000000),((3910844181:ℚ)/5000000000),((-32637597629:ℚ)/59100000000),((-3411150099:ℚ)/7625000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((246604223:ℚ)/2000000000),((5880531736877334736042410688967051054425849770237106908017:ℚ)/236098674956250000000000000000000000000000000000000000000000),((64629811928834301:ℚ)/486400000000000000)⟩
theorem valid16 : Valid tenth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-9:ℚ)/16),((-1:ℚ)/2),((1944990567:ℚ)/2500000000),((1659405881:ℚ)/2000000000),((-13910652929:ℚ)/24400000000),((-21790007:ℚ)/50000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((2362137309055162212092063991894260822654198754496200459:ℚ)/90792400000000000000000000000000000000000000000000000000),((16989439:ℚ)/128000000)⟩
theorem valid17 : Valid tenth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-9:ℚ)/16),((-1:ℚ)/2),((8255257869:ℚ)/10000000000),((10198069333:ℚ)/10000000000),((-86662623997:ℚ)/129600000000),((-7535257869:ℚ)/20000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1300784224932955543690452565574926048844982294314263203709:ℚ)/40814668800000000000000000000000000000000000000000000000000),((16989439:ℚ)/128000000)⟩
theorem valid18 : Valid tenth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-9:ℚ)/16),((-1:ℚ)/2),((507807963:ℚ)/500000000),((13999289711:ℚ)/10000000000),((-120873607399:ℚ)/160000000000),((-157269321:ℚ)/460000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((385661930369059019739075797472424955948185376484960719070583:ℚ)/10156800000000000000000000000000000000000000000000000000000000),((16989439:ℚ)/128000000)⟩
theorem valid19 : Valid tenth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet19 valid19
private theorem node0_2 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound tenth nn0 nn1 Qcell ((4481:ℚ)/6400) ((4519:ℚ)/6400) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4519:ℚ)/6400) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((4519:ℚ)/6400) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((4519:ℚ)/6400) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound tenth nn0 nn1 Qcell ((4519:ℚ)/6400) ((4557:ℚ)/6400) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound tenth nn0 nn1 Qcell ((4557:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound tenth nn0 nn1 Qcell ((4519:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_join node10_12 node12_15
private theorem node15_17 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf15 leaf16
private theorem node18_20 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf17 node18_20
private theorem node15_20 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node15_17 node17_20
private theorem node10_20 :
    CellBound tenth nn0 nn1 Qcell ((4519:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node10_15 node15_20
private theorem node0_20 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_20
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_20
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19]
theorem packet_count : packets.length = 20 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC08
#check @N11Formalization.C450TenthGroupedC08.bound
#print axioms N11Formalization.C450TenthGroupedC08.valid0
#print axioms N11Formalization.C450TenthGroupedC08.valid1
#print axioms N11Formalization.C450TenthGroupedC08.valid2
#print axioms N11Formalization.C450TenthGroupedC08.valid3
#print axioms N11Formalization.C450TenthGroupedC08.valid4
#print axioms N11Formalization.C450TenthGroupedC08.valid5
#print axioms N11Formalization.C450TenthGroupedC08.valid6
#print axioms N11Formalization.C450TenthGroupedC08.valid7
#print axioms N11Formalization.C450TenthGroupedC08.valid8
#print axioms N11Formalization.C450TenthGroupedC08.valid9
#print axioms N11Formalization.C450TenthGroupedC08.valid10
#print axioms N11Formalization.C450TenthGroupedC08.valid11
#print axioms N11Formalization.C450TenthGroupedC08.valid12
#print axioms N11Formalization.C450TenthGroupedC08.valid13
#print axioms N11Formalization.C450TenthGroupedC08.valid14
#print axioms N11Formalization.C450TenthGroupedC08.valid15
#print axioms N11Formalization.C450TenthGroupedC08.valid16
#print axioms N11Formalization.C450TenthGroupedC08.valid17
#print axioms N11Formalization.C450TenthGroupedC08.valid18
#print axioms N11Formalization.C450TenthGroupedC08.valid19
#print axioms N11Formalization.C450TenthGroupedC08.bound
#print axioms N11Formalization.C450TenthGroupedC08.endpoint_checks
