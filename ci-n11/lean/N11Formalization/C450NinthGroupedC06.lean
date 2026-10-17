import N11Formalization.C450NinthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450NinthGroupedC06
open C450GroupedPacketKernel C450GroupedClosedAssembly C450NinthData
def Qcell : RatInterval := ⟨((-11:ℚ)/16),((-5:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-11:ℚ)/16),((-5:ℚ)/8),((6371145977:ℚ)/10000000000),((6653304461:ℚ)/10000000000),((-2216333841:ℚ)/3200000000),((-5859145977:ℚ)/10300000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((360389229:ℚ)/625000000),((50450904509247796747295044019798422431305656570025654233:ℚ)/2172723200000000000000000000000000000000000000000000000000),((3125465829793581218926831:ℚ)/19456000000000000000000000)⟩
theorem valid0 : Valid ninth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet ninth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((1049:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((826098531:ℚ)/1250000000),((13544261:ℚ)/20000000),((-140026871:ℚ)/206000000),((-762098531:ℚ)/1311250000),((4901598247:ℚ)/5000000000),((616511681:ℚ)/625000000),((1987221391:ℚ)/10000000000),((2582252341:ℚ)/5000000000),((332224482000989477234857689125965608896564953866093063:ℚ)/15030473544087500000000000000000000000000000000000000000),((237594929447728673389:ℚ)/1478656000000000000000)⟩
theorem valid1 : Valid ninth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound ninth nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1049:ℚ)/1600),((267:ℚ)/400),((-11:ℚ)/16),((-5:ℚ)/8),((1345521103:ℚ)/2000000000),((861369229:ℚ)/1250000000),((-8915061519:ℚ)/13112500000),((-414373701:ℚ)/712000000),((4873244381:ℚ)/5000000000),((9803196499:ℚ)/10000000000),((2256500263:ℚ)/10000000000),((967696783:ℚ)/2000000000),((617046590148601307907972317045573885641274278979961325823:ℚ)/27903362612088012695312500000000000000000000000000000000000),((928562670956189923422069:ℚ)/5776000000000000000000000)⟩
theorem valid2 : Valid ninth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound ninth nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_of_packet ninth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-11:ℚ)/16),((-5:ℚ)/8),((3423210193:ℚ)/5000000000),((434397783:ℚ)/625000000),((-4498375613:ℚ)/6675000000),((-3167210193:ℚ)/5387500000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2245424209:ℚ)/5000000000),((87406270560563101738159652962355154751821579644520075607:ℚ)/4046407874728775024414062500000000000000000000000000000000),((696516855106584568502603:ℚ)/4332000000000000000000000)⟩
theorem valid3 : Valid ninth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet ninth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((6905826963:ℚ)/10000000000),((3504887299:ℚ)/5000000000),((-36313760289:ℚ)/53875000000),((-6393826963:ℚ)/10870000000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4307293999:ℚ)/10000000000),((24956078955434980100021960493340862674545440910192644688942977:ℚ)/1154784524082995605468750000000000000000000000000000000000000000),((14862802643474460564071709:ℚ)/92416000000000000000000000)⟩
theorem valid4 : Valid ninth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound ninth nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((1741308247:ℚ)/2500000000),((7069184061:ℚ)/10000000000),((-73281024671:ℚ)/108700000000),((-1613308247:ℚ)/2741250000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4116096221:ℚ)/10000000000),((1363830857009496660303667678605103656042825068438081040902471:ℚ)/63080407587185937500000000000000000000000000000000000000000000),((9389447790726945632930093:ℚ)/58368000000000000000000000)⟩
theorem valid5 : Valid ninth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2193:ℚ)/3200),((881:ℚ)/1280),((-11:ℚ)/16),((-5:ℚ)/8),((280985539:ℚ)/400000000),((7098888569:ℚ)/10000000000),((-24535924753:ℚ)/36550000000),((-260505539:ℚ)/440500000),((4828444327:ℚ)/5000000000),((9668970163:ℚ)/10000000000),((2627133759:ℚ)/10000000000),((783226403:ℚ)/2000000000),((1265825080241097161722599767947816230852687443453642093881281:ℚ)/59215307206338085937500000000000000000000000000000000000000000),((59470806256236388780958949:ℚ)/369664000000000000000000000)⟩
theorem valid6 : Valid ninth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound ninth nn0 nn1 Qcell ((2193:ℚ)/3200) ((881:ℚ)/1280) :=
  cell_of_packet ninth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((881:ℚ)/1280),((553:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((352717051:ℚ)/500000000),((7128592931:ℚ)/10000000000),((-73934522241:ℚ)/110125000000),((-327117051:ℚ)/553000000),((1205629803:ℚ)/1250000000),((9656888659:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1906216323:ℚ)/5000000000),((852835599350459897384931648529097910945563881139042486428937:ℚ)/39884859840081977844238281250000000000000000000000000000000000),((59478568880398515608985949:ℚ)/369664000000000000000000000)⟩
theorem valid7 : Valid ninth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound ninth nn0 nn1 Qcell ((881:ℚ)/1280) ((553:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((553:ℚ)/800),((4443:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7084043437:ℚ)/10000000000),((1789574287:ℚ)/2500000000),((-18565317157:ℚ)/27650000000),((-6572043437:ℚ)/11107500000),((4816708251:ℚ)/5000000000),((9645038429:ℚ)/10000000000),((1358023157:ℚ)/5000000000),((1852989371:ℚ)/5000000000),((13945358762519041850915012174746618768367997162459572759788109:ℚ)/652015709172240820312500000000000000000000000000000000000000000),((3717898632944585096079221:ℚ)/23104000000000000000000000)⟩
theorem valid8 : Valid ninth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((4443:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4443:ℚ)/6400),((2231:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((3556872863:ℚ)/5000000000),((7188001223:ℚ)/10000000000),((-24862671151:ℚ)/37025000000),((-3300872863:ℚ)/5577500000),((2405504993:ℚ)/2500000000),((9633416507:ℚ)/10000000000),((551641531:ℚ)/2000000000),((359652523:ℚ)/1000000000),((2111189837260853913506017624607841194004317987526159641518143:ℚ)/98683461974947515869140625000000000000000000000000000000000000),((59494233996837991249231461:ℚ)/369664000000000000000000000)⟩
theorem valid9 : Valid ninth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound ninth nn0 nn1 Qcell ((4443:ℚ)/6400) ((2231:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7143447889:ℚ)/10000000000),((3608852579:ℚ)/5000000000),((-37457378369:ℚ)/55775000000),((-6631447889:ℚ)/11202500000),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((435473611:ℚ)/1250000000),((18638019851560743907631067093893382889517433435651231281025937:ℚ)/870980904065008402343750000000000000000000000000000000000000000),((14875534122359211655698269:ℚ)/92416000000000000000000000)⟩
theorem valid10 : Valid ninth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound ninth nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((-11:ℚ)/16),((-5:ℚ)/8),((7173149927:ℚ)/10000000000),((7247408953:ℚ)/10000000000),((-75241498483:ℚ)/112025000000),((-2220383309:ℚ)/3750000000),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((673487901:ℚ)/2000000000),((6611862044400368882756291923916650158127495937865966811:ℚ)/308906764896011352539062500000000000000000000000000000000),((59510085604135271523463781:ℚ)/369664000000000000000000000)⟩
theorem valid11 : Valid ninth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound ninth nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet ninth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((7202851843:ℚ)/10000000000),((1819278153:ℚ)/2500000000),((-18892059683:ℚ)/28125000000),((-6690851843:ℚ)/11297500000),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((811772043:ℚ)/2500000000),((20263743627179988919846886907196760634983599522279023271706377:ℚ)/946500916099548339843750000000000000000000000000000000000000000),((11159640251525293654701743:ℚ)/69312000000000000000000000)⟩
theorem valid12 : Valid ninth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((7232553637:ℚ)/10000000000),((1461363227:ℚ)/2000000000),((-15178995497:ℚ)/22595000000),((-6720553637:ℚ)/11345000000),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((780567899:ℚ)/2500000000),((19871199273892952997672606447006826781855413084323725331289:ℚ)/927953159490608591796875000000000000000000000000000000000000),((2381044948031792653631661:ℚ)/14786560000000000000000000)⟩
theorem valid13 : Valid ninth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound ninth nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2269:ℚ)/3200),((4557:ℚ)/6400),((-11:ℚ)/16),((-5:ℚ)/8),((453890957:ℚ)/625000000),((1834129881:ℚ)/2500000000),((-19055428691:ℚ)/28362500000),((-140630319:ℚ)/237343750),((9568319513:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((2948974549:ℚ)/10000000000),((2992430501:ℚ)/10000000000),((7047314365929293068733903746796820231479053846053123723598843:ℚ)/329025146939616076660156250000000000000000000000000000000000000),((11162664877857268761969647:ℚ)/69312000000000000000000000)⟩
theorem valid14 : Valid ninth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_of_packet ninth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((4557:ℚ)/6400),((143:ℚ)/200),((-11:ℚ)/16),((-5:ℚ)/8),((1822989217:ℚ)/2500000000),((7366222781:ℚ)/10000000000),((-25516150197:ℚ)/37975000000),((-1694989217:ℚ)/2860000000),((9558216781:ℚ)/10000000000),((4784159759:ℚ)/5000000000),((149176903:ℚ)/500000000),((2856879303:ℚ)/10000000000),((372073442491381066353452139825275437247577953935608957463:ℚ)/17367623417675781250000000000000000000000000000000000000000),((59542348284947721228734749:ℚ)/369664000000000000000000000)⟩
theorem valid15 : Valid ninth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound ninth nn0 nn1 Qcell ((4557:ℚ)/6400) ((143:ℚ)/200) :=
  cell_of_packet ninth nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-11:ℚ)/16),((-5:ℚ)/8),((1830414577:ℚ)/2500000000),((3712814453:ℚ)/5000000000),((-38600958983:ℚ)/57200000000),((-1702414577:ℚ)/2883750000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((2714762163:ℚ)/10000000000),((1756244522643366717106544513410787400306038978181575119733:ℚ)/81059155112203125000000000000000000000000000000000000000000),((783712784270293486103199:ℚ)/4864000000000000000000000)⟩
theorem valid16 : Valid ninth packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound ninth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet ninth nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-11:ℚ)/16),((-5:ℚ)/8),((3690530421:ℚ)/5000000000),((3742517261:ℚ)/5000000000),((-38927689871:ℚ)/57675000000),((-3434530421:ℚ)/5815000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((15038277:ℚ)/62500000),((11716075222831723261107487117373763010377907710449930840572709:ℚ)/540606174502606347656250000000000000000000000000000000000000000),((14894692283803469016544189:ℚ)/92416000000000000000000000)⟩
theorem valid17 : Valid ninth packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet ninth nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-11:ℚ)/16),((-5:ℚ)/8),((3720231463:ℚ)/5000000000),((1900961069:ℚ)/2500000000),((-19790571759:ℚ)/29075000000),((-1154743821:ℚ)/1970000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1026293727:ℚ)/5000000000),((32999371293485269176271894826690388925059471814464075812487:ℚ)/1490430222737377929687500000000000000000000000000000000000000),((7844447702179121:ℚ)/48640000000000000)⟩
theorem valid18 : Valid ninth packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet ninth nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-11:ℚ)/16),((-5:ℚ)/8),((7559265787:ℚ)/10000000000),((1960364549:ℚ)/2500000000),((-6814670013:ℚ)/9850000000),((-7047265787:ℚ)/12200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((129476827:ℚ)/1250000000),((512010385566279791948769115290798226338998379869270796669:ℚ)/22225338228906250000000000000000000000000000000000000000000),((15685303637461629:ℚ)/97280000000000000)⟩
theorem valid19 : Valid ninth packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound ninth nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet ninth nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-11:ℚ)/16),((-5:ℚ)/8),((7796866567:ℚ)/10000000000),((8316665983:ℚ)/10000000000),((-87003325813:ℚ)/122000000000),((-7284866567:ℚ)/12960000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1838220693768900603184027037036707462290464048054417632152989:ℚ)/74461117050000000000000000000000000000000000000000000000000000),((20636937:ℚ)/128000000)⟩
theorem valid20 : Valid ninth packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet ninth nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-11:ℚ)/16),((-5:ℚ)/8),((4136025193:ℚ)/5000000000),((5108649819:ℚ)/5000000000),((-53955148009:ℚ)/64800000000),((-3880025193:ℚ)/8000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((171555968080582552386123128522462125855200082615404744899:ℚ)/5101833600000000000000000000000000000000000000000000000000),((20636937:ℚ)/128000000)⟩
theorem valid21 : Valid ninth packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet ninth nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-11:ℚ)/16),((-5:ℚ)/8),((5086305481:ℚ)/5000000000),((7009021671:ℚ)/5000000000),((-74859238381:ℚ)/80000000000),((-1610101827:ℚ)/3680000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((2904491760981248553850818845153872336079:ℚ)/67712000000000000000000000000000000000000),((20636937:ℚ)/128000000)⟩
theorem valid22 : Valid ninth packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound ninth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet ninth nn0 nn1 packet22 valid22
private theorem node0_2 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((1049:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound ninth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound ninth nn0 nn1 Qcell ((1049:ℚ)/1600) ((1087:ℚ)/1600) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join node0_2 node2_5
private theorem node6_8 :
    CellBound ninth nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_join leaf6 leaf7
private theorem node5_8 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf5 node6_8
private theorem node9_11 :
    CellBound ninth nn0 nn1 Qcell ((4443:ℚ)/6400) ((4481:ℚ)/6400) :=
  cell_join leaf9 leaf10
private theorem node8_11 :
    CellBound ninth nn0 nn1 Qcell ((553:ℚ)/800) ((4481:ℚ)/6400) :=
  cell_join leaf8 node9_11
private theorem node5_11 :
    CellBound ninth nn0 nn1 Qcell ((1087:ℚ)/1600) ((4481:ℚ)/6400) :=
  cell_join node5_8 node8_11
private theorem node0_11 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((4481:ℚ)/6400) :=
  cell_join node0_5 node5_11
private theorem node12_14 :
    CellBound ninth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_join leaf12 leaf13
private theorem node11_14 :
    CellBound ninth nn0 nn1 Qcell ((4481:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_join leaf11 node12_14
private theorem node15_17 :
    CellBound ninth nn0 nn1 Qcell ((4557:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound ninth nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf14 node15_17
private theorem node11_17 :
    CellBound ninth nn0 nn1 Qcell ((4481:ℚ)/6400) ((2307:ℚ)/3200) :=
  cell_join node11_14 node14_17
private theorem node18_20 :
    CellBound ninth nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf17 node18_20
private theorem node21_23 :
    CellBound ninth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf21 leaf22
private theorem node20_23 :
    CellBound ninth nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf20 node21_23
private theorem node17_23 :
    CellBound ninth nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node17_20 node20_23
private theorem node11_23 :
    CellBound ninth nn0 nn1 Qcell ((4481:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node11_17 node17_23
private theorem node0_23 :
    CellBound ninth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_11 node11_23
theorem bound : CellBound ninth nn0 nn1 Qcell (31/50) (69/50) := node0_23
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22]
theorem packet_count : packets.length = 23 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450NinthGroupedC06
#check @N11Formalization.C450NinthGroupedC06.bound
#print axioms N11Formalization.C450NinthGroupedC06.valid0
#print axioms N11Formalization.C450NinthGroupedC06.valid1
#print axioms N11Formalization.C450NinthGroupedC06.valid2
#print axioms N11Formalization.C450NinthGroupedC06.valid3
#print axioms N11Formalization.C450NinthGroupedC06.valid4
#print axioms N11Formalization.C450NinthGroupedC06.valid5
#print axioms N11Formalization.C450NinthGroupedC06.valid6
#print axioms N11Formalization.C450NinthGroupedC06.valid7
#print axioms N11Formalization.C450NinthGroupedC06.valid8
#print axioms N11Formalization.C450NinthGroupedC06.valid9
#print axioms N11Formalization.C450NinthGroupedC06.valid10
#print axioms N11Formalization.C450NinthGroupedC06.valid11
#print axioms N11Formalization.C450NinthGroupedC06.valid12
#print axioms N11Formalization.C450NinthGroupedC06.valid13
#print axioms N11Formalization.C450NinthGroupedC06.valid14
#print axioms N11Formalization.C450NinthGroupedC06.valid15
#print axioms N11Formalization.C450NinthGroupedC06.valid16
#print axioms N11Formalization.C450NinthGroupedC06.valid17
#print axioms N11Formalization.C450NinthGroupedC06.valid18
#print axioms N11Formalization.C450NinthGroupedC06.valid19
#print axioms N11Formalization.C450NinthGroupedC06.valid20
#print axioms N11Formalization.C450NinthGroupedC06.valid21
#print axioms N11Formalization.C450NinthGroupedC06.valid22
#print axioms N11Formalization.C450NinthGroupedC06.bound
#print axioms N11Formalization.C450NinthGroupedC06.endpoint_checks
