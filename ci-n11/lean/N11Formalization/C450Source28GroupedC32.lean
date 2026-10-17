import N11Formalization.C450Source28Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source28GroupedC32
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source28Data
def Qcell : RatInterval := ⟨((15:ℚ)/16),(1:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((15:ℚ)/16),(1:ℚ),((2559999999:ℚ)/5000000000),((170384973:ℚ)/312500000),((9343999997:ℚ)/10300000000),(1:ℚ),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((8316135267:ℚ)/10000000000),((-10103419247059729082784333692460483353366322054780416741:ℚ)/20488631250000000000000000000000000000000000000000000000),((-281315936178797967362701611:ℚ)/739328000000000000000000000)⟩
theorem valid0 : Valid source28 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source28 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((15:ℚ)/16),(1:ℚ),((2678749999:ℚ)/5000000000),((35563637:ℚ)/62500000),((108991573:ℚ)/120000000),(1:ℚ),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((7884659421:ℚ)/10000000000),((-1331215910389448188979566052969959932699695122303:ℚ)/2700000000000000000000000000000000000000000000000),((-273571886565468116170201611:ℚ)/739328000000000000000000000)⟩
theorem valid1 : Valid source28 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source28 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source28 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((2797499999:ℚ)/5000000000),((290455189:ℚ)/500000000),((10056499997:ℚ)/10870000000),(1:ℚ),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((743381539:ℚ)/1000000000),((-4115733908620693320667899266371856898585282691247074607:ℚ)/8027284393750000000000000000000000000000000000000000000),((-270616771525386042857701611:ℚ)/739328000000000000000000000)⟩
theorem valid2 : Valid source28 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((2856874999:ℚ)/5000000000),((5868562471:ℚ)/10000000000),((10234624997:ℚ)/10965000000),(1:ℚ),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((7199947209:ℚ)/10000000000),((-358679690109410362474486365722074895565289184489798189:ℚ)/686633011523437500000000000000000000000000000000000000),((-269167875422472052506451611:ℚ)/739328000000000000000000000)⟩
theorem valid3 : Valid source28 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((15:ℚ)/16),(1:ℚ),((2886562499:ℚ)/5000000000),((2964009861:ℚ)/5000000000),((10323687497:ℚ)/11060000000),(1:ℚ),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((442540667:ℚ)/625000000),((-206921283210181663961018397074773317290286550270661849:ℚ)/396357133593750000000000000000000000000000000000000000),((-267272675626321924827076611:ℚ)/739328000000000000000000000)⟩
theorem valid4 : Valid source28 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source28 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((2916249999:ℚ)/5000000000),((5987475569:ℚ)/10000000000),((10412749997:ℚ)/11155000000),(1:ℚ),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((217489629:ℚ)/312500000),((-282900914029507512673312019598893182626868344164701663:ℚ)/542211542529296875000000000000000000000000000000000000),((-265382293577254196065201611:ℚ)/739328000000000000000000000)⟩
theorem valid5 : Valid source28 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((4481:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((2945937499:ℚ)/5000000000),((6017202977:ℚ)/10000000000),((10501812497:ℚ)/11202500000),(1:ℚ),((1922169193:ℚ)/2000000000),((9622019977:ℚ)/10000000000),((349868089:ℚ)/1250000000),((6836907503:ℚ)/10000000000),((-185027261563303204093401027575972582795228076674818563:ℚ)/351467252503906250000000000000000000000000000000000000),((-264674589704115765420826611:ℚ)/739328000000000000000000000)⟩
theorem valid6 : Valid source28 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source28 nn0 nn1 Qcell ((2231:ℚ)/3200) ((4481:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4481:ℚ)/6400),((45:ℚ)/64),((15:ℚ)/16),(1:ℚ),((2960781249:ℚ)/5000000000),((47241641:ℚ)/78125000),((10546343747:ℚ)/11250000000),(1:ℚ),((599993229:ℚ)/625000000),((961084597:ℚ)/1000000000),((2838327983:ℚ)/10000000000),((6774829457:ℚ)/10000000000),((-54881910984679108945593738505903248774776881685324651:ℚ)/104284286499023437500000000000000000000000000000000000),((-263733599310206546972701611:ℚ)/739328000000000000000000000)⟩
theorem valid7 : Valid source28 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source28 nn0 nn1 Qcell ((4481:ℚ)/6400) ((45:ℚ)/64) :=
  cell_of_packet source28 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((45:ℚ)/64),((4519:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((2975624999:ℚ)/5000000000),((1215331357:ℚ)/2000000000),((10590874997:ℚ)/11297500000),(1:ℚ),((9589154297:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((575284399:ℚ)/2000000000),((6712268651:ℚ)/10000000000),((-4741324837304903089216011111642138534101751680061214583:ℚ)/9012122105371093750000000000000000000000000000000000000),((-262793812679484865213951611:ℚ)/739328000000000000000000000)⟩
theorem valid8 : Valid source28 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((4519:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4519:ℚ)/6400),((2269:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((2990468749:ℚ)/5000000000),((6106383193:ℚ)/10000000000),((10635406247:ℚ)/11345000000),(1:ℚ),((478931557:ℚ)/500000000),((4794577151:ℚ)/5000000000),((1456642997:ℚ)/5000000000),((3324605569:ℚ)/5000000000),((-11999723054693307716398418364547098360891246586950813:ℚ)/22815685759765625000000000000000000000000000000000000),((-261855229613838054544576611:ℚ)/739328000000000000000000000)⟩
theorem valid9 : Valid source28 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source28 nn0 nn1 Qcell ((4519:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2269:ℚ)/3200),((1819:ℚ)/2560),((15:ℚ)/16),(1:ℚ),((3005312499:ℚ)/5000000000),((244849851:ℚ)/400000000),((10679937497:ℚ)/11368750000),(1:ℚ),((9573449051:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((73281849:ℚ)/250000000),((3292821163:ℚ)/5000000000),((-4851222274692250829797260515297621897340293993035492387:ℚ)/9183710111999511718750000000000000000000000000000000000),((-261506759704161075604576611:ℚ)/739328000000000000000000000)⟩
theorem valid10 : Valid source28 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source28 nn0 nn1 Qcell ((2269:ℚ)/3200) ((1819:ℚ)/2560) :=
  cell_of_packet source28 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1819:ℚ)/2560),((4557:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((1506367187:ℚ)/2500000000),((1534027319:ℚ)/2500000000),((5351101561:ℚ)/5696250000),(1:ℚ),((9568319513:ℚ)/10000000000),((299170283:ℚ)/312500000),((2948974549:ℚ)/10000000000),((6553661437:ℚ)/10000000000),((-67790205556219525190682288122389525049140760448542899:ℚ)/128352588830566406250000000000000000000000000000000000),((-65259629481953920978273059:ℚ)/184832000000000000000000000)⟩
theorem valid11 : Valid source28 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source28 nn0 nn1 Qcell ((1819:ℚ)/2560) ((4557:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((4557:ℚ)/6400),((9133:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((3020156249:ℚ)/5000000000),((6150972197:ℚ)/10000000000),((10724468747:ℚ)/11416250000),(1:ℚ),((4781621099:ℚ)/5000000000),((4784159759:ℚ)/5000000000),((185399621:ℚ)/625000000),((6521546939:ℚ)/10000000000),((-1227673181518120802952631941002122803580405629171227537:ℚ)/2324825914419555664062500000000000000000000000000000000),((-260570576953588310473951611:ℚ)/739328000000000000000000000)⟩
theorem valid12 : Valid source28 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source28 nn0 nn1 Qcell ((4557:ℚ)/6400) ((9133:ℚ)/12800) :=
  cell_of_packet source28 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((9133:ℚ)/12800),((143:ℚ)/200),((15:ℚ)/16),(1:ℚ),((756894531:ℚ)/1250000000),((3082917519:ℚ)/5000000000),((244243963:ℚ)/260000000),(1:ℚ),((9558216781:ℚ)/10000000000),((9563242203:ℚ)/10000000000),((149176903:ℚ)/500000000),((6489296807:ℚ)/10000000000),((-57999346735295967512290830428241084246262325194673:ℚ)/109850000000000000000000000000000000000000000000000),((-16256433548842434705447171:ℚ)/46208000000000000000000000)⟩
theorem valid13 : Valid source28 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source28 nn0 nn1 Qcell ((9133:ℚ)/12800) ((143:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((143:ℚ)/200),((9171:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((3034999999:ℚ)/5000000000),((6180697799:ℚ)/10000000000),((10768999997:ℚ)/11463750000),(1:ℚ),((9553242939:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((600082529:ℚ)/2000000000),((6456908969:ℚ)/10000000000),((-14911997935158226027270775960309643970226510715855758981:ℚ)/28247589375402832031250000000000000000000000000000000000),((-259635597411487618352701611:ℚ)/739328000000000000000000000)⟩
theorem valid14 : Valid source28 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source28 nn0 nn1 Qcell ((143:ℚ)/200) ((9171:ℚ)/12800) :=
  cell_of_packet source28 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((9171:ℚ)/12800),((919:ℚ)/1280),((15:ℚ)/16),(1:ℚ),((1521210937:ℚ)/2500000000),((6195560483:ℚ)/10000000000),((5395632811:ℚ)/5743750000),(1:ℚ),((9548320353:ℚ)/10000000000),((149269421:ℚ)/156250000),((1508511599:ℚ)/5000000000),((6424381301:ℚ)/10000000000),((-1875315714155448086667868005844305311249502399725665003:ℚ)/3552939875793457031250000000000000000000000000000000000),((-64792139681186675077648059:ℚ)/184832000000000000000000000)⟩
theorem valid15 : Valid source28 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source28 nn0 nn1 Qcell ((9171:ℚ)/12800) ((919:ℚ)/1280) :=
  cell_of_packet source28 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((919:ℚ)/1280),((9209:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((3049843749:ℚ)/5000000000),((6210423087:ℚ)/10000000000),((10813531247:ℚ)/11511250000),(1:ℚ),((74558193:ℚ)/78125000),((4774160179:ℚ)/5000000000),((1516687521:ℚ)/5000000000),((1597927907:ℚ)/2500000000),((-921230059258980555495219865934960321909698032568439:ℚ)/1745616308590024709701538085937500000000000000000000),((-258701820840123800520826611:ℚ)/739328000000000000000000000)⟩
theorem valid16 : Valid source28 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source28 nn0 nn1 Qcell ((919:ℚ)/1280) ((9209:ℚ)/12800) :=
  cell_of_packet source28 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((9209:ℚ)/12800),((2307:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((382158203:ℚ)/625000000),((3112642807:ℚ)/5000000000),((1354474609:ℚ)/1441875000),(1:ℚ),((59616423:ℚ)/62500000),((9543448709:ℚ)/10000000000),((762368323:ℚ)/2500000000),((158972443:ℚ)/250000000),((-1158502317087271422383335131860157705692386581337:ℚ)/2195554097235202789306640625000000000000000000000),((-4034927869355489369115699:ℚ)/11552000000000000000000000)⟩
theorem valid17 : Valid source28 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source28 nn0 nn1 Qcell ((9209:ℚ)/12800) ((2307:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((2307:ℚ)/3200),((9247:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((3064687499:ℚ)/5000000000),((195004627:ℚ)/312500000),((10858062497:ℚ)/11558750000),(1:ℚ),((4766928483:ℚ)/5000000000),((1907725537:ℚ)/2000000000),((3065322907:ℚ)/10000000000),((1581484323:ℚ)/2500000000),((-3819097863170856139347368728510561966863409001074838129:ℚ)/7238921925869750976562500000000000000000000000000000000),((-257769247120629257618326611:ℚ)/739328000000000000000000000)⟩
theorem valid18 : Valid source28 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source28 nn0 nn1 Qcell ((2307:ℚ)/3200) ((9247:ℚ)/12800) :=
  cell_of_packet source28 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((9247:ℚ)/12800),((4633:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((1536054687:ℚ)/2500000000),((6255010437:ℚ)/10000000000),((5440164061:ℚ)/5791250000),(1:ℚ),((1905827251:ℚ)/2000000000),((9533856971:ℚ)/10000000000),((3080928657:ℚ)/10000000000),((6292827999:ℚ)/10000000000),((-25614073068469609450517764193677929922611653848664039:ℚ)/48557570379394531250000000000000000000000000000000000),((-64325852821439403626398059:ℚ)/184832000000000000000000000)⟩
theorem valid19 : Valid source28 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source28 nn0 nn1 Qcell ((9247:ℚ)/12800) ((4633:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨((4633:ℚ)/6400),((1857:ℚ)/2560),((15:ℚ)/16),(1:ℚ),((3079531249:ℚ)/5000000000),((6269872733:ℚ)/10000000000),((10902593747:ℚ)/11606250000),(1:ℚ),((9524465239:ℚ)/10000000000),((476456813:ℚ)/500000000),((3096295161:ℚ)/10000000000),((78244593:ℚ)/125000000),((-572625171796602154001197307747880199931969334431266153:ℚ)/1085708583068847656250000000000000000000000000000000000),((-256837876134136390285201611:ℚ)/739328000000000000000000000)⟩
theorem valid20 : Valid source28 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source28 nn0 nn1 Qcell ((4633:ℚ)/6400) ((1857:ℚ)/2560) :=
  cell_of_packet source28 nn0 nn1 packet20 valid20
def packet21 : Packet := ⟨((1857:ℚ)/2560),((1163:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((771738281:ℚ)/1250000000),((3142367477:ℚ)/5000000000),((2731214843:ℚ)/2907500000),(1:ℚ),((9519843613:ℚ)/10000000000),((2381116311:ℚ)/2500000000),((622285377:ℚ)/2000000000),((1556538287:ℚ)/2500000000),((-81008852857559433153529942319137049304894393725914577:ℚ)/153616967480468750000000000000000000000000000000000000),((-16023290099157532419822171:ℚ)/46208000000000000000000000)⟩
theorem valid21 : Valid source28 packet21 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf21 :
    CellBound source28 nn0 nn1 Qcell ((1857:ℚ)/2560) ((1163:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet21 valid21
def packet22 : Packet := ⟨((1163:ℚ)/1600),((9323:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((3094374999:ℚ)/5000000000),((6299597099:ℚ)/10000000000),((10947124997:ℚ)/11653750000),(1:ℚ),((2378817769:ℚ)/2500000000),((4759921809:ℚ)/5000000000),((156316407:ℚ)/500000000),((3096291297:ℚ)/5000000000),((-325977189095595196410165354584972525544452251116204007:ℚ)/618240036977386474609375000000000000000000000000000000),((-255907707682532532921451611:ℚ)/739328000000000000000000000)⟩
theorem valid22 : Valid source28 packet22 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf22 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((9323:ℚ)/12800) :=
  cell_of_packet source28 nn0 nn1 packet22 valid22
def packet23 : Packet := ⟨((9323:ℚ)/12800),((4671:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((1550898437:ℚ)/2500000000),((6314459169:ℚ)/10000000000),((5484695311:ℚ)/5838750000),(1:ℚ),((148605427:ℚ)/156250000),((9515271081:ℚ)/10000000000),((98156347:ℚ)/312500000),((307942659:ℚ)/500000000),((-160120610833806224434692951791583359359505749338581:ℚ)/303724419209361076354980468750000000000000000000000),((-63860768595637474944523059:ℚ)/184832000000000000000000000)⟩
theorem valid23 : Valid source28 packet23 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf23 :
    CellBound source28 nn0 nn1 Qcell ((9323:ℚ)/12800) ((4671:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet23 valid23
def packet24 : Packet := ⟨((4671:ℚ)/6400),((9361:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((3109218749:ℚ)/5000000000),((1265864233:ℚ)/2000000000),((999241477:ℚ)/1063750000),(1:ℚ),((1188284009:ℚ)/1250000000),((9510747333:ℚ)/10000000000),((157772791:ℚ)/500000000),((6124962241:ℚ)/10000000000),((-61961851236307590485450927140252238763554236051687:ℚ)/117548952293395996093750000000000000000000000000000),((-254978741646950086167076611:ℚ)/739328000000000000000000000)⟩
theorem valid24 : Valid source28 packet24 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf24 :
    CellBound source28 nn0 nn1 Qcell ((4671:ℚ)/6400) ((9361:ℚ)/12800) :=
  cell_of_packet source28 nn0 nn1 packet24 valid24
def packet25 : Packet := ⟨((9361:ℚ)/12800),((469:ℚ)/640),((15:ℚ)/16),(1:ℚ),((194790039:ℚ)/312500000),((3172091543:ℚ)/5000000000),((688370117:ℚ)/732812500),(1:ℚ),((9501845013:ℚ)/10000000000),((9506272077:ℚ)/10000000000),((792422551:ℚ)/2500000000),((3045453519:ℚ)/5000000000),((-3888877300371097612522652882691346744695527382624929:ℚ)/7378700423240661621093750000000000000000000000000000),((-994198084044357910970331:ℚ)/2888000000000000000000000)⟩
theorem valid25 : Valid source28 packet25 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf25 :
    CellBound source28 nn0 nn1 Qcell ((9361:ℚ)/12800) ((469:ℚ)/640) :=
  cell_of_packet source28 nn0 nn1 packet25 valid25
def packet26 : Packet := ⟨((469:ℚ)/640),((9399:ℚ)/12800),((15:ℚ)/16),(1:ℚ),((3124062499:ℚ)/5000000000),((3179522467:ℚ)/5000000000),((11036187497:ℚ)/11748750000),(1:ℚ),((474873293:ℚ)/500000000),((4750922509:ℚ)/5000000000),((636742009:ℚ)/2000000000),((6056684759:ℚ)/10000000000),((-6156291947491085826848794554358639631363083064827:ℚ)/11682491180419921875000000000000000000000000000000),((-254050977908521450662076611:ℚ)/739328000000000000000000000)⟩
theorem valid26 : Valid source28 packet26 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf26 :
    CellBound source28 nn0 nn1 Qcell ((469:ℚ)/640) ((9399:ℚ)/12800) :=
  cell_of_packet source28 nn0 nn1 packet26 valid26
def packet27 : Packet := ⟨((9399:ℚ)/12800),((4709:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((1565742187:ℚ)/2500000000),((6373906709:ℚ)/10000000000),((5529226561:ℚ)/5886250000),(1:ℚ),((9493134321:ℚ)/10000000000),((1899493173:ℚ)/2000000000),((1598759513:ℚ)/5000000000),((1204458503:ℚ)/2000000000),((-118520159485573055170189920074864020572217976491234841:ℚ)/224940916882324218750000000000000000000000000000000000),((-63396886706611890632023059:ℚ)/184832000000000000000000000)⟩
theorem valid27 : Valid source28 packet27 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf27 :
    CellBound source28 nn0 nn1 Qcell ((9399:ℚ)/12800) ((4709:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet27 valid27
def packet28 : Packet := ⟨((4709:ℚ)/6400),((591:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3138906249:ℚ)/5000000000),((6403630041:ℚ)/10000000000),((11080718747:ℚ)/11820000000),(1:ℚ),((4742306471:ℚ)/5000000000),((4746567163:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1496931833:ℚ)/2500000000),((-50123492550673136423552375510370085717251645598761371:ℚ)/95567162500000000000000000000000000000000000000000000),((-252535560842241775206451611:ℚ)/739328000000000000000000000)⟩
theorem valid28 : Valid source28 packet28 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf28 :
    CellBound source28 nn0 nn1 Qcell ((4709:ℚ)/6400) ((591:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet28 valid28
def packet29 : Packet := ⟨((591:ℚ)/800),((4747:ℚ)/6400),((15:ℚ)/16),(1:ℚ),((3153749999:ℚ)/5000000000),((3216676543:ℚ)/5000000000),((11125249997:ℚ)/11867500000),(1:ℚ),((9476278601:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1625358023:ℚ)/5000000000),((5918065851:ℚ)/10000000000),((-5477515346378757744775527691755874215415419739180559087:ℚ)/10446185617480468750000000000000000000000000000000000000),((-251610206849050067800201611:ℚ)/739328000000000000000000000)⟩
theorem valid29 : Valid source28 packet29 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf29 :
    CellBound source28 nn0 nn1 Qcell ((591:ℚ)/800) ((4747:ℚ)/6400) :=
  cell_of_packet source28 nn0 nn1 packet29 valid29
def packet30 : Packet := ⟨((4747:ℚ)/6400),((2383:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3168593749:ℚ)/5000000000),((6463075847:ℚ)/10000000000),((11169781247:ℚ)/11915000000),(1:ℚ),((9468129063:ℚ)/10000000000),((4738139303:ℚ)/5000000000),((3276137213:ℚ)/10000000000),((5847674811:ℚ)/10000000000),((-16626654976827370668459690977358234030697384308310524359:ℚ)/31716365360156250000000000000000000000000000000000000000),((-250686054637919241083326611:ℚ)/739328000000000000000000000)⟩
theorem valid30 : Valid source28 packet30 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf30 :
    CellBound source28 nn0 nn1 Qcell ((4747:ℚ)/6400) ((2383:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet30 valid30
def packet31 : Packet := ⟨((2383:ℚ)/3200),((957:ℚ)/1280),((15:ℚ)/16),(1:ℚ),((3183437499:ℚ)/5000000000),((6492798327:ℚ)/10000000000),((11214312497:ℚ)/11962500000),(1:ℚ),((75681297:ℚ)/80000000),((2367032267:ℚ)/2500000000),((1650403157:ℚ)/5000000000),((2888263599:ℚ)/5000000000),((-1076630124105505395745529250557514729715287701024249:ℚ)/2054220686718750000000000000000000000000000000000000),((-249763104089981695695826611:ℚ)/739328000000000000000000000)⟩
theorem valid31 : Valid source28 packet31 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf31 :
    CellBound source28 nn0 nn1 Qcell ((2383:ℚ)/3200) ((957:ℚ)/1280) :=
  cell_of_packet source28 nn0 nn1 packet31 valid31
def packet32 : Packet := ⟨((957:ℚ)/1280),((1201:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3198281249:ℚ)/5000000000),((652252053:ℚ)/1000000000),((11258843747:ℚ)/12010000000),(1:ℚ),((4726187811:ℚ)/5000000000),((946016213:ℚ)/1000000000),((831186567:ℚ)/2500000000),((1426148589:ℚ)/2500000000),((-4254906369585053152864836407028677606411404963932306731:ℚ)/8120266879687500000000000000000000000000000000000000000),((-248841355046747299157701611:ℚ)/739328000000000000000000000)⟩
theorem valid32 : Valid source28 packet32 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf32 :
    CellBound source28 nn0 nn1 Qcell ((957:ℚ)/1280) ((1201:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet32 valid32
def packet33 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3213124999:ℚ)/5000000000),((3290982059:ℚ)/5000000000),((11303374997:ℚ)/12105000000),(1:ℚ),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((703980731:ℚ)/1250000000),((-4318248511046329715469076380308172378737248563337213781:ℚ)/8314490895117187500000000000000000000000000000000000000),((-246743159971239606028951611:ℚ)/739328000000000000000000000)⟩
theorem valid33 : Valid source28 packet33 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf33 :
    CellBound source28 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source28 nn0 nn1 packet33 valid33
def packet34 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((15:ℚ)/16),(1:ℚ),((3242812499:ℚ)/5000000000),((1660351659:ℚ)/2500000000),((11392437497:ℚ)/12200000000),(1:ℚ),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2741885097:ℚ)/5000000000),((-17676731440766383531279764428225782194190344678896280161:ℚ)/34047150000000000000000000000000000000000000000000000000),((-244905689338420716559576611:ℚ)/739328000000000000000000000)⟩
theorem valid34 : Valid source28 packet34 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf34 :
    CellBound source28 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source28 nn0 nn1 packet34 valid34
def packet35 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3272499999:ℚ)/5000000000),((84503607:ℚ)/125000000),((11481499997:ℚ)/12390000000),(1:ℚ),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((5332014537:ℚ)/10000000000),((-6067028629522874496478519002922077439917925058116798583:ℚ)/11887593243750000000000000000000000000000000000000000000),((-240717840989779598807701611:ℚ)/739328000000000000000000000)⟩
theorem valid35 : Valid source28 packet35 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf35 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source28 nn0 nn1 packet35 valid35
def packet36 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3331874999:ℚ)/5000000000),((1719791623:ℚ)/2500000000),((11659624997:ℚ)/12580000000),(1:ℚ),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((2508053531:ℚ)/5000000000),((-4761477028328177838381361122532608533586973816790589989:ℚ)/9332182087500000000000000000000000000000000000000000000),((-237066991787846596536451611:ℚ)/739328000000000000000000000)⟩
theorem valid36 : Valid source28 packet36 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf36 :
    CellBound source28 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source28 nn0 nn1 packet36 valid36
def packet37 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((15:ℚ)/16),(1:ℚ),((3391249999:ℚ)/5000000000),((7116911087:ℚ)/10000000000),((11837749997:ℚ)/12960000000),(1:ℚ),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((4680843793:ℚ)/10000000000),((-2240677871077620139389374711905355750394239695669557989:ℚ)/4534963200000000000000000000000000000000000000000000000),((-228725392762515809455201611:ℚ)/739328000000000000000000000)⟩
theorem valid37 : Valid source28 packet37 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf37 :
    CellBound source28 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source28 nn0 nn1 packet37 valid37
def packet38 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3509999999:ℚ)/5000000000),((8067760919:ℚ)/10000000000),((12193999997:ℚ)/14480000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((786418339:ℚ)/2000000000),((-1476455108146600268645182737011549561191027227599034101:ℚ)/3557844600000000000000000000000000000000000000000000000),((-211798219840134690782701611:ℚ)/739328000000000000000000000)⟩
theorem valid38 : Valid source28 packet38 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf38 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source28 nn0 nn1 packet38 valid38
def packet39 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((15:ℚ)/16),(1:ℚ),((3984999999:ℚ)/5000000000),((9018449107:ℚ)/10000000000),((13618999997:ℚ)/16000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-2717655298735205531584890869546730656258830145732592687:ℚ)/6400000000000000000000000000000000000000000000000000000),((-301281669:ℚ)/1024000000)⟩
theorem valid39 : Valid source28 packet39 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf39 :
    CellBound source28 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source28 nn0 nn1 packet39 valid39
def packet40 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((15:ℚ)/16),(1:ℚ),((4459999999:ℚ)/5000000000),((2564050743:ℚ)/2000000000),((15043999997:ℚ)/22080000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-683702874916006721094607446794778061:ℚ)/2691145728000000000000000000000000000),((-301281669:ℚ)/1024000000)⟩
theorem valid40 : Valid source28 packet40 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf40 :
    CellBound source28 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source28 nn0 nn1 packet40 valid40
private theorem node0_2 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source28 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source28 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((4481:ℚ)/6400) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source28 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source28 nn0 nn1 Qcell ((4481:ℚ)/6400) ((2269:ℚ)/3200) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source28 nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source28 nn0 nn1 Qcell ((2269:ℚ)/3200) ((4557:ℚ)/6400) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source28 nn0 nn1 Qcell ((9133:ℚ)/12800) ((9171:ℚ)/12800) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source28 nn0 nn1 Qcell ((4557:ℚ)/6400) ((9171:ℚ)/12800) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source28 nn0 nn1 Qcell ((2269:ℚ)/3200) ((9171:ℚ)/12800) :=
  cell_join node10_12 node12_15
private theorem node15_17 :
    CellBound source28 nn0 nn1 Qcell ((9171:ℚ)/12800) ((9209:ℚ)/12800) :=
  cell_join leaf15 leaf16
private theorem node18_20 :
    CellBound source28 nn0 nn1 Qcell ((2307:ℚ)/3200) ((4633:ℚ)/6400) :=
  cell_join leaf18 leaf19
private theorem node17_20 :
    CellBound source28 nn0 nn1 Qcell ((9209:ℚ)/12800) ((4633:ℚ)/6400) :=
  cell_join leaf17 node18_20
private theorem node15_20 :
    CellBound source28 nn0 nn1 Qcell ((9171:ℚ)/12800) ((4633:ℚ)/6400) :=
  cell_join node15_17 node17_20
private theorem node10_20 :
    CellBound source28 nn0 nn1 Qcell ((2269:ℚ)/3200) ((4633:ℚ)/6400) :=
  cell_join node10_15 node15_20
private theorem node0_20 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((4633:ℚ)/6400) :=
  cell_join node0_10 node10_20
private theorem node20_22 :
    CellBound source28 nn0 nn1 Qcell ((4633:ℚ)/6400) ((1163:ℚ)/1600) :=
  cell_join leaf20 leaf21
private theorem node23_25 :
    CellBound source28 nn0 nn1 Qcell ((9323:ℚ)/12800) ((9361:ℚ)/12800) :=
  cell_join leaf23 leaf24
private theorem node22_25 :
    CellBound source28 nn0 nn1 Qcell ((1163:ℚ)/1600) ((9361:ℚ)/12800) :=
  cell_join leaf22 node23_25
private theorem node20_25 :
    CellBound source28 nn0 nn1 Qcell ((4633:ℚ)/6400) ((9361:ℚ)/12800) :=
  cell_join node20_22 node22_25
private theorem node25_27 :
    CellBound source28 nn0 nn1 Qcell ((9361:ℚ)/12800) ((9399:ℚ)/12800) :=
  cell_join leaf25 leaf26
private theorem node28_30 :
    CellBound source28 nn0 nn1 Qcell ((4709:ℚ)/6400) ((4747:ℚ)/6400) :=
  cell_join leaf28 leaf29
private theorem node27_30 :
    CellBound source28 nn0 nn1 Qcell ((9399:ℚ)/12800) ((4747:ℚ)/6400) :=
  cell_join leaf27 node28_30
private theorem node25_30 :
    CellBound source28 nn0 nn1 Qcell ((9361:ℚ)/12800) ((4747:ℚ)/6400) :=
  cell_join node25_27 node27_30
private theorem node20_30 :
    CellBound source28 nn0 nn1 Qcell ((4633:ℚ)/6400) ((4747:ℚ)/6400) :=
  cell_join node20_25 node25_30
private theorem node30_32 :
    CellBound source28 nn0 nn1 Qcell ((4747:ℚ)/6400) ((957:ℚ)/1280) :=
  cell_join leaf30 leaf31
private theorem node33_35 :
    CellBound source28 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf33 leaf34
private theorem node32_35 :
    CellBound source28 nn0 nn1 Qcell ((957:ℚ)/1280) ((61:ℚ)/80) :=
  cell_join leaf32 node33_35
private theorem node30_35 :
    CellBound source28 nn0 nn1 Qcell ((4747:ℚ)/6400) ((61:ℚ)/80) :=
  cell_join node30_32 node32_35
private theorem node36_38 :
    CellBound source28 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf36 leaf37
private theorem node35_38 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf35 node36_38
private theorem node39_41 :
    CellBound source28 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf39 leaf40
private theorem node38_41 :
    CellBound source28 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf38 node39_41
private theorem node35_41 :
    CellBound source28 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node35_38 node38_41
private theorem node30_41 :
    CellBound source28 nn0 nn1 Qcell ((4747:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node30_35 node35_41
private theorem node20_41 :
    CellBound source28 nn0 nn1 Qcell ((4633:ℚ)/6400) ((69:ℚ)/50) :=
  cell_join node20_30 node30_41
private theorem node0_41 :
    CellBound source28 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_20 node20_41
theorem bound : CellBound source28 nn0 nn1 Qcell (31/50) (69/50) := node0_41
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20,packet21,packet22,packet23,packet24,packet25,packet26,packet27,packet28,packet29,packet30,packet31,packet32,packet33,packet34,packet35,packet36,packet37,packet38,packet39,packet40]
theorem packet_count : packets.length = 41 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source28GroupedC32
#check @N11Formalization.C450Source28GroupedC32.bound
#print axioms N11Formalization.C450Source28GroupedC32.valid0
#print axioms N11Formalization.C450Source28GroupedC32.valid1
#print axioms N11Formalization.C450Source28GroupedC32.valid2
#print axioms N11Formalization.C450Source28GroupedC32.valid3
#print axioms N11Formalization.C450Source28GroupedC32.valid4
#print axioms N11Formalization.C450Source28GroupedC32.valid5
#print axioms N11Formalization.C450Source28GroupedC32.valid6
#print axioms N11Formalization.C450Source28GroupedC32.valid7
#print axioms N11Formalization.C450Source28GroupedC32.valid8
#print axioms N11Formalization.C450Source28GroupedC32.valid9
#print axioms N11Formalization.C450Source28GroupedC32.valid10
#print axioms N11Formalization.C450Source28GroupedC32.valid11
#print axioms N11Formalization.C450Source28GroupedC32.valid12
#print axioms N11Formalization.C450Source28GroupedC32.valid13
#print axioms N11Formalization.C450Source28GroupedC32.valid14
#print axioms N11Formalization.C450Source28GroupedC32.valid15
#print axioms N11Formalization.C450Source28GroupedC32.valid16
#print axioms N11Formalization.C450Source28GroupedC32.valid17
#print axioms N11Formalization.C450Source28GroupedC32.valid18
#print axioms N11Formalization.C450Source28GroupedC32.valid19
#print axioms N11Formalization.C450Source28GroupedC32.valid20
#print axioms N11Formalization.C450Source28GroupedC32.valid21
#print axioms N11Formalization.C450Source28GroupedC32.valid22
#print axioms N11Formalization.C450Source28GroupedC32.valid23
#print axioms N11Formalization.C450Source28GroupedC32.valid24
#print axioms N11Formalization.C450Source28GroupedC32.valid25
#print axioms N11Formalization.C450Source28GroupedC32.valid26
#print axioms N11Formalization.C450Source28GroupedC32.valid27
#print axioms N11Formalization.C450Source28GroupedC32.valid28
#print axioms N11Formalization.C450Source28GroupedC32.valid29
#print axioms N11Formalization.C450Source28GroupedC32.valid30
#print axioms N11Formalization.C450Source28GroupedC32.valid31
#print axioms N11Formalization.C450Source28GroupedC32.valid32
#print axioms N11Formalization.C450Source28GroupedC32.valid33
#print axioms N11Formalization.C450Source28GroupedC32.valid34
#print axioms N11Formalization.C450Source28GroupedC32.valid35
#print axioms N11Formalization.C450Source28GroupedC32.valid36
#print axioms N11Formalization.C450Source28GroupedC32.valid37
#print axioms N11Formalization.C450Source28GroupedC32.valid38
#print axioms N11Formalization.C450Source28GroupedC32.valid39
#print axioms N11Formalization.C450Source28GroupedC32.valid40
#print axioms N11Formalization.C450Source28GroupedC32.bound
#print axioms N11Formalization.C450Source28GroupedC32.endpoint_checks
