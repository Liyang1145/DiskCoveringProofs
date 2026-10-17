import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC15
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((-1:ℚ)/8),((-1:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-1:ℚ)/8),((-1:ℚ)/16),((6209285959:ℚ)/10000000000),((6700751459:ℚ)/10000000000),((-5100751459:ℚ)/49600000000),((-2369285959:ℚ)/106800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1229175217:ℚ)/2000000000),((311128629583594066309819808379881209735576766583927990049:ℚ)/29502952650000000000000000000000000000000000000000000000000),((1138614804131813605215257:ℚ)/231040000000000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((6684514779:ℚ)/10000000000),((6819575767:ℚ)/10000000000),((-1739858589:ℚ)/17800000000),((-2844514779:ℚ)/108700000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2479493767:ℚ)/5000000000),((3643751111763343608695153455807082325443009576603963763771:ℚ)/357214155521875000000000000000000000000000000000000000000000),((831245735870267520964833:ℚ)/231040000000000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((3401658491:ℚ)/5000000000),((6938397519:ℚ)/10000000000),((-5338397519:ℚ)/54350000000),((-1481658491:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2309882471:ℚ)/5000000000),((273508619163383123113447283158015416945915771872547792239:ℚ)/26927512763525390625000000000000000000000000000000000000000),((2277883231327237840597651:ℚ)/693120000000000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((6922117389:ℚ)/10000000000),((3498903739:ℚ)/5000000000),((-385557677:ℚ)/3950000000),((-3082117389:ℚ)/111550000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((4255667121:ℚ)/10000000000),((216248497549221790653777525278059657718003504387243910059:ℚ)/21417355929907226562500000000000000000000000000000000000000),((171036598959621370772937:ℚ)/57760000000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-1:ℚ)/8),((-1:ℚ)/16),((6981516949:ℚ)/10000000000),((3528608423:ℚ)/5000000000),((-2728608423:ℚ)/27887500000),((-3141516949:ℚ)/112500000000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4062209093:ℚ)/10000000000),((1172400548842370888851019097886944584559302645571872097017:ℚ)/116329121589660644531250000000000000000000000000000000000000),((162060404454952824010913:ℚ)/57760000000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((7040916093:ℚ)/10000000000),((7116625637:ℚ)/10000000000),((-5516625637:ℚ)/56250000000),((-3200916093:ℚ)/113450000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((964907577:ℚ)/2500000000),((1032916877355318289916673618128743708744644754613540117:ℚ)/102670585918945312500000000000000000000000000000000000000),((612365061193343700916393:ℚ)/231040000000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-1:ℚ)/8),((-1:ℚ)/16),((7100314833:ℚ)/10000000000),((1794008467:ℚ)/2500000000),((-1394008467:ℚ)/14181250000),((-3260314833:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((455800879:ℚ)/1250000000),((106621409269189422388769654042554627642613309315305915638053:ℚ)/10616041092800000000000000000000000000000000000000000000000000),((36032294886798160324433:ℚ)/14440000000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-1:ℚ)/8),((-1:ℚ)/16),((3579856589:ℚ)/5000000000),((144708831:ℚ)/200000000),((-112708831:ℚ)/1144000000),((-1659856589:ℚ)/57675000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((427568139:ℚ)/1250000000),((100740592771408705187441014404975059217910895923193089:ℚ)/10046855548948287963867187500000000000000000000000000000),((648835899245048756851:ℚ)/277248000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((7219111139:ℚ)/10000000000),((3647424349:ℚ)/5000000000),((-2847424349:ℚ)/28837500000),((-3379111139:ℚ)/116300000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((1589673867:ℚ)/5000000000),((113535834890756778391653354146360721112811095033468098458057:ℚ)/11340619007278125000000000000000000000000000000000000000000000),((126226161892362904355897:ℚ)/57760000000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-1:ℚ)/8),((-1:ℚ)/16),((1819627181:ℚ)/2500000000),((1838563831:ℚ)/2500000000),((-1438563831:ℚ)/14537500000),((-122803883:ℚ)/4187500000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1459505573:ℚ)/5000000000),((8003172429287018783151791153237431057571733524444654347:ℚ)/800599752044677734375000000000000000000000000000000000000),((29321306715512976335617:ℚ)/14440000000000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-1:ℚ)/8),((-1:ℚ)/16),((7337905943:ℚ)/10000000000),((3706830721:ℚ)/5000000000),((-2906830721:ℚ)/29312500000),((-3497905943:ℚ)/118200000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((164616311:ℚ)/625000000),((2013350186437563210443132506007068995903580334828282232241:ℚ)/201694496456250000000000000000000000000000000000000000000000),((108351338955992687729777:ℚ)/57760000000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-1:ℚ)/8),((-1:ℚ)/16),((1479460561:ℚ)/2000000000),((7532472199:ℚ)/10000000000),((-1977490733:ℚ)/19700000000),((-711460561:ℚ)/24020000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((2314739221:ℚ)/10000000000),((63907566837441297055250759409381204724706578954060469831:ℚ)/6398770301193750000000000000000000000000000000000000000000),((401231223336531945530497:ℚ)/231040000000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-1:ℚ)/8),((-1:ℚ)/16),((751609549:ℚ)/1000000000),((7651281063:ℚ)/10000000000),((-6051281063:ℚ)/60050000000),((-367609549:ℚ)/12200000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1487309047:ℚ)/10000000000),((203670584985830986531139397919755924293251404334840664527:ℚ)/20445313575000000000000000000000000000000000000000000000000),((34405990942077:ℚ)/24320000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/8),((-1:ℚ)/16),((1526977369:ℚ)/2000000000),((4063249623:ℚ)/5000000000),((-3263249623:ℚ)/30500000000),((-758977369:ℚ)/25920000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((11116364273480364767556660774284044247995385404805948023:ℚ)/1106531020800000000000000000000000000000000000000000000000),((37599:ℚ)/32000000)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/8),((-1:ℚ)/16),((8110040133:ℚ)/10000000000),((10027164601:ℚ)/10000000000),((-2809054867:ℚ)/21600000000),((-4270040133:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((3577478710184485888470221205694532041176972817343656161239:ℚ)/345600000000000000000000000000000000000000000000000000000000),((37599:ℚ)/32000000)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/8),((-1:ℚ)/16),((2502626903:ℚ)/2500000000),((6913972751:ℚ)/5000000000),((-6113972751:ℚ)/40000000000),((-1542626903:ℚ)/55200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((4457139711257040476296173013359060653405219424212066021:ℚ)/394210800000000000000000000000000000000000000000000000000),((37599:ℚ)/32000000)⟩
theorem valid15 : Valid seventh packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound seventh nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound seventh nn0 nn1 Qcell ((2231:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC15
#check @N11Formalization.C450SeventhGroupedC15.bound
#print axioms N11Formalization.C450SeventhGroupedC15.valid0
#print axioms N11Formalization.C450SeventhGroupedC15.valid1
#print axioms N11Formalization.C450SeventhGroupedC15.valid2
#print axioms N11Formalization.C450SeventhGroupedC15.valid3
#print axioms N11Formalization.C450SeventhGroupedC15.valid4
#print axioms N11Formalization.C450SeventhGroupedC15.valid5
#print axioms N11Formalization.C450SeventhGroupedC15.valid6
#print axioms N11Formalization.C450SeventhGroupedC15.valid7
#print axioms N11Formalization.C450SeventhGroupedC15.valid8
#print axioms N11Formalization.C450SeventhGroupedC15.valid9
#print axioms N11Formalization.C450SeventhGroupedC15.valid10
#print axioms N11Formalization.C450SeventhGroupedC15.valid11
#print axioms N11Formalization.C450SeventhGroupedC15.valid12
#print axioms N11Formalization.C450SeventhGroupedC15.valid13
#print axioms N11Formalization.C450SeventhGroupedC15.valid14
#print axioms N11Formalization.C450SeventhGroupedC15.valid15
#print axioms N11Formalization.C450SeventhGroupedC15.bound
#print axioms N11Formalization.C450SeventhGroupedC15.endpoint_checks
