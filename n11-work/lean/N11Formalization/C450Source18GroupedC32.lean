import N11Formalization.C450Source18Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source18GroupedC32
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source18Data
def Qcell : RatInterval := ⟨((15:ℚ)/16),(1:ℚ)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((15:ℚ)/16),(1:ℚ),((2759999999:ℚ)/5000000000),((1517820903:ℚ)/2500000000),((9303999997:ℚ)/10680000000),(1:ℚ),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((7578496019:ℚ)/10000000000),((-109536744613941564615010599242303143226781935701361879:ℚ)/951708150000000000000000000000000000000000000000000000),((-12303952240987660848014949:ℚ)/36966400000000000000000000)⟩
theorem valid0 : Valid source18 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((15:ℚ)/16),(1:ℚ),((5994999997:ℚ)/10000000000),((788613921:ℚ)/1250000000),((20032999991:ℚ)/22120000000),(1:ℚ),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1654791063:ℚ)/2500000000),((-2609945548270174369195979769261770355133646288324089:ℚ)/20068715625000000000000000000000000000000000000000000),((-48417051148256347638134541:ℚ)/147865600000000000000000000)⟩
theorem valid1 : Valid source18 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source18 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3116249999:ℚ)/5000000000),((6546530629:ℚ)/10000000000),((10372749997:ℚ)/11440000000),(1:ℚ),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((3046351779:ℚ)/5000000000),((-608497597639242965271930699403804781922395019102215079:ℚ)/4678731200000000000000000000000000000000000000000000000),((-11894992937489829833514949:ℚ)/36966400000000000000000000)⟩
theorem valid2 : Valid source18 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3234999999:ℚ)/5000000000),((833167167:ℚ)/1250000000),((10728999997:ℚ)/11630000000),(1:ℚ),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5523081931:ℚ)/10000000000),((-673562461325114569454786209176447892584555995669066391:ℚ)/4915742959375000000000000000000000000000000000000000000),((-11796208874826273954014949:ℚ)/36966400000000000000000000)⟩
theorem valid3 : Valid source18 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source18 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3294374999:ℚ)/5000000000),((6784142217:ℚ)/10000000000),((10907124997:ℚ)/11820000000),(1:ℚ),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((130441273:ℚ)/250000000),((-58875281873720102396707357813440149165843724414027133:ℚ)/430052231250000000000000000000000000000000000000000000),((-11691947257253944349264949:ℚ)/36966400000000000000000000)⟩
theorem valid4 : Valid source18 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3353749999:ℚ)/5000000000),((3451472681:ℚ)/5000000000),((11085249997:ℚ)/12010000000),(1:ℚ),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((195801933:ℚ)/400000000),((-555422266619925396780290952624742056845662432838935157:ℚ)/4060133439843750000000000000000000000000000000000000000),((-11587792649985813410514949:ℚ)/36966400000000000000000000)⟩
theorem valid5 : Valid source18 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source18 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((3413124999:ℚ)/5000000000),((1740586577:ℚ)/2500000000),((11263374997:ℚ)/12105000000),(1:ℚ),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((910319607:ℚ)/2000000000),((-582478666586750202736405355717804539090625261999062757:ℚ)/4157245447558593750000000000000000000000000000000000000),((-11538771756336783665764949:ℚ)/36966400000000000000000000)⟩
theorem valid6 : Valid source18 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((15:ℚ)/16),(1:ℚ),((3442812499:ℚ)/5000000000),((140434937:ℚ)/200000000),((11352437497:ℚ)/12200000000),(1:ℚ),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((273157663:ℚ)/625000000),((-2383918448286642495548984070729052839203630621973981617:ℚ)/17023575000000000000000000000000000000000000000000000000),((-11486787634187998973139949:ℚ)/36966400000000000000000000)⟩
theorem valid7 : Valid source18 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source18 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source18 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((61:ℚ)/80),((2459:ℚ)/3200),((15:ℚ)/16),(1:ℚ),((6944999997:ℚ)/10000000000),((1770286749:ℚ)/2500000000),((22882999991:ℚ)/24590000000),(1:ℚ),((2352332153:ℚ)/2500000000),((4711495903:ℚ)/5000000000),((5397209:ℚ)/15625000),((522767361:ℚ)/1250000000),((-406467512613837923255036670049737748545668271049007477:ℚ)/2904060269335937500000000000000000000000000000000000000),((-45739320917445439266134541:ℚ)/147865600000000000000000000)⟩
theorem valid8 : Valid source18 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((2459:ℚ)/3200) :=
  cell_of_packet source18 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2459:ℚ)/3200),((1239:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3502187499:ℚ)/5000000000),((7140546757:ℚ)/10000000000),((11530562497:ℚ)/12390000000),(1:ℚ),((9396330203:ℚ)/10000000000),((9409328617:ℚ)/10000000000),((3492400691:ℚ)/10000000000),((797081411:ℚ)/2000000000),((-831527809288169766206837766613677022730330727879293051:ℚ)/5943796621875000000000000000000000000000000000000000000),((-11382899531822546587389949:ℚ)/36966400000000000000000000)⟩
theorem valid9 : Valid source18 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source18 nn0 nn1 Qcell ((2459:ℚ)/3200) ((1239:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((15:ℚ)/16),(1:ℚ),((3531874999:ℚ)/5000000000),((7259345157:ℚ)/10000000000),((11619624997:ℚ)/12580000000),(1:ℚ),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((472377477:ℚ)/1250000000),((-637264509654215292294243719965118193634474654189322933:ℚ)/4666091043750000000000000000000000000000000000000000000),((-11275970171144845934264949:ℚ)/36966400000000000000000000)⟩
theorem valid10 : Valid source18 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source18 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source18 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((629:ℚ)/800),((1277:ℚ)/1600),((15:ℚ)/16),(1:ℚ),((3591249999:ℚ)/5000000000),((1475628423:ℚ)/2000000000),((11797749997:ℚ)/12770000000),(1:ℚ),((2337671911:ℚ)/2500000000),((9372267491:ℚ)/10000000000),((181171659:ℚ)/500000000),((832501297:ℚ)/2500000000),((-55528338327348097271316720942823454974067666082719519:ℚ)/406726744726562500000000000000000000000000000000000000),((-11172242903832739867514949:ℚ)/36966400000000000000000000)⟩
theorem valid11 : Valid source18 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source18 nn0 nn1 Qcell ((629:ℚ)/800) ((1277:ℚ)/1600) :=
  cell_of_packet source18 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1277:ℚ)/1600),((81:ℚ)/100),((15:ℚ)/16),(1:ℚ),((7301249997:ℚ)/10000000000),((1499387539:ℚ)/2000000000),((23951749991:ℚ)/25920000000),(1:ℚ),((9331481479:ℚ)/10000000000),((9350687649:ℚ)/10000000000),((735446993:ℚ)/2000000000),((2813164797:ℚ)/10000000000),((-2475885616267243136681486420618394312269688410060411191:ℚ)/18139852800000000000000000000000000000000000000000000000),((-44274489260521694502634541:ℚ)/147865600000000000000000000)⟩
theorem valid12 : Valid source18 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source18 nn0 nn1 Qcell ((1277:ℚ)/1600) ((81:ℚ)/100) :=
  cell_of_packet source18 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),((343:ℚ)/400),((15:ℚ)/16),(1:ℚ),((3709999999:ℚ)/5000000000),((3986053693:ℚ)/5000000000),((12153999997:ℚ)/13720000000),(1:ℚ),((57977633:ℚ)/62500000),((2332870371:ℚ)/2500000000),((1913736159:ℚ)/5000000000),((1090373701:ℚ)/5000000000),((-37715989393835572429516819601986390424848408226271:ℚ)/315262554687500000000000000000000000000000000000000),((-10979681935189078420014949:ℚ)/36966400000000000000000000)⟩
theorem valid13 : Valid source18 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source18 nn0 nn1 Qcell ((81:ℚ)/100) ((343:ℚ)/400) :=
  cell_of_packet source18 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((343:ℚ)/400),((181:ℚ)/200),((15:ℚ)/16),(1:ℚ),((3947499999:ℚ)/5000000000),((1055907407:ℚ)/1250000000),((12866499997:ℚ)/14480000000),(1:ℚ),((9252071821:ℚ)/10000000000),((1855284257:ℚ)/2000000000),((1946075537:ℚ)/5000000000),(0:ℚ),((-1144843271109161741524217527819031611063839545015682199:ℚ)/9487585600000000000000000000000000000000000000000000000),((-76106551:ℚ)/256000000)⟩
theorem valid14 : Valid source18 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source18 nn0 nn1 Qcell ((343:ℚ)/400) ((181:ℚ)/200) :=
  cell_of_packet source18 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((15:ℚ)/16),(1:ℚ),((4184999999:ℚ)/5000000000),((1879503939:ℚ)/2000000000),((13578999997:ℚ)/16000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-334097475282750543839620912575125069666195759660892639:ℚ)/3200000000000000000000000000000000000000000000000000000),((-76106551:ℚ)/256000000)⟩
theorem valid15 : Valid source18 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source18 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source18 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((15:ℚ)/16),(1:ℚ),((4659999999:ℚ)/5000000000),((412443837:ℚ)/312500000),((15003999997:ℚ)/22080000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-56717180030078533946376758211677917:ℚ)/1345572864000000000000000000000000000),((-76106551:ℚ)/256000000)⟩
theorem valid16 : Valid source18 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source18 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source18 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source18 nn0 nn1 Qcell ((553:ℚ)/800) ((1163:ℚ)/1600) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((1163:ℚ)/1600) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source18 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source18 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((61:ℚ)/80) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source18 nn0 nn1 Qcell ((1239:ℚ)/1600) ((1277:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((1277:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source18 nn0 nn1 Qcell ((1277:ℚ)/1600) ((343:ℚ)/400) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source18 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source18 nn0 nn1 Qcell ((343:ℚ)/400) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source18 nn0 nn1 Qcell ((1277:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source18 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source18 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source18 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source18GroupedC32
#check @N11Formalization.C450Source18GroupedC32.bound
#print axioms N11Formalization.C450Source18GroupedC32.valid0
#print axioms N11Formalization.C450Source18GroupedC32.valid1
#print axioms N11Formalization.C450Source18GroupedC32.valid2
#print axioms N11Formalization.C450Source18GroupedC32.valid3
#print axioms N11Formalization.C450Source18GroupedC32.valid4
#print axioms N11Formalization.C450Source18GroupedC32.valid5
#print axioms N11Formalization.C450Source18GroupedC32.valid6
#print axioms N11Formalization.C450Source18GroupedC32.valid7
#print axioms N11Formalization.C450Source18GroupedC32.valid8
#print axioms N11Formalization.C450Source18GroupedC32.valid9
#print axioms N11Formalization.C450Source18GroupedC32.valid10
#print axioms N11Formalization.C450Source18GroupedC32.valid11
#print axioms N11Formalization.C450Source18GroupedC32.valid12
#print axioms N11Formalization.C450Source18GroupedC32.valid13
#print axioms N11Formalization.C450Source18GroupedC32.valid14
#print axioms N11Formalization.C450Source18GroupedC32.valid15
#print axioms N11Formalization.C450Source18GroupedC32.valid16
#print axioms N11Formalization.C450Source18GroupedC32.bound
#print axioms N11Formalization.C450Source18GroupedC32.endpoint_checks
