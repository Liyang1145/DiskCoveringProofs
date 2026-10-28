import N11Formalization.C450Source27Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source27GroupedC03
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source27Data
def Qcell : RatInterval := ⟨((-7:ℚ)/8),((-13:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((2003:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((6985032399:ℚ)/10000000000),((1787273129:ℚ)/2500000000),((-10510911903:ℚ)/12400000000),((-74165421187:ℚ)/100150000000),((398569427:ℚ)/400000000),(1:ℚ),((845998389:ℚ)/10000000000),((2025243463:ℚ)/5000000000),((24137797143117188403823488781015601583067848291408562506809:ℚ)/76493926476160000000000000000000000000000000000000000000000),((94036569233580347823436151:ℚ)/115520000000000000000000000)⟩
theorem valid0 : Valid source27 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((2003:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((2003:ℚ)/3200),((1011:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((7044669093:ℚ)/10000000000),((3604329357:ℚ)/5000000000),((-21230305499:ℚ)/25037500000),((-74940698209:ℚ)/101100000000),((9929701407:ℚ)/10000000000),((62276473:ℚ)/62500000),((18538009:ℚ)/156250000),((769298283:ℚ)/2000000000),((10547838054650544478031283832884495904846108794927571897468079:ℚ)/33422117424036730957031250000000000000000000000000000000000000),((1130882197711975239651943517:ℚ)/1386240000000000000000000000)⟩
theorem valid1 : Valid source27 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source27 nn0 nn1 Qcell ((2003:ℚ)/3200) ((1011:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1011:ℚ)/1600),((4063:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((3552150419:ℚ)/5000000000),((1447688093:ℚ)/2000000000),((-8533816651:ℚ)/10110000000),((-37857955447:ℚ)/50787500000),((4956442379:ℚ)/5000000000),((2482425353:ℚ)/2500000000),((1320924081:ℚ)/10000000000),((3631671509:ℚ)/10000000000),((54177622481691659701826999369858919240994597489541605955221:ℚ)/174211053327754687500000000000000000000000000000000000000000),((60378886513243173754343039:ℚ)/73932800000000000000000000)⟩
theorem valid2 : Valid source27 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source27 nn0 nn1 Qcell ((1011:ℚ)/1600) ((4063:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((4063:ℚ)/6400),((2041:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((7134114897:ℚ)/10000000000),((1453644267:ℚ)/2000000000),((-504441757:ℚ)/597500000),((-5854114897:ℚ)/7850000000),((247409071:ℚ)/250000000),((9912884763:ℚ)/10000000000),((1440948769:ℚ)/10000000000),((1759792759:ℚ)/5000000000),((6388291176986247423880779341422177437812100782500139:ℚ)/20538705531677246093750000000000000000000000000000000),((502305244486966629470117:ℚ)/614400000000000000000000)⟩
theorem valid3 : Valid source27 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source27 nn0 nn1 Qcell ((4063:ℚ)/6400) ((2041:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2041:ℚ)/3200),((4101:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7163927771:ℚ)/10000000000),((912250167:ℚ)/1250000000),((-5385751169:ℚ)/6378125000),((-25497020341:ℚ)/34175000000),((4940065779:ℚ)/5000000000),((1979272569:ℚ)/2000000000),((774947369:ℚ)/5000000000),((3403973649:ℚ)/10000000000),((235675012489865601222731152446708159267378257209810129383927:ℚ)/757593315943172883987426757812500000000000000000000000000000),((70909278464889147689392037:ℚ)/86640000000000000000000000)⟩
theorem valid4 : Valid source27 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source27 nn0 nn1 Qcell ((2041:ℚ)/3200) ((4101:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((4101:ℚ)/6400),((103:ℚ)/160),((-7:ℚ)/8),((-13:ℚ)/16),((1798434869:ℚ)/2500000000),((7327780479:ℚ)/10000000000),((-43294463353:ℚ)/51262500000),((-19219653297:ℚ)/25750000000),((9864186891:ℚ)/10000000000),((9880131563:ℚ)/10000000000),((1649979683:ℚ)/10000000000),((1642231489:ℚ)/5000000000),((926347931719950559114052407321920252787818370017738039522317:ℚ)/2977368291712683105468750000000000000000000000000000000000000),((4543083461004495143586568853:ℚ)/5544960000000000000000000000)⟩
theorem valid5 : Valid source27 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source27 nn0 nn1 Qcell ((4101:ℚ)/6400) ((103:ℚ)/160) :=
  cell_of_packet source27 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((103:ℚ)/160),((4139:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7223550029:ℚ)/10000000000),((3678779389:ℚ)/5000000000),((-21751455723:ℚ)/25750000000),((-77266150377:ℚ)/103475000000),((984852489:ℚ)/1000000000),((616511681:ℚ)/625000000),((1742751127:ℚ)/10000000000),((790152657:ℚ)/2500000000),((5688617784124068265979052091167886307785696243291453031992509:ℚ)/18281110353874023437500000000000000000000000000000000000000000),((378997812623390320007293631:ℚ)/462080000000000000000000000)⟩
theorem valid6 : Valid source27 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((4139:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((4139:ℚ)/6400),((2079:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((1813339861:ℚ)/2500000000),((3693668121:ℚ)/5000000000),((-21855676847:ℚ)/25868750000),((-19413418193:ℚ)/25987500000),((4916570841:ℚ)/5000000000),((1969704979:ℚ)/2000000000),((1829340989:ℚ)/10000000000),((757970981:ℚ)/2500000000),((82505329332950805171589559457390846408907712665465993914161:ℚ)/265104284364249801635742187500000000000000000000000000000000),((1138216173648171063961568453:ℚ)/1386240000000000000000000000)⟩
theorem valid7 : Valid source27 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source27 nn0 nn1 Qcell ((4139:ℚ)/6400) ((2079:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2079:ℚ)/3200),((4177:ℚ)/6400),((-7:ℚ)/8),((-13:ℚ)/16),((7283167739:ℚ)/10000000000),((1483422577:ℚ)/2000000000),((-2927986013:ℚ)/3465000000),((-78041180607:ℚ)/104425000000),((4909016731:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((382121547:ℚ)/2000000000),((362204077:ℚ)/1250000000),((3565728888876389406180605563211621211369019201262211257929:ℚ)/11455749245009179687500000000000000000000000000000000000000),((60770083900988183689758119:ℚ)/73932800000000000000000000)⟩
theorem valid8 : Valid source27 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source27 nn0 nn1 Qcell ((2079:ℚ)/3200) ((4177:ℚ)/6400) :=
  cell_of_packet source27 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((4177:ℚ)/6400),((1049:ℚ)/1600),((-7:ℚ)/8),((-13:ℚ)/16),((457060933:ℚ)/625000000),((7446888717:ℚ)/10000000000),((-44128221019:ℚ)/52212500000),((-4901792129:ℚ)/6556250000),((4901598247:ℚ)/5000000000),((9818033467:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((1378524537:ℚ)/5000000000),((76186386457378125201673196836126055172134124568989645980622757:ℚ)/244734089450337014770507812500000000000000000000000000000000000),((4562648547002812298384332637:ℚ)/5544960000000000000000000000)⟩
theorem valid9 : Valid source27 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source27 nn0 nn1 Qcell ((4177:ℚ)/6400) ((1049:ℚ)/1600) :=
  cell_of_packet source27 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-7:ℚ)/8),((-13:ℚ)/16),((3671390513:ℚ)/5000000000),((7506437991:ℚ)/10000000000),((-44545065937:ℚ)/52450000000),((-39408076669:ℚ)/52925000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((2609109173:ℚ)/10000000000),((1276205139983872866467301208959615817025148058359625762425064519:ℚ)/4041645433668875781250000000000000000000000000000000000000000000),((4572435032011796262118699973:ℚ)/5544960000000000000000000000)⟩
theorem valid10 : Valid source27 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source27 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source27 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-7:ℚ)/8),((-13:ℚ)/16),((7402390011:ℚ)/10000000000),((945748019:ℚ)/1250000000),((-5620236133:ℚ)/6615625000),((-894281687:ℚ)/1200000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((2285378757:ℚ)/10000000000),((563637565723302413734760259470756545041026508440593699:ℚ)/1784852339172363281250000000000000000000000000000000000),((23865750851976357389319071:ℚ)/28880000000000000000000000)⟩
theorem valid11 : Valid source27 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source27 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source27 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((-7:ℚ)/8),((-13:ℚ)/16),((7461994809:ℚ)/10000000000),((7804139271:ℚ)/10000000000),((-46628974897:ℚ)/53400000000),((-80365932517:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((954300821:ℚ)/5000000000),((676218546967146929178957874029992905328459076331432394832173:ℚ)/1979870188050000000000000000000000000000000000000000000000000),((105905301:ℚ)/128000000)⟩
theorem valid12 : Valid source27 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source27 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-7:ℚ)/8),((-13:ℚ)/16),((7700374307:ℚ)/10000000000),((8042250699:ℚ)/10000000000),((-48295754893:ℚ)/55300000000),((-6420374307:ℚ)/8800000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),(0:ℚ),((6220990839525470556190189557965163628532572596814021583717:ℚ)/18270176443750000000000000000000000000000000000000000000000),((105905301:ℚ)/128000000)⟩
theorem valid13 : Valid source27 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source27 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source27 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-7:ℚ)/8),((-13:ℚ)/16),((7938695073:ℚ)/10000000000),((899433671:ℚ)/1000000000),((-5496035697:ℚ)/5720000000),((-86563035949:ℚ)/129600000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((278475658340384472477610571719966920804980355703616928253:ℚ)/639524070900000000000000000000000000000000000000000000000),((105905301:ℚ)/128000000)⟩
theorem valid14 : Valid source27 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source27 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-7:ℚ)/8),((-13:ℚ)/16),((277859211:ℚ)/312500000),((68108231:ℚ)/62500000),(-1:ℚ),((-3092169743:ℚ)/5000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((15106218077073339023494758154310529:ℚ)/31250000000000000000000000000000000),((105905301:ℚ)/128000000)⟩
theorem valid15 : Valid source27 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source27 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-7:ℚ)/8),((-13:ℚ)/16),((10795493349:ℚ)/10000000000),((14700812161:ℚ)/10000000000),(-1:ℚ),((-123701413537:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((12588218824144630619287930219:ℚ)/24376320000000000000000000000),((105905301:ℚ)/128000000)⟩
theorem valid16 : Valid source27 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source27 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source27 nn0 nn1 packet16 valid16
private theorem node0_2 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound source27 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((2041:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound source27 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound source27 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound source27 nn0 nn1 Qcell ((2041:ℚ)/3200) ((2079:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((2079:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound source27 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound source27 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound source27 nn0 nn1 Qcell ((2079:ℚ)/3200) ((267:ℚ)/400) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf12 leaf13
private theorem node15_17 :
    CellBound source27 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf15 leaf16
private theorem node14_17 :
    CellBound source27 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf14 node15_17
private theorem node12_17 :
    CellBound source27 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node12_14 node14_17
private theorem node8_17 :
    CellBound source27 nn0 nn1 Qcell ((2079:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_17
private theorem node0_17 :
    CellBound source27 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_17
theorem bound : CellBound source27 nn0 nn1 Qcell (31/50) (69/50) := node0_17
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16]
theorem packet_count : packets.length = 17 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source27GroupedC03
#check @N11Formalization.C450Source27GroupedC03.bound
#print axioms N11Formalization.C450Source27GroupedC03.valid0
#print axioms N11Formalization.C450Source27GroupedC03.valid1
#print axioms N11Formalization.C450Source27GroupedC03.valid2
#print axioms N11Formalization.C450Source27GroupedC03.valid3
#print axioms N11Formalization.C450Source27GroupedC03.valid4
#print axioms N11Formalization.C450Source27GroupedC03.valid5
#print axioms N11Formalization.C450Source27GroupedC03.valid6
#print axioms N11Formalization.C450Source27GroupedC03.valid7
#print axioms N11Formalization.C450Source27GroupedC03.valid8
#print axioms N11Formalization.C450Source27GroupedC03.valid9
#print axioms N11Formalization.C450Source27GroupedC03.valid10
#print axioms N11Formalization.C450Source27GroupedC03.valid11
#print axioms N11Formalization.C450Source27GroupedC03.valid12
#print axioms N11Formalization.C450Source27GroupedC03.valid13
#print axioms N11Formalization.C450Source27GroupedC03.valid14
#print axioms N11Formalization.C450Source27GroupedC03.valid15
#print axioms N11Formalization.C450Source27GroupedC03.valid16
#print axioms N11Formalization.C450Source27GroupedC03.bound
#print axioms N11Formalization.C450Source27GroupedC03.endpoint_checks
