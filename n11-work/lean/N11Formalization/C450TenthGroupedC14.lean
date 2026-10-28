import N11Formalization.C450TenthData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450TenthGroupedC14
open C450GroupedPacketKernel C450GroupedClosedAssembly C450TenthData
def Qcell : RatInterval := ⟨((-3:ℚ)/16),((-1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((-3:ℚ)/16),((-1:ℚ)/8),((6231865629:ℚ)/10000000000),((105205107:ℚ)/156250000),((-235615321:ℚ)/1550000000),((-1117288543:ℚ)/17800000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6094161977:ℚ)/10000000000),((6333573138924607333489929336770034823250774329113251667:ℚ)/273175487500000000000000000000000000000000000000000000000),((81801068321652278534931:ℚ)/7220000000000000000000000)⟩
theorem valid0 : Valid tenth packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet tenth nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((167686129:ℚ)/250000000),((6852040909:ℚ)/10000000000),((-15436122727:ℚ)/106800000000),((-95686129:ℚ)/1358750000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4895201783:ℚ)/10000000000),((1048981493931517196711152886739652982114291385570017:ℚ)/47034869494628906250000000000000000000000000000000000),((123734574051016802513099657:ℚ)/14786560000000000000000000000)⟩
theorem valid1 : Valid tenth packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound tenth nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((6826327359:ℚ)/10000000000),((6970949321:ℚ)/10000000000),((-15792847963:ℚ)/108700000000),((-3946327359:ℚ)/55300000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((4551366479:ℚ)/10000000000),((56994232366170164860944739004537393297031923022965190341:ℚ)/2564525025097656250000000000000000000000000000000000000000),((113231719657548482982115377:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid tenth packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((6945205009:ℚ)/10000000000),((14060803:ℚ)/20000000),((-31942409:ℚ)/221200000),((-4065205009:ℚ)/55775000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((2090737317:ℚ)/5000000000),((118207096580058714448606438301796327232069314215483500069:ℚ)/5354338982476806640625000000000000000000000000000000000000),((409753823129833117673:ℚ)/59146240000000000000000)⟩
theorem valid3 : Valid tenth packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound tenth nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/16),((-1:ℚ)/8),((35023211:ℚ)/50000000),((7089852373:ℚ)/10000000000),((-16149557119:ℚ)/111550000000),((-20623211:ℚ)/281250000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((15564457:ℚ)/39062500),((80136027490207813386664572400213611118319191624573:ℚ)/3635285049676895141601562500000000000000000000000000),((97193712313126849808553113:ℚ)/14786560000000000000000000000)⟩
theorem valid4 : Valid tenth packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet tenth nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((353203917:ℚ)/500000000),((1787325493:ℚ)/2500000000),((-4081976479:ℚ)/28125000000),((-209203917:ℚ)/2836250000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((1888924371:ℚ)/5000000000),((70625878045887410209251740551258538359001530502903:ℚ)/3208455809967041015625000000000000000000000000000000),((5746974657698353174987353:ℚ)/924160000000000000000000000)⟩
theorem valid5 : Valid tenth packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound tenth nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-3:ℚ)/16),((-1:ℚ)/8),((3561756727:ℚ)/5000000000),((7208750331:ℚ)/10000000000),((-16506250993:ℚ)/113450000000),((-2121756727:ℚ)/28600000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((711965729:ℚ)/2000000000),((7292644055027632850209053963002997838887408894495063223377:ℚ)/331751284150000000000000000000000000000000000000000000000000),((86712100092836094849789817:ℚ)/14786560000000000000000000000)⟩
theorem valid6 : Valid tenth packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet tenth nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((-3:ℚ)/16),((-1:ℚ)/8),((448934223:ℚ)/625000000),((3634098739:ℚ)/5000000000),((-8342296217:ℚ)/57200000000),((-89644741:ℚ)/1201562500),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3328203117:ℚ)/10000000000),((362615424908961485562717721426429050360054985891:ℚ)/16517478740774095058441162109375000000000000000000),((20368806645895247154208137:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid tenth packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound tenth nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet tenth nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((7242380707:ℚ)/10000000000),((1465528689:ℚ)/2000000000),((-3372586067:ℚ)/23070000000),((-4362380707:ℚ)/58150000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((615979893:ℚ)/2000000000),((62163332267320983232896168832657189168901476145715268718179:ℚ)/2835154751819531250000000000000000000000000000000000000000000),((3049638867038839493302337:ℚ)/591462400000000000000000000)⟩
theorem valid8 : Valid tenth packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((-3:ℚ)/16),((-1:ℚ)/8),((1460362579:ℚ)/2000000000),((369354413:ℚ)/500000000),((-852063239:ℚ)/5815000000),((-884362579:ℚ)/11725000000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((175655981:ℚ)/625000000),((109965968237099991426813582254306436551788292142430380887:ℚ)/5021361644824218750000000000000000000000000000000000000000),((177523332820362005262793:ℚ)/36966400000000000000000000)⟩
theorem valid9 : Valid tenth packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound tenth nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet tenth nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((-3:ℚ)/16),((-1:ℚ)/8),((1472248831:ℚ)/2000000000),((7446531951:ℚ)/10000000000),((-17219595853:ℚ)/117250000000),((-896248831:ℚ)/11820000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((314151243:ℚ)/1250000000),((1260566575614695595982416114990381619317161340428522869:ℚ)/57626998987500000000000000000000000000000000000000000000),((65780308796320992313159297:ℚ)/14786560000000000000000000000)⟩
theorem valid10 : Valid tenth packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet tenth nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((-3:ℚ)/16),((-1:ℚ)/8),((7420674509:ℚ)/10000000000),((7565416067:ℚ)/10000000000),((-17576248201:ℚ)/118200000000),((-4540674509:ℚ)/60050000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((544160347:ℚ)/2500000000),((1461048996252256218933225603031067945575309026612106669643:ℚ)/66653857304101562500000000000000000000000000000000000000000),((3203950633947895935161107:ℚ)/778240000000000000000000000)⟩
theorem valid11 : Valid tenth packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound tenth nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet tenth nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((-3:ℚ)/16),((-1:ℚ)/8),((7539532587:ℚ)/10000000000),((7684295999:ℚ)/10000000000),((-17932887997:ℚ)/120100000000),((-4659532587:ℚ)/61000000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1262284541:ℚ)/10000000000),((37268906881635425318855170307345557120499829338893340742273:ℚ)/1703776131250000000000000000000000000000000000000000000000000),((3287712627208701:ℚ)/972800000000000000)⟩
theorem valid12 : Valid tenth packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet tenth nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/16),((-1:ℚ)/8),((3829193647:ℚ)/5000000000),((8159777571:ℚ)/10000000000),((-19359332713:ℚ)/122000000000),((-2389193647:ℚ)/32400000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((96053044364157231323547235312883886308088639024014255131:ℚ)/4322386800000000000000000000000000000000000000000000000000),((3070043:ℚ)/1024000000)⟩
theorem valid13 : Valid tenth packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound tenth nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet tenth nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/16),((-1:ℚ)/8),((1016721923:ℚ)/1250000000),((10061245859:ℚ)/10000000000),((-25063737577:ℚ)/129600000000),((-656721923:ℚ)/10000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((11854872120590942335001888623828981741444348085312882897:ℚ)/506250000000000000000000000000000000000000000000000000000),((3070043:ℚ)/1024000000)⟩
theorem valid14 : Valid tenth packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet tenth nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/16),((-1:ℚ)/8),((10034958727:ℚ)/10000000000),((866435543:ℚ)/625000000),((-2279306629:ℚ)/10000000000),((-7154958727:ℚ)/110400000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((163224619074720075645479397739640660843100708772477001959:ℚ)/6307372800000000000000000000000000000000000000000000000000),((3070043:ℚ)/1024000000)⟩
theorem valid15 : Valid tenth packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound tenth nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet tenth nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound tenth nn0 nn1 Qcell ((1087:ℚ)/1600) ((2231:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((2231:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((2269:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound tenth nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound tenth nn0 nn1 Qcell ((2231:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((2307:ℚ)/3200) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound tenth nn0 nn1 Qcell ((469:ℚ)/640) ((1201:ℚ)/1600) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound tenth nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound tenth nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound tenth nn0 nn1 Qcell ((2307:ℚ)/3200) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound tenth nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound tenth nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450TenthGroupedC14
#check @N11Formalization.C450TenthGroupedC14.bound
#print axioms N11Formalization.C450TenthGroupedC14.valid0
#print axioms N11Formalization.C450TenthGroupedC14.valid1
#print axioms N11Formalization.C450TenthGroupedC14.valid2
#print axioms N11Formalization.C450TenthGroupedC14.valid3
#print axioms N11Formalization.C450TenthGroupedC14.valid4
#print axioms N11Formalization.C450TenthGroupedC14.valid5
#print axioms N11Formalization.C450TenthGroupedC14.valid6
#print axioms N11Formalization.C450TenthGroupedC14.valid7
#print axioms N11Formalization.C450TenthGroupedC14.valid8
#print axioms N11Formalization.C450TenthGroupedC14.valid9
#print axioms N11Formalization.C450TenthGroupedC14.valid10
#print axioms N11Formalization.C450TenthGroupedC14.valid11
#print axioms N11Formalization.C450TenthGroupedC14.valid12
#print axioms N11Formalization.C450TenthGroupedC14.valid13
#print axioms N11Formalization.C450TenthGroupedC14.valid14
#print axioms N11Formalization.C450TenthGroupedC14.valid15
#print axioms N11Formalization.C450TenthGroupedC14.bound
#print axioms N11Formalization.C450TenthGroupedC14.endpoint_checks
