import N11Formalization.C450Source29Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source29GroupedC31
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source29Data
def Qcell : RatInterval := ⟨((7:ℚ)/8),((15:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((7:ℚ)/8),((15:ℚ)/16),((321108617:ℚ)/625000000),((273561593:ℚ)/500000000),((2787760319:ℚ)/3218750000),(1:ℚ),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((1656901633:ℚ)/2000000000),((-19161932225091968642516103237235671:ℚ)/51801757812500000000000000000000000),((-3265784317929407647419943:ℚ)/7220000000000000000000000)⟩
theorem valid0 : Valid source29 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source29 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((7:ℚ)/8),((15:ℚ)/16),((1343922777:ℚ)/2500000000),((5709490967:ℚ)/10000000000),((3855819813:ℚ)/4450000000),(1:ℚ),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((785085579:ℚ)/1000000000),((-18357707840465035047841759004927369:ℚ)/49506250000000000000000000000000000),((-154014114682805336296029269:ℚ)/346560000000000000000000000)⟩
theorem valid1 : Valid source29 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source29 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source29 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((2806806003:ℚ)/5000000000),((5828600527:ℚ)/10000000000),((23967642021:ℚ)/27175000000),((21069801581:ℚ)/21360000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((7397558583:ℚ)/10000000000),((-83005054114088169927655892661222233060495527387708505832078923:ℚ)/215905698640771200000000000000000000000000000000000000000000000),((-610833644382814552253146349:ℚ)/1386240000000000000000000000)⟩
theorem valid2 : Valid source29 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((5732561391:ℚ)/10000000000),((2973848839:ℚ)/5000000000),((48767929737:ℚ)/55300000000),((10713546517:ℚ)/10870000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((7162328443:ℚ)/10000000000),((-25299071029335846635939635702606028065603200740137387620253:ℚ)/65753994995579296875000000000000000000000000000000000000000),((-2421468824211642263754255941:ℚ)/5544960000000000000000000000)⟩
theorem valid3 : Valid source29 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((7:ℚ)/8),((15:ℚ)/16),((585150391:ℚ)/1000000000),((3033391527:ℚ)/5000000000),((4960052737:ℚ)/5625000000),((10892174581:ℚ)/11060000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((6920574739:ℚ)/10000000000),((-12557643435973792153263995091435702451642905467706242501:ℚ)/32614529850000000000000000000000000000000000000000000000),((-420987215281034593707613:ℚ)/972800000000000000000000)⟩
theorem valid4 : Valid source29 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source29 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source29 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((597043991:ℚ)/1000000000),((765790189:ℚ)/1250000000),((5043307937:ℚ)/5672500000),((2745370567:ℚ)/2812500000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((6671566129:ℚ)/10000000000),((-280413541557095145171889064931588649145066207103009301704803:ℚ)/715857538032531738281250000000000000000000000000000000000000),((-7964203027175074665947047:ℚ)/18483200000000000000000000)⟩
theorem valid5 : Valid source29 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((188434549:ℚ)/312500000),((1546464311:ℚ)/2500000000),((1589041843:ℚ)/1787500000),((5535392933:ℚ)/5672500000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((3272038227:ℚ)/5000000000),((-365563583708204126366857600128191422950478695215214171513:ℚ)/933115916202894531250000000000000000000000000000000000000),((-774205880303654604279887:ℚ)/1805000000000000000000000)⟩
theorem valid6 : Valid source29 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source29 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((3044684859:ℚ)/5000000000),((3122695159:ℚ)/5000000000),((8544264671:ℚ)/9612500000),((11160085477:ℚ)/11440000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((801804403:ℚ)/1250000000),((-1626113992536330973479678253012923254358179756798230411604371:ℚ)/4150228741744800000000000000000000000000000000000000000000000),((-591866494798258686532950941:ℚ)/1386240000000000000000000000)⟩
theorem valid7 : Valid source29 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((1229766479:ℚ)/2000000000),((6304920799:ℚ)/10000000000),((10336365353:ℚ)/11630000000),((22498762397:ℚ)/23070000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((196328327:ℚ)/312500000),((-542310956870494749706754725890796106992276393094511531748811:ℚ)/1383951806726672250000000000000000000000000000000000000000000),((-31421032536899564186481367:ℚ)/73932800000000000000000000)⟩
theorem valid8 : Valid source29 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source29 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((7:ℚ)/8),((15:ℚ)/16),((6208293637:ℚ)/10000000000),((397778047:ℚ)/625000000),((52098055459:ℚ)/58625000000),((1417334141:ℚ)/1453750000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((1229628019:ℚ)/2000000000),((-1241449351184978805393482572808092264399050192881086756163:ℚ)/3167788292247317504882812500000000000000000000000000000000),((-781898278324026902530391903:ℚ)/1848320000000000000000000000)⟩
theorem valid9 : Valid source29 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source29 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source29 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((6267753479:ℚ)/10000000000),((1605993559:ℚ)/2500000000),((52514274353:ℚ)/59100000000),((5713980677:ℚ)/5862500000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1202233963:ℚ)/2000000000),((-43098185318356176259698480487991757738240693117263338181993:ℚ)/109962234134609985351562500000000000000000000000000000000000),((-778272717300613952829983367:ℚ)/1848320000000000000000000000)⟩
theorem valid10 : Valid source29 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source29 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((3163605977:ℚ)/5000000000),((6483497311:ℚ)/10000000000),((26465241839:ℚ)/29787500000),((23034491933:ℚ)/23640000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((1174282103:ℚ)/2000000000),((-551374959696837902820803132180001130691580684215807786604607571:ℚ)/1406668536014302800000000000000000000000000000000000000000000000),((-193662281621057650559630023:ℚ)/462080000000000000000000000)⟩
theorem valid11 : Valid source29 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source29 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((1277333819:ℚ)/2000000000),((1308603607:ℚ)/2000000000),((10669336733:ℚ)/12010000000),((4642610821:ℚ)/4766000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((5728655159:ℚ)/10000000000),((-23911160642265285360904445588027253964491012893343355060569:ℚ)/60996956149139646875000000000000000000000000000000000000000),((-30841100085565295363018207:ℚ)/73932800000000000000000000)⟩
theorem valid12 : Valid source29 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source29 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((1201:ℚ)/1600),((2421:ℚ)/3200),((7:ℚ)/8),((15:ℚ)/16),((3223062467:ℚ)/5000000000),((412658529:ℚ)/625000000),((26881437269:ℚ)/30262500000),((1461975587:ℚ)/1501250000),((4718667711:ℚ)/5000000000),((9452375627:ℚ)/10000000000),((674104879:ℚ)/2000000000),((5582670957:ℚ)/10000000000),((-16197002059984732462239517361475803762714417708152148807629:ℚ)/41314966290075036621093750000000000000000000000000000000000),((-191851960164632765399205743:ℚ)/462080000000000000000000000)⟩
theorem valid13 : Valid source29 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source29 nn0 nn1 Qcell ((1201:ℚ)/1600) ((2421:ℚ)/3200) :=
  cell_of_packet source29 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((2421:ℚ)/3200),((61:ℚ)/80),((7:ℚ)/8),((15:ℚ)/16),((6505579501:ℚ)/10000000000),((6662052651:ℚ)/10000000000),((54179056507:ℚ)/61000000000),((23570157953:ℚ)/24210000000),((9422991801:ℚ)/10000000000),((9437335427:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((5433194649:ℚ)/10000000000),((-129384919347114814855707318623557702238672219293732989919973:ℚ)/330007686621131250000000000000000000000000000000000000000000),((-763790138625207777515507087:ℚ)/1848320000000000000000000000)⟩
theorem valid14 : Valid source29 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source29 nn0 nn1 Qcell ((2421:ℚ)/3200) ((61:ℚ)/80) :=
  cell_of_packet source29 nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((7:ℚ)/8),((15:ℚ)/16),((6565032827:ℚ)/10000000000),((6781078507:ℚ)/10000000000),((54595229789:ℚ)/61950000000),((23927235521:ℚ)/24400000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((5279926603:ℚ)/10000000000),((-13460483579596458598325215537761926879320848762347959948124069:ℚ)/34844329970100000000000000000000000000000000000000000000000000),((-756358744719536207458633823:ℚ)/1848320000000000000000000000)⟩
theorem valid15 : Valid source29 packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source29 nn0 nn1 packet15 valid15
def packet16 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((7:ℚ)/8),((15:ℚ)/16),((6683935869:ℚ)/10000000000),((6900096003:ℚ)/10000000000),((55427551083:ℚ)/62900000000),((24284288009:ℚ)/24780000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((992117631:ℚ)/2000000000),((-14200123575167702168472106261507983928080629096454359610869:ℚ)/36743900613675732421875000000000000000000000000000000000000),((-2247400118816298404693219021:ℚ)/5544960000000000000000000000)⟩
theorem valid16 : Valid source29 packet16 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf16 :
    CellBound source29 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source29 nn0 nn1 packet16 valid16
def packet17 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((7:ℚ)/8),((15:ℚ)/16),((6802834279:ℚ)/10000000000),((1784526847:ℚ)/2500000000),((56259839953:ℚ)/64800000000),((6249580541:ℚ)/6290000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((4621189709:ℚ)/10000000000),((-3832870024415867154207606049824607176065299414413453883121:ℚ)/10204741112681250000000000000000000000000000000000000000000),((-734285880279841040317220167:ℚ)/1848320000000000000000000000)⟩
theorem valid17 : Valid source29 packet17 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf17 :
    CellBound source29 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source29 nn0 nn1 packet17 valid17
def packet18 : Packet := ⟨((81:ℚ)/100),((181:ℚ)/200),((7:ℚ)/8),((15:ℚ)/16),((7040618021:ℚ)/10000000000),((8089883787:ℚ)/10000000000),((57924326147:ℚ)/72400000000),(1:ℚ),((9252071821:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((1946075537:ℚ)/5000000000),((3860672009:ℚ)/10000000000),((-26159892320807879931024012028975184507:ℚ)/78626400000000000000000000000000000000),((-705518648001221009263694367:ℚ)/1848320000000000000000000000)⟩
theorem valid18 : Valid source29 packet18 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf18 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((181:ℚ)/200) :=
  cell_of_packet source29 nn0 nn1 packet18 valid18
def packet19 : Packet := ⟨((181:ℚ)/200),(1:ℚ),((7:ℚ)/8),((15:ℚ)/16),((3995801919:ℚ)/5000000000),((4520660949:ℚ)/5000000000),((32290613433:ℚ)/40000000000),(1:ℚ),((9249864861:ℚ)/10000000000),((4639000001:ℚ)/5000000000),((155918519:ℚ)/400000000),(0:ℚ),((-2699450248923980093110360286452831009:ℚ)/8000000000000000000000000000000000000),((-49004629:ℚ)/128000000)⟩
theorem valid19 : Valid source29 packet19 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf19 :
    CellBound source29 nn0 nn1 Qcell ((181:ℚ)/200) (1:ℚ) :=
  cell_of_packet source29 nn0 nn1 packet19 valid19
def packet20 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((7:ℚ)/8),((15:ℚ)/16),((8942402111:ℚ)/10000000000),((6422545777:ℚ)/5000000000),((71236814777:ℚ)/110400000000),(1:ℚ),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-1440951252551115911276602709:ℚ)/6094080000000000000000000000),((-49004629:ℚ)/128000000)⟩
theorem valid20 : Valid source29 packet20 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf20 :
    CellBound source29 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source29 nn0 nn1 packet20 valid20
private theorem node0_2 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join leaf0 leaf1
private theorem node3_5 :
    CellBound source29 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join leaf3 leaf4
private theorem node2_5 :
    CellBound source29 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf2 node3_5
private theorem node0_5 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_2 node2_5
private theorem node5_7 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf5 leaf6
private theorem node8_10 :
    CellBound source29 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source29 nn0 nn1 Qcell ((143:ℚ)/200) ((469:ℚ)/640) :=
  cell_join leaf7 node8_10
private theorem node5_10 :
    CellBound source29 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node5_7 node7_10
private theorem node0_10 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_5 node5_10
private theorem node10_12 :
    CellBound source29 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf10 leaf11
private theorem node13_15 :
    CellBound source29 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf13 leaf14
private theorem node12_15 :
    CellBound source29 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf12 node13_15
private theorem node10_15 :
    CellBound source29 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node10_12 node12_15
private theorem node16_18 :
    CellBound source29 nn0 nn1 Qcell ((1239:ℚ)/1600) ((81:ℚ)/100) :=
  cell_join leaf16 leaf17
private theorem node15_18 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf15 node16_18
private theorem node19_21 :
    CellBound source29 nn0 nn1 Qcell ((181:ℚ)/200) ((69:ℚ)/50) :=
  cell_join leaf19 leaf20
private theorem node18_21 :
    CellBound source29 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf18 node19_21
private theorem node15_21 :
    CellBound source29 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node15_18 node18_21
private theorem node10_21 :
    CellBound source29 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node10_15 node15_21
private theorem node0_21 :
    CellBound source29 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_10 node10_21
theorem bound : CellBound source29 nn0 nn1 Qcell (31/50) (69/50) := node0_21
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15,packet16,packet17,packet18,packet19,packet20]
theorem packet_count : packets.length = 21 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source29GroupedC31
#check @N11Formalization.C450Source29GroupedC31.bound
#print axioms N11Formalization.C450Source29GroupedC31.valid0
#print axioms N11Formalization.C450Source29GroupedC31.valid1
#print axioms N11Formalization.C450Source29GroupedC31.valid2
#print axioms N11Formalization.C450Source29GroupedC31.valid3
#print axioms N11Formalization.C450Source29GroupedC31.valid4
#print axioms N11Formalization.C450Source29GroupedC31.valid5
#print axioms N11Formalization.C450Source29GroupedC31.valid6
#print axioms N11Formalization.C450Source29GroupedC31.valid7
#print axioms N11Formalization.C450Source29GroupedC31.valid8
#print axioms N11Formalization.C450Source29GroupedC31.valid9
#print axioms N11Formalization.C450Source29GroupedC31.valid10
#print axioms N11Formalization.C450Source29GroupedC31.valid11
#print axioms N11Formalization.C450Source29GroupedC31.valid12
#print axioms N11Formalization.C450Source29GroupedC31.valid13
#print axioms N11Formalization.C450Source29GroupedC31.valid14
#print axioms N11Formalization.C450Source29GroupedC31.valid15
#print axioms N11Formalization.C450Source29GroupedC31.valid16
#print axioms N11Formalization.C450Source29GroupedC31.valid17
#print axioms N11Formalization.C450Source29GroupedC31.valid18
#print axioms N11Formalization.C450Source29GroupedC31.valid19
#print axioms N11Formalization.C450Source29GroupedC31.valid20
#print axioms N11Formalization.C450Source29GroupedC31.bound
#print axioms N11Formalization.C450Source29GroupedC31.endpoint_checks
