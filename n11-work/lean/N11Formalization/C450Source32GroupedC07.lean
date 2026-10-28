import N11Formalization.C450Source32Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source32GroupedC07
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source32Data
def Qcell : RatInterval := ⟨((-5:ℚ)/8),((-9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((1011:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((3397550039:ℚ)/5000000000),((3509583703:ℚ)/5000000000),((-2549583703:ℚ)/4960000000),((-20657950351:ℚ)/50550000000),((9929701407:ℚ)/10000000000),(1:ℚ),((18538009:ℚ)/156250000),((4643963003:ℚ)/10000000000),((4024183361674310037686363291:ℚ)/13202396250000000000000000000),((16244445509847444738502133:ℚ)/46208000000000000000000000)⟩
theorem valid0 : Valid source32 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((1011:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((1011:ℚ)/1600),((2041:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((1383074141:ℚ)/2000000000),((7079244883:ℚ)/10000000000),((-5159244883:ℚ)/10110000000),((-8479667269:ℚ)/20410000000),((247409071:ℚ)/250000000),((2482425353:ℚ)/2500000000),((1440948769:ℚ)/10000000000),((133659979:ℚ)/312500000),((52959575702877872163913437760758719143:ℚ)/175479312125000000000000000000000000000),((2559572584103683013382413:ℚ)/7393280000000000000000000)⟩
theorem valid1 : Valid source32 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source32 nn0 nn1 Qcell ((1011:ℚ)/1600) ((2041:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((2041:ℚ)/3200),((103:ℚ)/160),((-5:ℚ)/8),((-9:ℚ)/16),((1395096877:ℚ)/2000000000),((892413647:ℚ)/1250000000),((-652413647:ℚ)/1275625000),((-8587871893:ℚ)/20600000000),((9864186891:ℚ)/10000000000),((1979272569:ℚ)/2000000000),((1649979683:ℚ)/10000000000),((2041125209:ℚ)/5000000000),((783949783115359705537725452237334783629:ℚ)/2598356280000000000000000000000000000000),((2539604683805614691302317:ℚ)/7393280000000000000000000)⟩
theorem valid2 : Valid source32 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source32 nn0 nn1 Qcell ((2041:ℚ)/3200) ((103:ℚ)/160) :=
  cell_of_packet source32 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((103:ℚ)/160),((2079:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((1758896047:ℚ)/2500000000),((7199360653:ℚ)/10000000000),((-5279360653:ℚ)/10300000000),((-10870064423:ℚ)/25987500000),((4916570841:ℚ)/5000000000),((616511681:ℚ)/625000000),((1829340989:ℚ)/10000000000),((3878224081:ℚ)/10000000000),((2185617219002081121844907851596039067:ℚ)/7245944384765625000000000000000000000),((3936725569292965216665157:ℚ)/11552000000000000000000000)⟩
theorem valid3 : Valid source32 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((2079:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2079:ℚ)/3200),((1049:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((1419134101:ℚ)/2000000000),((7259399671:ℚ)/10000000000),((-5339399671:ℚ)/10395000000),((-8804206909:ℚ)/20980000000),((4901598247:ℚ)/5000000000),((9833141687:ℚ)/10000000000),((1987221391:ℚ)/10000000000),((1831752411:ℚ)/5000000000),((459939578282163343896403352847050758093:ℚ)/1525155786000000000000000000000000000000),((2499271588531394105187773:ℚ)/7393280000000000000000000)⟩
theorem valid4 : Valid source32 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source32 nn0 nn1 Qcell ((2079:ℚ)/3200) ((1049:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((1049:ℚ)/1600),((2117:ℚ)/3200),((-5:ℚ)/8),((-9:ℚ)/16),((715574371:ℚ)/1000000000),((7319426573:ℚ)/10000000000),((-5399426573:ℚ)/10490000000),((-4456169339:ℚ)/10585000000),((9774321709:ℚ)/10000000000),((9803196499:ℚ)/10000000000),((425706267:ℚ)/2000000000),((171804127:ℚ)/500000000),((2427256386948473793515325017709719541:ℚ)/8050157125000000000000000000000000000),((1716694128362896558213:ℚ)/5120000000000000000000)⟩
theorem valid5 : Valid source32 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source32 nn0 nn1 Qcell ((1049:ℚ)/1600) ((2117:ℚ)/3200) :=
  cell_of_packet source32 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2117:ℚ)/3200),((267:ℚ)/400),((-5:ℚ)/8),((-9:ℚ)/16),((1803951041:ℚ)/2500000000),((737944169:ℚ)/1000000000),((-18825661:ℚ)/36500000),((-11275559369:ℚ)/26700000000),((4873244381:ℚ)/5000000000),((4887160857:ℚ)/5000000000),((2256500263:ℚ)/10000000000),((399154729:ℚ)/1250000000),((13074249754476074821094072382647272781:ℚ)/43367475000000000000000000000000000000),((3841263326316690836155813:ℚ)/11552000000000000000000000)⟩
theorem valid6 : Valid source32 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source32 nn0 nn1 Qcell ((2117:ℚ)/3200) ((267:ℚ)/400) :=
  cell_of_packet source32 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((267:ℚ)/400),((431:ℚ)/640),((-5:ℚ)/8),((-9:ℚ)/16),((1455170443:ℚ)/2000000000),((7439445339:ℚ)/10000000000),((-1839815113:ℚ)/3560000000),((-9128533987:ℚ)/21550000000),((607479381:ℚ)/625000000),((9746488767:ℚ)/10000000000),((2373392223:ℚ)/10000000000),((2931133081:ℚ)/10000000000),((186889898366343481633706880093803675003:ℚ)/619977337500000000000000000000000000000),((2437778178185141643102077:ℚ)/7393280000000000000000000)⟩
theorem valid7 : Valid source32 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((431:ℚ)/640) :=
  cell_of_packet source32 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((431:ℚ)/640),((1087:ℚ)/1600),((-5:ℚ)/8),((-9:ℚ)/16),((36679441:ℚ)/50000000),((1874859457:ℚ)/2500000000),((-1394859457:ℚ)/2693750000),((-230914969:ℚ)/543500000),((9693839119:ℚ)/10000000000),((9719670101:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((1322019619:ℚ)/5000000000),((191879781793525110869437140229517103:ℚ)/636570298750000000000000000000000000),((1510634523253392518213:ℚ)/4620800000000000000000)⟩
theorem valid8 : Valid source32 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source32 nn0 nn1 Qcell ((431:ℚ)/640) ((1087:ℚ)/1600) :=
  cell_of_packet source32 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-5:ℚ)/8),((-9:ℚ)/16),((184897811:ℚ)/250000000),((3809695249:ℚ)/5000000000),((-2849695249:ℚ)/5435000000),((-1168080299:ℚ)/2765000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((290337523:ℚ)/1250000000),((9472503967020721835109419671724058703:ℚ)/31163848406250000000000000000000000000),((37439369941046172706733:ℚ)/115520000000000000000000)⟩
theorem valid9 : Valid source32 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source32 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source32 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((-5:ℚ)/8),((-9:ℚ)/16),((7515926927:ℚ)/10000000000),((3929587133:ℚ)/5000000000),((-2969587133:ℚ)/5530000000),((-47803342343:ℚ)/114400000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((372201263:ℚ)/2500000000),((859886076065630373770101277269820705583:ℚ)/2783580800000000000000000000000000000000),((58848264393280859181366917:ℚ)/184832000000000000000000000)⟩
theorem valid10 : Valid source32 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source32 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((143:ℚ)/200),((81:ℚ)/100),((-5:ℚ)/8),((-9:ℚ)/16),((3877913993:ℚ)/5000000000),((1102119257:ℚ)/1250000000),((-862119257:ℚ)/1430000000),((-24981225937:ℚ)/64800000000),((9331481479:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((56320387742110875722185673810085950297:ℚ)/166795200000000000000000000000000000000),((20118167:ℚ)/64000000)⟩
theorem valid11 : Valid source32 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source32 nn0 nn1 Qcell ((143:ℚ)/200) ((81:ℚ)/100) :=
  cell_of_packet source32 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-5:ℚ)/8),((-9:ℚ)/16),((4357003233:ℚ)/5000000000),((2145608199:ℚ)/2000000000),((-587202733:ℚ)/864000000),((-29293029097:ℚ)/80000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((26563743864081205899005688775310856733:ℚ)/72000000000000000000000000000000000000),((20118167:ℚ)/64000000)⟩
theorem valid12 : Valid source32 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source32 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-5:ℚ)/8),((-9:ℚ)/16),((10625659523:ℚ)/10000000000),((14541009773:ℚ)/10000000000),((-12621009773:ℚ)/16000000000),((-75790935707:ℚ)/220800000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((3500625951383883030911101589:ℚ)/8125440000000000000000000000),((20118167:ℚ)/64000000)⟩
theorem valid13 : Valid source32 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source32 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source32 nn0 nn1 packet13 valid13
private theorem node1_3 :
    CellBound source32 nn0 nn1 Qcell ((1011:ℚ)/1600) ((103:ℚ)/160) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((1049:ℚ)/1600) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source32 nn0 nn1 Qcell ((1049:ℚ)/1600) ((267:ℚ)/400) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source32 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_join node0_3 node3_7
private theorem node8_10 :
    CellBound source32 nn0 nn1 Qcell ((431:ℚ)/640) ((553:ℚ)/800) :=
  cell_join leaf8 leaf9
private theorem node7_10 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_join leaf7 node8_10
private theorem node10_12 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf10 leaf11
private theorem node12_14 :
    CellBound source32 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf12 leaf13
private theorem node10_14 :
    CellBound source32 nn0 nn1 Qcell ((553:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node10_12 node12_14
private theorem node7_14 :
    CellBound source32 nn0 nn1 Qcell ((267:ℚ)/400) ((69:ℚ)/50) :=
  cell_join node7_10 node10_14
private theorem node0_14 :
    CellBound source32 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_14
theorem bound : CellBound source32 nn0 nn1 Qcell (31/50) (69/50) := node0_14
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13]
theorem packet_count : packets.length = 14 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source32GroupedC07
#check @N11Formalization.C450Source32GroupedC07.bound
#print axioms N11Formalization.C450Source32GroupedC07.valid0
#print axioms N11Formalization.C450Source32GroupedC07.valid1
#print axioms N11Formalization.C450Source32GroupedC07.valid2
#print axioms N11Formalization.C450Source32GroupedC07.valid3
#print axioms N11Formalization.C450Source32GroupedC07.valid4
#print axioms N11Formalization.C450Source32GroupedC07.valid5
#print axioms N11Formalization.C450Source32GroupedC07.valid6
#print axioms N11Formalization.C450Source32GroupedC07.valid7
#print axioms N11Formalization.C450Source32GroupedC07.valid8
#print axioms N11Formalization.C450Source32GroupedC07.valid9
#print axioms N11Formalization.C450Source32GroupedC07.valid10
#print axioms N11Formalization.C450Source32GroupedC07.valid11
#print axioms N11Formalization.C450Source32GroupedC07.valid12
#print axioms N11Formalization.C450Source32GroupedC07.valid13
#print axioms N11Formalization.C450Source32GroupedC07.bound
#print axioms N11Formalization.C450Source32GroupedC07.endpoint_checks
