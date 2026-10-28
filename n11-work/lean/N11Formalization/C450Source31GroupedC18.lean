import N11Formalization.C450Source31Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source31GroupedC18
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source31Data
def Qcell : RatInterval := ⟨((1:ℚ)/16),((1:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/16),((1:ℚ)/8),((1186922347:ℚ)/2000000000),((250401599:ℚ)/400000000),((4898922347:ℚ)/20600000000),((634401599:ℚ)/1984000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((269895637:ℚ)/400000000),((-6717689368661166428773866872708824731766849045488352721:ℚ)/54636350000000000000000000000000000000000000000000000000),((-810886415004781042840227:ℚ)/2957312000000000000000000)⟩
theorem valid0 : Valid source31 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source31 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/16),((1:ℚ)/8),((6176444991:ℚ)/10000000000),((3250666537:ℚ)/5000000000),((24736444991:ℚ)/106800000000),((8050666537:ℚ)/25750000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((194388209:ℚ)/312500000),((-25050353415441924044047490455076250440906466342219914653:ℚ)/211490700000000000000000000000000000000000000000000000000),((-129983151370594938256369363:ℚ)/462080000000000000000000000)⟩
theorem valid1 : Valid source31 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source31 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((641796201:ℚ)/1000000000),((6621877891:ℚ)/10000000000),((2497796201:ℚ)/10870000000),((16221877891:ℚ)/53400000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((2826119633:ℚ)/5000000000),((-940087991199885442687208728754105019897613448825508587:ℚ)/8027284393750000000000000000000000000000000000000000000),((-28202183404803319320534073:ℚ)/97280000000000000000000000)⟩
theorem valid2 : Valid source31 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source31 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((6538612639:ℚ)/10000000000),((3371179843:ℚ)/5000000000),((25098612639:ℚ)/110600000000),((8171179843:ℚ)/27175000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((2674263023:ℚ)/5000000000),((-2172318167451663075212097175326170951816125918317685251:ℚ)/18874149218750000000000000000000000000000000000000000000),((-135563216265700271827188923:ℚ)/462080000000000000000000000)⟩
theorem valid3 : Valid source31 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/16),((1:ℚ)/8),((1664799111:ℚ)/2500000000),((3431390871:ℚ)/5000000000),((6304799111:ℚ)/28125000000),((8231390871:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1005710701:ℚ)/2000000000),((-2276589396978821771787851195446187668578066649743991:ℚ)/20116567611694335937500000000000000000000000000000000),((-137151543138976800587693907:ℚ)/462080000000000000000000000)⟩
theorem valid4 : Valid source31 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source31 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/16),((1:ℚ)/8),((1355943383:ℚ)/2000000000),((87289339:ℚ)/125000000),((5067943383:ℚ)/22880000000),((207289339:ℚ)/703125000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((117223843:ℚ)/250000000),((-8334184277406282247046263542575469129810269107777745469:ℚ)/74859699200000000000000000000000000000000000000000000000),((-86703387602542428922967:ℚ)/288800000000000000000000)⟩
theorem valid5 : Valid source31 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source31 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source31 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/16),((1:ℚ)/8),((69001773:ℚ)/100000000),((7103458671:ℚ)/10000000000),((254601773:ℚ)/1163000000),((16703458671:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((4325063643:ℚ)/10000000000),((-1077256559627185903704818716073729957263673675638391:ℚ)/9831485918750000000000000000000000000000000000000000),((-561139643969305597773439107:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source31 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source31 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/16),((1:ℚ)/8),((7020580627:ℚ)/10000000000),((3611859529:ℚ)/5000000000),((8526860209:ℚ)/39400000000),((8411859529:ℚ)/29075000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((3930097281:ℚ)/10000000000),((-10310654986071367944555956243420961318220217522564222563:ℚ)/95567162500000000000000000000000000000000000000000000000),((-141830074955812489869820307:ℚ)/462080000000000000000000000)⟩
theorem valid7 : Valid source31 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source31 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/16),((1:ℚ)/8),((3570464861:ℚ)/5000000000),((3732048067:ℚ)/5000000000),((12850464861:ℚ)/61000000000),((8532048067:ℚ)/29550000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((698696389:ℚ)/2000000000),((-147676938281153311711675794913079870751143467933743915327:ℚ)/1418631250000000000000000000000000000000000000000000000000),((-142527591857375338039292603:ℚ)/462080000000000000000000000)⟩
theorem valid8 : Valid source31 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source31 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source31 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/16),((1:ℚ)/8),((7381475617:ℚ)/10000000000),((7944335803:ℚ)/10000000000),((8647158539:ℚ)/43200000000),((17544335803:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((1201916509:ℚ)/5000000000),((-605902040338192281993904198637754625828265548135072153:ℚ)/6220800000000000000000000000000000000000000000000000000),((-76983107628857963:ℚ)/243200000000000000)⟩
theorem valid9 : Valid source31 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source31 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/16),((1:ℚ)/8),((3931011107:ℚ)/5000000000),((2465064183:ℚ)/2500000000),((13211011107:ℚ)/80000000000),((540562687:ℚ)/1800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-245430982069076639841607294154768922634786358535161312601:ℚ)/3200000000000000000000000000000000000000000000000000000000),((-41699957:ℚ)/128000000)⟩
theorem valid10 : Valid source31 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source31 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/16),((1:ℚ)/8),((4889436019:ℚ)/5000000000),((13358253:ℚ)/9765625),((14169436019:ℚ)/110400000000),((22733253:ℚ)/78125000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-4211824724807062837923003500326882972442650516116690739:ℚ)/77868800000000000000000000000000000000000000000000000000),((-41699957:ℚ)/128000000)⟩
theorem valid11 : Valid source31 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source31 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source31 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source31 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source31 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source31 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source31 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source31 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source31 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source31 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source31 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source31 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source31GroupedC18
#check @N11Formalization.C450Source31GroupedC18.bound
#print axioms N11Formalization.C450Source31GroupedC18.valid0
#print axioms N11Formalization.C450Source31GroupedC18.valid1
#print axioms N11Formalization.C450Source31GroupedC18.valid2
#print axioms N11Formalization.C450Source31GroupedC18.valid3
#print axioms N11Formalization.C450Source31GroupedC18.valid4
#print axioms N11Formalization.C450Source31GroupedC18.valid5
#print axioms N11Formalization.C450Source31GroupedC18.valid6
#print axioms N11Formalization.C450Source31GroupedC18.valid7
#print axioms N11Formalization.C450Source31GroupedC18.valid8
#print axioms N11Formalization.C450Source31GroupedC18.valid9
#print axioms N11Formalization.C450Source31GroupedC18.valid10
#print axioms N11Formalization.C450Source31GroupedC18.valid11
#print axioms N11Formalization.C450Source31GroupedC18.bound
#print axioms N11Formalization.C450Source31GroupedC18.endpoint_checks
