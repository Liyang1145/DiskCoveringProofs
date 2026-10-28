import N11Formalization.C450Source12Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source12GroupedC21
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source12Data
def Qcell : RatInterval := ⟨((1:ℚ)/4),((5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/4),((5:ℚ)/16),((6048395749:ℚ)/10000000000),((262550183:ℚ)/400000000),((7648395749:ℚ)/26700000000),((318870183:ℚ)/793600000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((1626000473:ℚ)/2500000000),((3254099081121845200334002128051127:ℚ)/185577906634752000000000000000000000),((-6077712029384214377434477:ℚ)/46208000000000000000000000)⟩
theorem valid0 : Valid source12 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source12 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((101943773:ℚ)/156250000),((1700410391:ℚ)/2500000000),((126943773:ℚ)/432031250),((684136797:ℚ)/1780000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((67313729:ℚ)/125000000),((1503080740308291514529575267064369782717778880539569563:ℚ)/96243689696875000000000000000000000000000000000000000000),((-3058937482076165825041:ℚ)/22562500000000000000000)⟩
theorem valid1 : Valid source12 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/4),((5:ℚ)/16),((6762352351:ℚ)/10000000000),((6920575233:ℚ)/10000000000),((8362352351:ℚ)/28125000000),((8328575233:ℚ)/22120000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((4739264079:ℚ)/10000000000),((241385161912183534784324890507698315042734670234920029:ℚ)/16307264925000000000000000000000000000000000000000000000),((-6358317174451525734941877:ℚ)/46208000000000000000000000)⟩
theorem valid2 : Valid source12 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source12 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source12 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/4),((5:ℚ)/16),((6881316337:ℚ)/10000000000),((3519751393:ℚ)/5000000000),((652408949:ℚ)/2200000000),((1407917131:ℚ)/3750000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((175355899:ℚ)/400000000),((4059307155046282417041602826855331821465240378139523:ℚ)/276947021484375000000000000000000000000000000000000000),((-6405153680829341727563413:ℚ)/46208000000000000000000000)⟩
theorem valid3 : Valid source12 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source12 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/4),((5:ℚ)/16),((7000273197:ℚ)/10000000000),((1419792873:ℚ)/2000000000),((8600273197:ℚ)/28837500000),((1701392873:ℚ)/4576000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((3999291591:ℚ)/10000000000),((237391444850959084037427375876728232390221157384072051763:ℚ)/16600914966979200000000000000000000000000000000000000000000),((-19356030947965736719066679:ℚ)/138624000000000000000000000)⟩
theorem valid4 : Valid source12 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source12 nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((1411949813:ℚ)/2000000000),((3579212263:ℚ)/5000000000),((1731949813:ℚ)/5815000000),((1427737421:ℚ)/3845000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((3793262011:ℚ)/10000000000),((17109192784535045861193525830148692158148436842255883157:ℚ)/1201347054450236328125000000000000000000000000000000000000),((-259017848960862364403213:ℚ)/1848320000000000000000000)⟩
theorem valid5 : Valid source12 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/4),((5:ℚ)/16),((7119223281:ℚ)/10000000000),((902235413:ℚ)/1250000000),((8719223281:ℚ)/29312500000),((1078235413:ℚ)/2907500000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3575990867:ℚ)/10000000000),((15970161713306435692084363252046003095235071222710361:ℚ)/1125724339817810058593750000000000000000000000000000000),((-19496661641317820628960191:ℚ)/138624000000000000000000000)⟩
theorem valid6 : Valid source12 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source12 nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet source12 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((1435739177:ℚ)/2000000000),((7277340733:ℚ)/10000000000),((1755739177:ℚ)/5910000000),((8685340733:ℚ)/23450000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((104540129:ℚ)/312500000),((2072347177115517621416315400850472721726836807775354371623:ℚ)/146616312179479980468750000000000000000000000000000000000000),((-260893332021411499948933:ℚ)/1848320000000000000000000)⟩
theorem valid7 : Valid source12 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((1:ℚ)/4),((5:ℚ)/16),((1809541729:ℚ)/2500000000),((1834199211:ℚ)/2500000000),((2209541729:ℚ)/7446875000),((2186199211:ℚ)/5910000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((3098137071:ℚ)/10000000000),((2149897484675500472623988412986855047822817238046877351809:ℚ)/152633304689051953125000000000000000000000000000000000000000),((-409111531201513924125357:ℚ)/2888000000000000000000000)⟩
theorem valid8 : Valid source12 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source12 nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet source12 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((1:ℚ)/4),((5:ℚ)/16),((7297636413:ℚ)/10000000000),((739625167:ℚ)/1000000000),((8897636413:ℚ)/30025000000),((880425167:ℚ)/2383000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((2830241019:ℚ)/10000000000),((6690192991467046838850243027427769709099360922114843919:ℚ)/476538719915153491210937500000000000000000000000000000000),((-54592029014701516473599:ℚ)/384000000000000000000000)⟩
theorem valid9 : Valid source12 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source12 nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet source12 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/4),((5:ℚ)/16),((7357104411:ℚ)/10000000000),((1503031517:ℚ)/2000000000),((8957104411:ℚ)/30500000000),((1784631517:ℚ)/4804000000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((101400831:ℚ)/400000000),((2289658817534327163053210004698344797279057989095807789:ℚ)/161149402983025000000000000000000000000000000000000000000),((-19778106871608901079474951:ℚ)/138624000000000000000000000)⟩
theorem valid10 : Valid source12 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source12 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source12 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/4),((5:ℚ)/16),((1869009013:ℚ)/2500000000),((3876477629:ℚ)/5000000000),((2269009013:ℚ)/7862500000),((4580477629:ℚ)/12200000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((1808622759:ℚ)/10000000000),((16712910214231017555720121213674321197020229304466367177:ℚ)/1150140750781250000000000000000000000000000000000000000000),((-414977543566286988296613:ℚ)/2888000000000000000000000)⟩
theorem valid11 : Valid source12 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet source12 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/4),((5:ℚ)/16),((7713882837:ℚ)/10000000000),((1598147089:ℚ)/2000000000),((9313882837:ℚ)/32400000000),((1879747089:ℚ)/5032000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((1565462031754934881076589268545594915454719149627073931:ℚ)/108850571868600000000000000000000000000000000000000000000),((-18527949:ℚ)/128000000)⟩
theorem valid12 : Valid source12 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source12 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source12 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/4),((5:ℚ)/16),((1590341849:ℚ)/2000000000),((2473124297:ℚ)/2500000000),((1910341849:ℚ)/8000000000),((941708099:ℚ)/2160000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((1512816421607659287243027170936181288139006811801:ℚ)/82012500000000000000000000000000000000000000000000),((-18527949:ℚ)/128000000)⟩
theorem valid13 : Valid source12 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source12 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/4),((5:ℚ)/16),((2463440373:ℚ)/2500000000),((13694564149:ℚ)/10000000000),((2863440373:ℚ)/13800000000),((15102564149:ℚ)/32000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((19586323023433892680371082337484234413:ℚ)/812544000000000000000000000000000000000),((-18527949:ℚ)/128000000)⟩
theorem valid14 : Valid source12 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source12 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source12 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source12 nn0 nn1 Qcell ((267:ℚ)/400) ((45:ℚ)/64) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((2307:ℚ)/3200) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source12 nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source12 nn0 nn1 Qcell ((45:ℚ)/64) ((469:ℚ)/640) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source12 nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source12 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source12 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source12 nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source12 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source12 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source12GroupedC21
#check @N11Formalization.C450Source12GroupedC21.bound
#print axioms N11Formalization.C450Source12GroupedC21.valid0
#print axioms N11Formalization.C450Source12GroupedC21.valid1
#print axioms N11Formalization.C450Source12GroupedC21.valid2
#print axioms N11Formalization.C450Source12GroupedC21.valid3
#print axioms N11Formalization.C450Source12GroupedC21.valid4
#print axioms N11Formalization.C450Source12GroupedC21.valid5
#print axioms N11Formalization.C450Source12GroupedC21.valid6
#print axioms N11Formalization.C450Source12GroupedC21.valid7
#print axioms N11Formalization.C450Source12GroupedC21.valid8
#print axioms N11Formalization.C450Source12GroupedC21.valid9
#print axioms N11Formalization.C450Source12GroupedC21.valid10
#print axioms N11Formalization.C450Source12GroupedC21.valid11
#print axioms N11Formalization.C450Source12GroupedC21.valid12
#print axioms N11Formalization.C450Source12GroupedC21.valid13
#print axioms N11Formalization.C450Source12GroupedC21.valid14
#print axioms N11Formalization.C450Source12GroupedC21.bound
#print axioms N11Formalization.C450Source12GroupedC21.endpoint_checks
