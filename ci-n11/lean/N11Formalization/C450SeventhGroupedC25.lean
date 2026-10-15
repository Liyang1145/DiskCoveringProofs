import N11Formalization.C450SeventhData
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450SeventhGroupedC25
open C450GroupedPacketKernel C450GroupedClosedAssembly C450SeventhData
def Qcell : RatInterval := ⟨((1:ℚ)/2),((9:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((1:ℚ)/2),((9:ℚ)/16),((6061823781:ℚ)/10000000000),((6572752433:ℚ)/10000000000),((6461823781:ℚ)/13350000000),((62994771897:ℚ)/99200000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((6474765961:ℚ)/10000000000),((2695599285531304867607:ℚ)/8911125000000000000000000),((-177762237115831637907578289:ℚ)/1848320000000000000000000000)⟩
theorem valid0 : Valid seventh packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet seventh nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((6537049907:ℚ)/10000000000),((85129121:ℚ)/125000000),((6937049907:ℚ)/13825000000),((271387363:ℚ)/445000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((4282047:ℚ)/8000000),((-5066889866223756072413995391177597397020378617716507:ℚ)/8257440283203125000000000000000000000000000000000000000),((-179217988092659353794969601:ℚ)/1848320000000000000000000000)⟩
theorem valid1 : Valid seventh packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound seventh nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/2),((9:ℚ)/16),((6774651309:ℚ)/10000000000),((1385823269:ℚ)/2000000000),((7174651309:ℚ)/14062500000),((13240409421:ℚ)/22120000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1175920429:ℚ)/2500000000),((-2964647541338392877880174768002089229974760760911183:ℚ)/2896785736083984375000000000000000000000000000000000000),((-179960097013877322950360769:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid seventh packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet seventh nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((1:ℚ)/2),((9:ℚ)/16),((43084059:ℚ)/62500000),((6988509217:ℚ)/10000000000),((91168118:ℚ)/177265625),((22245527651:ℚ)/37500000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((2173067841:ℚ)/5000000000),((-42412124021821573552325969736482518610422309639:ℚ)/34813973632454872131347656250000000000000000000000),((-7044324629544538733769:ℚ)/72200000000000000000000)⟩
theorem valid3 : Valid seventh packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound seventh nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((1:ℚ)/2),((9:ℚ)/16),((69528479:ℚ)/100000000),((7047901793:ℚ)/10000000000),((73528479:ℚ)/143000000),((67271116137:ℚ)/113450000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((4156639823:ℚ)/10000000000),((-3169420203337544954503315247593527936201913:ℚ)/2556125000000000000000000000000000000000000000),((-18052290710043609350809:ℚ)/184832000000000000000000)⟩
theorem valid4 : Valid seventh packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet seventh nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((143:ℚ)/200),((2307:ℚ)/3200),((1:ℚ)/2),((9:ℚ)/16),((7012245971:ℚ)/10000000000),((3553647039:ℚ)/5000000000),((2470748657:ℚ)/4806250000),((33902823351:ℚ)/57200000000),((59616423:ℚ)/62500000),((4779108393:ℚ)/5000000000),((762368323:ℚ)/2500000000),((395863487:ℚ)/1000000000),((-328033868564807881199863191909323630185732424205011:ℚ)/260213818931579589843750000000000000000000000000000000),((-180711696936970870286121409:ℚ)/1848320000000000000000000000)⟩
theorem valid5 : Valid seventh packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound seventh nn0 nn1 Qcell ((143:ℚ)/200) ((2307:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2307:ℚ)/3200),((1163:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((7071643661:ℚ)/10000000000),((7166686081:ℚ)/10000000000),((7471643661:ℚ)/14537500000),((22780058243:ℚ)/38450000000),((9519843613:ℚ)/10000000000),((1907725537:ℚ)/2000000000),((622285377:ℚ)/2000000000),((75015393:ℚ)/200000000),((-491719512175970527077004697146234913091580001278949:ℚ)/384042418701171875000000000000000000000000000000000000),((-180901080039811820874611329:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid seventh packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((1163:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((469:ℚ)/640),((1:ℚ)/2),((9:ℚ)/16),((356552049:ℚ)/500000000),((451629863:ℚ)/625000000),((376552049:ℚ)/732812500),((4304668767:ℚ)/7268750000),((9501845013:ℚ)/10000000000),((4759921809:ℚ)/5000000000),((792422551:ℚ)/2500000000),((3531299343:ℚ)/10000000000),((-171185308890694132797515825740620964101430504841:ℚ)/131762507557868957519531250000000000000000000000000),((-452727641073883489185849:ℚ)/4620800000000000000000000)⟩
theorem valid7 : Valid seventh packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound seventh nn0 nn1 Qcell ((1163:ℚ)/1600) ((469:ℚ)/640) :=
  cell_of_packet seventh nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((469:ℚ)/640),((591:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((3595218969:ℚ)/5000000000),((7285469267:ℚ)/10000000000),((3795218969:ℚ)/7387500000),((69409223403:ℚ)/117250000000),((4742306471:ℚ)/5000000000),((4750922509:ℚ)/5000000000),((806129637:ℚ)/2500000000),((1648951803:ℚ)/5000000000),((-138287647445299591273067165386809539369871800358763:ℚ)/104993220520019531250000000000000000000000000000000000),((-125541292331849341487649:ℚ)/1280000000000000000000000)⟩
theorem valid8 : Valid seventh packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((591:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((591:ℚ)/800),((2383:ℚ)/3200),((1:ℚ)/2),((9:ℚ)/16),((3624917271:ℚ)/5000000000),((3672430231:ℚ)/5000000000),((3824917271:ℚ)/7446875000),((11657290693:ℚ)/19700000000),((9468129063:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((3276137213:ℚ)/10000000000),((3047379969:ℚ)/10000000000),((-5165312121326545655763201007265308273969592340879677:ℚ)/3871626630878448486328125000000000000000000000000000000),((-45368197286111992822816809:ℚ)/462080000000000000000000000)⟩
theorem valid9 : Valid seventh packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound seventh nn0 nn1 Qcell ((591:ℚ)/800) ((2383:ℚ)/3200) :=
  cell_of_packet seventh nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((2383:ℚ)/3200),((1201:ℚ)/1600),((1:ℚ)/2),((9:ℚ)/16),((3654615401:ℚ)/5000000000),((3702125701:ℚ)/5000000000),((3854615401:ℚ)/7506250000),((35239131309:ℚ)/59575000000),((4726187811:ℚ)/5000000000),((2367032267:ℚ)/2500000000),((831186567:ℚ)/2500000000),((555017729:ℚ)/2000000000),((-111541649279165529329809123834717431375821418982849:ℚ)/82603626298904418945312500000000000000000000000000000),((-125806471955007986838209:ℚ)/1280000000000000000000000)⟩
theorem valid10 : Valid seventh packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound seventh nn0 nn1 Qcell ((2383:ℚ)/3200) ((1201:ℚ)/1600) :=
  cell_of_packet seventh nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((1:ℚ)/2),((9:ℚ)/16),((294745069:ℚ)/400000000),((940379067:ℚ)/1250000000),((310745069:ℚ)/610000000),((8943411603:ℚ)/15012500000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((618461699:ℚ)/2500000000),((-873100572892813579552722092661717719260197407901:ℚ)/709315625000000000000000000000000000000000000000000),((-290971032344506849799489:ℚ)/2957312000000000000000000)⟩
theorem valid11 : Valid seventh packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound seventh nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet seventh nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((629:ℚ)/800),((1:ℚ)/2),((9:ℚ)/16),((7487417593:ℚ)/10000000000),((7760591981:ℚ)/10000000000),((7887417593:ℚ)/15725000000),((73685327829:ℚ)/122000000000),((4686133743:ℚ)/5000000000),((4711495903:ℚ)/5000000000),((890514029:ℚ)/2500000000),((215422499:ℚ)/1250000000),((-3055376984329608151782541227880334461104057044949433:ℚ)/3037819689941406250000000000000000000000000000000000000),((-182243374768213609559014601:ℚ)/1848320000000000000000000000)⟩
theorem valid12 : Valid seventh packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_of_packet seventh nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((1:ℚ)/2),((9:ℚ)/16),((965624453:ℚ)/1250000000),((7998147939:ℚ)/10000000000),((1015624453:ℚ)/2025000000),((75823331451:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),(0:ℚ),((-1024647216943823978674020746091630981367804377071:ℚ)/961083984375000000000000000000000000000000000000000),((-10117:ℚ)/102400)⟩
theorem valid13 : Valid seventh packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound seventh nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet seventh nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/2),((9:ℚ)/16),((7962569077:ℚ)/10000000000),((989849989:ℚ)/1000000000),((8362569077:ℚ)/20000000000),((3097549967:ℚ)/4320000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((225075634248310018639893265369999:ℚ)/150000000000000000000000000000000000),((-10117:ℚ)/102400)⟩
theorem valid14 : Valid seventh packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet seventh nn0 nn1 packet14 valid14
def packet15 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/2),((9:ℚ)/16),((4931515527:ℚ)/5000000000),((13698913003:ℚ)/10000000000),((5131515527:ℚ)/13800000000),((127130217027:ℚ)/160000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((36336961947410213903423:ℚ)/9522000000000000000000000),((-10117:ℚ)/102400)⟩
theorem valid15 : Valid seventh packet15 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf15 :
    CellBound seventh nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet seventh nn0 nn1 packet15 valid15
private theorem node0_2 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((553:ℚ)/800) :=
  cell_join leaf0 leaf1
private theorem node2_4 :
    CellBound seventh nn0 nn1 Qcell ((553:ℚ)/800) ((2269:ℚ)/3200) :=
  cell_join leaf2 leaf3
private theorem node0_4 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((2269:ℚ)/3200) :=
  cell_join node0_2 node2_4
private theorem node4_6 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((2307:ℚ)/3200) :=
  cell_join leaf4 leaf5
private theorem node6_8 :
    CellBound seventh nn0 nn1 Qcell ((2307:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join leaf6 leaf7
private theorem node4_8 :
    CellBound seventh nn0 nn1 Qcell ((2269:ℚ)/3200) ((469:ℚ)/640) :=
  cell_join node4_6 node6_8
private theorem node0_8 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((469:ℚ)/640) :=
  cell_join node0_4 node4_8
private theorem node8_10 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((2383:ℚ)/3200) :=
  cell_join leaf8 leaf9
private theorem node10_12 :
    CellBound seventh nn0 nn1 Qcell ((2383:ℚ)/3200) ((61:ℚ)/80) :=
  cell_join leaf10 leaf11
private theorem node8_12 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((61:ℚ)/80) :=
  cell_join node8_10 node10_12
private theorem node12_14 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_join leaf12 leaf13
private theorem node14_16 :
    CellBound seventh nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf14 leaf15
private theorem node12_16 :
    CellBound seventh nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join node12_14 node14_16
private theorem node8_16 :
    CellBound seventh nn0 nn1 Qcell ((469:ℚ)/640) ((69:ℚ)/50) :=
  cell_join node8_12 node12_16
private theorem node0_16 :
    CellBound seventh nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_8 node8_16
theorem bound : CellBound seventh nn0 nn1 Qcell (31/50) (69/50) := node0_16
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14,packet15]
theorem packet_count : packets.length = 16 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450SeventhGroupedC25
#check @N11Formalization.C450SeventhGroupedC25.bound
#print axioms N11Formalization.C450SeventhGroupedC25.valid0
#print axioms N11Formalization.C450SeventhGroupedC25.valid1
#print axioms N11Formalization.C450SeventhGroupedC25.valid2
#print axioms N11Formalization.C450SeventhGroupedC25.valid3
#print axioms N11Formalization.C450SeventhGroupedC25.valid4
#print axioms N11Formalization.C450SeventhGroupedC25.valid5
#print axioms N11Formalization.C450SeventhGroupedC25.valid6
#print axioms N11Formalization.C450SeventhGroupedC25.valid7
#print axioms N11Formalization.C450SeventhGroupedC25.valid8
#print axioms N11Formalization.C450SeventhGroupedC25.valid9
#print axioms N11Formalization.C450SeventhGroupedC25.valid10
#print axioms N11Formalization.C450SeventhGroupedC25.valid11
#print axioms N11Formalization.C450SeventhGroupedC25.valid12
#print axioms N11Formalization.C450SeventhGroupedC25.valid13
#print axioms N11Formalization.C450SeventhGroupedC25.valid14
#print axioms N11Formalization.C450SeventhGroupedC25.valid15
#print axioms N11Formalization.C450SeventhGroupedC25.bound
#print axioms N11Formalization.C450SeventhGroupedC25.endpoint_checks
