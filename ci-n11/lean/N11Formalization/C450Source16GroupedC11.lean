import N11Formalization.C450Source16Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source16GroupedC11
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source16Data
def Qcell : RatInterval := ⟨((-3:ℚ)/8),((-5:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-3:ℚ)/8),((-5:ℚ)/16),((6352137279:ℚ)/10000000000),((3319212931:ℚ)/5000000000),((-7717638793:ℚ)/24800000000),((-4432137279:ℚ)/20600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((2905971609:ℚ)/5000000000),((1269074669877972511363083469381354150323959857660381703:ℚ)/21171585625000000000000000000000000000000000000000000000),((35911235207512407990637319:ℚ)/466944000000000000000000000)⟩
theorem valid0 : Valid source16 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source16 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-3:ℚ)/8),((-5:ℚ)/16),((6590483709:ℚ)/10000000000),((6876785477:ℚ)/10000000000),((-156799577:ℚ)/500000000),((-1556827903:ℚ)/7120000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((1042614431:ℚ)/2000000000),((419970039477067162458589288601224406950274637036329:ℚ)/7049690000000000000000000000000000000000000000000000),((34240544345683952473202879:ℚ)/466944000000000000000000000)⟩
theorem valid1 : Valid source16 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source16 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source16 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((3414384803:ℚ)/5000000000),((699594263:ℚ)/1000000000),((-1650782789:ℚ)/5340000000),((-2454384803:ℚ)/10870000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4544050747:ℚ)/10000000000),((520154968550239710011839781231161233300343004404605181:ℚ)/8930353888046875000000000000000000000000000000000000000),((2713837346051619924334677:ℚ)/38912000000000000000000000)⟩
theorem valid2 : Valid source16 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source16 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((2193:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((6947891851:ℚ)/10000000000),((440969743:ℚ)/625000000),((-1042909229:ℚ)/3396875000),((-5027891851:ℚ)/21930000000),((4834485079:ℚ)/5000000000),((2423459781:ℚ)/2500000000),((2580203419:ℚ)/10000000000),((4172759869:ℚ)/10000000000),((253002404310112172256011948737811874649878898222347569:ℚ)/4390412256035156250000000000000000000000000000000000000),((10575786666543799549622853:ℚ)/155648000000000000000000000)⟩
theorem valid3 : Valid source16 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source16 nn0 nn1 Qcell ((1087:ℚ)/1600) ((2193:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((2193:ℚ)/3200),((553:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((3503724057:ℚ)/5000000000),((1778771431:ℚ)/2500000000),((-4216314293:ℚ)/13706250000),((-363389151:ℚ)/1580000000),((1205629803:ℚ)/1250000000),((9668970163:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((3974974531:ℚ)/10000000000),((202647545493575813166953838373162107372481231721603:ℚ)/3519643642578125000000000000000000000000000000000000),((7826913459873441917827991:ℚ)/116736000000000000000000000)⟩
theorem valid4 : Valid source16 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source16 nn0 nn1 Qcell ((2193:ℚ)/3200) ((553:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((553:ℚ)/800),((2231:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((7067001249:ℚ)/10000000000),((286986089:ℚ)/400000000),((-681758267:ℚ)/2212000000),((-223782663:ℚ)/970000000),((2405504993:ℚ)/2500000000),((9645038429:ℚ)/10000000000),((551641531:ℚ)/2000000000),((3767408539:ℚ)/10000000000),((141772037387409913056277234858473026383172477323313:ℚ)/2464395356445312500000000000000000000000000000000000),((30887705560061449098002759:ℚ)/466944000000000000000000000)⟩
theorem valid5 : Valid source16 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((2231:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((2231:ℚ)/3200),((45:ℚ)/64),((-3:ℚ)/8),((-5:ℚ)/16),((890818917:ℚ)/1250000000),((7234215477:ℚ)/10000000000),((-17222646431:ℚ)/55775000000),((-72313213:ℚ)/312500000),((599993229:ℚ)/625000000),((9622019977:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((3548341521:ℚ)/10000000000),((3583046855073378323995880858992287241498484389127:ℚ)/62333419919013977050781250000000000000000000000000),((476054916223338145360751:ℚ)/7296000000000000000000000)⟩
theorem valid6 : Valid source16 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source16 nn0 nn1 Qcell ((2231:ℚ)/3200) ((45:ℚ)/64) :=
  cell_of_packet source16 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((45:ℚ)/64),((2269:ℚ)/3200),((-3:ℚ)/8),((-5:ℚ)/16),((3593049227:ℚ)/5000000000),((7293775561:ℚ)/10000000000),((-17401326683:ℚ)/56250000000),((-2633049227:ℚ)/11345000000),((478931557:ℚ)/500000000),((9599891669:ℚ)/10000000000),((1456642997:ℚ)/5000000000),((26523919:ℚ)/80000000),((49142926547918813151907204069635055268951374199407:ℚ)/855588215991210937500000000000000000000000000000000),((2503923379732570358240837:ℚ)/38912000000000000000000000)⟩
theorem valid7 : Valid source16 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((2269:ℚ)/3200) :=
  cell_of_packet source16 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((2269:ℚ)/3200),((143:ℚ)/200),((-3:ℚ)/8),((-5:ℚ)/16),((1811410669:ℚ)/2500000000),((1838333139:ℚ)/2500000000),((-4394999417:ℚ)/14181250000),((-1331410669:ℚ)/5720000000),((9558216781:ℚ)/10000000000),((1915726229:ℚ)/2000000000),((149176903:ℚ)/500000000),((30657093:ℚ)/100000000),((146468120989668178317434509518886302762958332659938259:ℚ)/2551932955000000000000000000000000000000000000000000000),((617216725815689908866933:ℚ)/9728000000000000000000000)⟩
theorem valid8 : Valid source16 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source16 nn0 nn1 Qcell ((2269:ℚ)/3200) ((143:ℚ)/200) :=
  cell_of_packet source16 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-3:ℚ)/8),((-5:ℚ)/16),((1826296019:ℚ)/2500000000),((1868109397:ℚ)/2500000000),((-4484328191:ℚ)/14300000000),((-1346296019:ℚ)/5815000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2794458581:ℚ)/10000000000),((127010002495369336695560664185275613622813902809434771:ℚ)/2196722634970703125000000000000000000000000000000000000),((608447520846082911929333:ℚ)/9728000000000000000000000)⟩
theorem valid9 : Valid source16 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source16 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-3:ℚ)/8),((-5:ℚ)/16),((58002021:ℚ)/78125000),((7591531157:ℚ)/10000000000),((-18294593471:ℚ)/58150000000),((-14334007:ℚ)/61562500),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((430938783:ℚ)/2000000000),((305955890105958593842513844328758150898964516383:ℚ)/5299787997603416442871093750000000000000000000000),((1731134225013546582719:ℚ)/28500000000000000000000)⟩
theorem valid10 : Valid source16 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source16 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source16 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-3:ℚ)/8),((-5:ℚ)/16),((3771661411:ℚ)/5000000000),((3914843029:ℚ)/5000000000),((-9504529087:ℚ)/29550000000),((-2811661411:ℚ)/12200000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1222031999:ℚ)/10000000000),((4906096183381956138010575382322496502107151700247540347:ℚ)/83841106875000000000000000000000000000000000000000000000),((2293278625352139435597013:ℚ)/38912000000000000000000000)⟩
theorem valid11 : Valid source16 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source16 nn0 nn1 packet11 valid11
def packet12 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-3:ℚ)/8),((-5:ℚ)/16),((7781421627:ℚ)/10000000000),((4152940107:ℚ)/5000000000),((-10218820321:ℚ)/30500000000),((-1953807209:ℚ)/8640000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((61410665312519513231400286448594703190199608083344201:ℚ)/1024565760000000000000000000000000000000000000000000000),((2378721:ℚ)/40960000)⟩
theorem valid12 : Valid source16 packet12 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf12 :
    CellBound source16 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source16 nn0 nn1 packet12 valid12
def packet13 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-3:ℚ)/8),((-5:ℚ)/16),((825751353:ℚ)/1000000000),((1020951927:ℚ)/1000000000),((-2614855781:ℚ)/6480000000),((-633751353:ℚ)/3200000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((4662761489823214226875230102030808601521867544228213:ℚ)/69120000000000000000000000000000000000000000000000000),((2378721:ℚ)/40960000)⟩
theorem valid13 : Valid source16 packet13 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf13 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source16 nn0 nn1 packet13 valid13
def packet14 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-3:ℚ)/8),((-5:ℚ)/16),((1270105153:ℚ)/1250000000),((14013786207:ℚ)/10000000000),((-37561358621:ℚ)/80000000000),((-1030105153:ℚ)/5520000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((755844414784776529745290290019090231982281668063517:ℚ)/9855270000000000000000000000000000000000000000000000),((2378721:ℚ)/40960000)⟩
theorem valid14 : Valid source16 packet14 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf14 :
    CellBound source16 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source16 nn0 nn1 packet14 valid14
private theorem node1_3 :
    CellBound source16 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node3_5 :
    CellBound source16 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_join leaf3 leaf4
private theorem node5_7 :
    CellBound source16 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_join leaf5 leaf6
private theorem node3_7 :
    CellBound source16 nn0 nn1 Qcell ((1087:ℚ)/1600) ((45:ℚ)/64) :=
  cell_join node3_5 node5_7
private theorem node0_7 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((45:ℚ)/64) :=
  cell_join node0_3 node3_7
private theorem node7_9 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_join leaf7 leaf8
private theorem node9_11 :
    CellBound source16 nn0 nn1 Qcell ((143:ℚ)/200) ((591:ℚ)/800) :=
  cell_join leaf9 leaf10
private theorem node7_11 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((591:ℚ)/800) :=
  cell_join node7_9 node9_11
private theorem node11_13 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((81:ℚ)/100) :=
  cell_join leaf11 leaf12
private theorem node13_15 :
    CellBound source16 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf13 leaf14
private theorem node11_15 :
    CellBound source16 nn0 nn1 Qcell ((591:ℚ)/800) ((69:ℚ)/50) :=
  cell_join node11_13 node13_15
private theorem node7_15 :
    CellBound source16 nn0 nn1 Qcell ((45:ℚ)/64) ((69:ℚ)/50) :=
  cell_join node7_11 node11_15
private theorem node0_15 :
    CellBound source16 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_7 node7_15
theorem bound : CellBound source16 nn0 nn1 Qcell (31/50) (69/50) := node0_15
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11,packet12,packet13,packet14]
theorem packet_count : packets.length = 15 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source16GroupedC11
#check @N11Formalization.C450Source16GroupedC11.bound
#print axioms N11Formalization.C450Source16GroupedC11.valid0
#print axioms N11Formalization.C450Source16GroupedC11.valid1
#print axioms N11Formalization.C450Source16GroupedC11.valid2
#print axioms N11Formalization.C450Source16GroupedC11.valid3
#print axioms N11Formalization.C450Source16GroupedC11.valid4
#print axioms N11Formalization.C450Source16GroupedC11.valid5
#print axioms N11Formalization.C450Source16GroupedC11.valid6
#print axioms N11Formalization.C450Source16GroupedC11.valid7
#print axioms N11Formalization.C450Source16GroupedC11.valid8
#print axioms N11Formalization.C450Source16GroupedC11.valid9
#print axioms N11Formalization.C450Source16GroupedC11.valid10
#print axioms N11Formalization.C450Source16GroupedC11.valid11
#print axioms N11Formalization.C450Source16GroupedC11.valid12
#print axioms N11Formalization.C450Source16GroupedC11.valid13
#print axioms N11Formalization.C450Source16GroupedC11.valid14
#print axioms N11Formalization.C450Source16GroupedC11.bound
#print axioms N11Formalization.C450Source16GroupedC11.endpoint_checks
