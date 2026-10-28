import N11Formalization.C450Source19Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source19GroupedC27
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source19Data
def Qcell : RatInterval := ⟨((5:ℚ)/8),((11:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((267:ℚ)/400),((5:ℚ)/8),((11:ℚ)/16),((568291429:ℚ)/1000000000),((1245771957:ℚ)/2000000000),((225697143:ℚ)/356000000),((16007491527:ℚ)/19840000000),((4873244381:ℚ)/5000000000),(1:ℚ),((2256500263:ℚ)/10000000000),((3630632839:ℚ)/5000000000),((-330324658765692950555059142823:ℚ)/11279504000000000000000000000000),((-7664673763805466466282703:ℚ)/22179840000000000000000000)⟩
theorem valid0 : Valid source19 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((267:ℚ)/400) :=
  cell_of_packet source19 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((267:ℚ)/400),((553:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((3079745481:ℚ)/5000000000),((6467088311:ℚ)/10000000000),((3623745481:ℚ)/5530000000),((82657971421:ℚ)/106800000000),((1205629803:ℚ)/1250000000),((9746488767:ℚ)/10000000000),((1336191689:ℚ)/5000000000),((1251721021:ℚ)/2000000000),((-121559382039383355262017856620129319417893983712327961:ℚ)/3170857068750000000000000000000000000000000000000000000),((-3360999556732973865991791:ℚ)/9728000000000000000000000)⟩
theorem valid1 : Valid source19 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((553:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((553:ℚ)/800),((143:ℚ)/200),((5:ℚ)/8),((11:ℚ)/16),((6397697673:ℚ)/10000000000),((670526823:ℚ)/1000000000),((7485697673:ℚ)/11440000000),((8527795053:ℚ)/11060000000),((9558216781:ℚ)/10000000000),((9645038429:ℚ)/10000000000),((149176903:ℚ)/500000000),((1140365567:ℚ)/2000000000),((-362528915326175660339557503740667085517355596715390411:ℚ)/9357462400000000000000000000000000000000000000000000000),((-1913136023643190941762263:ℚ)/5544960000000000000000000)⟩
theorem valid2 : Valid source19 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source19 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_of_packet source19 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((6635857239:ℚ)/10000000000),((341217073:ℚ)/500000000),((7723857239:ℚ)/11630000000),((333029831:ℚ)/440000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5091910967:ℚ)/10000000000),((-314318193998823084274890159073419718081612378620402359:ℚ)/7373614439062500000000000000000000000000000000000000000),((-159398973825775339023421:ℚ)/462080000000000000000000)⟩
theorem valid3 : Valid source19 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((3377460397:ℚ)/5000000000),((216981383:ℚ)/312500000),((3921460397:ℚ)/5910000000),((2746795213:ℚ)/3634375000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((297540331:ℚ)/625000000),((-41300404919109667934803234559554828643492118933431957:ℚ)/967617520312500000000000000000000000000000000000000000),((-124437816209041365586747:ℚ)/361000000000000000000000)⟩
theorem valid4 : Valid source19 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((591:ℚ)/800),((1201:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((6873974231:ℚ)/10000000000),((3531228559:ℚ)/5000000000),((7961974231:ℚ)/12010000000),((44603514149:ℚ)/59100000000),((4726187811:ℚ)/5000000000),((9484612947:ℚ)/10000000000),((831186567:ℚ)/2500000000),((881320247:ℚ)/2000000000),((-1387708760801522296948646026983163426310169838438892191:ℚ)/32481067518750000000000000000000000000000000000000000000),((-15915830772053810708440269:ℚ)/46208000000000000000000000)⟩
theorem valid5 : Valid source19 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source19 nn0 nn1 Qcell ((591:ℚ)/800) ((1201:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((1201:ℚ)/1600),((61:ℚ)/80),((5:ℚ)/8),((11:ℚ)/16),((699301803:ℚ)/1000000000),((224421891:ℚ)/312500000),((808101803:ℚ)/1220000000),((2828640801:ℚ)/3753125000),((9422991801:ℚ)/10000000000),((9452375627:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((4023739209:ℚ)/10000000000),((-485185699532021888284022103410981547767820840258729:ℚ)/11349050000000000000000000000000000000000000000000000),((-372732851113216768310839:ℚ)/1083000000000000000000000)⟩
theorem valid6 : Valid source19 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((61:ℚ)/80) :=
  cell_of_packet source19 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((61:ℚ)/80),((1239:ℚ)/1600),((5:ℚ)/8),((11:ℚ)/16),((3556026323:ℚ)/5000000000),((58404279:ℚ)/80000000),((1366675441:ℚ)/2065000000),((734607069:ℚ)/976000000),((9396330203:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((3492400691:ℚ)/10000000000),((1801424813:ℚ)/5000000000),((-588407977287209368718123355499643309359541820550107:ℚ)/13758788476562500000000000000000000000000000000000000),((-12203791210535192559287:ℚ)/35487744000000000000000)⟩
theorem valid7 : Valid source19 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((1239:ℚ)/1600) :=
  cell_of_packet source19 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((1239:ℚ)/1600),((629:ℚ)/800),((5:ℚ)/8),((11:ℚ)/16),((3615539251:ℚ)/5000000000),((3709780309:ℚ)/5000000000),((4159539251:ℚ)/6290000000),((46567583399:ℚ)/61950000000),((4686133743:ℚ)/5000000000),((293635319:ℚ)/312500000),((890514029:ℚ)/2500000000),((3128584111:ℚ)/10000000000),((-64961424588303242191679566322270086577588788496393:ℚ)/1518909844970703125000000000000000000000000000000000),((-15877085280649193649771269:ℚ)/46208000000000000000000000)⟩
theorem valid8 : Valid source19 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source19 nn0 nn1 Qcell ((1239:ℚ)/1600) ((629:ℚ)/800) :=
  cell_of_packet source19 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((629:ℚ)/800),((81:ℚ)/100),((5:ℚ)/8),((11:ℚ)/16),((3675047999:ℚ)/5000000000),((7657587769:ℚ)/10000000000),((156261037:ℚ)/240000000),((95753465459:ℚ)/125800000000),((9331481479:ℚ)/10000000000),((9372267491:ℚ)/10000000000),((735446993:ℚ)/2000000000),((642883233:ℚ)/2500000000),((-380194144426677228273506298395325875158843362151:ℚ)/9600000000000000000000000000000000000000000000000),((-83430846918207709:ℚ)/243200000000000000)⟩
theorem valid9 : Valid source19 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source19 nn0 nn1 Qcell ((629:ℚ)/800) ((81:ℚ)/100) :=
  cell_of_packet source19 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/8),((11:ℚ)/16),((7588107383:ℚ)/10000000000),((4780450657:ℚ)/5000000000),((8676107383:ℚ)/16000000000),((58344957227:ℚ)/64800000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((559504481:ℚ)/10000000000),((-40647699554024478194029931753144054878256630378552863:ℚ)/4800000000000000000000000000000000000000000000000000000),((-167042651750328453:ℚ)/486400000000000000)⟩
theorem valid10 : Valid source19 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source19 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/8),((11:ℚ)/16),((9491321893:ℚ)/10000000000),((1670598373:ℚ)/1250000000),((3526440631:ℚ)/7360000000),((19816582103:ℚ)/20000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((76248444870574472136833:ℚ)/5416960000000000000000000),((-10990243:ℚ)/32000000)⟩
theorem valid11 : Valid source19 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source19 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source19 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source19 nn0 nn1 Qcell ((267:ℚ)/400) ((143:ℚ)/200) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source19 nn0 nn1 Qcell ((1163:ℚ)/1600) ((1201:ℚ)/1600) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source19 nn0 nn1 Qcell ((143:ℚ)/200) ((1201:ℚ)/1600) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((1201:ℚ)/1600) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source19 nn0 nn1 Qcell ((61:ℚ)/80) ((629:ℚ)/800) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((629:ℚ)/800) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source19 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source19 nn0 nn1 Qcell ((629:ℚ)/800) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source19 nn0 nn1 Qcell ((1201:ℚ)/1600) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source19 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source19 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source19GroupedC27
#check @N11Formalization.C450Source19GroupedC27.bound
#print axioms N11Formalization.C450Source19GroupedC27.valid0
#print axioms N11Formalization.C450Source19GroupedC27.valid1
#print axioms N11Formalization.C450Source19GroupedC27.valid2
#print axioms N11Formalization.C450Source19GroupedC27.valid3
#print axioms N11Formalization.C450Source19GroupedC27.valid4
#print axioms N11Formalization.C450Source19GroupedC27.valid5
#print axioms N11Formalization.C450Source19GroupedC27.valid6
#print axioms N11Formalization.C450Source19GroupedC27.valid7
#print axioms N11Formalization.C450Source19GroupedC27.valid8
#print axioms N11Formalization.C450Source19GroupedC27.valid9
#print axioms N11Formalization.C450Source19GroupedC27.valid10
#print axioms N11Formalization.C450Source19GroupedC27.valid11
#print axioms N11Formalization.C450Source19GroupedC27.bound
#print axioms N11Formalization.C450Source19GroupedC27.endpoint_checks
