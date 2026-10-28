import N11Formalization.C450Source25Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source25GroupedC13
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source25Data
def Qcell : RatInterval := ⟨((-1:ℚ)/4),((-3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((-1:ℚ)/4),((-3:ℚ)/16),((6306288081:ℚ)/10000000000),((6610039739:ℚ)/10000000000),((-2930039739:ℚ)/24800000000),((-3558864243:ℚ)/103000000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((592092371:ℚ)/1000000000),((43088532392779453903396951130211390708185567452638984308087:ℚ)/211715856250000000000000000000000000000000000000000000000000),((-1201744202902897943084573:ℚ)/8192000000000000000000000)⟩
theorem valid0 : Valid source25 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source25 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((-1:ℚ)/4),((-3:ℚ)/16),((3273127879:ℚ)/5000000000),((856245509:ℚ)/1250000000),((-396245509:ℚ)/3218750000),((-713127879:ℚ)/17800000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((213150517:ℚ)/400000000),((183550095698191465592849826265735371958149052270106464747:ℚ)/907647587500000000000000000000000000000000000000000000000),((-118200174304280883952976693:ℚ)/739328000000000000000000000)⟩
theorem valid1 : Valid source25 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source25 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((1696511321:ℚ)/2500000000),((435616359:ℚ)/625000000),((-205616359:ℚ)/1668750000),((-1249533963:ℚ)/27175000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((4670493919:ℚ)/10000000000),((2225281102300406504362387980359122288606398306390274308353:ℚ)/11162942360058593750000000000000000000000000000000000000000),((-31999887038324567839563893:ℚ)/184832000000000000000000000)⟩
theorem valid2 : Valid source25 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source25 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((6905879187:ℚ)/10000000000),((7089719431:ℚ)/10000000000),((-3409719431:ℚ)/27175000000),((-5357637561:ℚ)/110600000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((215356471:ℚ)/500000000),((28569216016699364500237090342710314610508591270946628939213:ℚ)/143613401405468750000000000000000000000000000000000000000000),((-531682661667103054397093837:ℚ)/2957312000000000000000000000)⟩
theorem valid3 : Valid source25 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((-1:ℚ)/4),((-3:ℚ)/16),((1756418839:ℚ)/2500000000),((1441907839:ℚ)/2000000000),((-100843977:ℚ)/790000000),((-476418839:ℚ)/9375000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((1956277981:ℚ)/5000000000),((315564811710291171728740452019157497219467021557821571:ℚ)/1589208841323852539062500000000000000000000000000000000),((-34464041287665329103706133:ℚ)/184832000000000000000000000)⟩
theorem valid4 : Valid source25 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source25 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((-1:ℚ)/4),((-3:ℚ)/16),((893179467:ℚ)/1250000000),((91616537:ℚ)/125000000),((-45616537:ℚ)/351562500),((-759538401:ℚ)/14300000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((1738059429:ℚ)/5000000000),((10869799092797535324956451204259296041953975915226134273:ℚ)/54828881250000000000000000000000000000000000000000000000),((-8925382051402976816669597:ℚ)/46208000000000000000000000)⟩
theorem valid5 : Valid source25 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source25 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source25 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((-1:ℚ)/4),((-3:ℚ)/16),((7265162139:ℚ)/10000000000),((186226813:ℚ)/250000000),((-94226813:ℚ)/715000000),((-6435486417:ℚ)/116300000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((1489714421:ℚ)/5000000000),((278333747882135971285842644237539288866904567779414534043701:ℚ)/1405902486381250000000000000000000000000000000000000000000000),((-591082277658325951358126333:ℚ)/2957312000000000000000000000)⟩
theorem valid6 : Valid source25 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source25 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((-1:ℚ)/4),((-3:ℚ)/16),((7384856257:ℚ)/10000000000),((7568789551:ℚ)/10000000000),((-3888789551:ℚ)/29075000000),((-2264856257:ℚ)/39400000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((2385077173:ℚ)/10000000000),((21977878831644487290858278314853338389146265050794768618689:ℚ)/111144609987500000000000000000000000000000000000000000000000),((-610998367507987598923428677:ℚ)/2957312000000000000000000000)⟩
theorem valid7 : Valid source25 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source25 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((-1:ℚ)/4),((-3:ℚ)/16),((938064959:ℚ)/1250000000),((7808132203:ℚ)/10000000000),((-4128132203:ℚ)/29550000000),((-894194877:ℚ)/15250000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((793397607:ℚ)/5000000000),((869950059794553413765931329123199966384483261928611289931:ℚ)/4366724316406250000000000000000000000000000000000000000000),((-9858952091545396012684613:ℚ)/46208000000000000000000000)⟩
theorem valid8 : Valid source25 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source25 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source25 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((-1:ℚ)/4),((-3:ℚ)/16),((7743760213:ℚ)/10000000000),((25895281:ℚ)/31250000),((-14395281:ℚ)/95312500),((-2623760213:ℚ)/43200000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),(0:ℚ),((690215248863118626449081044123975849787266900433319932723:ℚ)/3415219200000000000000000000000000000000000000000000000000),((-224015371:ℚ)/1024000000)⟩
theorem valid9 : Valid source25 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source25 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((-1:ℚ)/4),((-3:ℚ)/16),((8221932043:ℚ)/10000000000),((2039341257:ℚ)/2000000000),((-1303341257:ℚ)/6480000000),((-9305796129:ℚ)/160000000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((151425175869260972899132806531806598608233982748142648523753:ℚ)/691200000000000000000000000000000000000000000000000000000000),((-224015371:ℚ)/1024000000)⟩
theorem valid10 : Valid source25 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source25 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((-1:ℚ)/4),((-3:ℚ)/16),((1266448013:ℚ)/1250000000),((3502165017:ℚ)/2500000000),((-2582165017:ℚ)/10000000000),((-626448013:ℚ)/9200000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((302655201698427017200627959064068890411874282674649807:ℚ)/1216700000000000000000000000000000000000000000000000000),((-224015371:ℚ)/1024000000)⟩
theorem valid11 : Valid source25 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source25 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source25 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source25 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source25 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source25 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source25 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source25 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source25 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source25 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source25 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source25 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source25GroupedC13
#check @N11Formalization.C450Source25GroupedC13.bound
#print axioms N11Formalization.C450Source25GroupedC13.valid0
#print axioms N11Formalization.C450Source25GroupedC13.valid1
#print axioms N11Formalization.C450Source25GroupedC13.valid2
#print axioms N11Formalization.C450Source25GroupedC13.valid3
#print axioms N11Formalization.C450Source25GroupedC13.valid4
#print axioms N11Formalization.C450Source25GroupedC13.valid5
#print axioms N11Formalization.C450Source25GroupedC13.valid6
#print axioms N11Formalization.C450Source25GroupedC13.valid7
#print axioms N11Formalization.C450Source25GroupedC13.valid8
#print axioms N11Formalization.C450Source25GroupedC13.valid9
#print axioms N11Formalization.C450Source25GroupedC13.valid10
#print axioms N11Formalization.C450Source25GroupedC13.valid11
#print axioms N11Formalization.C450Source25GroupedC13.bound
#print axioms N11Formalization.C450Source25GroupedC13.endpoint_checks
