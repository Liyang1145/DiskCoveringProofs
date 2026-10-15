import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC19
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((1:ℚ)/8),((3:ℚ)/16)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((1:ℚ)/8),((3:ℚ)/16),((5831177807:ℚ)/10000000000),((3081923653:ℚ)/5000000000),((15751177807:ℚ)/51500000000),((19485770959:ℚ)/49600000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3481190613:ℚ)/5000000000),((-52145127498748569249984708832021100766991485507697824547357:ℚ)/246119682890625000000000000000000000000000000000000000000000),((-1080154756829446509917308701:ℚ)/3696640000000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((1:ℚ)/8),((3:ℚ)/16),((6073525657:ℚ)/10000000000),((3202822013:ℚ)/5000000000),((5331175219:ℚ)/17800000000),((19848466039:ℚ)/51500000000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((3224597901:ℚ)/5000000000),((-1926511934086203035142413379183306445549253396817580357083:ℚ)/9348770151250000000000000000000000000000000000000000000000),((-1097556267944495289767531341:ℚ)/3696640000000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((1263103733:ℚ)/2000000000),((6526426801:ℚ)/10000000000),((3247103733:ℚ)/10870000000),((40059280403:ℚ)/106800000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((737390759:ℚ)/1250000000),((-3907582907837093233424844566618741256341026354138066776383:ℚ)/19075235904868125000000000000000000000000000000000000000000),((-4493883205428682491345661189:ℚ)/14786560000000000000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((1609098541:ℚ)/2500000000),((3323568997:ℚ)/5000000000),((4089098541:ℚ)/13825000000),((20210706991:ℚ)/54350000000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((1121359021:ℚ)/2000000000),((-881068973875188478831935206057431645245594182898442827219:ℚ)/4355685472314300537109375000000000000000000000000000000000),((-1131719340675484452104651101:ℚ)/3696640000000000000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((1:ℚ)/8),((3:ℚ)/16),((6557194731:ℚ)/10000000000),((1691945337:ℚ)/2500000000),((16477194731:ℚ)/56250000000),((10195836011:ℚ)/27650000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((530036179:ℚ)/1000000000),((-1008392024501704095121090548526359819351051809459620467239:ℚ)/5046055912971496582031250000000000000000000000000000000000),((-284948356971363504863265941:ℚ)/924160000000000000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((1:ℚ)/8),((3:ℚ)/16),((6677924293:ℚ)/10000000000),((6888360351:ℚ)/10000000000),((16597924293:ℚ)/57200000000),((41145081053:ℚ)/112500000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((4977181593:ℚ)/10000000000),((-623782981186152872444518228430196866549277103518339327727:ℚ)/3158143560000000000000000000000000000000000000000000000000),((-4590774546281487127726095589:ℚ)/14786560000000000000000000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((1:ℚ)/8),((3:ℚ)/16),((6798586503:ℚ)/10000000000),((7008878251:ℚ)/10000000000),((16718586503:ℚ)/58150000000),((41506634753:ℚ)/114400000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((2316855051:ℚ)/5000000000),((-490816950740129159372284624338733449235198390910061318483031:ℚ)/2513050694406484375000000000000000000000000000000000000000000),((-243246421171993899224894831:ℚ)/778240000000000000000000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((1:ℚ)/8),((3:ℚ)/16),((6919184767:ℚ)/10000000000),((3564669041:ℚ)/5000000000),((5613061589:ℚ)/19700000000),((20934007123:ℚ)/58150000000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((170600173:ℚ)/400000000),((-312174787221123351139956291575876038448652198792686875668013:ℚ)/1615764767693281250000000000000000000000000000000000000000000),((-1162974517419261225582898309:ℚ)/3696640000000000000000000000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((1:ℚ)/8),((3:ℚ)/16),((3519861131:ℚ)/5000000000),((3685047343:ℚ)/5000000000),((8479861131:ℚ)/30500000000),((21295142029:ℚ)/59100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((1931900449:ℚ)/5000000000),((-129394804896703488193558538952538386499228359069206185190547:ℚ)/688195752265625000000000000000000000000000000000000000000000),((-1160155641858969735162453061:ℚ)/3696640000000000000000000000)⟩
theorem valid8 : Valid source33 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source33 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((1:ℚ)/8),((3:ℚ)/16),((3640313317:ℚ)/5000000000),((7851024297:ℚ)/10000000000),((8600313317:ℚ)/32400000000),((44033072891:ℚ)/122000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((727327937:ℚ)/2500000000),((-4717521205940647133793928384064247083896709058670943799503:ℚ)/26366559480000000000000000000000000000000000000000000000000),((-30921459963501099:ℚ)/97280000000000000)⟩
theorem valid9 : Valid source33 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((1:ℚ)/8),((3:ℚ)/16),((7761824789:ℚ)/10000000000),((9769032701:ℚ)/10000000000),((17681824789:ℚ)/80000000000),((49787098103:ℚ)/129600000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),(0:ℚ),((-34982986953757157872391486594743376105986431066378829784773:ℚ)/233280000000000000000000000000000000000000000000000000000000),((-338273479:ℚ)/1024000000)⟩
theorem valid10 : Valid source33 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((1:ℚ)/8),((3:ℚ)/16),((4840322569:ℚ)/5000000000),((1359005093:ℚ)/1000000000),((9800322569:ℚ)/55200000000),((6125015279:ℚ)/16000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-9678315858953618392938642841471017435742154561077023251:ℚ)/78842160000000000000000000000000000000000000000000000000),((-338273479:ℚ)/1024000000)⟩
theorem valid11 : Valid source33 packet11 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf11 :
    CellBound source33 nn0 nn1 Qcell (1:ℚ) ((69:ℚ)/50) :=
  cell_of_packet source33 nn0 nn1 packet11 valid11
private theorem node1_3 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((1087:ℚ)/1600) :=
  cell_join leaf1 leaf2
private theorem node0_3 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((1087:ℚ)/1600) :=
  cell_join leaf0 node1_3
private theorem node4_6 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((143:ℚ)/200) :=
  cell_join leaf4 leaf5
private theorem node3_6 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((143:ℚ)/200) :=
  cell_join leaf3 node4_6
private theorem node0_6 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((143:ℚ)/200) :=
  cell_join node0_3 node3_6
private theorem node7_9 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((61:ℚ)/80) :=
  cell_join leaf7 leaf8
private theorem node6_9 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((61:ℚ)/80) :=
  cell_join leaf6 node7_9
private theorem node10_12 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) ((69:ℚ)/50) :=
  cell_join leaf10 leaf11
private theorem node9_12 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((69:ℚ)/50) :=
  cell_join leaf9 node10_12
private theorem node6_12 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((69:ℚ)/50) :=
  cell_join node6_9 node9_12
private theorem node0_12 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((69:ℚ)/50) :=
  cell_join node0_6 node6_12
theorem bound : CellBound source33 nn0 nn1 Qcell (31/50) (69/50) := node0_12
def packets : List Packet := [packet0,packet1,packet2,packet3,packet4,packet5,packet6,packet7,packet8,packet9,packet10,packet11]
theorem packet_count : packets.length = 12 := by decide +kernel
theorem endpoint_checks :
    packets.all (fun p => decide (p.lo ≤ p.hi ∧ p.qLo ≤ p.qHi)) = true := by decide +kernel
end N11Formalization.C450Source33GroupedC19
#check @N11Formalization.C450Source33GroupedC19.bound
#print axioms N11Formalization.C450Source33GroupedC19.valid0
#print axioms N11Formalization.C450Source33GroupedC19.valid1
#print axioms N11Formalization.C450Source33GroupedC19.valid2
#print axioms N11Formalization.C450Source33GroupedC19.valid3
#print axioms N11Formalization.C450Source33GroupedC19.valid4
#print axioms N11Formalization.C450Source33GroupedC19.valid5
#print axioms N11Formalization.C450Source33GroupedC19.valid6
#print axioms N11Formalization.C450Source33GroupedC19.valid7
#print axioms N11Formalization.C450Source33GroupedC19.valid8
#print axioms N11Formalization.C450Source33GroupedC19.valid9
#print axioms N11Formalization.C450Source33GroupedC19.valid10
#print axioms N11Formalization.C450Source33GroupedC19.valid11
#print axioms N11Formalization.C450Source33GroupedC19.bound
#print axioms N11Formalization.C450Source33GroupedC19.endpoint_checks
