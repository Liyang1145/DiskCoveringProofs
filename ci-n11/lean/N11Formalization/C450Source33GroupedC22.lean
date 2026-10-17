import N11Formalization.C450Source33Data
set_option autoImplicit false
noncomputable section
namespace N11Formalization.C450Source33GroupedC22
open C450GroupedPacketKernel C450GroupedClosedAssembly C450Source33Data
def Qcell : RatInterval := ⟨((5:ℚ)/16),((3:ℚ)/8)⟩
def packet0 : Packet := ⟨((31:ℚ)/50),((103:ℚ)/160),((5:ℚ)/16),((3:ℚ)/8),((5605392343:ℚ)/10000000000),((1188263999:ℚ)/2000000000),((9573392343:ℚ)/20600000000),((5612791997:ℚ)/9920000000),((9864186891:ℚ)/10000000000),(1:ℚ),((1649979683:ℚ)/10000000000),((3706794229:ℚ)/5000000000),((-55956705669954693093784439912933219929235719704504342521:ℚ)/188526981120000000000000000000000000000000000000000000000),((-27103797259361266831522037:ℚ)/73932800000000000000000000)⟩
theorem valid0 : Valid source33 packet0 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf0 :
    CellBound source33 nn0 nn1 Qcell ((31:ℚ)/50) ((103:ℚ)/160) :=
  cell_of_packet source33 nn0 nn1 packet0 valid0
def packet1 : Packet := ⟨((103:ℚ)/160),((267:ℚ)/400),((5:ℚ)/16),((3:ℚ)/8),((5847195763:ℚ)/10000000000),((386421857:ℚ)/625000000),((3271731921:ℚ)/7120000000),((1799265571:ℚ)/3218750000),((4873244381:ℚ)/5000000000),((616511681:ℚ)/625000000),((2256500263:ℚ)/10000000000),((6929453253:ℚ)/10000000000),((-135637461032129068062998216289195295646139044628482147:ℚ)/463737025260925292968750000000000000000000000000000000),((-2643110892461759100882113:ℚ)/7220000000000000000000000)⟩
theorem valid1 : Valid source33 packet1 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf1 :
    CellBound source33 nn0 nn1 Qcell ((103:ℚ)/160) ((267:ℚ)/400) :=
  cell_of_packet source33 nn0 nn1 packet1 valid1
def packet2 : Packet := ⟨((267:ℚ)/400),((1087:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((3044342589:ℚ)/5000000000),((6303359089:ℚ)/10000000000),((5028342589:ℚ)/10870000000),((29150077267:ℚ)/53400000000),((9693839119:ℚ)/10000000000),((9746488767:ℚ)/10000000000),((2480870833:ℚ)/10000000000),((641594039:ℚ)/1000000000),((-10130067512090746960623576148703949267473200632175907806511:ℚ)/34483558635000000000000000000000000000000000000000000000000),((-682683669341756443690085077:ℚ)/1848320000000000000000000000)⟩
theorem valid2 : Valid source33 packet2 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf2 :
    CellBound source33 nn0 nn1 Qcell ((267:ℚ)/400) ((1087:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet2 valid2
def packet3 : Packet := ⟨((1087:ℚ)/1600),((553:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((6209322763:ℚ)/10000000000),((2055649:ℚ)/3200000),((10177322763:ℚ)/22120000000),((9443747:ℚ)/17392000),((1205629803:ℚ)/1250000000),((2423459781:ℚ)/2500000000),((1336191689:ℚ)/5000000000),((6145792101:ℚ)/10000000000),((-3552441759336394608926003970022651947435570767:ℚ)/12175784968440000000000000000000000000000000000),((-349102357806333845257:ℚ)/946339840000000000000)⟩
theorem valid3 : Valid source33 packet3 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf3 :
    CellBound source33 nn0 nn1 Qcell ((1087:ℚ)/1600) ((553:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet3 valid3
def packet4 : Packet := ⟨((553:ℚ)/800),((45:ℚ)/64),((5:ℚ)/16),((3:ℚ)/8),((3164946997:ℚ)/5000000000),((654438523:ℚ)/1000000000),((5148946997:ℚ)/11250000000),((426759367:ℚ)/790000000),((599993229:ℚ)/625000000),((9645038429:ℚ)/10000000000),((2838327983:ℚ)/10000000000),((5865037233:ℚ)/10000000000),((-238772906274466498000169474849658403686173947952820233:ℚ)/823845863342285156250000000000000000000000000000000000),((-6808540932940861381278573:ℚ)/18483200000000000000000000)⟩
theorem valid4 : Valid source33 packet4 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf4 :
    CellBound source33 nn0 nn1 Qcell ((553:ℚ)/800) ((45:ℚ)/64) :=
  cell_of_packet source33 nn0 nn1 packet4 valid4
def packet5 : Packet := ⟨((45:ℚ)/64),((143:ℚ)/200),((5:ℚ)/16),((3:ℚ)/8),((1290080467:ℚ)/2000000000),((3332404289:ℚ)/5000000000),((189425497:ℚ)/416000000),((15117212867:ℚ)/28125000000),((9558216781:ℚ)/10000000000),((9599891669:ℚ)/10000000000),((149176903:ℚ)/500000000),((696504633:ℚ)/1250000000),((-349695323559426786324259626723899007854880734570803:ℚ)/1214853120000000000000000000000000000000000000000000),((-169931131778733662222252277:ℚ)/462080000000000000000000000)⟩
theorem valid5 : Valid source33 packet5 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf5 :
    CellBound source33 nn0 nn1 Qcell ((45:ℚ)/64) ((143:ℚ)/200) :=
  cell_of_packet source33 nn0 nn1 packet5 valid5
def packet6 : Packet := ⟨((143:ℚ)/200),((1163:ℚ)/1600),((5:ℚ)/16),((3:ℚ)/8),((657085101:ℚ)/1000000000),((6785176129:ℚ)/10000000000),((1053885101:ℚ)/2326000000),((30595528387:ℚ)/57200000000),((9519843613:ℚ)/10000000000),((4779108393:ℚ)/5000000000),((622285377:ℚ)/2000000000),((5264711239:ℚ)/10000000000),((-45994958405944917209362087197388192925939377267826907253:ℚ)/160835244442015000000000000000000000000000000000000000000),((-678452035443153236826889717:ℚ)/1848320000000000000000000000)⟩
theorem valid6 : Valid source33 packet6 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf6 :
    CellBound source33 nn0 nn1 Qcell ((143:ℚ)/200) ((1163:ℚ)/1600) :=
  cell_of_packet source33 nn0 nn1 packet6 valid6
def packet7 : Packet := ⟨((1163:ℚ)/1600),((591:ℚ)/800),((5:ℚ)/16),((3:ℚ)/8),((267649721:ℚ)/400000000),((1726372661:ℚ)/2500000000),((426369721:ℚ)/945600000),((7739117983:ℚ)/14537500000),((4742306471:ℚ)/5000000000),((4759921809:ℚ)/5000000000),((806129637:ℚ)/2500000000),((4940349829:ℚ)/10000000000),((-5642634379070617922469896775455308889027082845568598433:ℚ)/19854517465415040000000000000000000000000000000000000000),((-2227094726618549990399583:ℚ)/6080000000000000000000000)⟩
theorem valid7 : Valid source33 packet7 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf7 :
    CellBound source33 nn0 nn1 Qcell ((1163:ℚ)/1600) ((591:ℚ)/800) :=
  cell_of_packet source33 nn0 nn1 packet7 valid7
def packet8 : Packet := ⟨((591:ℚ)/800),((61:ℚ)/80),((5:ℚ)/16),((3:ℚ)/8),((6811581187:ℚ)/10000000000),((7145970733:ℚ)/10000000000),((10779581187:ℚ)/24400000000),((31677912199:ℚ)/59100000000),((9422991801:ℚ)/10000000000),((9484612947:ℚ)/10000000000),((1706816001:ℚ)/5000000000),((2297654191:ℚ)/5000000000),((-98032840852953256109456636249331636294917307995981649971451:ℚ)/352356225160000000000000000000000000000000000000000000000000),((-667059511270067400902381693:ℚ)/1848320000000000000000000000)⟩
theorem valid8 : Valid source33 packet8 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf8 :
    CellBound source33 nn0 nn1 Qcell ((591:ℚ)/800) ((61:ℚ)/80) :=
  cell_of_packet source33 nn0 nn1 packet8 valid8
def packet9 : Packet := ⟨((61:ℚ)/80),((81:ℚ)/100),((5:ℚ)/16),((3:ℚ)/8),((7052106277:ℚ)/10000000000),((7626397697:ℚ)/10000000000),((1224456253:ℚ)/2880000000),((33119193091:ℚ)/61000000000),((9331481479:ℚ)/10000000000),((4711495903:ℚ)/5000000000),((735446993:ℚ)/2000000000),((1910163861:ℚ)/5000000000),((-4955830681346228813132258073500344876771157738610024487:ℚ)/18518077440000000000000000000000000000000000000000000000),((-17037060155083723:ℚ)/48640000000000000)⟩
theorem valid9 : Valid source33 packet9 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf9 :
    CellBound source33 nn0 nn1 Qcell ((61:ℚ)/80) ((81:ℚ)/100) :=
  cell_of_packet source33 nn0 nn1 packet9 valid9
def packet10 : Packet := ⟨((81:ℚ)/100),(1:ℚ),((5:ℚ)/16),((3:ℚ)/8),((7532615051:ℚ)/10000000000),((4771442753:ℚ)/5000000000),((11500615051:ℚ)/32000000000),((19434328259:ℚ)/32400000000),((9249864861:ℚ)/10000000000),((2332870371:ℚ)/2500000000),((155918519:ℚ)/400000000),((666317269:ℚ)/5000000000),((-3419410413315228684402257542333144636881616130856108221467:ℚ)/14929920000000000000000000000000000000000000000000000000000),((-17743407572354949:ℚ)/48640000000000000)⟩
theorem valid10 : Valid source33 packet10 := by
  constructor <;> (try unfold RatInterval.Contains) <;> decide +kernel
private theorem leaf10 :
    CellBound source33 nn0 nn1 Qcell ((81:ℚ)/100) (1:ℚ) :=
  cell_of_packet source33 nn0 nn1 packet10 valid10
def packet11 : Packet := ⟨(1:ℚ),((69:ℚ)/50),((5:ℚ)/16),((3:ℚ)/8),((9449350429:ℚ)/10000000000),((13362138407:ℚ)/10000000000),((4472450143:ℚ)/14720000000),((50326415221:ℚ)/80000000000),((4638999999:ℚ)/5000000000),(1:ℚ),((1911621469:ℚ)/5000000000),(0:ℚ),((-294026308220352903452042171371789232907486540649658773:ℚ)/1495080960000000000000000000000000000000000000000000000),((-46953851:ℚ)/128000000)⟩
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
end N11Formalization.C450Source33GroupedC22
#check @N11Formalization.C450Source33GroupedC22.bound
#print axioms N11Formalization.C450Source33GroupedC22.valid0
#print axioms N11Formalization.C450Source33GroupedC22.valid1
#print axioms N11Formalization.C450Source33GroupedC22.valid2
#print axioms N11Formalization.C450Source33GroupedC22.valid3
#print axioms N11Formalization.C450Source33GroupedC22.valid4
#print axioms N11Formalization.C450Source33GroupedC22.valid5
#print axioms N11Formalization.C450Source33GroupedC22.valid6
#print axioms N11Formalization.C450Source33GroupedC22.valid7
#print axioms N11Formalization.C450Source33GroupedC22.valid8
#print axioms N11Formalization.C450Source33GroupedC22.valid9
#print axioms N11Formalization.C450Source33GroupedC22.valid10
#print axioms N11Formalization.C450Source33GroupedC22.valid11
#print axioms N11Formalization.C450Source33GroupedC22.bound
#print axioms N11Formalization.C450Source33GroupedC22.endpoint_checks
